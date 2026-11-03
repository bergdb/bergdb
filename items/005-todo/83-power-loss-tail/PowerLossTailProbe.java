package bergdb.core;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.RandomAccessFile;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.concurrent.atomic.AtomicLong;

import bergdb.common.Bytes;
import bergdb.dag.Keys;
import bergdb.dag.Node;
import bergdb.dag.ValueNode;
import bergdb.pub.util.SyncLevel;
import bergdb.storage.RecoverableStream;
import bergdb.stream.FileStream;
import bergdb.stream.FileStreamIo;

/** Item-local experiment, bergdb 005-83, "Power-loss tail experiment". */
public final class PowerLossTailProbe {
    private static final int BUFFER_SIZE = 10_000_000;
    private static final int BUFFER_TIME = 60_000; // Batch deterministically; forces stay on.
    private static final int RECOVERY_WRITE_LIMIT = 2_500_000;
    private static final List<Row> rows = new ArrayList<Row>();
    private static Path output;
    private static String filter;

    record Scenario(String name, int startupDistance, int seedValueSize, int tailValueSize) {}
    record Tx(long time, long pos, long last, Map<String, byte[]> values) {}
    record Capture(Map<String, byte[]> files, Map<String, byte[]> forced, long from, long to) {}
    record Input(String name, String kind, Map<String, byte[]> files, long damageStart,
            int damageBytes, Tx target) {}

    /** These are real force calls. The snapshots are taken after write and before force. */
    static final class CaptureIo extends FileStreamIo {
        final Path directory;
        final Map<String, byte[]> forced = new TreeMap<String, byte[]>();
        final Set<String> names = new TreeSet<String>();
        final List<Capture> captures = new ArrayList<Capture>();
        volatile boolean armed;
        int fileForces, directoryForces;

        CaptureIo(Path directory) { this.directory = directory.toAbsolutePath(); }

        @Override protected synchronized void forceFile(File file, RandomAccessFile handle)
                throws IOException {
            super.forceFile(file, handle);
            forced.put(file.getName(), Files.readAllBytes(file.toPath()));
            fileForces++;
        }

        @Override protected synchronized void forceDirectory(File dir) throws IOException {
            super.forceDirectory(dir);
            if (dir.toPath().toAbsolutePath().equals(directory)) {
                names.clear();
                try (var paths = Files.list(directory)) {
                    paths.filter(p -> p.toString().endsWith(".bergdb"))
                            .forEach(p -> names.add(p.getFileName().toString()));
                }
            }
            directoryForces++;
        }

        Map<String, byte[]> durable() {
            Map<String, byte[]> result = new TreeMap<String, byte[]>();
            for (String name : names) {
                result.put(name, forced.getOrDefault(name, new byte[0]).clone());
            }
            return result;
        }

        @Override protected synchronized void write(File file, RandomAccessFile handle,
                byte[] bytes, int offset, int length) throws IOException {
            long from = fileStart(file.getName()) + handle.getFilePointer();
            super.write(file, handle, bytes, offset, length);
            if (armed) {
                require(names.contains(file.getName()), "append before its name was forced");
                Map<String, byte[]> before = durable();
                Map<String, byte[]> image = copy(before);
                image.put(file.getName(), Files.readAllBytes(file.toPath()));
                require(end(before) == from, "write did not follow the forced prefix");
                preservesForced(before, image);
                captures.add(new Capture(image, before, from, from + length));
            }
        }
    }

    /** Count production recovery writes; bound pathological corrupt-size experiments. */
    static final class CountIo extends FileStreamIo {
        final AtomicLong bytes = new AtomicLong();
        volatile boolean guardFired;
        @Override protected void write(File file, RandomAccessFile handle, byte[] data,
                int offset, int length) throws IOException {
            if (bytes.get() + length > RECOVERY_WRITE_LIMIT) {
                guardFired = true;
                throw new IOException("PROBE WRITE LIMIT: " + RECOVERY_WRITE_LIMIT);
            }
            super.write(file, handle, data, offset, length);
            bytes.addAndGet(length);
        }
    }

    static final class Row {
        String scenario, image, kind, order, stage = "start", outcome = "", error = "";
        String activeAfterError = "", postErrorWrite = "";
        long acknowledged, forcedEnd, capturedEnd, damageStart;
        int damageBytes;
        long recoveredTime = -1, recoveryWrites, growthAfterStart, logicalGrowth;
        boolean continued;
        List<String> fields() {
            return List.of(scenario, image, kind, order, Long.toString(acknowledged),
                    Long.toString(forcedEnd), Long.toString(capturedEnd),
                    Long.toString(damageStart), Integer.toString(damageBytes),
                    Long.toString(recoveredTime), stage, outcome,
                    Long.toString(recoveryWrites), Long.toString(growthAfterStart), Long.toString(logicalGrowth),
                    activeAfterError, postErrorWrite, Boolean.toString(continued), error);
        }
    }

    public static void main(String[] args) throws Exception {
        output = Path.of(args[0]).toAbsolutePath();
        filter = args.length > 1 ? args[1] : "";
        Files.createDirectories(output);
        List<Scenario> scenarios = List.of(new Scenario("replay", 50_000_000, 1024, 8000),
                new Scenario("bounded", 2048, 1024, 8000), new Scenario("meta", 2048, 6000, 8000),
                new Scenario("lazy", 2048, 180000, 20000));
        for (Scenario scenario : scenarios) {
            for (int seed : new int[] {11, 29}) runSource(scenario, seed);
        }
        Path results = output.resolve("results.tsv");
        try (PrintWriter out = new PrintWriter(Files.newBufferedWriter(results))) {
            out.println("scenario\timage\tkind\torder\tack_time\tforced_end\tcaptured_end"
                    + "\tdamage_start\tdamage_bytes\trecovered_time\tstage\toutcome"
                    + "\trecovery_writes\tgrowth_after_start\tlogical_growth\tactive_after_error"
                    + "\tpost_error_write\tcontinued\terror");
            for (Row row : rows) out.println(String.join("\t", row.fields()));
        }
        long controls = rows.stream().filter(r -> r.kind.equals("control")).count();
        long controlFailures = rows.stream().filter(r -> r.kind.equals("control")
                && !r.outcome.equals("RECOVERED")).count();
        long negatives = rows.stream().filter(r -> r.kind.equals("negative")).count();
        long missedNegatives = rows.stream().filter(r -> r.kind.equals("negative")
                && !r.outcome.equals("ACK_LOSS")).count();
        long holes = rows.stream().filter(r -> r.kind.equals("hole")).count();
        long holeFailures = rows.stream().filter(r -> r.kind.equals("hole")
                && !r.outcome.equals("RECOVERED")).count();
        System.out.println("PROBE COMPLETE rows=" + rows.size() + " controls=" + controls
                + " control_failures=" + controlFailures + " negatives=" + negatives
                + " missed_negatives=" + missedNegatives + " hole_checks=" + holes
                + " hole_failures=" + holeFailures + " results=" + results);
        require(controlFailures == 0, "undamaged or prefix control failed");
        require(missedNegatives == 0, "oracle missed deliberately lost acknowledged data");
        require(rows.stream().noneMatch(r -> r.outcome.equals("PROBE_LIMIT")),
                "probe guard fired: a case needs isolation");
        if (Boolean.getBoolean("requireRecovery")) {
            require(holeFailures == 0, "recovery does not tolerate the injected tail holes");
        }
    }

    private static DbBuilder builder(Path dir, FileStreamIo io, Scenario scenario,
            CoreTestClock clock) throws IOException {
        return Db.builder().testId().noEvict().retainForever().maxNodeSize8()
                .startupDistance(scenario.startupDistance()).clock(clock)
                .stream("main", new FileStream(dir.toFile(), io), BUFFER_SIZE, BUFFER_TIME);
    }

    private static void runSource(Scenario scenario, int seed) throws Exception {
        String name = scenario.name() + "-s" + seed;
        if (filter.contains("/") && !filter.startsWith(name + "/")) return;
        Path dir = output.resolve(name).resolve("source");
        Files.createDirectories(dir);
        CaptureIo io = new CaptureIo(dir);
        CoreTestClock clock = new CoreTestClock();
        Db db = builder(dir, io, scenario, clock).start();
        List<Tx> history = new ArrayList<Tx>();
        Random random = new Random(seed);
        try {
            for (int i = 0; i < 24; i++) {
                Map<String, byte[]> values = new LinkedHashMap<String, byte[]>();
                values.put("/base/" + i, value(random, scenario.seedValueSize()));
                if (i == 0) {
                    values.put("/anchor", new byte[] {9, 8, 7, 6});
                    values.put("/counter", text("0"));
                }
                history.add(put(db, clock, 100 + i, values));
            }
            db.sync(SyncLevel.ORDINARY);
            long acknowledged = history.get(history.size() - 1).time();
            long acknowledgedEnd = end(io.durable());
            io.armed = true;
            for (int i = 0; i < 12; i++) {
                // A later transaction actually computes from the preceding one's value.
                int counter = Integer.parseInt(DbUtil.getString(db, "/counter"));
                Map<String, byte[]> values = new LinkedHashMap<String, byte[]>();
                values.put("/counter", text(Integer.toString(counter + 1)));
                values.put("/tail/" + i, value(random, scenario.tailValueSize() + i * 13));
                history.add(put(db, clock, 200 + i, values));
            }
            // Requests the flush. Every captured image precedes this sync's completion.
            db.sync(SyncLevel.ORDINARY);
            io.armed = false;
            Capture cap = null;
            for (Capture candidate : io.captures) {
                long complete = history.stream().filter(t -> t.time() > acknowledged
                        && t.pos() >= candidate.from() && t.last() < candidate.to()).count();
                if (complete >= 2) cap = candidate;
            }
            require(cap != null, "need multiple complete records in one unforced write");
            final Capture selected = cap;
            require(cap.from() >= acknowledgedEnd, "captured write overlaps synced bytes");
            List<Tx> targets = history.stream().filter(t -> t.time() > acknowledged
                    && t.pos() >= selected.from() && t.last() < selected.to()).toList();
            require(targets.size() >= 2, "need multiple complete records in one unforced write");
            Tx first = targets.get(0);
            byte[] record = db.internal().nodeStream().readTransBytes(first.pos());
            StoredTrans stored = StoredTrans.parse(first.pos(), record);
            ValueNode blob = Arrays.stream(stored.nodes).map(n -> n.getNode())
                    .filter(n -> n instanceof ValueNode && ((ValueNode) n).value != null
                            && ((ValueNode) n).value.length > 4096)
                    .map(n -> (ValueNode) n).findFirst().orElseThrow();
            if (scenario.name().equals("lazy")) {
                require(first.last() < (cap.to() - 128) / 200000 * 200000,
                        "lazy scenario did not retain a later complete meta block");
            }
            restore(cap.forced(), output.resolve(name).resolve("forced"));
            restore(cap.files(), output.resolve(name).resolve("capture"));
            long payload = RecoverableStream.getSpos(blob.getSpos(), 24 + 64);
            List<Input> cases = new ArrayList<Input>();
            cases.add(new Input("full", "control", copy(cap.files()), -1, 0, first));
            addPrefix(cases, "lost-write", cap, cap.from(), first);
            addPrefix(cases, "prefix-record-boundary", cap, first.pos(), first);
            addPrefix(cases, "prefix-header-1", cap, first.pos() + 1, first);
            addPrefix(cases, "prefix-header-3", cap, first.pos() + 3, first);
            addPrefix(cases, "prefix-body", cap, payload, first);
            addPrefix(cases, "prefix-before-marker", cap, first.last(), first);
            addHole(cases, "zero-record-size", cap, first.pos(), 4, first);
            addHole(cases, "zero-record-time", cap,
                    RecoverableStream.getSpos(first.pos(), 8), 8, first);
            addHole(cases, "zero-node-size", cap, blob.getSpos(), 4, first);
            addHole(cases, "zero-node-checksum", cap,
                    RecoverableStream.getSpos(blob.getSpos(), 6), 2, first);
            addHole(cases, "zero-value-512", cap, payload, 512, first);
            long page = (cap.from() + 4095) / 4096 * 4096;
            addHole(cases, "zero-page-4096", cap, page, 4096, first);
            addHole(cases, "zero-commit-marker", cap, first.last(), 1, first);
            Map<String, byte[]> grown = copy(cap.files());
            int oldSize = intAt(grown, first.pos());
            setInt(grown, first.pos(), oldSize ^ (1 << 20));
            cases.add(new Input("size-grow-bitflip", "corrupt-input", grown,
                    first.pos(), 4, first));
            // Outside the fault model: proves that the acknowledged-prefix oracle fires.
            cases.add(new Input("lost-ack-negative", "negative",
                    prefix(cap.files(), Db.CREATION_LENGTH), 0, 0, first));
            Path manifest = output.resolve(name).resolve("capture.txt");
            Files.writeString(manifest, "scenario=" + scenario.name() + " seed=" + seed
                    + " startupDistance=" + scenario.startupDistance() + " maxNodeSize=8"
                    + " bufferSize=" + BUFFER_SIZE + " bufferTime=" + BUFFER_TIME
                    + " retain=forever eviction=off\nack_time=" + acknowledged
                    + " ack_end=" + acknowledgedEnd + " forced_end=" + end(cap.forced())
                    + " capture_from=" + cap.from() + " capture_to=" + cap.to()
                    + " complete_tail_records=" + targets.size() + " target_time=" + first.time()
                    + " target_pos=" + first.pos() + " target_blob=" + blob.getSpos()
                    + " original_node_checksum=" + unsignedShortAt(cap.files(),
                            RecoverableStream.getSpos(blob.getSpos(), 6))
                    + " last_complete_meta=" + ((cap.to() - 128) / 200000 * 200000)
                    + " target_before_last_meta=" + (first.last() < (cap.to() - 128) / 200000 * 200000)
                    + "\nfile_forces=" + io.fileForces + " directory_forces=" + io.directoryForces
                    + " forced_sha256=" + hash(cap.forced()) + "\n");
            try (PrintWriter txs = new PrintWriter(Files.newBufferedWriter(
                    output.resolve(name).resolve("transactions.tsv")))) {
                txs.println("time\tposition\tlast\tkeys\tvalues_sha256");
                for (Tx tx : history) txs.println(tx.time() + "\t" + tx.pos() + "\t" + tx.last()
                        + "\t" + String.join(",", tx.values().keySet()) + "\t" + hash(tx.values()));
            }
            db.close();
            db = null;
            for (Input input : cases) {
                String id = name + "/" + input.name();
                if (!filter.isEmpty() && !id.contains(filter)) continue;
                if (!input.kind().equals("negative")) preservesForced(cap.forced(), input.files());
                Path image = output.resolve(name).resolve(input.name()).resolve("image");
                restore(input.files(), image);
                runCase(name, scenario, history, acknowledged, cap, input, "values");
                if (input.kind().equals("hole")) {
                    runCase(name, scenario, history, acknowledged, cap, input, "transaction");
                }
            }
        } finally {
            io.armed = false;
            if (db != null) db.close();
        }
    }

    private static void runCase(String name, Scenario scenario, List<Tx> history,
            long acknowledged, Capture cap, Input input, String order) throws Exception {
        Row r = new Row();
        r.scenario = name; r.image = input.name(); r.kind = input.kind(); r.order = order;
        r.acknowledged = acknowledged; r.forcedEnd = end(cap.forced());
        r.capturedEnd = end(input.files()); r.damageStart = input.damageStart();
        r.damageBytes = input.damageBytes();
        Path dir = output.resolve(name).resolve(input.name()).resolve(order);
        restore(input.files(), dir);
        CountIo io = new CountIo();
        Db db = null;
        Throwable failure = null;
        long before = end(input.files());
        try {
            CoreTestClock clock = new CoreTestClock(); clock.setTime(10000);
            db = builder(dir, io, scenario, clock).build();
            db.start();
            r.recoveredTime = db.lookupTime(Long.MAX_VALUE);
            synchronized (db.internal().getWriteLock()) {
                r.logicalGrowth = db.internal().nodeStream().getLength() - before;
            }
            r.stage = "acknowledged-prefix";
            if (r.recoveredTime < acknowledged) {
                r.outcome = "ACK_LOSS";
                throw new AssertionError("acknowledged " + acknowledged + ", recovered " + r.recoveredTime);
            }
            require(history.stream().anyMatch(t -> t.time() == r.recoveredTime),
                    "recovered time does not name a known transaction");
            r.stage = "sync-recovery";
            db.sync(SyncLevel.ORDINARY);
            r.recoveryWrites = io.bytes.get();
            r.growthAfterStart = diskEnd(dir) - before;
            if (order.equals("transaction") && input.target().time() <= r.recoveredTime) {
                r.stage = "getTrans-target";
                db.getTrans(input.target().pos());
            }
            r.stage = "values";
            checkValues(db, history, r.recoveredTime);
            r.stage = "transactions";
            for (Tx tx : history) if (tx.time() <= r.recoveredTime) {
                require(db.getTrans(tx.pos()).tt == tx.time(), "wrong transaction time at " + tx.pos());
            }
            // Close before continuing so even queued recovery padding is measured. sync()
            // only waits for the last committed transaction, which may precede that padding.
            r.stage = "close-recovery";
            db.close(); db = null;
            r.recoveryWrites = io.bytes.get();
            r.growthAfterStart = diskEnd(dir) - before;
            r.stage = "reopen-recovery";
            CoreTestClock restartClock = new CoreTestClock(); restartClock.setTime(10000);
            db = builder(dir, new FileStreamIo(), scenario, restartClock).start();
            require(db.lookupTime(Long.MAX_VALUE) == r.recoveredTime, "recovery changed at second start");
            r.stage = "continue";
            Tx fresh = put(db, restartClock, 20000, Map.of("/after-power-loss", text("continued")));
            db.sync(SyncLevel.ORDINARY);
            db.close(); db = null;
            CoreTestClock nextClock = new CoreTestClock(); nextClock.setTime(30000);
            db = builder(dir, new FileStreamIo(), scenario, nextClock).start();
            require(Arrays.equals(text("continued"), DbUtil.get(db, "/after-power-loss")),
                    "fresh transaction lost after sync and reopen");
            require(db.getTrans(fresh.pos()).tt == fresh.time(), "fresh transaction not readable");
            checkValues(db, history, r.recoveredTime);
            r.continued = true;
            r.stage = "complete";
            r.outcome = "RECOVERED";
        } catch (Throwable e) {
            failure = e;
            if (r.outcome.isEmpty()) r.outcome = io.guardFired ? "PROBE_LIMIT" : "RECOVERY_FAILURE";
            r.error = describe(e);
            if (db != null) r.activeAfterError = Boolean.toString(db.internal().isActive());
            if (order.equals("transaction") && r.stage.equals("getTrans-target")
                    && db != null && db.internal().isActive()) {
                try {
                    db.execute(db.trans().put("/after-detected-corruption", "accepted").build());
                    db.sync(SyncLevel.ORDINARY);
                    r.postErrorWrite = "accepted";
                } catch (Throwable post) { r.postErrorWrite = "refused:" + describe(post); }
            }
        } finally {
            if (r.stage.equals("start") || r.stage.equals("acknowledged-prefix")
                    || r.stage.equals("sync-recovery")) r.recoveryWrites = io.bytes.get();
            if (db != null) {
                try { db.close(); } catch (Throwable closing) {
                    if (failure != null) failure.addSuppressed(closing);
                    else throw closing;
                }
            }
            if (!r.continued && r.postErrorWrite.isEmpty()) {
                r.recoveryWrites = io.bytes.get();
                r.growthAfterStart = diskEnd(dir) - before;
            }
            try (PrintWriter trace = new PrintWriter(Files.newBufferedWriter(dir.resolve("trace.txt")))) {
                trace.println(String.join("\t", r.fields()));
                if (failure != null) failure.printStackTrace(trace);
            }
            rows.add(r);
            System.out.println(name + "/" + input.name() + " " + order + " "
                    + r.outcome + " stage=" + r.stage + " recovered=" + r.recoveredTime
                    + " recoveryWrites=" + r.recoveryWrites + " active=" + r.activeAfterError);
        }
    }

    private static Tx put(Db db, CoreTestClock clock, long time, Map<String, byte[]> values) {
        clock.setTime(time);
        Trans.Builder builder = db.trans();
        values.forEach((key, value) -> builder.put(key, value));
        Trans tx = builder.build(); db.execute(tx);
        return new Tx(tx.tt, tx.tpos, tx.lastPos, new TreeMap<String, byte[]>(values));
    }

    private static void checkValues(Db db, List<Tx> history, long recoveredTime) {
        Set<String> keys = new TreeSet<String>();
        history.forEach(t -> keys.addAll(t.values().keySet()));
        List<Long> times = new ArrayList<Long>(); times.add(recoveredTime);
        history.stream().filter(t -> t.time() <= recoveredTime).forEach(t -> times.add(t.time()));
        for (long time : times) {
            Map<String, byte[]> model = new TreeMap<String, byte[]>();
            history.stream().filter(t -> t.time() <= time).forEach(t -> model.putAll(t.values()));
            for (String key : keys) require(Arrays.equals(model.get(key), DbUtil.get(db, time, key)),
                    "value differs from transaction prefix: " + key + " at " + time);
        }
    }

    private static void addPrefix(List<Input> cases, String name, Capture cap, long cut, Tx target) {
        require(cut >= cap.from() && cut <= cap.to(), "prefix cut outside unforced write");
        cases.add(new Input(name, "control", prefix(cap.files(), cut), cut, 0, target));
    }

    private static void addHole(List<Input> cases, String name, Capture cap, long pos,
            int length, Tx target) {
        require(pos >= cap.from() && pos + length <= cap.to(), "hole outside unforced write");
        Map<String, byte[]> files = copy(cap.files());
        int changed = 0;
        for (int i = 0; i < length; i++) { if (at(files, pos + i) != 0) changed++; set(files, pos + i, (byte) 0); }
        require(changed > 0, "hole did not change bytes: " + name);
        cases.add(new Input(name, "hole", files, pos, length, target));
    }

    private static Map<String, byte[]> copy(Map<String, byte[]> files) {
        Map<String, byte[]> result = new TreeMap<String, byte[]>();
        files.forEach((name, bytes) -> result.put(name, bytes.clone())); return result;
    }
    private static long fileStart(String name) { return Long.parseLong(name.substring(0, 14)) * 100000L; }
    private static long end(Map<String, byte[]> files) {
        return files.entrySet().stream().mapToLong(e -> fileStart(e.getKey()) + e.getValue().length).max().orElse(0);
    }
    private static Map<String, byte[]> prefix(Map<String, byte[]> files, long cut) {
        Map<String, byte[]> result = new TreeMap<String, byte[]>();
        files.forEach((name, bytes) -> {
            long first = fileStart(name);
            if (first <= cut) result.put(name, Arrays.copyOf(bytes,
                    (int) Math.max(0, Math.min(bytes.length, cut - first))));
        }); return result;
    }
    private static byte at(Map<String, byte[]> files, long pos) {
        for (var e : files.entrySet()) {
            long offset = pos - fileStart(e.getKey());
            if (offset >= 0 && offset < e.getValue().length) return e.getValue()[(int) offset];
        } throw new AssertionError("no byte at " + pos);
    }
    private static void set(Map<String, byte[]> files, long pos, byte value) {
        for (var e : files.entrySet()) {
            long offset = pos - fileStart(e.getKey());
            if (offset >= 0 && offset < e.getValue().length) { e.getValue()[(int) offset] = value; return; }
        } throw new AssertionError("no byte to change at " + pos);
    }
    private static int intAt(Map<String, byte[]> files, long pos) {
        byte[] b = new byte[4]; for (int i = 0; i < 4; i++) b[i] = at(files, RecoverableStream.getSpos(pos, i));
        return Bytes.bytesToIntLE(b, 0);
    }
    private static int unsignedShortAt(Map<String, byte[]> files, long pos) {
        return (at(files, pos) & 255) | (at(files, RecoverableStream.getSpos(pos, 1)) & 255) << 8;
    }
    private static void setInt(Map<String, byte[]> files, long pos, int value) {
        byte[] b = new byte[4]; Bytes.intToBytesLE(value, b, 0);
        for (int i = 0; i < 4; i++) set(files, RecoverableStream.getSpos(pos, i), b[i]);
    }
    private static void preservesForced(Map<String, byte[]> forced, Map<String, byte[]> image) {
        forced.forEach((name, bytes) -> {
            byte[] actual = image.get(name);
            require(actual != null && actual.length >= bytes.length, "lost forced name/bytes: " + name);
            for (int i = 0; i < bytes.length; i++) require(bytes[i] == actual[i], "changed forced byte: " + name + ":" + i);
        });
    }
    private static void restore(Map<String, byte[]> files, Path dir) throws IOException {
        require(!Files.exists(dir), "refuse to overwrite experiment directory " + dir);
        Files.createDirectories(dir);
        for (var e : files.entrySet()) Files.write(dir.resolve(e.getKey()), e.getValue());
    }
    private static long diskEnd(Path dir) throws IOException {
        try (var paths = Files.list(dir)) {
            return paths.filter(p -> p.toString().endsWith(".bergdb")).mapToLong(p -> {
                try { return fileStart(p.getFileName().toString()) + Files.size(p); }
                catch (IOException e) { throw new RuntimeException(e); }
            }).max().orElse(0);
        }
    }
    private static byte[] value(Random random, int size) { byte[] b = new byte[size]; random.nextBytes(b); return b; }
    private static byte[] text(String s) { return s.getBytes(StandardCharsets.UTF_8); }
    private static String hash(Map<String, byte[]> files) throws Exception {
        MessageDigest d = MessageDigest.getInstance("SHA-256");
        for (var e : files.entrySet()) { d.update(text(e.getKey())); d.update(e.getValue()); }
        return java.util.HexFormat.of().formatHex(d.digest());
    }
    private static String describe(Throwable e) {
        StringBuilder s = new StringBuilder();
        for (Throwable t = e; t != null; t = t.getCause()) {
            if (s.length() > 0) s.append(" <- ");
            s.append(t.getClass().getSimpleName()).append(": ").append(t.getMessage());
        }
        return s.toString().replace('\t', ' ').replace('\n', ' ').replace('\r', ' ');
    }
    private static void require(boolean condition, String message) {
        if (!condition) throw new AssertionError(message);
    }
}
