package bergdb.core;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Map;
import java.util.TreeMap;

import bergdb.stream.FileStream;

/** Recheck 012-14, section 6.6's original image on a fresh copy only. */
public final class RefusedStartProbe {
    public static void main(String[] args) throws Exception {
        Path source = Path.of(args[0]), destination = Path.of(args[1]);
        if (Files.exists(destination)) throw new IllegalArgumentException("destination exists");
        Map<String, byte[]> before = files(source);
        Files.createDirectories(destination);
        for (var entry : before.entrySet()) Files.write(destination.resolve(entry.getKey()), entry.getValue());
        var io = new PowerLossTailProbe.CountIo();
        Db db = Db.builder().testId().noEvict().maxNodeSize8().clock(new CoreTestClock())
                .mainStream(new FileStream(destination.toFile(), io)).build();
        Throwable failure = null;
        boolean opened = false;
        try { db.start(); opened = true; }
        catch (Throwable e) { failure = e; }
        finally { db.close(); }
        Map<String, byte[]> after = files(destination);
        for (var entry : before.entrySet()) {
            byte[] actual = after.get(entry.getKey());
            if (actual == null || actual.length < entry.getValue().length
                    || !Arrays.equals(entry.getValue(), Arrays.copyOf(actual, entry.getValue().length))) {
                throw new AssertionError("existing bytes changed: " + entry.getKey());
            }
        }
        System.out.println("opened=" + opened + " originalBytes=" + length(before)
                + " finalBytes=" + length(after) + " written=" + io.bytes.get()
                + " growth=" + (length(after)-length(before)) + " originalBytesPreserved=true"
                + " guardFired=" + io.guardFired);
        if (failure != null) failure.printStackTrace(System.out);
        if (io.guardFired) throw new AssertionError("probe write limit fired");
    }

    private static Map<String, byte[]> files(Path dir) throws Exception {
        Map<String, byte[]> result = new TreeMap<String, byte[]>();
        try (var paths = Files.list(dir)) {
            for (Path path : paths.filter(p -> p.toString().endsWith(".bergdb")).toList()) {
                result.put(path.getFileName().toString(), Files.readAllBytes(path));
            }
        }
        return result;
    }
    private static long length(Map<String, byte[]> files) {
        return files.values().stream().mapToLong(b -> b.length).sum();
    }
}
