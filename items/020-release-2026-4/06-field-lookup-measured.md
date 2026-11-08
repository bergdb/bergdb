# 020-06 A field's lookup in an object's bytes, measured

Created 2026-11-08 by Frans Lundberg. Status: done. How fast a field is
found in a stored object's bytes, in the format of 020-05's option (f)
(DbObject's table with Binson's values): a linear scan of compact hashes
at the start of the bytes against a binary search on the names, and close
variants, in Java and C, hot and cold, for objects of 1 to 100 fields;
the collisions of the hash functions on real field names; the cache lines
each variant touches; a recommendation for the format.

Frans, 2026-11-08, 09:32: "Start another subagent at XHigh to
investigate the performance of lookup scans of 16-bit hashes vs binary
search for fields as above. I think this should be measured. Scanning
only the beginning of the value bytes to find a field is more
cache-aware. A linear search using compact hashes could be faster than
binary search. We will see. Normally, we have fewer than 100 fields of an
object. This can be assumed. This is recommanded by Binson and for actual
object in object-oriented languages, we typically have less than 20
fields, I think."

How each fact is known: **run** with a label means a program's output, in
`/Users/f/fl/bench/006-15/020-06/out/` (section 16): J, Java, runs 1 to
3; J2, Java, runs 4 and 5 (sections 9 and 12); C, C, runs 1 to 3; T, the
bytes each lookup reads, traced; K, the hash collisions. **code** means
read in the source named (BergDB at `37e8db7`). All times are ns per
lookup, the median of the runs' medians.


## 1. In short

* **Frans's guess holds.** A scan of 16-bit hashes at the start of the
  bytes (H16) is faster than a binary search on the names (B) from 1 to
  100 fields, hot and cold, in Java and C, but in two corners (below).
  Up to 20 fields, the typical objects, hot: hits 1.1 to 1.5 times faster
  in Java (27 against 35 ns at 8 fields, 31 against 46 at 20), 1.7 to 1.9
  times in C (19 against 32, 22 against 41); misses 2.4 to 3.1 times (8
  against 26 ns, 13 against 33).
* **Cold, the cache argument shows on misses.** H16 reads 1.3 to 1.6
  cache lines of 64 bytes for a miss at 8 to 20 fields, B 2.8 to 4.5 (T);
  a cold miss, one lookup at a time, takes 148 to 153 ns against 217 to
  296 (J). A hit needs the field's own line in any layout, so it gains
  less: 201 against 224 ns at 8 fields, 250 against 306 at 20, 335
  against 402 at 100.
* **Hot, it is branches and loop length.** A scalar scan costs about 0.6
  ns a hash in Java: at 100 fields H16 ties B on hits (59 and 60 ns) and
  loses on misses (65 against 48). A scan of four hashes per 64-bit read
  (H16w) wins everywhere: 44 and 32 ns at 100 fields; in C a NEON scan,
  12 ns per miss at 100 fields.
* **Where B wins**: a hot miss from about 70 fields against a scalar scan
  in Java, and the index case (one field looked up in every object of a
  class, so that the branches are predicted), hot, from about 50 fields.
  The word scan is ahead there or within 4 ns.
* **Hash width: 16 bits.** 8 bits saves a byte per field and is as fast
  up to about 32 fields; above, its false matches (a name compared for
  nothing, a cache line more when cold) cost: 0.37 per miss at 100
  fields, a cold miss 236 against 195 ns.
* **Hash function: one over the whole name.** Today's (length, first and
  last char) takes 2,145 of the 65,536 values on 16,944 JDK field names;
  half of the 20-field objects have two names with one hash
  (`majorTickSpacing`, `minorTickSpacing`). FNV-1a folded to 16 bits is
  as good as random: at most 1.6 false compares per 1,000 lookups up to
  100 fields (K).
* **From a Java `String`**, the API case, the hash costs: FNV-1a over the
  chars adds 15 to 19 ns per lookup (hot, 1 to 20 fields), `getBytes`
  and FNV-1a 23 to 26, today's O(1) hash 1 to 4, the cached
  `String.hashCode` 0 to 3. A key held as bytes and hash, as an index
  function holds it, costs nothing.
* **Recommended for (f)** (section 14): after the count, n 16-bit
  FNV-1a hashes of the UTF-8 names, then the table of offsets; a lookup
  scans the hashes and compares the name where a hash matches; no binary
  search. The cost: 2 bytes a field, 6.6 % of a 20-field object here,
  `Payment` 41 bytes instead of 35.


## 2. The question and the method

The question: in the format "as above", the coordinator's sketch in
006-15, section 1, carried out in 020-05 as option (f), is a field found
faster by a linear scan of compact hashes stored at the start of the
object, or by a binary search on the names through the table of offsets?
And which hash width and function? Frans: objects have fewer than 100
fields, typically under 20.

Measured: the lookup alone, a function from (the bytes, the object's
position, the wanted name) to the position of the field's value, or −1;
the variants and layouts of section 3; 1, 2, 4, 8, 12, 16, 20, 32, 50
and 100 fields; hits on a uniform field and misses (a name not in the
object); four cache states and an index case (section 4); the wanted name
precomputed (its UTF-8 bytes and hash) or given as a Java `String`
(section 10); Java and, at 8, 20 and 100 fields, C. Then, without timing:
the bytes and cache lines each lookup reads (T), and the collisions of
five hash functions on real name sets (K).

Not measured: BergDB itself. No code in `java/` was run or changed;
today's reader parses the whole object (020-05, section 6.1), so these
are the times of a reader that does not exist yet.


## 3. The layouts and the lookups

An object as in 020-05's (f): a type byte that gives the width w of the
offsets (1, 2 or 4 bytes, the smallest that fits), the count, a table,
then the fields in the order of their names' unsigned UTF-8 bytes, each a
name length (1 byte), the name and a value in Binson's encoding. In the
test the type byte is 0x51, 0x52 or 0x54 (a stand-in for (f)'s 0x48 to
0x4a), the count 1 byte, and the table holds each field's start from the
fields' start, as the sketch's example (offsets 0, 10, 21); (f) stores
each field's end, which changes no read: field i starts at end i − 1. The
layouts differ in the table only:

    O     type count off[n]            fields    variants B, L
    H16   type count h16[n] off[n]     fields    variants H16, H16w (C: H16v)
    H8    type count h8[n] off[n]      fields    variants H8, H8w (C: H8v)
    D     type count (h16 off32)[n]    fields    variant D, today's table
    H16i  type count (h16 off)[n]      fields    variant H16i (section 12)
    field = nameLen(1) name value        off: w bytes; off32: from the object's start

`Payment` (020-05, section 3) in each, as run (`Payment.java`):

    O, 35 bytes:
      51 03  00 0a 15                    w = 1, 3 fields; offsets 0, 10, 21
      06 616d6f756e74  11 f401           "amount" 500
      04 66726f6d      14 04 31303031    "from" "1001"
      02 746f          14 04 31303032    "to" "1002"
    H16, 41 bytes:
      51 03  cc39 b815 610a  00 0a 15    hashes 0x39cc 0x15b8 0x0a61, offsets
      06 616d6f756e74 ...                the fields as in O
    H8, 38 bytes:
      51 03  f5 ad 6b  00 0a 15  06 ...  8-bit hashes, offsets, fields
    D, 50 bytes:
      54 03  391c 14000000  7d1b 1e000000  131d 29000000  06 ...
                                         today's hash and the offset from the
                                         object's start, per field
    H16i, 41 bytes:
      51 03  cc39 00  b815 0a  610a 15  06 ...

The lookups (code: `Lookup.java`, `lookup.c`):

* **B**: a binary search; a probe reads `off[mid]` and the name there,
  compares it with the wanted one as unsigned bytes, and goes left or
  right: at most ⌈log2(n + 1)⌉ probes, 7 at 100 fields.
* **L**: a linear scan of the names in order: reads `off[i]` and the
  name's first byte; skips smaller ones, stops at a greater one (a miss);
  on an equal first byte compares the name.
* **H16**: for each i, if `h16[i]` equals the wanted hash, reads `off[i]`
  and compares the name (length, then bytes). A miss reads the 2n hash
  bytes and nothing else (but for false matches).
* **H16w**: the same, four hashes per 64-bit read: XOR with the hash in
  every lane, the zero-lane test `(x − 0x0001…) & ~x & 0x8000…`, each
  flagged lane checked exactly. In C, **H16v**: NEON, eight hashes per
  128-bit compare.
* **H8, H8w, H8v**: as H16 with 8-bit hashes; eight per 64-bit read,
  sixteen per NEON compare.
* **D**: as H16 over today's 6-byte entries (020-05, section 3: hash
  int16, offset int32), with today's hash.
* **H16T**: H16 with today's hash instead of FNV-1a (section 11).

A name is compared by a byte loop in Java (in a trial, `Arrays.equals`
and `Arrays.compareUnsigned` were 0 to 11 ns slower on these short names,
and a 64-bit-word compare the same as the loop), by `memcmp` in C.

The hashes (K; code: `Lookup.java`):

* **today**: `(len + 23 * name[0] + 43 * name[len - 1]) & 0xffff`, as
  `DbObject.hash` over UTF-16 units (the same over UTF-8 bytes for ASCII
  names, all names here); 8 bits: the low byte.
* **FNV-1a**: 32-bit FNV-1a over the UTF-8 bytes, folded:
  `h16 = (h ^ (h >>> 16)) & 0xffff`, `h8 = (h16 ^ (h16 >>> 8)) & 0xff`.
* **hashCode**: Java's `String.hashCode` (over UTF-16 units), folded as
  FNV-1a's.
* **mul4**: the length, the first, middle and last bytes in one word,
  times 0x9E3779B1, the top bits. O(1).
* **word**: the first and the last 8 bytes as words, each times an odd
  constant, XOR the length, times a third, the top bits. O(1) for any
  length. Collisions only, not timed.


## 4. The workload

* **Names** (`Names.java`): the classes of 14 JDK 27 modules (`java.base`,
  `java.desktop`, `java.sql`, `java.xml`, `jdk.compiler` and nine more):
  16,415 scanned, 12,700 with fields; a class's instance fields with
  those of its superclasses, names of 2 to 20 bytes without `$`; 16,944
  distinct names, camelCase with shared prefixes, as `java.awt.Component`'s
  `minSize`, `minSizeSet`, `maxSize`, `maxSizeSet`, `prefSize` or
  `javax.swing.JTable`'s `rowHeight`, `rowMargin`, `rowSelectionAllowed`,
  `selectionModel`, `selectionForeground`. BergDB's own tests were not
  used.
* **Objects of n fields**: a schema is a class with a distinct set of
  names, classes of n to 2n − 1 names first, n of its names at random; 64
  schemas per field count (52 at 100 fields: all classes with 100 names
  or more and a distinct set, most of them Swing and AWT components);
  2,048 objects (templates), template t of schema t modulo the number of
  schemas. For K, up to
  1,000 schemas per field count.
* **Misses**: 16 names per schema, from the other schemas' names, so with
  the same prefixes.
* **Values**, drawn per field: 25 % small integers (0 to 999), 10 %
  64-bit integers, 10 % booleans, 5 % doubles, 25 % short strings (1 to
  16 bytes), 8 % longer strings (20 to 120), 7 % byte arrays (8 to 64), 5 %
  nested objects (2 to 5 small fields), 5 % arrays of 2 to 8 small
  integers; Binson's encodings. A field takes about 30 bytes, so the names
  of an object of 20 fields spread over 600 bytes, five to ten lines.

Header and object sizes, bytes, mean (T):

| n   | O (B, L) | H16 |  H8 |   D | object (O) | H16 adds, % |
|-----|-----|-----|-----|-----|------|-----|
| 1   |   3 |   5 |   4 |   8 |   28 | 7.2 |
| 2   |   4 |   8 |   6 |  14 |   54 | 7.4 |
| 4   |   6 |  14 |  10 |  26 |  112 | 7.1 |
| 8   |  11 |  27 |  19 |  50 |  222 | 7.3 |
| 12  |  22 |  47 |  34 |  74 |  356 | 6.8 |
| 16  |  34 |  66 |  50 |  98 |  477 | 6.7 |
| 20  |  42 |  82 |  62 | 122 |  609 | 6.6 |
| 32  |  66 | 130 |  98 | 194 |  993 | 6.4 |
| 50  | 102 | 202 | 152 | 302 | 1556 | 6.4 |
| 100 | 202 | 402 | 302 | 602 | 3134 | 6.4 |

**Cache states** (F53: L1 128 KB per core, L2 12 MB per cluster of four,
a 24 MB system cache):

* **hot**: 16 objects of 16 schemas, 0.4 KB (1 field) to 50 KB (100
  fields), in L1; 16,384 visits of a random object and a random field
  (or miss name), in passes of 15 ms per round.
* **warm**: the objects in the first 4 MB of the cold set, in L2; 100,000
  visits, a pass to load them, a pass timed.
* **cold**: copies of the templates, 256 MB (2^28 bytes) in layout O, up
  to 320 MB in D, 85,000 objects at 100 fields to 9.9 million at 1; 50,000
  visits in random order per round, a 48 MB read before each round to
  empty the caches. Two ways: **cold**, one lookup at a time (below), and
  **stream**, independent lookups that the CPU may overlap.
* **index case** (section 9): one field, or one miss name, in every object
  of one class, the field drawn anew each round: **hot**, 16 objects of
  one schema; **cold**, a 256 MB set of copies of that schema's 32
  templates (40 at 100 fields).

**One lookup at a time.** In hot, warm, cold and the index case, each
lookup's position depends on the previous lookup's result and on the
previous object's first byte, with terms that are always 0 (`(r + 1) >>>
31` for r ≥ −1, and the sign of the type byte); cold and the cold index
case add an `isb` after each lookup (Java: `Thread.onSpinWait` with
`-XX:OnSpinWaitInst=isb`). Why
(C, 8 fields, cold misses): a miss returns a constant on the predicted
path, and the CPU runs ahead into the next lookups; with the result term
only, H16 took 34 ns and B 75, as independent lookups; a `dmb ishld` or
`dsb ish` after each lookup changed nothing (33 to 39 ns); with the byte
term, 127 to 133 ns for every variant (only the first line waited for);
with an `isb`, H16 142 and B 210. The `isb` costs 8 to 14 ns a lookup
itself (C, hot, with and without; `hotSerial` in the outputs), about the
same for all variants. In Java, the `isb` was checked the same way: cold
misses at 8 fields, B 216 and H16 148 ns with it, 144 and 136 without.


## 5. Machine, programs, runs

* **Machine**: F53, Apple M1 Pro (8 performance and 2 efficiency cores),
  32 GB, macOS 27, 128-byte cache lines (`hw.cachelinesize`), 16 KB
  pages. **Java**: OpenJDK 27 (Homebrew, 2026-09-15), `-Xms4g -Xmx4g`,
  G1, one thread. **C**: Apple clang 21, `cc -O2`.
* **Harness**: no JMH offline (none in `~/.m2`), so a hand-made one: each
  variant its own loop with the lookup inlined; per state and variant a
  warm-up of 0.3 s (0.15 s after the first state); 9 rounds, the variants
  in turn with a rotating start, fresh random visits each round; the
  median per JVM run. Java: a new JVM per field count and run. Every
  result is consumed: each timed pass's sum of results is checked against
  the expected sum.
* **Checks before timing**: in each JVM, every variant against the
  positions the encoder recorded, on 200,000 lookups (hits and misses,
  every state): all agree. C: 132,768 lookups per run, the same.
* **Runs** (`run.sh`, `run2.sh`, `out/run.log`): J at 10:04 to 10:28, J2
  and C at 10:35 to 10:50; trials and probes 09:44 to 10:34 (sections 4
  and 12 cite some; none in the tables). Before each run: no `QUIET-BLOCK` marker, no other JVM or
  benchmark in `ps` (VS Code's Java only), and a 1-minute load under 4:
  the first run waited from 09:59 to 10:04 for the load to fall from 10.6
  (`mediaanalysisd`, XProtect and Spotlight were busy). Load during the
  runs 2.3 to 4.0. About 47 minutes of timing in all.
* **Spread**: J's three runs agree within 10 % on 951 of 980 cells outside
  the index case (at most 22 %); C's within 9 % on all 264; J2 against J
  on 700 common cells, 1.5 % mean difference outside the index case. The
  index case varies by design: each round looks up another field.


## 6. Hot

J, hits:

| n   |  B |   L | H16 | H16w | H8 | H8w |  D |
|-----|-----|-----|-----|-----|-----|-----|-----|
| 1   | 21 |  21 | 17 | 20 | 17 | 20 | 16 |
| 2   | 25 |  24 | 22 | 20 | 22 | 21 | 21 |
| 4   | 31 |  32 | 27 | 24 | 26 | 21 | 24 |
| 8   | 35 |  36 | 27 | 25 | 25 | 22 | 26 |
| 12  | 39 |  46 | 30 | 29 | 29 | 28 | 29 |
| 16  | 45 |  56 | 31 | 29 | 28 | 27 | 29 |
| 20  | 46 |  60 | 31 | 30 | 30 | 28 | 32 |
| 32  | 52 |  77 | 38 | 35 | 36 | 31 | 37 |
| 50  | 54 |  93 | 43 | 37 | 43 | 32 | 44 |
| 100 | 60 | 125 | 59 | 44 | 62 | 37 | 63 |

J, misses:

| n   |  B |   L | H16 | H16w |  H8 | H8w |   D |
|-----|-----|-----|-----|-----|-----|-----|-----|
| 1   | 11 | 9.6 | 4.8 | 6.6 | 4.4 | 6.3 | 4.1 |
| 2   | 17 |  15 | 5.5 | 6.6 | 5.2 | 6.5 | 4.5 |
| 4   | 24 |  20 | 7.8 | 7.7 | 4.8 | 6.1 | 5.6 |
| 8   | 26 |  24 | 8.3 | 6.5 | 7.3 | 6.0 | 7.8 |
| 12  | 31 |  31 |  11 | 6.7 |  10 | 8.1 |  10 |
| 16  | 32 |  34 |  12 | 7.5 |  12 | 9.0 |  12 |
| 20  | 33 |  38 |  13 | 7.7 |  13 |  11 |  16 |
| 32  | 36 |  49 |  21 |  14 |  23 |  12 |  24 |
| 50  | 41 |  71 |  33 |  20 |  37 |  16 |  39 |
| 100 | 48 | 101 |  65 |  32 |  82 |  24 |  76 |

C (H16-c computes the FNV-1a hash of the wanted name at each lookup):

| Variant | hit 8 | hit 20 | hit 100 | miss 8 | miss 20 | miss 100 |
|-------|-----|-----|-----|-----|-----|-----|
| B     | 32 | 41 | 54 |  22 |  26 | 42 |
| L     | 28 | 41 | 85 |  16 |  22 | 66 |
| H16   | 19 | 22 | 35 | 5.3 | 8.1 | 35 |
| H16v  | 16 | 23 | 28 | 5.9 | 6.5 | 12 |
| H16T  | 20 | 22 | 36 | 5.4 | 8.5 | 36 |
| H8    | 19 | 22 | 37 | 5.3 | 9.3 | 41 |
| H8v   | 16 | 18 | 29 | 6.0 | 7.5 | 14 |
| D     | 18 | 21 | 34 | 4.5 | 8.4 | 34 |
| H16-c | 27 | 32 | 47 |  18 |  22 | 47 |

* Hits: H16 under B at every count to 50 fields, equal at 100 (J); in C
  at 8, 20 and 100. A hit costs a branch mispredicted where the hash
  matches, and the name compare; B pays a branch per probe and a compare
  per probe.
* Misses: a scalar scan costs about 0.6 ns a hash in Java and 0.35 in C;
  B grows with log2 n. In Java they cross at about 70 fields (33 against
  41 ns at 50, 65 against 48 at 100); in C not by 100 (35 against 42).
  The word scan and NEON scan cost 0.3 and 0.1 ns a hash: no crossover.
* L is the worst above 4 fields: 60 ns per hit at 20 fields, 125 at 100.
* Warm (L2), J: the same picture, 2 to 30 ns more; at 20 fields hits B
  65, H16 37, D 39; misses B 46, H16 15, H16w 11.

J, warm, hits:

| n   |  B |   L | H16 | H16w | H8 | H8w |  D |
|-----|-----|-----|-----|-----|-----|-----|-----|
| 1   | 29 |  28 | 19 | 22 | 18 | 23 | 20 |
| 2   | 34 |  33 | 27 | 23 | 26 | 24 | 26 |
| 4   | 43 |  42 | 33 | 27 | 34 | 25 | 31 |
| 8   | 50 |  47 | 34 | 32 | 33 | 28 | 34 |
| 12  | 56 |  56 | 37 | 36 | 36 | 34 | 36 |
| 16  | 63 |  68 | 38 | 37 | 36 | 34 | 38 |
| 20  | 65 |  73 | 37 | 37 | 37 | 35 | 39 |
| 32  | 75 |  87 | 42 | 41 | 42 | 39 | 44 |
| 50  | 79 |  98 | 48 | 44 | 49 | 40 | 50 |
| 100 | 89 | 143 | 64 | 51 | 69 | 47 | 68 |

J, warm, misses:

| n   |  B |   L | H16 | H16w |  H8 | H8w |  D |
|-----|-----|-----|-----|-----|-----|-----|-----|
| 1   | 16 |  15 |  10 | 11 | 9.9 | 11 | 11 |
| 2   | 21 |  19 | 9.7 | 11 | 9.6 | 10 | 11 |
| 4   | 31 |  27 |  11 | 11 |  10 | 11 | 11 |
| 8   | 34 |  31 |  10 | 10 |  11 | 10 | 12 |
| 12  | 43 |  40 |  13 | 10 |  13 | 12 | 13 |
| 16  | 44 |  44 |  14 | 11 |  14 | 11 | 14 |
| 20  | 46 |  48 |  15 | 11 |  15 | 12 | 18 |
| 32  | 57 |  60 |  22 | 16 |  24 | 14 | 26 |
| 50  | 64 |  78 |  34 | 21 |  37 | 18 | 41 |
| 100 | 72 | 114 |  66 | 35 |  84 | 27 | 78 |


## 7. Cold

J, one lookup at a time, hits:

| n   |   B |   L | H16 | H16w |  H8 | H8w |   D |
|-----|-----|-----|-----|-----|-----|-----|-----|
| 1   | 159 | 159 | 153 | 158 | 151 | 157 | 153 |
| 2   | 168 | 168 | 164 | 164 | 162 | 162 | 166 |
| 4   | 189 | 187 | 180 | 177 | 177 | 176 | 185 |
| 8   | 224 | 212 | 201 | 204 | 201 | 198 | 208 |
| 12  | 261 | 243 | 222 | 230 | 222 | 224 | 223 |
| 16  | 288 | 266 | 238 | 243 | 238 | 239 | 228 |
| 20  | 306 | 282 | 250 | 256 | 251 | 249 | 223 |
| 32  | 335 | 317 | 262 | 269 | 268 | 270 | 240 |
| 50  | 345 | 347 | 293 | 274 | 287 | 287 | 274 |
| 100 | 402 | 394 | 335 | 303 | 340 | 308 | 308 |

J, one lookup at a time, misses:

| n   |   B |   L | H16 | H16w |  H8 | H8w |   D |
|-----|-----|-----|-----|-----|-----|-----|-----|
| 1   | 150 | 148 | 142 | 147 | 140 | 146 | 144 |
| 2   | 160 | 159 | 144 | 147 | 141 | 146 | 145 |
| 4   | 182 | 176 | 145 | 147 | 142 | 145 | 149 |
| 8   | 217 | 199 | 148 | 147 | 146 | 144 | 155 |
| 12  | 256 | 234 | 150 | 147 | 149 | 147 | 161 |
| 16  | 280 | 250 | 151 | 147 | 151 | 147 | 164 |
| 20  | 296 | 263 | 153 | 146 | 155 | 150 | 165 |
| 32  | 327 | 297 | 158 | 151 | 164 | 158 | 176 |
| 50  | 344 | 338 | 170 | 152 | 182 | 167 | 192 |
| 100 | 393 | 364 | 195 | 167 | 236 | 190 | 218 |

C, one lookup at a time:

| Variant | hit 8 | hit 20 | hit 100 | miss 8 | miss 20 | miss 100 |
|-------|-----|-----|-----|-----|-----|-----|
| B     | 216 | 302 | 397 | 211 | 291 | 390 |
| L     | 203 | 268 | 372 | 194 | 251 | 350 |
| H16   | 200 | 245 | 338 | 143 | 148 | 185 |
| H16v  | 199 | 262 | 335 | 148 | 157 | 189 |
| H16T  | 200 | 247 | 345 | 144 | 149 | 198 |
| H8    | 195 | 244 | 333 | 142 | 150 | 215 |
| H8v   | 195 | 253 | 331 | 149 | 156 | 205 |
| D     | 213 | 212 | 300 | 151 | 161 | 216 |
| H16-c | 207 | 251 | 324 | 153 | 157 | 191 |

J, stream (independent lookups), hits:

| n   |   B |   L | H16 | H16w |  H8 | H8w |   D |
|-----|-----|-----|-----|-----|-----|-----|-----|
| 1   |  77 |  78 |  56 |  77 |  53 |  76 |  50 |
| 2   |  84 |  85 |  70 |  78 |  69 |  78 |  63 |
| 4   | 114 | 112 |  96 |  91 |  98 |  82 |  77 |
| 8   | 147 | 158 |  99 |  94 |  95 |  88 |  96 |
| 12  | 174 | 178 | 115 | 108 | 115 | 109 | 114 |
| 16  | 176 | 201 | 136 | 113 | 144 | 109 | 122 |
| 20  | 208 | 239 | 155 | 118 | 161 | 113 | 146 |
| 32  | 218 | 292 | 165 | 156 | 172 | 130 | 161 |
| 50  | 245 | 324 | 177 | 162 | 174 | 143 | 175 |
| 100 | 310 | 370 | 211 | 179 | 213 | 177 | 203 |

J, stream, misses:

| n   |   B |   L | H16 | H16w |  H8 | H8w |   D |
|-----|-----|-----|-----|-----|-----|-----|-----|
| 1   |  45 |  32 |  29 |  38 |  28 |  32 |  25 |
| 2   |  72 |  46 |  30 |  38 |  35 |  39 |  28 |
| 4   |  96 |  91 |  38 |  49 |  25 |  32 |  32 |
| 8   | 126 | 138 |  48 |  37 |  44 |  31 |  48 |
| 12  | 152 | 160 |  66 |  40 |  73 |  43 |  61 |
| 16  | 166 | 164 |  71 |  46 |  79 |  48 |  73 |
| 20  | 169 | 190 |  75 |  46 |  81 |  53 |  81 |
| 32  | 189 | 265 | 130 |  72 | 137 |  59 | 131 |
| 50  | 203 | 310 | 141 | 110 | 148 |  77 | 154 |
| 100 | 250 | 337 | 169 | 129 | 200 | 134 | 195 |

C, stream:

| Variant | hit 8 | hit 20 | hit 100 | miss 8 | miss 20 | miss 100 |
|------|-----|-----|-----|-----|-----|-----|
| B    | 125 | 164 | 247 | 75 | 107 | 187 |
| L    | 134 | 194 | 349 | 74 | 149 | 325 |
| H16  |  86 |  96 | 181 | 34 |  68 | 156 |
| H16v |  46 |  64 | 122 | 22 |  32 |  82 |
| H8   |  86 |  96 | 178 | 34 |  68 | 177 |
| H8v  |  45 |  56 |  96 | 22 |  30 |  71 |
| D    |  63 |  92 | 182 | 35 |  71 | 180 |

* **A miss** in a hashed layout is about one memory access (140 to 165 ns
  here, the `isb` included, for H16 and H8 up to 32 fields), and grows to
  167 (H16w) and 195 (H16) at 100 fields, where the hash array takes 200
  bytes. B's probes leave the header line one after the other: 217 ns at
  8 fields, 296 at 20, 393 at 100, 1.5 to 2 times H16.
* **A hit** needs two accesses in a hashed layout, the header then the
  field, and B up to one per probe: B takes 11 to 22 % longer than H16
  (224 against 201 at 8 fields, 306 against 250 at 20, 402 against 335 at
  100). D is the fastest from 16 to 32 fields, and with H16w at 50 and
  100 (section 12).
* **Stream**: the CPU overlaps lookups, and the fewer lines a lookup
  needs, the more of them it overlaps: misses at 20 fields B 169, H16 75,
  H16w 46 (J); C's NEON scan of 16-bit hashes, 22 to 82 ns per miss and
  46 to 122 per hit (8 to 100 fields).
* **L** reads its names in order, which the prefetcher follows: its cold
  hits lie between B's and H16's up to 32 fields; its misses cost a little
  less than B's.
* The scan's cost hardly shows cold: H16, H16w, H8 and H8w are within 5 %
  of each other on hits and 9 % on misses up to 32 fields.


## 8. Cache lines touched

The bytes each lookup reads, traced (T: the same lookups with a record of
each read, checked to return the same results), on 20,000 cold visits;
lines of 64 bytes, in brackets of 128 (F53's), the object at a random
place in its line. Hits:

| n   |         B |           L |       H16 |        H8 |         D |      H16i |
|-----|-----------|-------------|-----------|-----------|-----------|-----------|
| 1   | 1.2 (1.1) |   1.2 (1.1) | 1.2 (1.1) | 1.2 (1.1) | 1.2 (1.1) | 1.2 (1.1) |
| 2   | 1.4 (1.2) |   1.4 (1.2) | 1.4 (1.2) | 1.4 (1.2) | 1.5 (1.3) | 1.4 (1.2) |
| 4   | 1.9 (1.5) |   1.8 (1.4) | 1.8 (1.5) | 1.8 (1.5) | 2.0 (1.6) | 1.8 (1.5) |
| 8   | 2.7 (2.0) |   2.6 (1.9) | 2.3 (1.9) | 2.1 (1.8) | 2.5 (2.0) | 2.2 (1.8) |
| 12  | 3.4 (2.6) |   3.7 (2.5) | 2.6 (2.2) | 2.5 (2.1) | 2.8 (2.3) | 2.5 (2.1) |
| 16  | 3.9 (3.0) |   4.7 (3.0) | 2.9 (2.3) | 2.7 (2.2) | 3.0 (2.5) | 2.7 (2.3) |
| 20  | 4.3 (3.4) |   5.7 (3.5) | 3.1 (2.5) | 2.8 (2.4) | 3.2 (2.6) | 2.9 (2.4) |
| 32  | 5.2 (4.1) |   8.6 (5.1) | 3.7 (2.8) | 3.3 (2.6) | 3.8 (2.9) | 3.2 (2.6) |
| 50  | 6.1 (4.9) |  12.9 (7.5) | 4.0 (3.3) | 3.7 (3.0) | 4.7 (3.4) | 3.8 (2.9) |
| 100 | 7.9 (6.3) | 24.3 (14.1) | 4.8 (3.9) | 4.3 (3.7) | 7.1 (4.6) | 5.4 (3.7) |

Misses:

| n   |         B |           L |       H16 |        H8 |          D |      H16i |
|-----|-----------|-------------|-----------|-----------|------------|-----------|
| 1   | 1.1 (1.0) |   1.1 (1.0) | 1.1 (1.0) | 1.0 (1.0) |  1.1 (1.0) | 1.1 (1.0) |
| 2   | 1.3 (1.2) |   1.3 (1.2) | 1.1 (1.0) | 1.1 (1.0) |  1.1 (1.1) | 1.1 (1.1) |
| 4   | 1.9 (1.5) |   1.8 (1.4) | 1.1 (1.1) | 1.1 (1.1) |  1.3 (1.2) | 1.2 (1.1) |
| 8   | 2.8 (2.0) |   2.6 (1.9) | 1.3 (1.1) | 1.1 (1.1) |  1.7 (1.4) | 1.4 (1.2) |
| 12  | 3.5 (2.7) |   3.7 (2.5) | 1.4 (1.2) | 1.2 (1.1) |  2.1 (1.6) | 1.7 (1.4) |
| 16  | 4.2 (3.2) |   4.8 (3.1) | 1.5 (1.3) | 1.3 (1.2) |  2.5 (1.7) | 2.0 (1.5) |
| 20  | 4.5 (3.5) |   5.7 (3.6) | 1.6 (1.3) | 1.4 (1.2) |  2.9 (1.9) | 2.2 (1.6) |
| 32  | 5.5 (4.3) |   8.8 (5.3) | 2.0 (1.5) | 1.7 (1.4) |  4.0 (2.5) | 3.0 (2.0) |
| 50  | 6.5 (5.1) |  13.9 (8.2) | 2.6 (1.8) | 2.2 (1.7) |  5.7 (3.4) | 4.1 (2.5) |
| 100 | 8.2 (6.5) | 22.5 (13.1) | 4.1 (2.6) | 3.3 (2.4) | 10.4 (5.8) | 7.2 (4.1) |

Analytically, for an object at a random place in its lines of L bytes:

* **H16, a miss**: reads the type, the count and 2n hash bytes, 2n + 2
  bytes from the start: 1 + (2n + 1) / L lines, 1.6 at 20 fields (64-byte
  lines); a hit reads the hashes up to the match, one offset (n·w bytes
  further on, often the same line) and the field's name: about one line
  more.
* **H8**: n + 2 bytes for a miss, 1 + (n + 1) / L lines; but a false match
  (n / 256 per miss) adds the line of a field.
* **D**: 6n + 2 bytes for a miss, 1 + (6n + 1) / L: 2.9 at 20 fields.
* **B**: ⌈log2(n + 1)⌉ probes, each an offset in the header and a name
  elsewhere: up to 1 + ⌈log2(n + 1)⌉ lines, 4.5 at 20 fields; and they
  are read one after the other, as each probe needs the one before.
* **L**: every name up to the place of the wanted one: half the object
  for a hit, all of it up to the place for a miss.

Frans's point, "scanning only the beginning of the value bytes", is the
miss row: a hashed layout reads the header and nothing else. On 128-byte
lines everything costs fewer lines; the order of the variants stays.


## 9. The index case: one field again and again

An index function looks up the same name in every object of a class: the
place of the field, and so every branch, is the same each time. J2, hot,
hits:

| n   |  B |  L | H16 | H16w | H8w |  D |
|-----|-----|-----|-----|-----|-----|-----|
| 1   | 12 | 12 | 12 | 16 | 17 | 11 |
| 2   | 12 | 12 | 13 | 16 | 17 | 12 |
| 4   | 14 | 16 | 14 | 18 | 17 | 11 |
| 8   | 18 | 18 | 13 | 16 | 18 | 12 |
| 12  | 22 | 24 | 16 | 17 | 19 | 13 |
| 16  | 16 | 27 | 15 | 16 | 18 | 15 |
| 20  | 21 | 25 | 15 | 17 | 17 | 15 |
| 32  | 24 | 67 | 18 | 18 | 18 | 18 |
| 50  | 26 | 54 | 28 | 21 | 20 | 30 |
| 100 | 29 | 79 | 34 | 24 | 22 | 36 |

J2, hot, misses:

| n   |   B |   L | H16 | H16w | H8w |   D |
|-----|-----|-----|-----|-----|-----|-----|
| 1   | 5.8 | 4.5 | 4.8 | 6.5 | 6.2 | 4.4 |
| 2   | 8.8 | 5.5 | 5.2 | 6.5 | 6.5 | 4.9 |
| 4   | 9.8 | 6.0 | 7.0 | 7.0 | 7.8 | 6.0 |
| 8   |  12 | 7.1 | 7.8 | 6.3 | 5.9 | 8.1 |
| 12  |  18 |  15 |  10 | 6.9 | 7.1 | 9.9 |
| 16  |  17 |  27 |  12 | 7.5 | 7.0 |  13 |
| 20  |  18 |  28 |  12 | 7.6 | 9.3 |  15 |
| 32  |  20 |  44 |  21 |  13 |  10 |  24 |
| 50  |  22 |  41 |  33 |  17 |  13 |  38 |
| 100 |  25 |  96 |  81 |  29 |  22 |  75 |

J2, cold, one lookup at a time, hits:

| n   |   B |   L | H16 | H16w | H8w |   D |
|-----|-----|-----|-----|-----|-----|-----|
| 1   | 155 | 155 | 155 | 159 | 160 | 155 |
| 2   | 170 | 170 | 171 | 172 | 173 | 173 |
| 4   | 174 | 174 | 172 | 174 | 174 | 178 |
| 8   | 183 | 180 | 187 | 188 | 184 | 200 |
| 12  | 250 | 247 | 240 | 243 | 240 | 233 |
| 16  | 272 | 269 | 256 | 257 | 257 | 242 |
| 20  | 270 | 243 | 252 | 252 | 248 | 236 |
| 32  | 293 | 311 | 284 | 279 | 268 | 245 |
| 50  | 315 | 344 | 294 | 285 | 276 | 270 |
| 100 | 316 | 386 | 319 | 282 | 281 | 279 |

J2, cold, misses:

| n   |   B |   L | H16 | H16w | H8w |   D |
|-----|-----|-----|-----|-----|-----|-----|
| 1   | 148 | 146 | 141 | 145 | 146 | 142 |
| 2   | 164 | 162 | 143 | 146 | 146 | 144 |
| 4   | 176 | 174 | 144 | 148 | 147 | 147 |
| 8   | 210 | 207 | 146 | 147 | 143 | 153 |
| 12  | 217 | 213 | 150 | 145 | 143 | 158 |
| 16  | 273 | 282 | 151 | 144 | 139 | 160 |
| 20  | 282 | 287 | 155 | 150 | 141 | 162 |
| 32  | 312 | 334 | 156 | 148 | 142 | 171 |
| 50  | 313 | 325 | 168 | 150 | 146 | 183 |
| 100 | 322 | 427 | 198 | 161 | 254 | 208 |

* With its branches predicted, B gets cheap: hot, 29 ns per hit and 25
  per miss at 100 fields, against H16's 34 and 81; the word scans keep up
  (H16w 24 and 29, H8w 22 and 22). Up to 20 fields H16 is faster.
* Cold, B's hits come close to H16's (the CPU fetches the predicted
  probes ahead), its misses do not: 282 against 155 ns at 20 fields.
* H8w's cold miss at 100 fields, 254 ns: in the index case a collision is
  not random but the same in every object; a wanted name that shares its
  8-bit hash with a field of the class pays a name compare, and a line,
  in every object. With 16 bits the chance is 256 times smaller.


## 10. The wanted name as a Java `String`

`get(String name)`, the API case: the lookup gets a `String` and computes
the hash; it compares chars with the stored bytes, which is right for
ASCII, and leaves for a slow path (`getBytes`) at a char ≥ 0x80 (never
taken here: all names are ASCII). B-S: B by chars; H16-S: FNV-1a over the
chars; H16-G: `getBytes` and FNV-1a; H16T-S: today's hash, O(1), on H16
with today's hashes; H16J-S: `String.hashCode` (cached in the `String`),
on H16 with that hash; D-S: D by chars. Hot, hits:

| n   |  B | B-S | H16 | H16-S | H16-G | H16T-S | H16J-S | D-S |
|-----|-----|-----|-----|-----|-----|-----|-----|-----|
| 1   | 21 |  35 | 17 | 37 | 33 | 34 | 32 |  30 |
| 2   | 25 |  43 | 22 | 41 | 37 | 40 | 36 |  39 |
| 4   | 31 |  52 | 27 | 45 | 42 | 44 | 41 |  43 |
| 8   | 35 |  56 | 27 | 51 | 45 | 47 | 43 |  48 |
| 12  | 39 |  64 | 30 | 57 | 49 | 51 | 47 |  54 |
| 16  | 45 |  75 | 31 | 59 | 51 | 52 | 49 |  59 |
| 20  | 46 |  77 | 31 | 63 | 54 | 54 | 52 |  64 |
| 32  | 52 |  86 | 38 | 68 | 60 | 59 | 56 |  78 |
| 50  | 54 |  89 | 43 | 70 | 66 | 62 | 68 |  97 |
| 100 | 60 | 100 | 59 | 88 | 89 | 76 | 93 | 148 |

Hot, misses:

| n   |  B | B-S | H16 | H16-S | H16-G | H16T-S | H16J-S | D-S |
|-----|-----|-----|-----|-----|-----|-----|-----|-----|
| 1   | 11 | 15 | 4.8 | 20 | 28 | 7.3 | 5.4 | 5.9 |
| 2   | 17 | 21 | 5.5 | 20 | 29 | 8.2 | 5.9 | 6.5 |
| 4   | 24 | 30 | 7.8 | 23 | 31 | 9.1 | 7.7 | 8.6 |
| 8   | 26 | 34 | 8.3 | 25 | 33 |  12 |  11 |  12 |
| 12  | 31 | 40 |  11 | 28 | 36 |  14 |  13 |  17 |
| 16  | 32 | 42 |  12 | 30 | 37 |  16 |  14 |  21 |
| 20  | 33 | 44 |  13 | 32 | 39 |  18 |  16 |  27 |
| 32  | 36 | 49 |  21 | 39 | 46 |  24 |  21 |  52 |
| 50  | 41 | 57 |  33 | 46 | 56 |  32 |  41 |  88 |
| 100 | 48 | 67 |  65 | 69 | 89 |  58 |  90 | 215 |

Cold, one lookup at a time, hits:

| n   |   B | B-S | H16 | H16-S | H16-G | H16T-S | H16J-S | D-S |
|-----|-----|-----|-----|-----|-----|-----|-----|-----|
| 1   | 159 | 172 | 153 | 170 | 160 | 162 | 163 | 161 |
| 2   | 168 | 184 | 164 | 181 | 170 | 175 | 175 | 177 |
| 4   | 189 | 211 | 180 | 198 | 189 | 191 | 192 | 198 |
| 8   | 224 | 249 | 201 | 219 | 208 | 212 | 214 | 222 |
| 12  | 261 | 292 | 222 | 240 | 228 | 234 | 236 | 233 |
| 16  | 288 | 320 | 238 | 249 | 239 | 246 | 248 | 240 |
| 20  | 306 | 337 | 250 | 258 | 248 | 256 | 256 | 237 |
| 32  | 335 | 349 | 262 | 284 | 266 | 286 | 282 | 249 |
| 50  | 345 | 380 | 293 | 314 | 296 | 314 | 310 | 284 |
| 100 | 402 | 448 | 335 | 355 | 334 | 362 | 352 | 323 |

Cold, misses:

| n   |   B | B-S | H16 | H16-S | H16-G | H16T-S | H16J-S | D-S |
|-----|-----|-----|-----|-----|-----|-----|-----|-----|
| 1   | 150 | 154 | 142 | 150 | 150 | 145 | 142 | 143 |
| 2   | 160 | 167 | 144 | 154 | 150 | 146 | 142 | 144 |
| 4   | 182 | 190 | 145 | 156 | 159 | 145 | 143 | 147 |
| 8   | 217 | 228 | 148 | 160 | 158 | 150 | 146 | 153 |
| 12  | 256 | 269 | 150 | 162 | 161 | 151 | 148 | 158 |
| 16  | 280 | 294 | 151 | 163 | 163 | 154 | 150 | 161 |
| 20  | 296 | 310 | 153 | 165 | 165 | 156 | 151 | 164 |
| 32  | 327 | 336 | 158 | 174 | 175 | 164 | 160 | 173 |
| 50  | 344 | 363 | 170 | 185 | 183 | 181 | 171 | 189 |
| 100 | 393 | 415 | 195 | 223 | 208 | 222 | 211 | 219 |

* The hash, on misses: FNV-1a over the chars adds 15 to 19 ns a lookup
  hot (H16-S against H16, 1 to 20 fields; FNV-1a is a chain of
  multiplies, about 1.3 ns a byte); `getBytes` and FNV-1a 23 to 26;
  today's O(1) hash 1 to 4; `String.hashCode` 0 to 3 (computed once per
  `String`). In C, computing FNV-1a at each lookup adds 8 to 14 ns hot
  (H16-c).
* A hit also pays the compare by chars: H16J-S 43 against H16's 27 ns at
  8 fields, 52 against 31 at 20; `charAt` checks each index.
* Cold, these costs are partly hidden: up to 18 ns on 150 to 260.
* At 50 and 100 fields the `String` variants' scans ran slower than the
  same loop with bytes (D-S 215 against D's 76 ns per hot miss at 100,
  H16J-S 90 against H16's 65): the JIT's code for the larger methods,
  most likely; not examined.

So a hash over the stored UTF-8 bytes makes Java's `get(String)` pay
about 15 ns a lookup hot, unless the caller holds the name as a key
(UTF-8 bytes and hash, made once), as an index function can. A hash
defined as Java's `String.hashCode` folded costs Java about 2 ns, and is
as random-like in K, but every other reader then computes Java's hash
over UTF-16 units (a 31-polynomial; over the bytes for ASCII names).


## 11. Hash width and function: collisions

K: false name compares per 1,000 lookups, hits / misses, a linear scan in
name order; "objects" is the number of schemas; random is the
expectation for a perfect hash ((n − 1) / 2 / 2^b per hit, n / 2^b per
miss); 0 is none, 0.0 under 0.05. 16 bits:

| n   | objects |     today |      mul4 |    FNV-1a |  hashCode |      word |    random |
|-----|------|-----------|-----------|-----------|-----------|-----------|-----------|
| 1   | 1000 |   0 / 1.0 |   0 / 0.1 |   0 / 0.1 |     0 / 0 |     0 / 0 |   0 / 0.0 |
| 2   | 1000 | 2.0 / 2.0 |   0 / 0.0 |   0 / 0.0 |   0 / 0.0 |   0 / 0.1 | 0.0 / 0.0 |
| 4   | 1000 | 8.5 / 3.8 | 3.5 / 0.1 |   0 / 0.1 |   0 / 0.1 |   0 / 0.0 | 0.0 / 0.1 |
| 8   | 1000 |  23 / 8.0 | 8.2 / 0.2 |   0 / 0.1 |     0 / 0 |   0 / 0.1 | 0.1 / 0.1 |
| 12  | 1000 |   35 / 13 |  12 / 0.6 | 0.1 / 0.2 |   0 / 0.3 | 0.2 / 0.1 | 0.1 / 0.2 |
| 16  |  744 |   41 / 16 |  15 / 0.6 | 0.1 / 0.1 |   0 / 0.1 | 0.1 / 0.2 | 0.1 / 0.2 |
| 20  |  544 |   55 / 19 |  21 / 1.4 |   0 / 0.3 |   0 / 0.2 |   0 / 0.3 | 0.1 / 0.3 |
| 32  |  309 |   79 / 34 |  35 / 2.6 | 0.1 / 1.0 | 0.1 / 0.3 |   0 / 0.5 | 0.2 / 0.5 |
| 50  |  197 |   91 / 53 |  59 / 6.5 | 0.1 / 1.6 |   0 / 0.3 |   0 / 0.8 | 0.4 / 0.8 |
| 100 |   52 |  129 / 66 |  72 / 4.8 | 0.6 / 0.6 | 0.2 / 2.4 |     0 / 0 | 0.8 / 1.5 |

8 bits:

| n   | objects |     today |      mul4 |    FNV-1a |  hashCode |      word |    random |
|-----|------|-----------|-----------|-----------|-----------|-----------|-----------|
| 1   | 1000 |   0 / 4.2 |   0 / 3.8 |   0 / 4.2 |   0 / 3.8 |   0 / 4.1 |   0 / 3.9 |
| 2   | 1000 | 3.5 / 8.7 | 2.5 / 8.8 | 1.0 / 8.5 | 1.5 / 7.3 | 2.5 / 9.1 | 1.9 / 7.8 |
| 4   | 1000 |   13 / 18 |  8.0 / 17 |  6.5 / 17 |  5.8 / 15 |  4.8 / 15 |  5.9 / 16 |
| 8   | 1000 |   33 / 37 |   25 / 31 |   13 / 31 |   11 / 29 |   11 / 29 |   14 / 31 |
| 12  | 1000 |   50 / 54 |   34 / 46 |   22 / 46 |   20 / 48 |   19 / 47 |   21 / 47 |
| 16  |  744 |   67 / 68 |   45 / 65 |   28 / 63 |   30 / 62 |   27 / 58 |   29 / 62 |
| 20  |  544 |   85 / 83 |   59 / 78 |   39 / 81 |   43 / 80 |   40 / 75 |   37 / 78 |
| 32  |  309 | 125 / 139 | 102 / 127 |  61 / 129 |  69 / 122 |  76 / 126 |  61 / 125 |
| 50  |  197 | 154 / 211 | 173 / 210 | 100 / 187 | 111 / 198 | 133 / 206 |  96 / 195 |
| 100 |   52 | 274 / 380 | 287 / 383 | 187 / 370 | 222 / 420 | 265 / 400 | 193 / 391 |

Objects with at least one pair of equal hashes, %, 16 bits:

| n   | today | mul4 | FNV-1a | hashCode | word | random |
|-----|-----|-----|-----|-----|-----|-----|
| 8   |  14 |  6 | 0 | 0 | 0 | 0 |
| 12  |  30 | 12 | 0 | 0 | 0 | 0 |
| 16  |  39 | 16 | 0 | 0 | 0 | 0 |
| 20  |  51 | 24 | 0 | 0 | 0 | 0 |
| 32  |  70 | 42 | 0 | 0 | 0 | 1 |
| 50  |  94 | 76 | 1 | 0 | 0 | 2 |
| 100 | 100 | 98 | 6 | 2 | 0 | 7 |

8 bits:

| n   | today | mul4 | FNV-1a | hashCode | word | random |
|-----|-----|-----|-----|-----|-----|-----|
| 8   |  21 |  18 |   9 |   8 |   9 |  10 |
| 12  |  42 |  34 |  24 |  22 |  21 |  23 |
| 16  |  59 |  49 |  38 |  39 |  36 |  37 |
| 20  |  74 |  64 |  57 |  59 |  56 |  52 |
| 32  |  93 |  94 |  88 |  90 |  91 |  86 |
| 50  |  99 | 100 |  98 |  99 | 100 |  99 |
| 100 | 100 | 100 | 100 | 100 | 100 | 100 |

* On all 16,944 names, 16 bits: today's hash takes 2,145 values, the
  largest bucket 50 names; mul4 12,760, at most 13; FNV-1a, hashCode and
  word about 14,900, at most 4.
* Today's hash fails on names that differ in the middle: `majorTickSpacing`
  and `minorTickSpacing` (`JSlider`), `componentListener` and
  `containerListener`, `st_atime_sec`, `st_ctime_sec`, `st_mtime_sec`
  (`UnixFileAttributes`). At 16 bits it is 40 to 400 times worse than
  random; it costs time where a false match takes a line: cold misses at
  50 and 100 fields, 178 against 170 ns and 208 against 195 (H16T against
  H16, J), cold hits at 100, 342 against 335; elsewhere within 2 ns.
* 8 bits is random-like with any of the hashes, and random is the
  problem: 0.08 false compares per miss at 20 fields, 0.37 at 100.
* FNV-1a, hashCode and word are as good as random at 16 bits; so is word,
  which reads at most 16 bytes of a name.


## 12. Interleaved entries, and D's cold hits

D (today's table: hash and 32-bit offset per field, 6 bytes) had the
fastest cold hits from 16 fields, in both languages (J 223 against H16's
250 ns at 20 fields, C 212 against 245; at 100, 308 and 300 against 335
and 338), though it reads more lines (T). A guess, that the offset next
to its hash saves an access, led to H16i: (hash, offset of w bytes) per
field, H16's bytes in D's order. J2, H16 / H16i / D:

| n   |      hot hit |        hot miss |        cold hit |       cold miss |
|-----|--------------|-----------------|-----------------|-----------------|
| 1   | 19 / 18 / 16 | 4.8 / 4.3 / 4.1 | 153 / 154 / 154 | 143 / 145 / 144 |
| 2   | 22 / 22 / 20 | 5.5 / 5.2 / 4.5 | 164 / 166 / 166 | 144 / 147 / 146 |
| 4   | 28 / 30 / 24 | 7.8 / 9.9 / 5.6 | 180 / 182 / 185 | 147 / 150 / 149 |
| 8   | 28 / 30 / 26 |  8.2 / 11 / 7.7 | 201 / 207 / 209 | 148 / 157 / 156 |
| 12  | 30 / 34 / 28 |    11 / 14 / 10 | 223 / 238 / 225 | 152 / 168 / 161 |
| 16  | 31 / 36 / 30 |    13 / 18 / 13 | 237 / 256 / 225 | 152 / 174 / 163 |
| 20  | 33 / 38 / 32 |    13 / 23 / 16 | 251 / 272 / 224 | 152 / 179 / 165 |
| 32  | 37 / 48 / 37 |    21 / 39 / 24 | 266 / 299 / 241 | 158 / 200 / 176 |
| 50  | 43 / 58 / 44 |    33 / 59 / 39 | 293 / 317 / 273 | 169 / 263 / 192 |
| 100 | 60 / 87 / 63 |   79 / 123 / 76 | 336 / 372 / 317 | 208 / 270 / 226 |

C, one lookup at a time (H16p: H16 with a prefetch of the offset table's
first and last bytes at the start):

| Variant | hit 8 | hit 20 | hit 100 | miss 8 | miss 20 | miss 100 |
|------|-----|-----|-----|-----|-----|-----|
| H16  | 200 | 245 | 338 | 143 | 148 | 185 |
| H16i | 199 | 264 | 336 | 151 | 174 | 260 |
| H16p | 199 | 244 | 324 | 143 | 143 | 178 |
| D    | 213 | 212 | 300 | 151 | 161 | 216 |

* H16i is no better on hits and worse on misses, so the offset's place
  is not it; nor the offset table's line (H16p), nor the first three
  lines of the fields (a prefetch probe, `probe-prefetch.c`: 241 against
  245 ns at 20 fields).
* By the field's place (C, 20 fields, the same field in every object,
  `lookup coldPos`): H16 takes 185 ns for the first field and rises to
  276 for the last; D 197 for the first, 260 at the eighth, then falls
  to 236 for the last. D's later fields are cheaper.
* Not explained. A guess: D's longer header (122 bytes at 20 fields),
  read in order, lets the hardware prefetcher run on into the fields.
* D's cost: (4 − w)·n bytes more than H16, 2n at w = 2, and slower
  misses: 165 against 153 ns at 20 fields, 218 against 195 at 100.


## 13. What it means

* **The hash scan wins where Frans expected**, and most on misses, which
  are common: an index over a field that some objects lack, a filter, a
  `has`. From 1 to 20 fields, hot, 1.1 to 1.5 times faster than B on
  hits and 2.4 to 3.1 on misses (J); cold, 1.0 to 1.2 on hits and 1.1 to
  1.9 on misses (1.5 to 1.9 from 8 fields).
* **The crossover is above the typical object.** A scalar scan in Java
  loses to B only on hot misses from about 70 fields, and in the index
  case from about 50. A reader that scans a word at a time has no
  crossover up to 100 fields. A hybrid, the scan below some count and B
  above, would gain only in those corners, at the price of two lookups to
  test; not worth it below 100 fields.
* **16 bits, not 8.** 8 bits saves n bytes (3 % of an object here), and is
  as fast up to about 32 fields; above, the false matches cost cold
  lines, and in the index case a collision repeats in every object.
* **A hash over the whole name.** FNV-1a: simple in every language,
  random-like on real names; its cost, about 1.3 ns a byte when computed
  at a lookup, falls on `get(String)` only.
* **The layout of the hashes:** contiguous, before the offsets (H16).
  Interleaving them with the offsets (H16i) made misses slower and hits no
  faster. D's faster cold hits are real but not understood, and D costs
  2n bytes more and slower misses.
* **L, a scan of the names**, is never the best choice above 2 fields.


## 14. Recommendation for 020-05's format

For (f), variant H of 020-05, section 12b.4, with these choices:

1. **The table**: after the count, n hashes of 16 bits (little-endian),
   one per field in the fields' order, then the n offsets (ends) of w
   bytes. 2n bytes per object: `Payment` 41 bytes instead of 35, a
   20-field object here 6.6 % more.
2. **The hash**: FNV-1a, 32 bits, over the name's UTF-8 bytes, folded to
   16: `h = 0x811c9dc5; for each byte b: h = (h ^ b) * 0x01000193;
   h16 = (h ^ (h >>> 16)) & 0xffff`. No rule on equal hashes: a reader
   compares the name wherever the hash matches.
3. **The lookup**: scan the hashes in order; where one matches, compare
   the name's length and bytes; a miss reads the 2n + 2 header bytes
   only. How to scan is the reader's: a word at a time in Java (four per
   64-bit read), NEON or SSE in C. No binary search needed below 100
   fields.
4. **The API**: a key form for repeated lookups (the name's UTF-8 bytes
   and hash, made once), for index functions and `getX` paths that know
   their names; `get(String)` hashes the chars, about 15 ns hot. A writer
   of a class's objects hashes its field names once per class.
5. **For Frans, one choice**: FNV-1a over the bytes (recommended: a
   format for several languages, defined on its own stored bytes), or
   Java's `String.hashCode` folded (Java's `get(String)` 8 to 15 ns
   faster hot; every other language computes Java's hash over UTF-16
   units).

020-05's recommendation, B unless H is clearly faster under 20 fields:
it is, hot 1.1 to 1.5 times on hits and 2.4 to 3.1 on misses (J; C 1.7
to 1.9 on hits), cold 1.5 to 1.9 times on misses from 8 fields; on cold
hits only 1.0 to 1.2 times. B stays the fallback if 2 bytes a field
matter more: it costs, at 20 fields (J), 15 ns more per hot hit, 20 per
hot miss, 56 per cold hit and 143 per cold miss.


## 15. Limits

* One machine, Apple M1 Pro, 128-byte lines and a large L1: on x86 with
  64-byte lines a lookup reads more lines (T), which favours the variants
  that read fewer, the hashed ones; not measured there.
* One thread, the lookup alone: no BergDB read path around it (the
  stream, the transaction, the decode of the value). Next to a value read
  from a cold stream, a lookup is a small part.
* Objects made of real names but synthetic values; ASCII names only, so
  the non-ASCII paths of section 10 untimed.
* The cold set at 100 fields holds 85,000 objects; a round of 50,000
  visits revisits some, whose lines may still be in the 24 MB system
  cache: the cold figures at 50 and 100 fields may be a little low.
* "cold" includes an `isb`, 8 to 14 ns a lookup, about the same for all.
* Java's JIT: a scalar scan of 100 hashes took 65 to 79 ns in the five
  JVM runs (H16, hot miss; J and J2); the `String` variants at 50 and 100
  fields (section 10). The word scan was steady: 31.4 to 31.6 ns.
* The count is 1 byte here (n ≤ 255); offsets are starts, not (f)'s ends.
* Not measured: (f)'s names apart from the values (020-05, section
  12b.10; B's probes would then read one area: about 2 to 3 lines
  instead of 4.3 at 20 fields, an estimate); nested paths; the writer's
  cost of the hashes; several threads; another JVM, machine or compiler.


## 16. Files

In `/Users/f/fl/bench/006-15/020-06/`:

* `java/Names.java`: the field names of the JDK's classes, to
  `out/names.txt`.
* `java/Lookup.java`: the encoder, the layouts, the lookups, the harness
  (`time`), the collision table (`coll`), the trace of the lines
  (`lines`), the export for C (`export`). `java/Payment.java`: section
  3's bytes.
* `c/lookup.c`: the C harness (`hot`, `cold`, `coldStream`, `hotSerial`,
  and the probe `coldPos`); `c/probe-prefetch.c`: the prefetch probe of
  section 12; `c/data-n*.bin`: the exported keys and templates.
* `run.sh`, `run2.sh`: the runs; `summarize.py`, `tables.py`,
  `tables2.py`: the summaries; `item/gen.py` and `item/template.md`:
  this item's tables from the outputs.
* `out/`: `java-n*-r*.txt` (J), `java2-n*-r*.txt` (J2), `c-n*-r*.txt`
  (C), `c-first/` (C's first runs, without H16i and H16p), `lines.txt`
  (T), `coll.txt` (K), `summary.txt` (every cell, its runs, minimum and
  maximum), `run.log`, `trial-n8.txt`.


## 17. Log

2026-11-08. Written by agent m06 of coord-1108 (006-15) at Frans's
request (09:32); measured 09:44 to 10:50 on F53; the programs and outputs
in `/Users/f/fl/bench/006-15/020-06/`. No code changed.
