# 020-16 Fuzzing of the object format, the index keys and the index definitions

Created 2026-11-09 by Frans Lundberg. Status: open.

A bug hunt for release 2026.4 (020): every reader of bytes that 2026.4
added, fuzzed with oracles from the specs (020-07, 020-09, 020-10). One of
the five hunts that coord-1109 started at 09:22, written without reading
the other hunts' findings.


## 1. The request

Frans, 2026-11-09, 09:21: "Start 1 to 4".
coord-1109's task for 020-16: fuzz ObjectFormat's reader against 020-07
and its second implementation, the detection of what a stored value is,
IndexKeys and IndexDefinition against 020-10, and DataObjects' get
against 020-09; a quick pass on F53 before 13:00, longer campaigns on s1
or after 13:00; stop when each area has run clean for 30 minutes after
the last fix, or at 15:00.


## 2. The method

A fuzzer, `bergdb.pubimp.FormatFuzzer` (in the clone, committed with
`java/stress/fuzz.sh`), with six areas: objects, keys, data, kinds,
starts and guesses. Each iteration has its own
`Random` from the seed and the iteration's number, so a failure is
repeated alone: `FormatFuzzer AREA SEED SECONDS ITERATION`.

### 2.1. objects: ObjectFormat against 020-07

The inputs, about 9,000 a second on F53:

* valid values from `ObjectFormatTester.Gen` (every type and edge, depth
  1 to 16, widths 1, 2 and 4, up to about 300 fields);
* a deviant writer: the model written with exactly one rule broken at one
  random place, every other byte as a conforming writer writes it, so the
  codes the bytes break are known: a width not the smallest, an integer or
  a length in more bytes, another NaN, two fields swapped, a duplicate
  name, an empty name, ill-formed UTF-8 in a name or a string (every class
  of table 3-7, at a char boundary), bytes after a value in its field, a
  byte that starts no value, a count above 32,767, a negative length, a
  container past level 16, trailing bytes, another header, a top value
  that is not an object, two ends merged;
* every count, end, name length, length, integer, double and type byte of
  a valid value set to extremes (0, 1, 0x7f, 0x80, 0xff, 0x7fff, 0x8000,
  0xffff, 2^31 - 1, 2^31, 2^32 - 1, the old value plus or minus 1 or 2,
  NaN patterns);
* bytes changed, flipped, inserted, deleted, repeated, swapped, cut and
  appended, 1 to 8 changes; two values crossed at random places;
* deep nesting (14 to 200,000 arrays, ended or not; up to 300 objects;
  mixed), counts and lengths of up to 2^32 - 1 with no bytes behind them;
  the header and random bytes.

The oracles, on every input: (a) the full check accepts, or throws
`BadFormatException` whose message starts with a code of 020-07, section
7.2 and ends with the spec's reference, and nothing else; the least of
three times under 20 ms + 200 ns a byte; an allocation of at most 4 KB
for an accepted value, 64 KB for a refusal (020-07, section 7.1: nothing
allocated for a count or a length read); (b) the same verdict as `Ref`,
`ObjectFormatTester`'s second codec, and for a deviant both codes among
the known ones; (c) an accepted value decodes as `Ref` decodes it and is
written again to the same bytes by the codec and by `Ref` (one object,
one byte string), and `isFormat1` is false; (d) each lookup of a path
(every name, names before, between and after them, random names) by the
binary search (`ObjectFormat.find`) gives the position a linear scan of
the fields gives, and the decoded value's; on refused bytes a lookup
gives a value, absent or `BadFormatException`, never another exception,
and a position inside the value; (e) `new DbObject` refuses with the same
code, or reads each field as decoded: `getType`, `has`, `getDbValue` (its
size and bytes), the typed getters, `getObject`, `getArray` and each of its
elements' bytes, `has` and the typed getters of nested paths; and
`DbObject.Builder`, given the values read, writes the same bytes.

The programs written apart for 020-07 (`/Users/f/fl/bench/006-15/020-07/`)
check a corpus of the inputs: `xcheck.py` imports `check.py`, the second
implementation written from the spec, and `XF2.java` runs `F2`, 020-07's
sketch; both in `/Users/f/fl/bench/2026-11-09/f16/xcheck/`. For each
input: the same verdict, a refusal's code among the deviant's known
ones, the same decoded value, their own writers giving the bytes again,
and the same lookups.

### 2.2. keys: IndexKeys and IndexDefinition against 020-10

* Pairs of values of each level type (long and double edges, random
  doubles but NaN, strings of any code point with U+0000 to U+0002,
  bytes with 00, 01, 02, fe, ff, lengths up to about 4,300, and pairs
  that share a prefix or differ by one element): the encodings' unsigned
  order is the values' (code points for strings, -0.0 equal to 0.0), equal
  values give equal encodings and others neither one a prefix of the
  other's, each encoding is a reference's written apart (BigInteger for
  v + 2^63, the escapes by hand), and decodes to the value; NaN refused.
* The prefix rule (E'(p) a prefix of E(v) exactly when v starts with p)
  and succ (z starts with x exactly when x <= z < succ(x)).
* Entries of random definitions (1 to 8 levels, paths of 1 to 16 parts,
  names with '.', ',', U+0000, 255 bytes): the tuple order of (levels, K);
  the parse; changed entry keys (the prefix kept, or not) either parsed,
  each level read and the key written again to the same bytes, or refused
  with `InternalDataException`, nothing else.
* Markers' and definitions' keys, changed: parsed to a name and a
  generation whose key is the same bytes, or `InternalDataException`.
* Definitions: written and read again; changed bytes, or a changed field
  in the model (fields removed or added, other types, version 2, gen 0 or
  -1, other states, bad directories, 0 or 9 levels, a level with another
  field or type, paths of 0 or 17 parts, empty or 256-byte parts), read
  only if a reference written from 020-10, section 4.2's table takes them,
  and then written again to the same bytes; else `InternalDataException`.
* The index function, `entryLevels` and `entry`, on objects with values
  on the definition's paths (of the level's kind mostly, NaN, any other
  kind, absent, a path through a scalar, strings and bytes of 4,080 to
  4,100 bytes with escapes, changed bytes, keys with suffixes) against a
  reference from section 3.3's table and the reference encodings.

### 2.3. data: DataObjects' get against 020-09

Random stored objects into `AllTypes` (a field of every type of 020-09's
closed list: the 8 primitives, the 8 wrappers, `String`, `byte[]`,
arrays of each, `byte[][]`, `byte[][][]`, `int[][]`, `String[][]`,
`long[][][]`, a nested class, its arrays), `Inner` (which holds itself),
`Sub` (a subclass) and at the top `int`, `Integer`, `long`, `char`,
`double`, `float`, `boolean`, `Byte`, `Short`, `int[]`, `String[]`,
`byte[][]`, `Inner[]`, `double[][]`, `Character[]`: values of every kind,
texts that parse or almost do (` 12 `, `0x1p3`, `1_000`, `NaN`, `1e400`,
digits beyond long's range, Arabic-Indic digits, `+-1`, U+00A0 and
U+2007 before a digit), doubles at every integer type's edges, ill-formed
UTF-8 in bytes, stored fields the class lacks, a transient's name. The
oracle: no exception, and the value of a reference written here from
020-09, sections 5.4 to 5.9, deeply (doubles and floats by
`Double.compare`, so -0.0 counts and NaN is one), by the get's two ways
(`KvToObjectImp`, `DbObject.toJavaObject`). And the put and get again of
random `AllTypes` values, none null but those left out: the same values,
the constructor's where left out.

### 2.4. kinds: what a stored value is, through a database

Each iteration a memory database with indexes `s` (string), `l` (long),
`b` (bytes) and `d` (double) on `/k/`, made before the puts or built
over them, and `/n/` without one; 3 to 27 puts and deletes at keys of
every suffix (none, `.obj`, `.txt`, `.bin`, `.h`, `v1.2`), by `w()` or
`rw()`, of values that look like other kinds: Strings (any, starting
with "bergo" U+0001, a whole format-1 object in ASCII, empty), byte[]s
(format 2, a mutant of it that fails the check, the header alone, the
empty object, 2026.3's real format-1 objects, format-1 objects in ASCII,
UTF-8, random, empty), `DbObject`s and Data Objects. The oracle, the
rules of `Connection.get`'s, `IndexBuilder`'s and `UsePrimaryBuilder`'s
Javadoc: each put taken or refused as they say (an object at a key with a
suffix; a byte[] of format 1 at an object key of an indexed directory);
a build fails exactly when an object key of the directory holds a
format-1 structure (String or byte[]); every key read as `byte[]`,
`String`, `Object`, `DbObject` and a Data Object class, each the value or
the exception the rules give; `usePrimary` of each type over each
directory, its keys in key order and each value or exception; each
active index scanned whole, and with random `eq`, `from`, `to`, both,
`prefix` and `backward()` (bounds from the entries, near them, or
random), against a reference from the decoded values; NaN, a lone
surrogate or an argument of another type refused. One step in five is an
`rw()` of 2 to 4 puts and deletes, often at one key: each key's last
operation counts (015-40), an object at a key with a suffix refuses the
transaction at its put, a byte[] of format 1 as a key's last value at an
object key of an indexed directory refuses it at the commit, and a
refused transaction changes nothing.

### 2.5. starts: what a start reads of the indexes

A probe first (`/Users/f/fl/bench/2026-11-09/f16/probe/`, `ProbeStart`),
then area 5 of the fuzzer: a database with two indexes on a memory
stream; one change of its internal keys written through the Core (a
definition's bytes or fields changed, a definition's key changed, a
marker's key changed, an entry's key changed, a key under `/#i/dii/`, an
index made through `IndexBuilder` with edge names, directories and
paths, or a key under the indexed directory that is no key of it, a '/'
in its name, an empty name or no ikey, before a build over the
directory, which must be active with the directory's entries only); a
start on a copy of the stream. The oracle (020-10, sections
4.1, 4.2 and 4.5): it starts exactly when the reference says the keys
and values under `/#i/` are an index's, else it is refused with
`InternalDataException` (`VersioningStreamException` for format 1),
nothing else; started, each index scans, and every definition the start
holds is the one in the stream.

### 2.6. guesses: the smaller readers

`ObjectFormat.isFormat1`, the format-1 guess (020-08, section 3), on
2026.3's real objects, the empty and the null object and format-1
objects in ASCII, changed (bytes, or a number of the table or a field
set to an extreme), against a reference written from its Javadoc (its
details checked against the code, so not wholly apart);
`StringUtil.isWellFormedUtf8` and `ObjectFormat.utf8Fault` on strings
of any code point, with ill-formed sequences of every class and changed
bytes, against Java's decoder (021-06; 020-07, R11);
`Keys.bkey2ikeyOrNull` (021-06) against its Javadoc's rule, and the
bkey of the ikey it gives is the bkey again.

### 2.7. Checking the fuzzer

Faults planted one at a time in a copy of a production class, compiled
ahead of the build on the class path (`plant.py` in
`/Users/f/fl/bench/2026-11-09/f16/plant/`), the matching area run 10 s
on seed 7: of 32 plants, 27 found, each within seconds, and 5
equivalent, none missed:

* ObjectFormat (11, all found): the NaN check, an end above the last
  end, the binary search's step, a length's fewest bytes, surrogates and
  overlong E0 forms in UTF-8, an array's depth, a string past its
  extent, a field past its extent in a lookup, a value that ends before
  its field, a format-1 count of 0 with bytes after it (area guesses);
* IndexKeys, IndexManager, IndexBuilderImp (5, all found): the double's
  sort long, a byte below 2 in K, and F16-1's, F16-2's and F16-3's fixes
  taken out (areas keys and starts);
* IndexDefinition (4: 1 found, 3 equivalent): a state not checked is
  found; 9 levels taken by the constructor are refused by the reader's
  loop, 17 parts taken by the loop by the constructor, and the 4,096
  bytes' early test's case by the size check after the escapes;
* DataObjects (3, all found): the char's clamp, NaN as a boolean, the
  text's trim;
* Entries, KvToObjectImp, RwEnvironmentImp, UseIndexBuilderImp (8: 7
  found, 1 equivalent): `.bin` taken as an object key, an object key's
  rule dropped for an object, format 1 for `Object.class`, a String put's
  entries, from exclusive, to exclusive, the prefix's end; a suffix rule
  changed where no key can tell;
* IndexKeys' parse (1, equivalent): a long level of 7 bytes, which the
  missing K refuses anyway.

### 2.8. The runs

Every run clean but the quick passes that found F16-1 (area keys) and
the probes that found F16-2 and F16-3. Minutes are each area's; on s1
the areas take turns of a minute, on F53 at 11:04 they ran in parallel,
one JVM each.

| Where | When        | Code                         | Seeds        | Minutes an area |
|-------|-------------|------------------------------|--------------|-----------------|
| F53 | 09:35-10:43 | as it was written            | 1 to 7       | under 2 a run |
| s1  | 09:57-10:20 | F16-1 fixed; 4 areas         | 1000 to 1022 | 5 or 6        |
| s1  | 10:21-10:39 | F16-2 fixed; 6 areas         | 2000 to 2016 | 2 or 3        |
| s1  | 10:39-11:41 | b1a659f, all fixed; 6 areas  | 3000 to 3060 | 10 or 11      |
| F53 | 11:04-11:37 | b1a659f; 6 areas in parallel | 6000 to 6507 | 32            |

On F53 at `b1a659f` in 32 minutes: objects 12,001,449 inputs, keys
333,804,120, data 26,882,039, kinds 4,413,673 puts and rw()s, starts
876,826 starts, guesses 132,739,227. The corpora for the programs written
apart: seeds 2 and 5, 296,049 inputs below 40,000 bytes in all, 0
disagreements with `check.py`; F2 differs only by N16-1.

After the campaign, at `b1a659f` on F53: harness H2
(`IndexHarness 7001 5000 1 4`, a restart every 500 steps, so the start's
scan of F16-2) OK on 4 seeds; harness H3 (`IndexJobsHarness`) OK on
seed 7101 (30 runs), and on seed 7102 (1,000 runs) one finding, not of
020-16's code: `IndexJobsHarness 7229 1 500` reports a status ("INTERRUPT
at BUILD_STEP 2, 500 objects, no racing writes, deleted during the build:
build 1 ended FAILED ... the index was deleted, not [ACTIVE]"), the same
at `a9e5488` and at `main`'s `2c248ff`. Not looked into: for the hunts of
the harnesses and the jobs (020-17, 020-18), or whoever reads this first.


## 3. The findings

| ID    | Severity | What                                                  | Fix (clone) |
|-------|----------|-------------------------------------------------------|-------------|
| F16-1 | low      | A corrupt entry's K without an ikey: a scan's IAE     | a3c5e61     |
| F16-2 | low      | A value at /#i/didef/ hid every definition at a start | 19cd6a4     |
| F16-3 | low      | A build failed over a key /dp/-a/b (a Core write)     | dfb7df4     |
| N16-1 | none     | F2's full check misses an end above the last end      | none        |

**F16-1** (low): `IndexKeys.parseEntry`
(`java/src/bergdb/pubimp/IndexKeys.java`, line 614 at `a9e5488`) checked
that K starts with 0x2f and has no byte below 2, not that it is an ikey's
bkey. An entry key whose K has the byte 0x31 ('/' + 2, which no bkey has)
or bytes that, each less 2, are not well-formed UTF-8, written through
the Core or left by a fault, parsed; a scan that met it threw from
`hasNext()` the `IllegalArgumentException` of `Keys.bkey2ikey` ("The bkey
has no ikey"), a caller's error, not the `InternalDataException` that
020-10, section 4.4 asks for a key that does not parse. No wrong result:
the scan stopped. Found by area keys at once (seed 1, iteration 1).
Fixed in the clone's `a3c5e61`: `parseEntry` refuses such a K
(`Keys.bkey2ikeyOrNull`). Tests: `IndexKeysTester.testParseEntryRefused`
(three new cases) and `PubTesterIndex.testCorruptEntryKey` (a scan,
forward and backward, throws `InternalDataException` naming the key);
both failed before. BEFORE COMMIT OK. 020-10, section 4.4's parse rule
for K could say "the bkey of an ikey's file part"; not edited here.

**F16-2** (low: only a write through the Core or a fault makes it, but
its effect is silent): `IndexManager.scan`
(`java/src/bergdb/pubimp/IndexManager.java`, line 539 at `a9e5488`),
which a start uses to read `/#i/dii/`, `/#i/didef/` and `/#i/didel/`,
and a cleanup to read a deleted generation's entries, starts at its
prefix, inclusive, and stops at the first key for which `Keys.isPrefix`
is false; `isPrefix` is false for the prefix's own key, the first a scan
meets. A value at exactly `/#i/didef/` therefore ended the start's scan
before any definition: the database started without its indexes, writes
were not indexed, `useIndex` (which reads the definition itself) gave
stale results (in the probe `ProbeHidden`, 1 result where 2 values
matched), and a second index of the same name could be created. A value
at `/#i/didel/` hid every marker (no cleanup resumed), at `/#i/dii/` the
definitions of format 1 (not refused); one at a generation's prefix
ended its cleanup at once (its entries kept). 020-10, section 4.5 reads
every definition under the prefix, and 4.2 refuses one that breaks a
rule. Found by the start probe (seed 1, iteration 86: a definition's key
cut to the prefix). Fix: the scan takes the prefix's own key as under
it; a start refuses it (`InternalDataException`, naming the key;
`VersioningStreamException` under `/#i/dii/`), a cleanup deletes it.
Test: `PubTesterIndexJobs.testStartRefusesBadIndexData`, three new cases,
which failed before (started with bad index data 3). The listing
(`UsePrimaryBuilderImp`) and a build (`IndexBuilderImp`) start after
their prefix, exclusive, so a key equal to it does not end them; the
Core's `GetMany.Prefix` and `PrefixN` have no user.

**F16-3** (low: only a write through the Core makes it): a build
(`IndexBuilderImp`'s step, `java/src/bergdb/pubimp/IndexBuilderImp.java`,
line 470 at `a9e5488`) read every key under its directory's file prefix
(`idir` and `-`) that has an ikey, also one whose name holds a '/', such
as `/dp/-a/b`, which is no key of the directory and which `usePrimary`
skips (021-06's rule). For `/dp/-a/b` holding an object of the index's
kind, `IndexKeys.fileKey` threw `IllegalArgumentException`, and the build
failed as for a bug, at every start, so no index of that directory could
be built; for `/dp/-a/-b` or `/dp/-a/dq/-c` the build put an entry whose K
names another key (`-b`, `-c`), harmless as a scan reads that key's value
and skips it, but an entry of no key of the directory. Found by a probe
(`ProbeSlash`) while reading the build for the start probe. Fix: the step
skips a key whose name holds a '/', as the listing does. Test:
`PubTesterIndexJobs.testBuildSkipsKeysWithASlashInTheName` (each of the
three keys: the build is active, one entry, the scan gives the
directory's key only), which failed before.

**N16-1** (not BergDB's code): `F2.java`, 020-07's sketch, reads past
its extent on an end above the last end (`ArrayIndexOutOfBoundsException`,
11 of 132,525 inputs of one corpus), as its `checkObject` lacks the test
`e > size` that `ObjectFormat` has (020-07, R4). On every other input F2
agrees with ObjectFormat. The vectors' 38,579 mutants did not meet it.

Observations, no fault by the Javadoc's words:

* O16-1, for Frans: `get(key, DbObject.class)` and `get(key, C)` read a
  value of format 2 at a key with a suffix (such as `x.bin`, a byte[]
  put) as an object, while `get(key, Object.class)` there gives the
  byte[] (a String at `.txt`), and `usePrimary(DbObject.class)` and
  `usePrimary(C)` leave the key out (`UsePrimaryBuilder`'s Javadoc: an
  object is at an object key; 020-10, section 3.5 says only "a value with
  format 2's header that passes the full check"). `Connection.get`'s
  Javadoc refuses "a value that is not a stored object", and its
  `Object.class` paragraph defines a stored object at an object key; read
  so, the first two should refuse. Area kinds takes today's behaviour.
  Whether a get of an object at a key with a suffix should refuse, or the
  listing's word "object" drop the key's rule, is Frans's.
* O16-2, words of 020-10: section 4.4's parse of K ("non-empty, first byte
  0x2f, no byte below 2") could add "the bkey of an ikey's file part"
  (F16-1), section 4.5 "the prefix's own key included" (F16-2), and
  section 6.1 that a build skips a key whose name holds a '/' (F16-3).
  Not edited here (only this file is mine).
* O16-3: `ObjectFormat.isFormat1`'s Javadoc says a nested object's bytes
  start with "bergo" and the version 1; the code also asks for at least
  8 of them (a whole object's head). The reference of area guesses takes
  the code's reading.


## 4. State

Done: the fuzzer's six areas, run on F53 and s1 (section 5); three
faults found, each fixed in the clone with a test that failed before,
one commit each, BEFORE COMMIT OK under the gate lock; the fuzzer
committed with `java/stress/fuzz.sh` and a unit test per area (about 2
s). The clone's branch `main`, six commits on `a9e5488`:

| Commit  | What                                                     |
|---------|----------------------------------------------------------|
| a3c5e61 | F16-1, `IndexKeys.parseEntry` refuses K without an ikey  |
| 7725e0a | FormatFuzzer (areas objects, keys, data, kinds), fuzz.sh |
| 19cd6a4 | F16-2, `IndexManager.scan` takes the prefix's own key    |
| 00f8c98 | FormatFuzzer's areas starts and guesses                  |
| dfb7df4 | F16-3, a build skips a key whose name holds a '/'        |
| b1a659f | area starts: a build over keys that are no key of it     |

They apply to `main` at `2c248ff` without a conflict, and that tree
passes the gate (BEFORE COMMIT OK, unit 1,483, f 86, demos). To take
them: `git -C /Users/f/fl/repos/bergdb fetch
/Users/f/fl/bench/2026-11-09/clone-f16 main:f16`, then cherry-pick
`a9e5488..f16`.

Left, for whoever takes the commits: the night.sh line for the fuzzer
(proposed: `sh java/stress/fuzz.sh 12`, twelve minutes, two turns of
each area, new seeds each day) and README.md's list of scripts (one
line, `java/stress/fuzz.sh  # the fuzzer of 020-16 (8 minutes; MINUTES
SEED)`), which go together, as README.md says night.sh runs every script
it lists; 020-10's words (O16-2); O16-1 for Frans.

To continue: `java/stress/fuzz.sh MINUTES SEED` on any machine (one
core); a failure prints its area, seed and iteration, and
`FormatFuzzer AREA SEED 10 ITERATION` repeats it alone. The corpus for
the 020-07 programs written apart: `FormatFuzzer objects SEED SECONDS 0
FILE 1`, then `xcheck.py` and `XF2` as in section 2.1.


## Log

2026-11-09, 09:24. Started, in the clone
`/Users/f/fl/bench/2026-11-09/clone-f16` at `a9e5488`.

2026-11-09, 09:51. Areas objects, keys and data written and run on F53;
F16-1 found by area keys; the corpus of seed 2 (132,525 inputs) checked
by `check.py` (0 disagreements) and F2 (N16-1).

2026-11-09, 09:57. Campaign 1 on s1: `fuzz.sh 160 1000`, the four areas
in turns of a minute, seeds 1000 on, in `/root/bench/2026-11-09-f16/`.

2026-11-09, 10:01. F16-1 committed in the clone (`a3c5e61`), BEFORE
COMMIT OK; area kinds written, with bounded scans and a double index.

2026-11-09, 10:15. The fuzzer committed in the clone (`7725e0a`), BEFORE
COMMIT OK; F16-2 found by the start probe, its test failing, fixed.

2026-11-09, 10:21. F16-2 committed (`19cd6a4`); campaign 1 on s1 ended
(23 turns of a minute, seeds 1000 to 1022, clean); campaign 2 started
with areas starts and guesses (`00f8c98`, committed 10:32).

2026-11-09, 10:39. F16-3 found by a probe of the build, fixed and
committed (`dfb7df4`); campaign 2 ended (17 turns, seeds 2000 to 2016,
clean); campaign 3 started on s1 with all three fixes (`fuzz.sh 140
3000`); an interim note to the coordinator.

2026-11-09, 10:43. Area starts' build over keys that are no key of the
directory committed (`b1a659f`); the corpus of seed 5 (164,929 inputs)
checked by `check.py` (0 disagreements) and F2 (N16-1 only). The six
commits apply to `main` at `2c248ff` without a conflict, and that tree
passes the gate (10:54).

2026-11-09, 11:04. The last campaign on F53 before 13:00, as the
coordinator allowed (11:03): six areas in parallel, 32 minutes, clean;
then H2 and H3 (section 2.8). Campaign 3 on s1 stopped at 11:41 (61
turns, clean). The stop rule is met: each area ran clean for at least 32
minutes after the last fix (F16-3, 10:38).
