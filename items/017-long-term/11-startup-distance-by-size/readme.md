017-11. A startup distance that follows the database's size
============================================================

Created 2026-11-12 by Frans Lundberg. Status: open.

Open (notes only). Not for release 2026.5; perhaps for 2026.6 (026), if
the study gets that far; open-ended.

What this topic holds: whether BergDB's default startup distance (sd)
could follow the size of the database, so that no user has to choose it;
what is known of the trade it moves along (a start's time and heap
against a put's stream bytes); the rules it could follow and what they
give; what such a rule touches (P2, P5, P10, the Lean bounds, the take
after a decrease, reclaim, the API); what is not known; and a plan to
find out, cheapest decisive step first. Nothing decided, no code changed.


## 1. The question

Frans, 2026-11-12, 12:46, after 024-05's QF3 (a put's stream bytes grow
with the logarithm of the keys at a fixed startup distance): "QF3 is
really important to me. Great to see the measurement results. We are
really starting to understand this tradeoff well. Startup time vs KV put
size. I think the measurements indicate a new possibility. To remove this
as a setting the user must consider. Currently this must be set by the
user. No default is good for all databases. However, a startup distance
that depends on the size of the database in number of KVs could perhaps
be a default users won't need to think about. This is a big step and not
for now. It would need to be studied in much greater detail."

The question: can the default startup distance be a function of the
database's size, in number of KVs, such that users need not think about
it, and at what price?

Why it matters:

* **The user must choose sd today.** The default is 50 MB, clamped to 5
  to 1000 MB (`DatabaseBuilder.startupDistanceInMb`); an existing
  database keeps the value stored in its stream, and
  `Database.setStartupDistanceInMb` changes it while it runs (005-53).
  The Javadoc advises 5 for a low-end PC with 0.5 GB of RAM and 200 to
  1000 for 10 million keys or more (005-38): a choice the user makes with
  numbers in hand. 010-01's P10 (no administration, few settings: "the
  defaults work") names this a deviation.
* **No default is good for all sizes.** At 50 MB a put of a 24-byte key
  and an 8-byte value writes 268 bytes of stream at 1M keys (model), 867
  at 10M and 1,244 at 50M (measured), and 1,383 at 100M (model) (006-19,
  section 3.5). A default chosen for 100M keys, 500 MB or more, gives a
  database of 1M keys a start ten times as long and ten times the pinned
  heap that it needs (section 3.2).
* **The trade.** A put's stream bytes are a function of sd / K alone, K
  the number of keys (section 2.1); a start's time and the heap that the
  database must keep follow sd (section 2.2). So at a fixed sd a put
  costs more as the database grows (024-04's aim 2, operations
  proportional to their work; 024-05, OP3 and BD5), and with sd
  proportional to K a put costs the same at every size while a start and
  the pinned heap grow with K (010-01's P5, bounded startup). sd only
  moves along that line (006-19, section 4.2, point 7). The study is
  where on the line a default should sit at each size, and how BergDB
  would get there by itself.


## 2. What is known

### 2.1. A put's stream bytes: the scale law

* **The mechanism** (006-19, sections 3.2 and 4.1). A put makes every
  index node on its path dirty. A dirty node is not written by its
  transaction: it stays in D until its transaction is about sd behind
  the end of the stream, and the take then writes it whole; puts that
  reach it in between are absorbed. So a put costs about one node write
  for each level of the tree whose nodes outnumber the puts in a window,
  and a fraction on the level above. The window holds P = 0.7 sd / B
  puts, B the bytes a put (0.7 is a fit to today's paced take, within 15
  % at 10M and 50M keys). K and sd enter only as P / (n_c K), n_c the
  nodes a key of a level, so B is a function of sd / K alone, for a key
  shape, a value size and a node size (006-19, section 4.2, point 1).
* **Checked**: 854 bytes a put at 1M keys and 5 MB against 867 at 10M
  keys and 50 MB (006-19, sections 1 and 7.1). 024-05's OP3 cites it;
  its BD5 (proposed, not decided) states a put's bytes with retention
  forever as a function of sd / K: at most 900 at 5 bytes of sd a key,
  550 at 20, 200 at 100.
* **The curve** for 24-byte keys (`key24`), 8-byte values, uniform
  updates in transactions of 1,000 puts, retention forever, today's
  paced take (006-19, section 3.5; 007-07, sections 10 and 11):

| sd a key | Bytes a put | Keys, sd | Source |
|---|---|---|---|
| 0.5 B | 1,383    | 100M, 50 MB               | model (006-19, 4.1)                |
| 1 B   | 1,244    | 50M, 50 MB                | measured (007-07, 11)              |
| 2 B   | 1,106    | 100M, 200 MB              | model                              |
| 4 B   | 851      | 50M, 200 MB               | measured (007-07, 11)              |
| 5 B   | 854; 867 | 1M, 5 MB; 10M, 50 MB      | measured (006-19, 7.1; 007-07, 10) |
| 10 B  | 658      | 100M, 1000 MB             | model                              |
| 20 B  | 460; 524 | 50M, 1000 MB; 10M, 200 MB | measured (007-07, 11; 10)          |
| 50 B  | 268      | 1M, 50 MB                 | model                              |
| 100 B | 190      | 10M, 1000 MB              | measured (007-07, 10)              |

  The two pairs at the same sd a key differ by 1.5 % (5 bytes a key) and
  14 % (20 bytes a key), and the point at 4 bytes a key (50M keys) lies
  below those at 5: the law holds to about 15 %. Below 5 bytes a key two
  points are measured, both at 50M keys, and none below 1 byte a key.
* **At a fixed sd** each tenfold growth of K adds about one node write,
  400 to 650 bytes a put in the model's middle range (006-19, section
  4.2, point 2): log(K / window), the shape of an LSM tree's write
  amplification, but a node a level, not a rewrite of the data. **With
  sd proportional to K** a put costs the same at every K (024-05, OP3:
  "constant if sd follows the keys").
* **Other workloads** (006-19, section 4.2, points 4 to 6). The index
  costs about the same bytes for the same P whatever the value size, so
  larger values write fewer index bytes over the user's bytes (1.3 to 2.4
  times for 1 KB values against 6 to 43 for 32-byte KVs); at a fixed sd
  they put fewer puts in a window. The transaction's size does not
  matter. Sequential keys cost 90 bytes a put, a hot set about half of
  uniform updates, and random 24-byte keys (`rnd24`) about 480 bytes
  more whatever the sd. The law is calibrated on `key24` with uniform
  updates, the usual worst case.
* 024-03's fill (13-byte keys, 100-byte values, 50 MB) wrote 328 bytes a
  put at 1M keys and 722 at 10M (024-03, section 3; 024-05, OP3): the
  same growth in another workload.
* **Reclaim**, with a finite retention, adds at most about a third
  (006-19, section 3.4; 024-05, BD5).

### 2.2. What sd costs: a start's time, its heap, a cold start

* **A warm start follows the puts in its section** more than the
  section's bytes: 62 to 70 ms a MB of section at 10M keys with 8-byte
  values, 86 to 104 at 50M keys, 45 with 100-byte values and 9 with 10
  kB values (007-05, "What it means", point 1; measured with the take
  before 007-07 and before 005-57 took rule 4's reads away). Its fit:
  time ≈ 9.3 ms × section MB + 7.2 µs × puts rerun + 5.0 µs × reads
  (007-05, "Where the time goes, warm"). On today's code, 024-03 measured
  1.5 s at 1M keys and 2.1 s at 10M keys at 50 MB (13-byte keys, 100-byte
  values; 024-03, section 3), about 30 and 42 ms a MB. 024-05's BD6
  proposes at most 0.1 s a MB of sd, warm.
* **The section is near sd**: today's paced take holds it at 1.00 to
  1.14 sd (docs/levels.md, section 5, Limits; 007-06; 007-07), and below
  2 sd by `T3_take`, proved (section 2.3).
* **At a fixed sd a start hardly grows with K**: 1.5 s at 1M keys and
  2.1 s at 10M at the same 50 MB (024-03). That is P5 as it holds today
  (024-05, OP7: "A start follows sd, not the keys").
* **Large sd** (007-05, warm, F53, the take before 007-07): 12.4 s at 200
  MB and 70 s at 1000 MB with 10M keys; 26 and 86 s at 200 and 1000 MB
  with 50M keys. 10 s warm on F53 held up to about 75 MB of sd at 10M
  keys with 8-byte values and 50 MB at 50M keys, counting a section of
  twice sd; s1's CPU is about half as fast (007-05, point 1). With
  today's section of about sd, about 140 MB at 10M keys (006-19, section
  4.2, point 7).
* **Heap**: D, the index nodes changed since the startup position, which
  eviction never takes, is about 2 to 3 times sd of heap (the builder's
  Javadoc; 2.5 sd in 024-05's BD11). A start's peak is 3.3 to 4.9 times
  sd, D included, whatever the cache budget (019-45); a start needs about
  twice sd of heap above what the running database needs (docs/levels.md,
  section 7). With eviction the heap has no term in the keys today: the
  budget, D and a fixed part (024-05, BD11, proposed).
* **Cold**: 46 s on s1 at 10M keys and 50 MB since 005-57 (214 s before),
  most of it the rerun's first touches (007-05, point 3; docs/levels.md,
  section 5). Not measured at another sd since 005-57. Not bounded by a
  proof: the records at the section's ends (T4) and a cold start's reads
  into older records (024-05, OP7).
* **A transaction larger than sd** makes every start read all of it
  until about twice sd has been written after it (020-24-13, U13-7; the
  builder's Javadoc).

### 2.3. The take and its bounds (item 007)

* Each commit writes index nodes of D in whole transactions, oldest
  first (`TransSeq.take`): its share, in proportion to the stream it
  adds, share = D (o / O) (S / sd), with o the record's own bytes, O the
  section's and S the section's length; and, the deadline, every
  transaction that begins 2 sd or more before the end of the stream
  (005-49; 007-03, step 3; docs/levels.md, section 5).
* **T3** (007-01): a startup pos policy that keeps up with a distance d
  bounds the startup section. **`T3_take`** (007-08): for BergDB's take
  with any pace, if the setting is at most M in T(1) to T(k), the section
  without its last record costs less than 2 M after T(k), with and
  without restarts. **`T3_take_step`**: after any transaction the
  section costs less than the larger of twice that transaction's setting
  and what it cost before. **`T3_take_decrease`**: after a decrease to
  sd', held constant, the section never costs more than the larger of
  what it cost at the decrease and 2 sd', loses at least one unit with
  every transaction while it costs 2 sd' or more, and is below 2 sd'
  from then on.
* **sd is a function of time in the model already**: `takePolicy size
  (sd : Time → Nat) pace`, "The setting is any function of i"
  (lean/SIS/Bound.lean), but one function for every stream. Section 3.6
  says what a rule needs beyond it.
* Not proved: T4, a bound on D for a start, and a cold start's reads
  (007-03; 017-04).

### 2.4. Changing sd while the database runs

* **005-53** (done 2026-10-28, option E): `Database.setStartupDistanceInMb`,
  one call, in force when it returns. `Db.setStartupDistance` clamps to
  400 kB to 1000 MB and commits a transaction of the database's own with
  a 200 kB value, so that a meta block (one every 200 kB of stream, sd at
  offset 40, 4 bytes) records it; a start reads the last valid meta
  block's value (005-53, report, section 1.2; 017-07, section 2, which
  considers an internal KV instead). The change is a transaction in the
  stream, so P2 holds as for any transaction (005-53, report, section 5);
  `DbTesterRestart.testSameStreamAfterDecreaseWithRestartsF` checks a
  decrease with restarts, byte for byte.
* **An increase** is free in bytes: "After an increase, commits write
  less of the index until the section has grown to the setting"
  (`Database.setStartupDistanceInMb`'s Javadoc). D and the next start
  grow with it.
* **A decrease** (D4:B; 007-03; 007-07, section 10): the share follows
  the new setting at once, and while the section spans more than twice
  the new setting the deadline is at that span, which shrinks with every
  commit. At 10M keys one call from 1000 to 100 MB or from 200 to 50 MB
  wrote no record over 5.4 MB, and the section was below the new 2 sd
  after 0.08 to 0.67M puts. At 50M keys the largest records were 13 to
  15 MB, as the share's factor S / sd is up to 10 during the catch-up
  (007-07, section 11; 024-05, OP4).
* **024-31** (today, in progress): the share counts the section's span
  as at most 2 sd. At 10M keys it halves the catch-up's largest records
  (200 to 50 MB: 4.12 to 2.36 MB; 1000 to 100 MB: 1.90 to 0.99 MB) and
  lengthens the catch-up (1000 to 100 MB: 2.88M puts and 1,451 MB of
  stream, against 0.64M and 795 MB). With a setting that has not been
  lowered the stream is the same, byte for byte; the Lean theorems hold
  for any pace; 50M keys not run (024-31, sections 1 and 9). An sd that
  follows K changes by itself, and goes down after mass deletes, so this
  is the mechanism such a rule would lean on.
* **Reclaim** (finite retention): an iteration begins after at least 2
  sd of stream, read from the live setting since 005-61; a larger sd
  cuts later and keeps more on disk (the builder's Javadoc; 020-24-06,
  U6-2).

### 2.5. The principles it touches

* **P2, a deterministic stream** (010-01): the stream's bytes are a
  function of the accepted transactions and the stream-affecting
  settings, not of timing, threads, restarts or the cache; Frans,
  2015-12-28: "a restart can be inserted between any two transactions
  without affecting the bytes in the stream". sd shapes the bytes (it
  decides which index nodes each record takes), which is why it is kept
  in the stream (005-53, report, section 1.2).
* **P5, bounded startup** (010-01): "the time does not grow with the
  data"; 2013-08: "a short and constant startup time (O(1) in big O
  notation). This is important as your data grows."; 2016-05-05: "The
  startup time of DB must be O(1), or at least not greater than
  O(log(G.size()))" (docs/sources/startup.md, point 4).
* **P10, no administration, few settings** (010-01): "the defaults work:
  there is no need to tune settings for good performance". Its "Where
  BergDB stands" names the default sd a deviation ("from about 10M keys,
  200 to 1000 MB does (005-38)") and quotes 2013-04-08: "It is not clear
  to me how to do automatic startupDistance changes based on db size."
* **Aim 2 of 2026.5** (024-04): QF3 is decided for 2026.5: a put's bytes
  stated as a function of sd / K, the default sd fixed, the curve
  documented (024-05, QF3). This topic is what may come after.

### 2.6. Levers beside sd

* **A compact stored form of the index nodes** (026-01, moved from
  024-20; for 2026.6): encoding C keeps 38 to 47 % of today's index
  bytes. As sd counts stream bytes, a compact section holds more
  transactions: a stream at 50 MB wrote 48 and 53 % less than today's in
  the overwrites at 1M and 10M keys, and a start reruns about 1.6 to 1.8
  times the transactions (026-01, sections 1 and 5.2). Its QC3 asks
  whether sd stays in stream bytes and the default is set again by
  measurement. It moves the trade's line, not its shape.
* **The take's pacing** (006-19, section 6.2): up to 10 to 20 % at the
  same sd, if the paced take wrote as a window of sd rather than 0.7 sd;
  why it does not is not known.
* **Delta writes of key nodes** (006-19, section 6.6): 2 to 3 times fewer
  bytes, estimated, with chains to read; kept for later.
* **Node fan-out** (006-19, section 6.4): small; 024-19's study.

### 2.7. Frans's notes, 2008 to 2016 (F1-007)

From F1-007's notes (in the f1 repo, `a/007-bergdb-261012/bergdb/doc/`):

* 2009-11-01, the old log (`log-old/2008-2011-log.txt`), "IDEA: continuos
  check-pointing": let index nodes "write its state (pointers) to TStream
  iff it is older than 100 MB (in TStream) when its pointers changed? This
  would be SO nice - no explicite check points! To start database, just
  read the last 100 MB." 2010-05-10: "I use a startup distance (for
  example 100 MB) and "continous checkpointing". I like this approach."
  years.txt, 2009: "continuos check-pointing" and fixed startup distance.
  The distance was a fixed number from the start.
* 2013-01 notes, "startupDistance": the setting is needed by the start
  before the database has really started, so it is in the meta block;
  "It would be nice to be able to increase it if necessary. Decreasing it
  seems less important."
* 2013-04 notes (status of 2013-04-08), "Startup distance", "Automatic
  increase / decrease": "Should we have automatic increases / decreases
  of startupDistance? I do not know how to do this best. Alternative
  include: * After a Reclaim scan, KV count is known. * Percentage of
  stream size that is occupied by dirty node writes. How to increase
  startup distace with DB size? We do not know. See study on
  startupDistance vs stream size. Made with fixed db size of 1M. How
  about startupDistance of 1M and 10M and varying db size: 10k, 30k,
  100k, 300k, 1M, 3M. 12 cases to measure." Its conclusions: "It is not
  clear to me how to do automatic startupDistance changes based on db
  size." and "We need measurement of stream space of dirty node KVs vs
  ordinary KVs." For a large decrease: steps with "a dummy transaction
  after each change. This is to avoid a huge transaction with dirty
  nodes." (today D4:B, one call; 007-03).
* So the question is thirteen years old. Both of 2013's measures are
  among the candidates of section 3 (reclaim's count as a source of K,
  section 3.3; the index's share of the stream, rule R6), and the twelve
  cases he proposed are what 006-19's scale law has since answered in
  part: the bytes depend on sd / K alone.


## 3. What a size-dependent default could be

### 3.1. The trade, in one line

From sections 2.1 and 2.2, for small values:

* a put's bytes B = g(sd / K), falling as sd / K grows;
* a warm start about 40 to 100 ms a MB of sd on F53, and little else that
  grows with K (1.5 s at 1M keys, 2.1 s at 10M, both at 50 MB);
* the heap that must be kept, D, about 2 to 3 sd; a start's peak 3.3 to
  4.9 sd.

So a put's bytes are constant if and only if sd grows as K, and then a
start's time and the pinned heap grow as K: at 5 bytes of sd a key, about
0.2 to 0.5 s of warm start and 10 to 15 MB of pinned heap for each
million keys. A fixed sd keeps the start constant (P5) and pays about one
node write a put for each tenfold K (aim 2). Between them, sd
proportional to K^α for 0 < α < 1 gives a start that grows as K^α and
bytes that grow by 1 − α node writes for each tenfold K. No rule escapes
the line; a rule chooses a path along it, and a cap returns to the fixed
sd's behaviour above it. Only a format lever (2.6) moves the line.

In outline, a leveled LSM tree makes the fixed-sd choice: its recovery
replays a log bounded by its memtables, and it pays log K in compaction
(006-19, section 5, for its write amplification).

### 3.2. Candidate rules

Each rule gives the setting that the take uses in transaction i, sd(i),
from the database's state before T(i). K is the number of live keys
(section 3.3 for how BergDB would know it). The floor and the cap are
today's clamps, 5 and 1000 MB, unless said.

* **R0, today**: sd = 50 MB, or the user's value. The baseline.
* **R1, c bytes a key**: sd = c K, at least 5 MB, at most 1000 MB. c = 5
  keeps today's 870 bytes a put of `key24` (at 10M keys) at every K up to
  200M keys, where it reaches the cap; c = 20 gives 460 to 524 up to 50M
  keys. 006-19 suggests it (section 6.1: "for example 20 bytes a key,
  capped by a memory budget"; its "Risk": "what it does at a start and
  on a shrinking database needs a design") and recommends the curve for
  the documentation (section 8, point 2), which QF3 decided for 2026.5.
  A variant, **R1p**, counts in puts rather than bytes: sd such that the
  window holds p puts a live key, the law's own variable (P / K, 2.1),
  which does not depend on the value size or on the stored form (026-01,
  QC3). In bytes it is p K times the section's mean bytes a put, a fixed
  point, as the bytes a put fall when sd grows.
* **R2, today's below a size**: sd = max(50 MB, c K), at most 1000 MB.
  At c = 5, R0 below 10M keys and R1 above.
* **R3, a power of K**: sd = 50 MB × (K / 10M)^α, 0 < α < 1, with the
  floor and the cap. At α = 1/2 the start grows as the square root of K
  and a put's bytes by about half a node write for each tenfold K. α = 0
  is R0 and α = 1 is R1 at c = 5. A logarithm (sd proportional to log K)
  would keep P5's 2016 wording, O(log), but buys little: K / log K grows
  nearly as K.
* **R4, steps**: R1, R2 or R3 rounded up to a power of two times 50 MB
  (down to 6.25 MB and up to 800 MB), with hysteresis: up when the rule's
  value passes the next step, down only when it falls below half of the
  step below. About one change for each doubling of K, seven from 6.25
  to 800 MB, each a transaction like today's setter's.
* **R5, from the stream's size**: sd = f times the kept stream (from the
  first position kept to the end), with the cap. Free to know (3.3), but
  it measures what was written, not what is stored: with the default
  retention, forever, it grows with every update, so updates of a fixed
  K would drive sd to the cap; under reclaim the kept stream is 4.5 to 6
  times a fresh database's (024-05, ST3), a proxy of the size within that
  factor.
* **R6, feedback on the index's share** (2013's second measure): sd up
  one step while the index nodes take more than a target share of the
  stream written in the last windows (for example three times the user's
  records), down one step while they take less than a lower target. It
  needs no K, and it follows the key shape, the skew and the value size,
  which a rule in K does not (2.1: a hot set costs half, sequential keys
  90 bytes); for uniform updates it ends where R1 does, start and heap
  included. A control loop: its stability is to be shown.

What they give for `key24`, 8-byte values and uniform updates: sd, and a
put's stream bytes. "m" is 006-19's model, "l" the scale law applied to a
measurement at the same sd a key (2.1's table), "i" interpolated in that
table; the others are measured.

| Rule                       | 1M keys             | 10M keys     | 100M keys             |
|---|---|---|---|
| R0, 50 MB                  | 50 MB: 268 m        | 50 MB: 867   | 50 MB: 1,383 m        |
| R1, c = 5                  | 5 MB: 854           | 50 MB: 867   | 500 MB: 870 l         |
| R1, c = 20                 | 20 MB: 460 to 524 l | 200 MB: 524  | 1000 MB (cap): 658 m  |
| R2, max(50 MB, 5 B a key)  | 50 MB: 268 m        | 50 MB: 867   | 500 MB: 870 l         |
| R3, α = 1/2                | 16 MB: about 550 i  | 50 MB: 867   | 158 MB: about 1,160 i |

And what each sd costs (2.2): a warm start at 40 to 100 ms a MB, D at 2
to 3 sd, a start's peak at 3.3 to 4.9 sd. Measured: 1.5 to 2.1 s at 50 MB
(024-03), 12.4 s at 200 MB and 70 to 86 s at 1000 MB (007-05, the old
take); nothing at 100M keys. s1 about twice as slow.

| sd      | Warm start, F53 | D in the heap  | A start's peak  |
|---|---|---|---|
| 5 MB    | 0.2 to 0.5 s    | 10 to 15 MB    | 17 to 25 MB     |
| 16 MB   | 0.6 to 1.6 s    | 32 to 48 MB    | 53 to 78 MB     |
| 50 MB   | 2 to 5 s        | 100 to 150 MB  | 165 to 245 MB   |
| 158 MB  | 6 to 16 s       | 0.3 to 0.5 GB  | 0.5 to 0.8 GB   |
| 200 MB  | 8 to 20 s       | 0.4 to 0.6 GB  | 0.7 to 1.0 GB   |
| 500 MB  | 20 to 50 s      | 1.0 to 1.5 GB  | 1.7 to 2.5 GB   |
| 1000 MB | 40 to 100 s     | 2 to 3 GB      | 3.3 to 4.9 GB   |

Read together:

* **R1 at c = 5** keeps 870 bytes a put up to 200M keys. Its warm start
  is 0.2 to 0.5 s a million keys: 2 to 5 s at 10M, as today, and 20 to
  50 s at 100M. Cold on s1, if 46 s at 50 MB were linear in sd, 7 to 8
  minutes at 500 MB (not known, question 4). D grows by 10 to 15 MB a
  million keys.
* **Below 10M keys R1 gives a smaller sd than today**: at 1M keys three
  times the bytes a put (854 against 268) for a start and a pinned heap
  ten times smaller. R2 keeps today's there. Which a small database
  wants is question 10.
* **R1 at c = 20** writes 40 % fewer bytes a put than R0 at 10M keys
  (524 against 867) and 63 % fewer at 50M (460 against 1,244), for warm
  starts of 8 to 20 s at 10M keys; at 100M keys it is capped.
* **R3 at α = 1/2** at 100M keys: starts of 6 to 16 s and about 1,160
  bytes a put, against 2 to 5 s and 1,383 for R0 and 20 to 50 s and 870
  for R1.
* At 1G keys R1 at c = 5 wants 5 GB: past the cap and past what the meta
  block's 4-byte field holds (3.7).

### 3.3. "The size of the database", and how BergDB would know it

The scale law's variable is K, the live keys; Frans's words are "the
size of the database in number of KVs". The candidates:

* **Live keys, K.** Not known today. The Core keeps no count (a reading
  of `Db`, `Dag` and `Reclaim` on 2026-11-12): `DbScan` counts by a full
  scan, and reclaim's `IterationInfo.kvCount`, with a finite retention
  only, counts what its iteration scanned and keeps it in reclaim's table
  in the stream (Frans's first measure of 2013). A count could be a
  by-product of the paths that puts and deletes already follow: a put
  whose leaf holds a live klong of its compare value replaces a key (the
  writer makes that klong dead, 024-23), else it adds one; a delete that
  finds a live key removes one. It would count every key of the Core,
  BergDB's own included (index entries, reclaim's table, the setter's
  dummy key). It could be kept for a start in three ways:
  (a) a field of each record, the count after it: a record format
  change, for 026's stable format or later;
  (b) a field of the meta block, the count after the record that ends at
  its position (005-68), which a start reads and brings up to date by
  the rerun of the transactions after it (all of them are in the
  section, which is longer than 200 kB): a meta block format change;
  (c) reclaim's count, only with a finite retention and an iteration
  late.
  The tree model (024-12) defines a tree's live keys; a Java count would
  be checked against it by the tree checker.
* **Live bytes** (keys and values): the same mechanism, a second count.
  With sd proportional to the live bytes, the window's puts a key stay
  about the same for every value size (P = 0.7 sd / B, and B grows with
  the value as the live bytes do), so a put's index bytes do too, where
  a rule in K gives large values fewer puts a window. A start, which
  follows the puts in the section (2.2), then grows as K for every value
  size. R1p has the same property directly.
* **The stream's length, or the kept stream.** Free and exact at a start
  (the end of the stream, the first position kept): R5. Not the size
  (3.2, R5).
* **Key nodes.** Since format 7's merges (024-21) the live key nodes are
  at most S + (n + S − 1) / (m − 1) for n live keys in S segment trees
  (docs/levels.md, section 5), and at least about n / 30 at node size 30:
  K within a factor of about 4 when the segment trees are large. No
  count either.
* **The index's share of the stream** (R6): the take knows the bytes it
  writes and each record's own bytes (o and O of the share), so a share
  over the last windows is a function of the section's records, known at
  a start from the section.

### 3.4. When sd changes, and what a change costs

When:

* **On every commit** (R1 to R3 as they stand): the take reads sd(i) =
  rule(K before T(i)); no transaction of its own; the setting moves in
  small steps, and the share's factor S / sd stays near 1 except after a
  large change of K in one transaction (a mass delete). A start must
  compute the same sd at the same record, so it needs K at every record,
  (a) or (b) of 3.3. The meta block's field would hold the rule's
  constant, not the setting.
* **In steps** (R4, R6): each change a transaction of the database's
  own, as `Db.setStartupDistance` writes one today, so a start reads the
  setting as today and needs K only to decide the next step: no record
  format change with K kept as in (b) or (c). About seven changes from
  6.25 to 800 MB, 0.2 MB of stream each.
* **At a start**: not on its own. A start that chose sd from the size it
  finds would make the bytes depend on where restarts fall, against P2
  (3.5), unless it computes what the running database would have had at
  that record, which is "on every commit".
* **On the user's call only** (R0 with advice): the documentation of
  2026.5 (QF3), or a method that returns the rule's value for the user
  to set. The fallback if no rule is chosen.

What a change costs:

* **An increase**: no catch-up; commits write less of the index until
  the section has grown (2.4). A put's bytes fall; D, the next start and
  a start's heap grow over about sd of stream. Under R1 that growth is as
  slow as K's.
* **A decrease**: a catch-up (2.4). The section shrinks with every commit
  (`T3_take_decrease`), and the share's factor writes larger records
  meanwhile: 3.3 to 5.4 MB at 10M keys and 13 to 15 MB at 50M for a
  fourfold or tenfold decrease, halved at 10M by 024-31's cap at the
  price of a longer catch-up. A halving, R4's step, is not measured.
  Under a rule, decreases come from deletes: a delete of 90 % of the keys
  in one transaction cuts R1's sd tenfold at the next commit, on top of
  the deletes' own index writes (88 % of a delete workload's stream is
  index, 026-01, section 1). Hysteresis (R4) defers it. An sd larger than
  the rule wants costs start and heap only, never correctness.
* **Flapping**: a queue (puts and deletes of the same keys) or a cache
  with expiry holds K near one value; a rule without hysteresis near a
  step would change sd back and forth.

### 3.5. P2, the deterministic stream

A rule keeps P2 if and only if sd(i) is a function of the accepted
transactions before T(i) and the stream-affecting settings, and a start
recomputes the same value at the same record.

* K, the live bytes, the key nodes, the stream's length and the index's
  share are all functions of the accepted transactions. So R1 to R6 can
  keep P2, with K kept as in 3.3 (a) or (b), or each change written as a
  transaction (steps). Reclaim's count (c) is written by reclaim's own
  transactions, which are a function of the stream too.
* A rule in the heap, the cache budget, the machine or the clock (a start
  budget in seconds) would break P2: the bytes would depend on the run.
  Such an input must become a setting kept in the stream, as sd is
  (005-53's rule: a setting that shapes the stream's bytes is kept in the
  stream, one that does not lasts for the run). The cache size, a setting
  for the run today, would become one that shapes the bytes if a rule's
  cap came from it.
* Checked as today: a restart after every few commits gives the same
  stream (as `testSameStreamAfterDecreaseWithRestartsF` does for a
  decrease), and StreamDigest, with a workload that crosses steps up and
  down.

### 3.6. The Lean model

* T3's statements for the take take sd as a function of time already:
  `takePolicy size (sd : Time → Nat) pace`, `sd i` the setting in
  transaction i, "any function of i" (lean/SIS/Bound.lean). It is one
  function for every stream: "in Java it changes only by
  `Db.setStartupDistance`". A rule makes sd a function of the stream
  before T(i) (through K), which the trusted definition does not allow as
  it stands.
* Two ways. (a) Make `takePolicy`'s sd a function of the stream and i (a
  change of a trusted definition); the pace is already "any predicate on
  the stream and T(i)". `take_step` rests on `takePolicy_keepsUp`, the
  take keeping up with max(2 sd, span) in the transaction at hand, so the
  theorems should carry over, with the cap as `T3_take`'s M; not checked.
  (b) For one run, define sd(i) as the rule's value along that run and
  show that the two policies agree on the run's streams: a lemma, no
  trusted change.
* `T3_take_decrease` assumes the setting constant after a decrease. For
  a setting that keeps falling (deletes over many commits),
  `T3_take_step` applies: the section after a transaction costs less
  than the larger of twice the current setting and what it cost before,
  whatever the sequence of settings.
* The theorems bound the section's stream bytes, not a start's time.
  Under R1 the bound is a function of K, 2 c K. A bound on a start's time
  is T4's (007-03, not proved); under a rule it would be restated in K.
* A Java count of K would be checked against the model's tree (024-12,
  `lake exe treecheck`), not proved.

### 3.7. What else a rule touches

* **024-05's bounds** (proposed). BD5 becomes a constant (at most 900
  bytes a put at c = 5 for `key24`). BD6 (at most 0.1 s a MB of sd)
  becomes a start in K, about 0.5 s a million keys at c = 5. BD11 (the
  heap with eviction, no term in the keys) gets one: D at 10 to 15 bytes
  a key at c = 5, beside MEM's about 130 bytes a KV without eviction
  (BD12). OP7 ("A start follows sd, not the keys") no longer holds.
* **Reclaim**: iterations start after 2 sd of growth, so under R1 they
  are spaced as K, as an iteration's rewrite is (at most the live data
  once; 006-19, section 3.4). The stream kept (024-05, ST3 and QF1) would
  be measured again.
* **The clamps**: the Pub API's 5 to 1000 MB, the core's 400 kB to 1000
  MB, and the meta block's 4-byte field, at most 2,147 MB (`MetaBlock`,
  offset 40). R1 reaches 1000 MB at 200M keys at c = 5, at 50M at c = 20;
  above, the cap returns to R0's growth. Past 2,147 MB the field needs a
  wider format or a unit.
* **The API**: what `startupDistanceInMb` and `setStartupDistanceInMb`
  would mean under a rule: (a) a user's value fixes sd and turns the rule
  off, today's behaviour for whoever sets it; (b) it sets the rule's
  constant; (c) it sets the cap. P10 favours one setting or none. A
  planned fast restart lowers sd for a while (006-06; 005-53, "The
  issue"): under (a) it would turn the rule off until it is turned on
  again.
* **Existing databases**: 2026.5 refuses 2026.4's (record format 7), so a
  rule in a later release decides only what a 2026.5 database does.
* **The compact stored form** (026-01): with encoding C the same sd holds
  1.6 to 1.8 times the transactions (QC3), so a rule's constant in bytes
  a key would be set again with it; R1p's would not.


## 4. What is not known

1. **P5 or aim 2.** Is a default whose warm start grows with K (0.2 to
   0.5 s and 10 to 15 MB of pinned heap a million keys at c = 5)
   acceptable, or must a start stay bounded by a constant, with a cap
   that returns to today's growth of the bytes above it? Frans's
   question; the rest depends on it.
2. **The scale law where large databases live.** Below 5 bytes of sd a
   key two points are measured (1 and 4 bytes, at 50M keys), none below
   1 byte; 100M keys never ran (024-05, section 5). Does a put's bytes
   stay a function of sd / K at 0.5 to 10 bytes a key, and within what
   error (1.5 and 14 % at the two measured pairs)?
3. **A start under a rule.** At a fixed sd / K, does a warm start grow as
   K (the puts rerun) or faster (deeper paths, more reads a put: 62 to 70
   ms a MB at 10M keys, 86 to 104 at 50M in 007-05)? Do D and a start's
   peak stay at 2 to 3 and 3.3 to 4.9 sd at every K?
4. **A cold start under a rule.** 46 s at 10M keys and 50 MB on s1 is
   the only point since 005-57. Is it linear in sd? If so, R1's default
   gives cold starts of minutes at 100M keys.
5. **Which measure.** K, the live bytes, puts a key (R1p) or the index's
   share (R6)? Which fits other key shapes (`rnd24`, sequential keys),
   skew (a hot set) and value sizes, where a rule in K gives too much or
   too little?
6. **The count's price.** Bytes a record or a meta block field, CPU on
   the write path, exactness through splits, merges, root collapse,
   reclaim's rewrites and the rerun; whether BergDB's own keys count.
7. **When to change.** On every commit or in steps; the step and the
   hysteresis; what a halving costs on 024-31's capped take (records,
   catch-up); what a mass delete costs with the rule following.
8. **A feedback rule's stability** (R6, R1p): does it settle without
   oscillation when a workload's mix changes?
9. **The cap.** 1000 MB, a heap figure (which would make the cache size
   shape the stream, 3.5), or a start budget in MB of sd? And past the
   meta block's 2,147 MB?
10. **Small databases.** The floor, 5 MB (R1), or today's 50 MB (R2)?
    Frans, 2026-10-26, on measurements: "We should use at a startup
    distance of at least 50 MB." (007's log); whether that also speaks
    for the default's floor is his call.
11. **The API and P10.** Does the user keep a setting, and what does it
    mean (3.7)?
12. **The Lean model.** Does `T3_take` carry over to an sd that is a
    function of the stream (3.6), and does the deadline at max(2 sd,
    span) behave as intended when sd moves at every commit?
13. **Reclaim under a rule.** The stream kept (ST3) and the pacing, with
    iterations spaced as K.
14. **The release timing.** If K must be in the record format (3.3, a),
    it is decided before 2026.6's stable format is fixed (026); in the
    meta block or by steps it can come later.


## 5. A plan for studying it

Ordered by cost, the decisive steps first. Each step: what it answers,
how, the machine time, and what Frans decides. Heavy runs take a slot
(`slot.sh`), bytes-only runs one slot, timing runs both. Runs below 50 MB
of sd stand for larger databases by the scale law; they are not settings
to cite in docs/levels.md (Frans, 2026-10-26).

1. **The principle** (question 1). How: Frans reads section 3.2's tables;
   if he wants more, an agent extends 006-19's model
   (`/Users/f/fl/bench/2026-11-09/a19/wamodel.py`) with a start's time
   (007-05's fit, refitted to 024-03's starts on today's code) and D's
   heap, and prints R0 to R4 and R1p for K from 100k to 1G, for 8-byte
   and 100-byte values, with and without encoding C (026-01). Machine
   time: none (seconds of Python; about an hour of an agent). Frans
   decides **D1**: may a default's start grow with K, and up to what? If
   not, the topic parks with R0 and 2026.5's documentation (QF3).
2. **The scale law at the sizes that matter** (question 2). How: 024-05's
   GM4, which is 006-19's M2 (section 7.2, its commands): WriteBench at
   10M keys with sd 5, 20 and 100 MB (standing for 100M keys at 50, 200
   and 1000 MB), and at 1M keys with 0.5 and 2 MB through the core (100M
   at 50 and 200 MB; the core's floor is 400 kB). Machine: F53, one slot,
   bytes only, a 12 GB heap: about 30 to 40 minutes for the three at 10M
   (8 to 12 minutes each) and 10 for the two at 1M. Answers whether a
   put's bytes are g(sd / K) at 0.5 to 10 bytes a key, and turns the
   model's 100M row into a measurement by the law. Frans: nothing, unless
   the law fails; then a rule in K is in question and R6 comes forward.
3. **A start under a rule** (questions 3 and 4). How: `key24` databases
   at 5 bytes of sd a key, 1M keys at 5 MB, 10M at 50 MB, 30M at 150 MB
   (50M needed a 22 GB heap; 30M fits F53), made by WriteBench's updates;
   three warm starts each with 007-05's StartupBench; a start's heap peak
   by 019-45's `RerunHeapProbe`. Cold on s1 at 1M and 10M keys with
   007-05's s1 scripts (other sessions time there: check ps first).
   Machine: F53 about 1 to 1.5 hours in one slot to make them, 30 minutes
   with both slots to time the starts; s1 a night. Answers the start and
   the heap a million keys at a fixed sd / K, and whether they are linear.
   Frans decides **D2**: the constant (c, or α) and the cap.
4. **Knowing K** (questions 5, 6 and 14). How: a design note in this
   topic, no runs: the count's mechanism (3.3), where it is kept (a
   record field, the meta block, steps), what a start and the rerun do,
   BergDB's own keys, its check against the tree model (024-12); R6's
   control loop on paper with step 2's numbers. Machine: none; an agent,
   about half a day. Frans decides **D3**: the measure, and whether a
   field is reserved in 2026.6's stable format. This decision has a
   deadline: 026's format work.
5. **Changes** (question 7). How: on 024-31's capped take once it has
   landed, at 10M keys: a doubling (50 to 100 MB), a halving (100 to 50
   MB), and a delete of 90 % of the keys with sd following R1 (50 to 5
   MB) and with R4's hysteresis; 024-31's `run.sh`, `catchup.py` and
   `ratchet.py`. Machine: F53, one slot, bytes only, three runs of about
   20 to 30 minutes. Answers the largest record and the catch-up's length
   for a rule's changes. Frans decides **D4**: every commit or steps, and
   the hysteresis.
6. **Other workloads** (question 5). How: with the measure of D3 and the
   constant of D2: a hot set, sequential keys, `rnd24`, 100-byte and 1 KB
   values (006-19's M3), at 1M and 10M keys. Machine: F53, one slot,
   bytes only, about six runs of 10 minutes. Answers whether a rule in K
   fits them, or R6 or R1p is needed.
7. **A prototype and the model** (questions 8, 11 and 12). How: in a
   clone, the rule as a policy beside the take, the count, the API's
   meaning (3.7, a to c); a restart-invariance test that crosses steps;
   StreamDigest; before-commit and level2.sh. In Lean, sd as a function
   of the stream (3.6, way a or b), `lake build`. Machine: about an hour
   of holds for the gates; an agent, about a day. Frans approves the
   trusted change and any format change.
8. **100M keys** (questions 2 to 4 at the size itself). How: 024-05's
   GM7 with the rule (500 MB at c = 5): F53 cannot hold 100M keys in
   memory, so eviction on a FileStream, or s1 over a night; a put's
   bytes, a warm and a cold start. Machine: hours. Answers the rule at
   the size it is for.
9. **The decision** (Frans): a rule into a release (2026.6 if D3's field
   is in its format, else later), with docs/levels.md, section 5, the
   Javadoc of both setters and 024-05's bounds restated in K; or park.

| Step | What | F53 | s1 | Frans decides |
|---|---|---|---|---|
| 1 | the principle, the curves  | none                        | none    | D1: may a start grow |
| 2 | the scale law, 0.5 to 10 B | 45 min, one slot            | none    | only if it fails     |
| 3 | a start under a rule       | 1.5 h one slot, 30 min both | a night | D2: c or α, the cap  |
| 4 | knowing K                  | none                        | none    | D3: measure, format  |
| 5 | changes                    | 1.5 h, one slot             | none    | D4: steps or not     |
| 6 | other workloads            | 1 h, one slot               | none    |                      |
| 7 | a prototype, Lean          | 1 h of gates                | none    | the trusted change   |
| 8 | 100M keys                  | hours, with eviction        | a night |                      |
| 9 | the decision               | none                        | none    | the release          |

"One slot" runs count bytes only; "both" is the timing hold of step 3's
starts.


## 6. Frans's notes

2026-11-12, 12:46, on 024-05's QF3 (decided for 2026.5 as recommended:
a put's bytes stated as a function of sd / K, the default sd fixed, the
curve documented): "QF3 is really important to me. Great to see the
measurement results. We are really starting to understand this tradeoff
well. Startup time vs KV put size. I think the measurements indicate a
new possibility. To remove this as a setting the user must consider.
Currently this must be set by the user. No default is good for all
databases. However, a startup distance that depends on the size of the
database in number of KVs could perhaps be a default users won't need to
think about. This is a big step and not for now. It would need to be
studied in much greater detail. [...] Move this discussion to a new item
of 017. Have a subagent at xhigh write the item. Gather what to already
know in the item. Plan for studying deeper what we do not know yet. We
put it in 017 since we don't know if it will make it into 2026.6. It is
currently open-ended."

His earlier notes on the same question, 2008 to 2016, are in 2.7.


## 7. Log

2026-11-12. Created at Frans's request (12:46), from 024-05's QF3, by an
agent ("sdk") of the day's coordinator (coord-1112), Claude (Opus 5.5,
Claude Code): what is known (024-05, 006-19, 007, 005-53, 024-31, 019-45,
010-01, 026-01, F1-007's notes), the candidate rules with their numbers,
what they touch, the open questions and a plan. No runs, no code.


## State

2026-11-12, 13:03.

* **Done**: sections 1 to 7, written from the items cited, the Javadoc
  of `DatabaseBuilder.startupDistanceInMb` and
  `Database.setStartupDistanceInMb`, lean/SIS/Bound.lean and
  BoundTheorems.lean, and F1-007's notes; a grep of the Core for a count
  of live keys (none but `DbScan` and reclaim's `IterationInfo.kvCount`).
* **Not done**: nothing of the plan; no clone, no branch, no run. 017's
  index line and the commit are the coordinator's.
* **To continue**: step 1 of section 5, with Frans.
