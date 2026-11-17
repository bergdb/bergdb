# 023 Codex options. The main alternatives

2026-11-10. Phase 1. Input: 023-01 and 023-02 at 93f0fe94.
The baseline is 2f018b9e. The stopped prototype is on
020-30-codex-proto, 680764e2. This study changes no code.

## 1. Recommendation

Study small versioned edits first: remove an empty subtree in the deleting
transaction, repair underfill when needed, and sweep old entries in bounded
steps. This is option B below. It keeps the present node histories, lazy
writing and startup design. It offers a way to keep the good scan result
without making a new path for every delete.

Keep the whole-path copy, option A, as a reference for correctness and cost.
Its present write cost is too high to select it for production. Study
same-id pruning at the retention frontier, option C, as a second, limited
investigation. It may save copying, but changes more of the correctness
argument. A rebuild in steps, option D, is a reserve option.

None is a completed solution to R1 to R27. In particular, no small constant
K for cleanup, no complete reclaim progress bound, and no performance result
at 10M or 100M keys has been established.

## 2. What must be solved together

Here B is the node limit, 30 klongs by default; H is the key-node path
height; R is the retain duration; f is the first available lookup time.

There are four jobs, with different deadlines.

1. Stop scans passing empty subtrees. Do this when a delete makes them
   empty. It must work at every available time, with R forever too.
2. Remove expired entries from nodes that still serve live data. Deleted
   entries and overwritten entries both need this. Waiting for another
   ordinary write to fill their node is not enough.
3. Keep shape and reclaim work bounded. Empty removal gives R12 (a).
   Merging, root contraction or an equivalent rebuild is needed for the
   stronger comparison with a fresh twin, R12 (b), and live-key height.
4. Release memory and reduce containers after their entries leave.
   Eviction alone does not shorten a path array or a hash table.

These are separate decisions. An empty node can be unlinked while the old
node stays in history. An expired klong can remain in a nonempty node even
after every empty node has gone. A small current tree can coexist with a
large retained stream and many cached historical objects.

023-02, section 2, covers most of this inventory. The probes also found
old metadata after a cut, counted across NodeCollection's startup Rule R
map and position cache. Include both in the audit, alongside K16 and K18.
Audit Db.opMarks, replacedInTrans, TransNodes and serialization buffers
for retained capacity too. Their names here are audit targets, not a claim
that each is an unbounded leak.

All options below include the memory work in section 7 and a bounded end
for reclaim's touch, as in 021-25, fix (a). The end-key scan of 021-28
remains useful. Neither fix removes the deleted head of a range.

Pure deferred cleanup fails even the amortized R9. After D empty nodes
are left, repeat the same empty scan q times without writes. Its cost is
qD; the update credit stays fixed. Choose D much larger than H, then q
large enough, and R9's inequality fails. Cleaning up at a later time also
leaves repeated scans at an earlier available time costly.

## 3. A. Copy the current path on each delete

### 3.1 Mechanism

The successful deleting transaction builds the leaf's current contents
without the key. It builds replacement parents up to the space root.
Each replacement has only the entries needed now. An empty child goes.
This continues through the leaves that connect successive key segments.
The empty map gets one empty root.

The transaction repairs a child below a minimum occupancy. It takes an
adjacent sibling, merges if the pair fits, otherwise redistributes.
It contracts a segment root with only one child. Old nodes keep the
histories needed by earlier lookups. A new top node selects the new root
from the delete's time. Several changes in one transaction reuse nodes
created by that transaction.

This is the prototype's method. It uses a minimum of B / 4 entries,
rounded down. For B = 30 that is 7. It prefers the left sibling and
sets a changed routing separator to its live child's lower bound.
These choices are deterministic.

For the wider R7, this alone is incomplete. Overwrites can still leave
shadowed entries in live nodes. Add an explicit bounded sweep that makes
fresh current versions of those nodes and their needed links. Merely
touching a node copies its old entries too.
Reclaim would own this extra sweep when R is finite.

### 3.2 Bounds and costs

No empty subtree remains in the selected current tree. Each historical
tree keeps the same property if each delete was handled this way when
that tree was current. With occupancy repair, height and node count
depend on the keys live at that lookup time. Section 9 gives the bound.

An isolated successful delete can create O(H) key nodes, and a top node.
At B = 30 each written key-node image is at most 512 bytes. Copying a
path can therefore add up to about 512H bytes of key-node images, plus
siblings, the top, the delete record and dirty-list fields. Writing is
lazy; several deletes in a batch can share these costs.

This loses much of the present coalescing of changes to one dirty node.
Successive transactions create different node identities. Those earlier
nodes may be needed throughout R. This is a real cost of this option,
not just a poor cache policy.

For each new key node the present accounting starts at 80 + 24C bytes,
where C is its array capacity, before handles, table entries and pointees
(KeyNode.getMemSize; Residents). Thus a delete also allocates O(BH)
index memory in the worst case. Historical paths can accumulate through
the retained window. Eviction limits residency, not retained stream bytes.

R11 asks for O(1) amortized new nodes. Whole-path copying does not meet
that part as written. Even for short keys, deleting half a large balanced
map leaves height of order log N. Each transaction still copies its path.
O(H) work and O(H) nodes changed are different requirements from O(1)
new nodes.

### 3.3 Risks and work

History and readers have a fairly direct argument: retain the old tree;
publish a new tree at the transaction's time. Earlier entries must not
be edited. Nodes created and removed in one transaction must leave neither
new unreachable nodes nor current entries in retired nodes.

The creation order changes. Startup must replay it exactly, including
merges, root contraction and same-transaction reuse. A format distinction
is required even if every node has the old byte layout. The prototype
uses record format 6 and refuses format 5.

The usual append and cut protocol can remain. Its crash, dirty-set and
handle obligations still need checking. Generic Lean recovery theorems
may remain applicable; the new transitions must meet their assumptions.
The C port must reproduce every allocation and sibling choice.

Allow 2 to 3 person-days in phase 2 to audit this reference and measure
what part of its cost can be removed. A production candidate would still
need the common work in section 12. Do not invest in tuning this option
before comparing B.

## 4. B. Small versioned edits, with a sweep

### 4.1 Mechanism

An ordinary delete keeps the current bitmap operation. When the leaf has
no live entry, the same transaction deletes the parent's link at the same
time. Repeat upward, across segment boundaries too. An earlier lookup
still sees the old link. An inner node must retain a valid lower bound
for every key routed to it.

There are two useful variants:

* B1 removes empties and contracts roots. It accepts sparse nonempty
  nodes and height from the earlier population.
* B2 also repairs underfill. At a low occupancy it merges or redistributes
  siblings, then appends versioned replacements in their parent.
  Most deletes do not change parents. Space and time splits handle full
  histories, as they do now.

Use separated thresholds for split and merge. Otherwise alternating puts
and deletes at a boundary can repeatedly copy the same siblings.

A deterministic sweep is also needed. In bounded, resumable steps, it
visits current nodes, including nonempty ones with shadowed entries.
It forces a fresh compact current version where needed. It does not wait
for the node to fill. Children are dealt with before the parent is
finished, so the parent's compact version can drop their obsolete links.
Its cursor and any structural action must survive and replay at startup.
Recompute compacted routing bounds too. Keeping an old separator forever
would leave the strict reading of F1 unresolved.

Reclaim owns this sweep with finite R, as a distinct phase of its work.
Each step is an internal transaction after a user transaction, under the
writer's lock. It records the cursor and structural action. R forever
needs no expiry sweep; empty removal and occupancy repair still happen.
Whether to share the current iteration or add a separate recorded pass
is a phase 2 scheduling decision.

This is more than today's touch. A touch is not rerun and creates no
node. A cleanup that creates nodes cannot be put into that hook without
also specifying how the startup rerun makes the same nodes.

### 4.2 Bounds and costs

B1 gives O((n + 1)H) scan follows and current nodes. It does not give
height in live keys or a close twin. B2 aims to give the stronger bound
of section 9. Both protect historical scans by removing empty links at
the original delete time, rather than at the later sweep.

The common delete appends a TIME and bitmap as needed. Each klong occupies
16 bytes in a serialized key node, but the serializer writes the whole
node, not an incremental 16-byte patch. The benefit is reuse of its id
and coalescing while dirty. Parent changes and new nodes occur at repair
or split events, rather than at every level on every delete.

A repair cascade can still cost O(BH) work and node-image bytes. The
amortized number of new nodes needs a potential argument for the actual
time-split and segment rules. Ordinary B-tree intuition is not that
argument. R11's unit for long keys also needs clarification.

The sweep reads and rewrites O(current index bytes) per full pass.
Budget it from the user's work, and charge index nodes, not just values.
Prove it finishes while that index is changing. No measured write or
memory multiplier is available for B.

Common deletes reuse their node arrays. Repair and split steps can
allocate O(BH) bytes at once; the intended amortized allocation is much
lower than A's. The sweep needs a bounded cursor or stack, O(H), and a
bounded work batch. Fresh replacements must still be retained for older
views. These are costs to measure, not a claim of today's heap usage.

### 4.3 Risks and work

This uses the existing history representation. Readers at earlier times
keep their old links; a bitmap or replacement of time tt is invisible
before tt. It has the best chance of retaining the present Lean
assumptions and handle rules with a small change.

The difficult cases are parent lower bounds, an empty last segment tree,
repairs after earlier changes in the same transaction, and the sweep's
replay. Store its action or derive it entirely from persisted state.
Do not derive it from cache residence, elapsed CPU time or an eviction
schedule. Crash recovery must see each step as one transaction.

Use a new replay version unless a compatibility proof permits otherwise.
The C work is the deletion cascade, sibling repair, sweep state and
matching id order, followed by new cross vectors.

Allow 4 to 7 person-days in phase 2 for B1 and B2 sketches, the replay
argument, the amortized bound and count-based comparisons. This is the
first candidate to take further.

## 5. C. Prune old history at the frontier, keeping node ids

### 5.1 Mechanism

Use B's synchronous empty removal, and B2's shape repair if F5 requires it.
Change the way the later sweep removes expired history.
Reclaim does it in bounded transactions after f has advanced.

For a node, compute its state at f and the changes after f. Omit entries
that cannot affect any lookup at or after f. Keep the value needed at f
and every subsequent transition. Rebuild bitmap indexes when positions
in the klong array change.

Write a new representation under the same node id. Publish a replacement
object; do not shorten an array while a reader searches it. Record enough
frontier and version information that loading an old physical version,
Rule R, startup truncation and later serialization all agree.

Writing that image alone is insufficient. An available historical path
may still name an older position. It must resolve to an equivalent pruned
image through persisted id information, or its needed links must be
rewritten safely. Specify that mechanism before claiming earlier release
of bytes. The existing pSafe and CutOK conditions cannot be bypassed.

This is not KeyNode.lastVersion(now). That keeps only the latest state
and would lose values needed inside the retained window.

### 5.2 Bounds, costs and risks

Scan and shape bounds come from the synchronous part, as for B.
Pruning current nodes is O(current index bytes). Pruning all available
representations can also require work over retained history and links;
that cost belongs in R13's window term. It avoids new identities just
to remove slots. Avoiding another retention wait requires the redirection
argument above. Otherwise it has B's wait.

It still writes node images, at most 512 bytes each at B = 30.
Publishing one replacement costs O(B) temporary node memory; a step
must bound how many it holds. Old objects may remain with readers.
Persisted redirection metadata, if used, is an additional space cost.
No byte or memory savings have been measured.

This option changes the representation of past entries. The present
lemma M and physical history-copy assumptions cannot simply be cited.
The new invariant must say that every retained lookup has the same
answer under both representations. Handles must distinguish a sufficient
new representation from an old load, and must not restore pruned history.

Replay needs the same recorded frontier, not the wall clock at restart.
The format must name the new meaning and representation. Byte-cut crashes
and cuts concurrent with old readers need a new argument. The Lean
physical layer, trace checker and C loader have more work than for B.

Allow 3 to 5 person-days for a phase 2 feasibility study, after B's basic
mechanism is clear. Start with a single node, old readers and startup.
Stop if this needs a broad redesign of handles or the physical model.

## 6. D. Rebuild an index or subtree in steps

The deleting transaction still removes empty links by time, as in B1.
Without that part, rebuilding later does not meet R9.

A deterministic worker builds a compact replacement of a selected
subtree in small recorded steps. It shares immutable values. It records
or incorporates intervening writes, then publishes the new subtree.
Old roots remain for the retained times. A low density starts the work
early enough that its old and new trees remain within a chosen space
factor. The final publication must be small.
The writer starts the work on a density threshold, with no new setting;
later calls fund its steps, including with R forever.

One rebuild costs O(subtree index bytes) read and written, plus intervening
changes. Rebuilding after a fixed amount of lost occupancy may amortize
this over deletes. A rebuild on every delete costs O(N) and is excluded.
Both trees and their retained predecessors cost memory and stream space.
If the worker falls behind, the promised shape bound disappears.
An index of J nodes can require about 512J image bytes per rebuild at
B = 30, before staging and change records. It can hold two indexes,
O(BJ) object bytes each, plus the updates made while it builds.

Readers need an exact rule for the old tree, new tree and concurrent
changes at each lookup time. The cursor, id allocation and publication
must replay; a crash must leave one well-defined stage. A new format is
likely. Lean needs explicit transitions for the extra structure and its
live pointers. C must mirror the builder and staging state.
Unfinished new nodes cannot simply wait unreachable: that violates A3.
They need a valid staging anchor or a changed model.

Allow 5 to 10 person-days for phase 2. Keep this as a reserve if local
repair proves too costly. A whole-index builder, two generations and a
change log are more machinery than this bug currently justifies.

## 7. Memory and reclamation common to the options

Use the stream's persisted cut and lookup frontier to discard metadata
that can no longer serve an available read. Do this in bounded work units
triggered by calls, not by a timer. This preserves 010-01, P2 to P4.

After entries leave, shrink their containers with hysteresis. Include
Cache3's maps, startup Rule R maps, position caches, writer scratch arrays
and temporary lists. Clearing references releases objects; clearing a
large array does not release the array. Copying an entire large table in
one call is also a cost that must be bounded.

Written old objects may stay cached below the budget. R4 allows this
until eviction takes them; noEvict is explicitly outside the memory
requirements (023-02, section 7.1). What matters first is that no
available path follows them and none remains pinned. If handles are
removed, their state and the references needed by readers must remain
valid, as in item 009.

Also clear obsolete memory pointees in objects that stay live, including
old skip links. Preserve the references that serialization would use;
otherwise a memory cleanup can change bytes, contrary to R17 and R20.

K18 is already a bounded STM structure. If its expired pairs are removed,
advance the validation floor too: an older read set must rerun rather
than pass validation because its conflicting hash has disappeared.
The prototype does this. A fixed working capacity and a history-sized
capacity are different things.

The prototype's extra expiry passes are useful experiments. Its snapshots
and table rebuilds do not establish P1 or R11 at 100M keys. A work limit
of 64 visited entries does not bound the cost of first taking a snapshot
of a large bucket, or rebuilding its backing table.

## 8. Verdict against R1 to R27

M means the mechanism supports the requirement by the argument above.
P means partial, a design choice remains, or an essential bound or
integration check is missing. N means a known conflict. These are design
verdicts, not test certificates.

A includes the proposed extra sweep for old versions; the stopped
prototype does not include it. B means B2. C includes B2's synchronous
structural edits. D includes B1's immediate empty removal.

| Requirement | A | B | C | D |
|---|---|---|---|---|
| R1  answers at available times | M | M | P | P |
| R2  no expired stream bytes    | P | P | P | P |
| R3  no expired reachable part  | M | M | P | P |
| R4  memory released or cached  | P | P | P | P |
| R5  no later work on it        | P | P | P | P |
| R6  reclaim keeps up           | P | P | P | P |
| R7  every ended version        | M | M | P | P |
| R8  retain forever             | M | M | M | M |
| R9  scan amortization          | M | M | M | M |
| R10 get path and live height   | M | M | M | P |
| R11 proportional write work    | N | P | P | P |
| R12 current index and shape    | M | M | M | P |
| R13 stream space bound         | P | P | P | P |
| R14 pinned and total memory    | P | P | P | P |
| R15 bounded startup            | M | M | P | P |
| R16 concurrent readers         | M | M | P | P |
| R17 rerun and deterministic id | P | P | P | P |
| R18 byte-cut crashes           | P | P | P | P |
| R19 safe reclaim cuts          | P | P | P | P |
| R20 eviction invariance        | P | P | P | P |
| R21 principles                 | P | P | P | P |
| R22 approved format change     | P | P | P | P |
| R23 earlier databases          | P | P | P | P |
| R24 Lean alignment             | P | P | P | P |
| R25 C byte equality            | P | P | P | P |
| R26 near present performance   | N | P | P | P |
| R27 complete regression gates  | P | P | P | P |

R11's N for A concerns new nodes, not the bound on changed nodes.
R26's N means it is not near the baseline in the measured write cost.
Frans may choose a larger tolerance; that does not remove R11's issue.
B1 would change R10 and R12 to P for their stronger live-data wishes.
R22 and R23 need an approved concrete format and compatibility policy.
No option may silently open old records with different replay rules.
The prototype without A's proposed sweep does not meet R7. Its final
saved state does not meet the complete R27 gate.

## 9. The bounds to seek in phase 2

Let S be the sum of the segment counts of the live keys at the lookup
time: a key of L bytes has floor(L / 7) + 1 segments. Let H be that time's
total key-node path height, as in 023-02. Both directions have the same
argument.

If every followed subtree contains a live KV, charge its visit to one
of its returned descendants and that descendant's H ancestors. The
start and stop paths add O(H). A scan therefore follows O((n + 1)H)
key nodes. This is stronger than R9's lifetime inequality; it needs no
credit from earlier deletes. Arbitrary stop conditions count every KV
they are handed, as R9 specifies.

The claim needs to hold for the tree selected at the lookup time.
Pruning at a later time does not repair an earlier tree. It also needs
to include segment trees. A 280-byte key has 41 segments, not one.
Key reconstruction and reading the values add their bytes to real work.
The pointer-count bound does not make long keys free.
These counts exclude the top-node search for a historical root. Include
that search, record framing and actual I/O in the performance comparison.

With minimum occupancy and root contraction, every inner node within
a segment tree has at least two children. Let T be the number of
nonempty segment trees, E their total leaf entries and N the live KVs.
There is one next-segment entry per tree other than the first:

    E = N + T - 1 <= S
    current key nodes <= 2E - T <= 2S

The empty map has one key node. At B = 30 this gives a loose ceiling of
512 times the node count in serialized key-node bytes. Occupancy gives
a better bound for short keys. Each segment tree's height is logarithmic
in its live entries, with a base set by the minimum occupancy.

B1 has only the weaker union-of-live-paths bound, O((N + 1)H).
It can leave long unary paths in a once-large tree. Root contraction
alone does not remove all such paths below a branching root.

For stream space, count live index and values, retained changes, startup
distance, and outstanding sweep and iteration work. Historical values
inside R cannot be charged to the latest live map alone. R13's form is
appropriate; no numerical constants for it are proved here.

In particular, K = 2 in 023-02, F6, is a hypothesis. A fresh node made at
cleanup time c leaves its predecessor available for earlier times until
f passes c. That may require another retention period. A complete bound
must cover that wait, the sweep, pEnd, pSafe, durable cuts, R changes and
the number of cuts. A rule about one copied node passing a cut does not
bound this whole sequence.

## 10. Measurements from the stopped run

### 10.1 What was run

The attached probes and results belong to 020-30's independent study.
They compare the baseline jar with prototype builds made before the stop.
The saved commit contains the last source state; these checkpoints are
not a complete test of that final state.

DeletedCostProbe inserts binary 5-byte keys, with 64-byte values, in
batches of 32. It deletes all but the last 16, or keeps one key in 64.
R is forever and eviction is disabled. Startup distance is 1 MB.
Its listener counts actual key-node follows. The scan-byte columns below
are serialized sizes of distinct key nodes followed, not measured disk I/O.

| Inserted | Survivors | Baseline follows | Prototype follows |
|---|---|---|---|
| 16,384    | 16     | 1,330  | 1     |
| 16,384    | 256    | 1,330  | 18    |
| 1,000,000 | 16     | 81,419 | 1     |
| 1,000,000 | 15,625 | 81,419 | 1,116 |

Forward and backward counts agree in each row.

| Inserted | Survivors | Baseline node bytes | Prototype node bytes |
|---|---|---|---|
| 16,384    | 16     | 402,128    | 304     |
| 16,384    | 256    | 399,440    | 5,232   |
| 1,000,000 | 16     | 24,544,480 | 304     |
| 1,000,000 | 15,625 | 24,377,856 | 321,408 |

Deleting all 128 keys of length 280 leaves an empty scan following
5,130 nodes, 334,544 node bytes, on the baseline. The prototype follows
one empty root, 48 bytes. Earlier-time scans of the populated maps are
also checked by the resource tests.

A missing-key get at 1M follows 7 nodes on the baseline. It follows
1 for the tail-survivor prototype and 4 for its sparse-survivor tree.
This is path height, not a walk over all deleted keys.

### 10.2 Delete bytes and cache nodes

Delete bytes are total appended stream growth during the delete phase.
They include takes and all record contents, not just bitmap bytes.
Cache nodes are objects in Cache3, including historical index and top
nodes. They are not current-tree node counts or heap-byte measurements.

| Inserted | Survivors | Delete bytes, base | Delete bytes, prototype | Ratio |
|---|---|---|---|---|
| 16,384    | 16     | 858,664    | 1,018,032   | 1.19 |
| 16,384    | 256    | 831,592    | 1,006,536   | 1.21 |
| 1,000,000 | 16     | 61,350,024 | 111,929,040 | 1.82 |
| 1,000,000 | 15,625 | 60,681,136 | 122,975,264 | 2.03 |

| Inserted | Survivors | Cache nodes, base | Cache nodes, prototype | Ratio |
|---|---|---|---|---|
| 16,384    | 16     | 1,983   | 4,448   | 2.24 |
| 16,384    | 256    | 1,983   | 4,711   | 2.38 |
| 1,000,000 | 16     | 121,181 | 336,981 | 2.78 |
| 1,000,000 | 15,625 | 121,181 | 355,142 | 2.93 |

Thus "twice the delete bytes and three times the cache nodes" is a fair
description of these 1M runs. It is not the result at 16K, not a result
with default eviction, and not a threefold heap-byte or pinned-memory
measurement.

New path identities and retained history explain the direction of both
costs. Their exact factors depend on batch size, occupancy, key shape,
startup distance, retention and eviction. Same-transaction reuse,
allocation sizes and obsolete temporary nodes can improve a prototype.
They cannot make separate transactions' retained path copies disappear.
The batches of 32 favor A. An unbatched version of this same experiment
has not been measured.

### 10.3 FIFO

FifoProbe uses 300,000 transactions, 1,024 live timestamp keys, values of
80 to 479 bytes, startup distance 2 MB, R = 20 s, and 1.5 ms per
transaction. It uses CutStream and no eviction. Its deterministic values
are not the exact original 021-25 workload. Compare its two runs here,
not their bytes with 021-25's report.

Writer follows count PutData's mutation and touch paths. They exclude
the preflight bound's reads, ordinary reader probes and serialization.
Writer followed-node bytes count an image at every follow, including
repeated follows. They are a work measure, not bytes read from disk.

| Measure at 300,000 | Baseline | Prototype |
|---|---|---|
| Total appended bytes        | 225,450,320   | 1,244,464,312 |
| Bytes after decided cut     | 147,078,600   | 84,507,768    |
| Completed iterations / cuts | 15 / 14       | 89 / 84       |
| now - f, seconds            | 233.40        | 23.79         |
| Current scan nodes          | 34,883        | 124           |
| Current scan node bytes     | 8,307,136     | 28,224        |
| Largest user record, bytes  | 3,870,592     | 43,728        |
| Max scan nodes in one step  | 16,676        | 15            |
| Max nodes dirtied in a step | 16,255        | 7             |
| Writer key-node follows     | 4,610,874     | 2,299,513     |
| Writer followed-node bytes  | 1,469,555,152 | 476,305,984   |
| Cache nodes                 | 83,147        | 100,093       |
| Restart node loads          | 33,946        | 549           |

The prototype's retained stream is smaller and its cuts keep up in this
run. Its total write volume is 5.52 times the baseline. This is a more
serious R26 result than "twice". It cannot be hidden by reporting only
the final kept bytes. It also shows why there is no universal cache
multiplier: this run has finite retention and extra expiry work.

From 50K to 300K, prototype current scans stay at 123 to 125 nodes.
Kept bytes range from 77.7 to 84.5 MB. Baseline scans rise from 5,818
to 34,883 nodes and its available-time lag grows. This supports the
diagnosis and the prototype's mechanism. It is not a proof of R6 or R13.

### 10.4 Expiry

AgeProbe inserts 256 keys of length 28, restarts, deletes them, then
sets R = 1 s. It performs 12,000 small maintenance puts, advancing the
test clock 50 ms per put. A twin only receives the maintenance puts.
Both use startup distance 4 KB and no eviction.

At the end the cut is past the deletes in both tested builds:

| Measure | Baseline | Prototype |
|---|---|---|
| Kept bytes                  | 460,864 | 199,712 |
| Control's kept bytes        | 191,400 | 191,400 |
| Resident initial node ids   | 399     | 0       |
| Old metadata entries        | 275     | 0       |
| Old STM hash pairs          | 256     | 0       |
| Current scan nodes          | 1,052   | 7       |
| Stored initial-node bytes   | 100,912 | 0       |
| Original value/delete bytes | 0       | 0       |

The seven prototype nodes also serve the maintenance and internal keys.
The prototype's tracked old resources are already zero at 250 puts.
The baseline's value records have gone, but its old index and metadata
remain. This is evidence that cutting values alone is insufficient.
It does not establish a universal cleanup deadline or K.

### 10.5 Test limits

Five resource regressions fail on the baseline: the deleted prefix,
long-key empty map, sparse survivors, retained fence or slot, and expiry.
Prototype checkpoints pass those five.

An earlier checkpoint printed BEFORE COMMIT OK: 1,632 unit tests,
90 f-tests and 14 demo runs. A later checkpoint printed LEVEL 3 OK in
quick mode, including ten Lean conformance traces and 124 checked cuts.
The preserved StreamDigest runs cover twelve configurations and four
modes; the modes agree within each build. The two builds' bytes differ
by design.

The saved prototype is not gated. The newest mixed-prefix test fails
at its first restart because its helper creates node size 8 and restarts
with 30. That is a test setup error, not evidence that size 8's algorithm
works. No code was changed after the phase 1 instruction.

There is no level 4 or night result for the saved state, no default-cache
MEM comparison, no performance.sh quick or reference comparison, no
10M or 100M run, and no full application reproduction or hashed FIFO
comparison in this study. R24, R26 and R27 remain open.

## 11. Decisions that separate the choices

| Decision | Recommendation | Related requirement |
|---|---|---|
| Empty removal now or later | At the deleting transaction's time  | R8, R9, R12   |
| Whole path or local edits  | Local versioned edits first         | R11, R26      |
| Sparse nodes or repair     | Study B1 and B2; prefer B2 if cheap | R10, R12      |
| Wait for natural splits    | No; sweep every relevant live node  | R2, R3, R7    |
| Replacement or pruning     | Replacement first; timebox C        | R16, R24      |
| Who schedules the sweep    | Persisted, call-funded work         | R6, R17, R21  |
| Memory release             | Shrink containers in bounded steps  | R4, R14       |
| Old database replay        | Version it; never silently change   | R17, R22, R23 |

The sweep is required for overwrites too. B's new versions made at cleanup
time offer a simpler first argument, but may add lag. C is worth
examining if that lag or the extra versions prove expensive.

Treat 021-25 (a) and (c), and 021-28, as supporting fixes. Fix (b),
the deleted index, still needs synchronous structural work. The queue
head of U16-1, empty tail of U17-1, and metrics FIFO of U18-1 are different
tests; passing one does not cover the other two (023-01, section 1.1).

## 12. Phase 2 work and the cost to finish

| Choice | Phase 2 decision |
|---|---|
| B1, B2 | Deep study first; compare local repair and its absence |
| C      | Limited feasibility study of pruning and old links     |
| A      | Reference and audit; no production tuning yet          |
| D      | Reserve; study deeply only if local repair fails       |

First compare B1 and B2 with A's count results. Require every available
time, both directions, and R forever. Then specify the sweep, its stored
state, id order, work budget and cleanup lag before implementing it.
Give C a separate feasibility decision after that.

For R24, check A1 to A5, TREE, A6', A-COPY, CutOK, C-L, C-P and C-H.
In particular, copied or repaired nodes must get fresh deterministic ids,
old nodes must get no new entry once unreachable, and same-transaction
temporary nodes must not appear as new reachable nodes in the trace.
Root contraction must preserve a valid level assignment.

Lean's generic recovery and restart results are conditional on these
assumptions. They do not prove scan cost, keys, occupancy, Java concurrency
or the new sweep's progress. C needs a representation-pruning relation
in addition to the existing history-copy relation. Bounds can be argued
and tested in this phase; 023-02 does not require their formal proof.

A rough production allowance, after a phase 2 choice, follows. These
are person-days, not elapsed promises. They include review and another
round after findings. They assume an experienced Core maintainer.

| Work | A | B | C | D |
|---|---|---|---|---|
| Java hardening and cleanup    | 8-15 | 10-18 | 15-25 | 20-35 |
| Tests, counts and performance | 6-10 | 6-10  | 8-12  | 10-15 |
| Lean and trace alignment      | 3-6  | 3-6   | 8-15  | 6-12  |
| C port and cross checks       | 4-7  | 5-9   | 8-14  | 10-18 |
| Levels and release documents  | 1-2  | 1-2   | 2-3   | 2-3   |

B totals about 25 to 45 person-days. A still has its structural R11 and
performance objections; this estimate does not make them acceptable.
Migration or conversion of old databases is additional work. The ranges
have not been validated by implementation of B, C or D.

For Java, preserve preflight bounds and the record limit, startup distance
changes, dirty-set pins and every current failure path. Measure time
briefly on a quiet machine, but use nodes, records and bytes first.
Repeat the hello-world and steady-state twins at 1M, 10M and 100M.
Measure overwrites and puts without deletes too.

For C, port the exact node rules, split and merge ordering, frontier and
sweep records, pointer resolution and shrinking containers. Add the
allocation-failure paths. Re-pin 022's Java reference, regenerate vectors,
then run cross full, corrupt, crash, reclaim and scale tests.

Update levels.md, sections 3 to 7, the format authority and trace format
where changed, and release notes with the bounds, lag, costs and old-file
policy. Keep a passing older gate distinct from a gate of the final tree.

Drop pure deferred cleanup, scan-only range bounds as the solution,
unconditional whole-database rebuilding, and eviction-driven structural
cleanup. The first two fail the repeated-head scan. The third violates
R11 and P1. The last makes structure depend on memory pressure, cannot
repair scans with R forever, and risks R17 and R20.

| Incomplete mechanism alone | Requirements it misses |
|---|---|
| End-key scans             | R2-R7, R9, R12                    |
| Remove empties at a split | R2-R7, R9: a node may never split |
| Cleanup only in reclaim   | R8, R9, R12 (a) before its pass   |
| Rebuild on every delete   | R11, R21                          |
| Let eviction edit the Dag | R9 with R forever; R17, R20       |

Replacing the segmented index with a new full-key tree is also outside
this phase 2 recommendation. It may reduce long-key constants but changes
all the Core algorithms, format, alignment and C port. The present
evidence does not require that scope.

## 13. Questions for Frans

1. F1 and F2: include expired slots, shadowed slots and internal keys?
   Recommend yes. Keep a distinct milestone for cleanup in nonempty
   nodes; empty removal alone cannot honestly be called the whole rule.
2. F3: at every available time? Recommend yes. It rules out fixing only
   the latest tree while repeatedly scanning the same costly old view.
3. F4: require a worst scan bound too? Recommend aim for the direct
   O((n + 1)H) bound from empty removal, then measure single-call bytes
   and pauses. The amortized R9 remains the minimum contract.
4. F5: merge? Recommend compare B1 with B2 in phase 2 and prefer bounded
   underfill. State the weaker height guarantee explicitly if B1 ships.
5. F6: is K = 2 fixed? Recommend leave the number open until the sweep,
   retention wait and durable-cut sequence have a complete bound.
   A small constant is a target, not an established property.
6. F7: progress while idle? Recommend progress funded by writes, as P3.
   Do not add a timer or a maintenance API in this fix.
7. F8: retain forever? Recommend keep all needed history and require
   bounded scans immediately. No cleanup opportunity may be assumed.
8. F9: older databases? Recommend an explicit new replay version and
   clear refusal for the first candidate. Study bounded conversion
   separately if existing 2026.3 files must be opened. Leaving their
   old empty paths in place does not meet the same R9. A full cleanup
   at startup conflicts with R15. An online transition needs an explicit
   temporary bound.
9. F10: format change? Recommend allow it and record the exact change
   under 018-01. A changed node-id creation order is a format change
   even with identical field layouts.
10. F11: release scope? Recommend select B's mechanism first. Immediate
    empty removal, reclaim progress and the full regression gates are
    inseparable. If nonempty-node vacuum or underfill is deferred,
    name the unmet R2 to R7 or R12 (b) explicitly.
11. F12: performance tolerance? Recommend separate limits for appended
    bytes, retained bytes, pinned bytes, resident bytes, throughput and
    worst call. Do not accept A's 5.52-fold FIFO writes as near today's.
    Approve numerical tolerances after the first B measurements.
12. R11, related to F5 and F12: what is O(1) new nodes counted per?
    Recommend per operation for fixed key length, and per new segment
    for long keys. Keep O(H) changed nodes distinct from new identities.
    Whole-path copying still needs a deliberate exception or rejection.

## 14. Evidence and scope

The measurements are the DeletedCostProbe, FifoProbe and AgeProbe results
in 020-30's saved study material. Results named baseline-16384,
baseline-1000000, baseline-fifo-300000 and baseline-age have their
prototype counterparts. The baseline-tests and digest results are there
too. The extra counter-key FIFO is not used for the timestamp comparison.

The design arguments use 023-01, sections 3 to 10; 023-02, R1 to R27;
010-01, P1 to P5 and P8 to P13; 021-25, section "Cause";
011-01, Q1 and Q7; and the Core and Lean sources in this clone.
The original-note evidence is F1-007, June 2012 "Thoughts on delete",
July 2012 "Space reclaim", and December 2015 "Recreatable TransSeq".
The first planned empty removal; the second considered piggyback reclaim;
the third insists on the same structure and stream through restarts.

This phase adds no implementation and runs no new database tests.
The independent study uses only this clone and the allowed original
notes. The prototype remains an experiment, with the limitations above.
