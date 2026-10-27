005-57. Investigate startup without rule 4's header reads
=========================================================

Status: open (investigated 2026-10-27, see Findings; java/ not changed).
Kind: investigate. Created 2026-10-27.

Registered at Frans's request (2026-10-27: "Eliminating these reads seem
like the way forward to recude the startup time. Add this as a todo item to
005. Investigate this in detail and document your findings in the item. Use
two example scenarios for which we test performance. For each scenario, make
a comparison of startup time between release 2026.1, the current code, and
the updated code after we do these changes. Create the item, investigate the
solution, but don't implement the change in the java/ yet."), after the
discussion of 007-05's results: rule 4 (`DbStarter.linkD`) and the pointer
reconciliation of 2016 and 2017.


The issue
---------

A cold start took minutes: 214 and 209 s on s1 at 10M keys and startup
distances of 50 and 200 MB (007-05), and three quarters of its random reads
were rule 4's. For each pointer of D's nodes that holds no handle,
`NodeCollection.idOf` reads the pointee's header to learn its id: 863,405
and 1,253,830 reads, of which 0.4 and 5.4 percent find a canonical object to
link. Rule 4 (bergdb item 001, R8, 2026-10-17; 001-08, M44) links those
pointers so that a node of D never names an older version of a node written
after the restart. Frans: a node that stays dirty is written at least once
every startup section, so startup's maps should know the ids that matter,
as the reconciliation of 2017 knew the versions to move pointers to.


Questions
---------

1. Which of rule 4's pointers can name a node with a canonical object, and
   can startup tell them from what it has read, without reading the stream?
2. Does eviction change that?
3. What does the change give, in two scenarios, against release 2026.1 and
   the current code, warm and cold?
4. Where do the reads go: does anything else read the same headers?
5. What would the change be, in java/ and in the Lean model?


Done when
---------

A report with the argument, a prototype on a scratch clone checked against
rule 4 by id, the two scenarios measured on the three versions, and the
change proposed. Then Frans decides whether to make it.


Findings (2026-10-27)
---------------------

The report: [57-startup-header-reads/report.md](57-startup-header-reads/report.md).

1. Rule 4 needs no reads (report, section 2): a pointer of a node of D that
   names a node with a canonical object names a vpos, a position in
   `posToId` (a version in the section, or the version before a key node's
   first version there: the 2017 reconciliation's map), or that canonical
   object's own position. That follows from the record rule and the take
   (001-08, 5.4, case 5): every write of y after the latest version of x, x
   in D, is in the section. Exception: top nodes have no `prevPos` (011-03,
   G3), so a top node's pointer may still need a header; none did on the
   two databases.
2. Eviction is why rule 4 exists (the stale pointer after the restart,
   001-08, M44), but it does not change the argument.
3. The writer reads the same kind of header when it writes D's nodes
   (`resolvePointers`, `idOf`): 1.48 million reads in the first 300
   transactions after a start at 50 MB, today too. Rule 4 by position alone
   moves cost there on a cold cache. By the same argument the writer needs
   no reads either, with a map of the pinned objects by position (report,
   section 3): part 2.
4. Prototypes of part 1 and of parts 1 and 2 (`prototype.diff`,
   `prototype-2.diff`), checked against the code by id in every startup and
   every `resolvePointers` of before-commit, level2.sh and level4.sh, and on
   the two databases: no difference (report, section 5).
5. The two scenarios (report, sections 6 and 7), 10M keys, 8-byte values:

       Startup               2026.1   current   parts 1 and 2
       A, 50 MB, warm         7.4 s     7.7 s           6.8 s
       A, 50 MB, cold         240 s     214 s           «TBD»
       B, 200 MB, warm       12.9 s    13.2 s          12.5 s
       B, 200 MB, cold        «TBD»     «TBD»           «TBD»

   Warm on F53, cold on s1. With part 1 alone the cold start at 50 MB is
   46 s. After the start, on an uncached copy on F53, a start and 300
   transactions take 35.5 s today and 25.0 s with both parts.
6. What is left of a cold start is the rerun's loads, about 34 s of the 46
   on s1 at 50 MB (report, section 8).
7. The Lean model needs no change; the gates' conformance checks the change
   (report, section 9).

Proposed (report, section 10): both parts, with the check kept under
assertions as a test-only check; S for part 1, M for part 2. Questions for
Frans in section 11.


Size and order
--------------

The change: S to M, after Frans's go. It is 007-03's step 6, options B and
more: it removes the reads instead of reducing them.
