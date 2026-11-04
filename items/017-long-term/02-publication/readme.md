017-02. The literature and the options for a publication
========================================================

Status: open. Created 2026-10-19 as 005-06; moved here by Frans on
2026-11-04, as a long-term topic. The text below is 005-06's as it was
when it moved; the investigation's files are in this directory.


The question
------------

Investigate the literature and the possibility of publishing. What to
publish: self-indexed streams? The whole BergDB database? Something else?
And where and how.


What exists
-----------

* [docs/prior-art.md](../../011-docs-archive/02-prior-art.md) (draft 2, 2026-10-12, with a
  closure review): the literature by layer, and which parts seem new. Its
  section 5 names self-indexed streams as the candidate novel concept (the
  stream is the database; continuous, per-node checkpointing; mixed stream
  and memory pointers; data written at once, the index lazily) with four
  properties P1 to P4. Novelty is provisional, not established.
* [docs/problem.md](../../011-docs-archive/01-problem.md), Q12 (novelty), the question put
  to Tore Risch in 2012: does it make a paper?
* [docs/reference-theory.md](../../011-docs-archive/08-reference-theory.md), item 004's
  literature on swizzling ([004-01](../../004-indirect-swizzling/01-report.md)),
  and the sources in [docs/sources/](../../../docs/sources/) (Frans's 2012
  self-indexed streams paper draft v5, the 2015 algorithms).
* The Lean model and its proofs, the alignment reports and the conformance
  evidence (items 001 and before): a verified storage engine with checked
  conformance is a contribution of its own kind.


Candidate publications
----------------------

1. **Self-indexed streams**: the concept, the algorithm, the bounded
   startup, and measurements. A systems paper.
2. **BergDB as a whole**: the multiversion index, self-indexed streams,
   reclaim and eviction, as a system with an evaluation against comparable
   engines.
3. **The verification**: a Lean model of a real storage engine, proved for
   recovery, restarts, reclaim and eviction, and aligned with the Java code
   by trace conformance; how an AI-assisted proof effort went. A formal
   methods or experience paper.
4. **Something smaller first**: a technical report or preprint (arXiv), a
   series of blog posts, a talk; to establish the ideas and get feedback.


Questions for the investigation
-------------------------------

1. **Novelty**: finish what prior-art.md left provisional. Read the primary
   sources it lists as not yet verified, and search for newer work (2015 to
   2026): log-structured and append-only B-trees, Bw-tree and LLAMA,
   LeanStore and pointer swizzling, ForestDB, the wandering tree problem,
   copy-on-write B-trees (LMDB, Btrfs), multiversion B-trees, temporal
   databases, continuous checkpointing. Which of P1 to P4 survive?
2. **Venues**: which fit each candidate, their deadlines and what they
   expect. Systems and databases (VLDB, SIGMOD, ICDE, EuroSys, FAST, DaMoN,
   CIDR for vision papers), formal methods (ITP, CPP, CAV, FM), practice
   (USENIX ;login:, ACM Queue), arXiv.
3. **What a paper needs** that does not exist yet: an evaluation against
   other engines (RocksDB, LMDB, Berkeley DB JE, others) on standard
   workloads, a clear statement of the model's assumptions (TREE, A6',
   A-COPY and T-SCHEME are checked, not proved; 005-04), a co-author with
   academic experience?
4. **Order**: which first, and whether one supports the others.


Done when
---------

A report: the literature reviewed with sources, the novelty claims that hold
with their evidence, the candidate publications ranked by value and effort,
the venues, and what each would need. It feeds 005-05 (now 017-01).


First step
----------

Reread prior-art.md's section 5 and its list of unverified sources, and turn
them into a reading list with priorities.


Size
----

M to L: mostly reading and web research.


Files
-----

* [literature.md](literature.md). The literature of 2026-11-04's search,
  with sources, years, links and what was read: storage and recovery
  (Berkeley DB JE, bcachefs, LeanStore, FineLine, FOEDUS, LLAMA and more)
  and transactions (OCC, STM, JVSTM, Hyder, FoundationDB, Datomic,
  Convex and more).
* [self-indexed-streams.md](self-indexed-streams.md). The case for a paper
  on self-indexed streams: the method as it is in 2026, which of P1 to P4
  survive, what a paper would claim, the evaluation it needs, a reading
  list by priority.
* [transactions.md](transactions.md). The code-only transactions: where
  the 2012 to 2013 description is, the mechanism and its isolation, the
  comparison with other work, what may be new, whether it is worth a
  publication.
* [options.md](options.md). The candidate publications ranked by value
  and effort, the venues with their next deadlines, what each needs,
  suggestions of new angles, a tentative order, and questions for Frans.


Log
---

2026-11-04. Explored by Claude (Opus 5.5) at Frans's request, with three
web searches by subagents (storage and recovery, transactions, venues)
and a reading of the 2008 to 2013 notes and the 2013 to 2017 Git bundle
in F1-007: wrote literature.md, self-indexed-streams.md, transactions.md
and options.md. Found: P1 to P4 are each known, their combination and
BergDB's way of avoiding the wandering tree were not found; the
code-only transactions are known as a combination (JVSTM, Hyder,
FoundationDB, Convex), their description is KissDB's get-started page of
release 2013.1.130606. The text above this section is unchanged. Frans
decides later.
