017-02, the options for a publication
=====================================

Created 2026-11-04 by Claude (Opus 5.5) for Frans Lundberg, for 017-02.
Status: options for Frans to decide on later; the recommendation in
section 5 is tentative.

The candidate publications of 017-02, ranked by value and effort, with
the venues that fit, what each needs, an order, my own suggestions, and
questions for Frans. The novelty findings behind it are in
[self-indexed-streams.md](self-indexed-streams.md) and
[transactions.md](transactions.md). Whether to publish BergDB at all, its
licence and money are 017-01's; they come up here only where a
publication depends on them.

The venue facts are from a web search of 2026-11-04 by a subagent, which
checked each date against the venue's own call unless marked **NV** (not
verified: inferred from earlier years or from a secondary source). I have
not rechecked them. Check every date again before planning on it.


# 1. The candidates, ranked

Value means what the publication does for BergDB's ideas: whether it
establishes them, gets expert feedback, reaches users. Effort is the
work before submission, for Frans with AI agents; S is days, M weeks, L
months.

1. **A technical report on self-indexed streams (arXiv).** Value high,
   effort M. The method, the model and its proofs (T1, T2, T3), the
   Java implementation and the measurements that exist (startup, Level 3
   and 4 costs), with the related work of self-indexed-streams.md,
   section 3. It dates the ideas, can be cited by every later paper and
   can be sent to people for feedback. Needs: a public repository or at
   least a public artifact (017-01), and an arXiv endorser (section 3).
   No evaluation against other engines, which is what makes it M and not
   L.
2. **A systems paper on self-indexed streams.** Value highest, effort L.
   The claims of self-indexed-streams.md, section 4, with the evaluation
   of its section 5 (Berkeley DB JE, LMDB, RocksDB; startup against size;
   write cost; latency; history). Venues: PVLDB regular research, FAST,
   SIGMOD, EuroSys (section 2).
3. **The verification: a Lean model of a real storage engine, aligned by
   trace conformance, and how the AI-assisted proof effort went.** Value
   high, in a different community; effort M. Most of the material exists
   (lean/, 001, 007, 009-05, 011-11, the trace checker). Needs: the
   assumptions stated (TREE, A6', A-COPY, T-SCHEME; 005-04), what is and
   is not proved said plainly, numbers on the effort (lines, days,
   sessions, what the agents did and what Frans did), and the AI
   disclosure each venue asks for. Venues: CAV's application and
   experience track, NFM, ITP, CPP.
4. **Blog posts.** Value medium (reach, a first public explanation),
   effort S each. See section 4 for a series. Needs a place to post and,
   for links to code, the public repository.
5. **BergDB as a whole.** Value medium to high, effort L. A system paper
   of the whole (index, self-indexed streams, reclaim, eviction with
   handles, code-only transactions) with an evaluation; much of it shared
   with candidate 2. Venues: CIDR (6 pages, systems with a vision), the
   SIGMOD industrial track, a demo. Better after candidate 2, or instead
   of it if Frans prefers one paper.
6. **Code-only transactions.** Value low to medium as research, effort S
   for a blog post, M for a workshop paper. transactions.md, section 6:
   a blog post and a section of candidate 2 or 5; a workshop paper (PaPoC,
   MPLR) only with an isolation proof, phantom-safe range reads and
   measured rerun rates.
7. **Talks.** Value medium for reach, effort S to M each. Lean Together
   (the proofs), Jfokus and JavaZone (the Java database and its
   transactions), HPTS (a one-page position paper; by invitation).


# 2. Venues

Grouped by candidate, the soonest first. Dates are 2026 or 2027 as
written.


## 2.1 For the systems paper (2) and BergDB as a whole (5)

* **PVLDB vol 20 (VLDB 2027, Athens, 23 to 27 August 2027).**
  https://www.vldb.org/pvldb/volumes/20/submission. Regular research, 12
  pages without references; Experiment, Analysis and Benchmark; Vision, 6
  pages. Paper due the 1st of each month, abstract the 25th before, from
  1 December 2026 to 1 March 2027; one revision; papers accepted by 1 July
  2027 present in 2027. Single-blind (no need to hide BergDB's name). Code
  and data at a public archival place. No affiliation rule found. The
  best fit for candidate 2: monthly deadlines fit an independent author,
  and the revision round lets reviewers ask for more evaluation. Vol 21
  (VLDB 2028) should continue the cycle from about April 2027 (NV).
* **SIGMOD 2027 industrial track**: 24 November 2026; 12 pages, not
  anonymous, at least one author outside academia; covers open-source
  systems. Too soon for this year without an evaluation. SIGMOD 2027
  research rounds have all passed; SIGMOD 2028's first round about
  mid-January 2027 (NV); double-blind; no arXiv posting during review.
* **SIGMOD 2027 demos**: 11 January 2027. A demo of bounded startup and
  as-of reads could come early, as a companion to a paper.
* **ICDE 2027 (Copenhagen, 17 to 21 May 2027)**: research round 2 on 11
  November 2026; DEFT, its vision track, abstract 15 November, paper 22
  November 2026, 6 to 12 pages. Too soon.
* **CIDR 2027** has passed (4 August 2026). **CIDR 2028**: about August
  2027 (NV); 6 pages, single-blind, one submission a person. A good fit
  for BergDB as a whole, as an innovative system with a vision (one
  stream, history, proofs).
* **FAST '27** has passed. **FAST '28** (28 February to 1 March 2028,
  NV): spring deadline about mid-March 2027 (NV); 12 or 6 pages;
  double-blind; values new artifacts; a "Deployed System" track.
* **EuroSys 2027** has passed; EuroSys 2028's spring cycle about May 2027
  (NV); 12 pages, double-blind, experience papers welcome, AI use must be
  fully disclosed.
* **OSDI '27**: abstract 1 December, paper 8 December 2026. Very
  competitive; text "wholly or largely generated by AI" counts as fraud,
  and coding agents must be disclosed. Not recommended.
* **HotStorage 2027**: not announced (NV); 2026's was 5 pages, at SOSP,
  deadline in June. A position paper there is a cheap way to get storage
  researchers' view before the full paper (section 4).
* **DaMoN 2027** (at SIGMOD, NV about February 2027): 6-page full or
  2-page short papers on hardware-conscious data management. A fit for
  the klong nodes or eviction with handles, less for the method.
* **BTW 2027** has passed; **EDBT 2027** has passed.
* **USENIX ATC** ended under USENIX after 2025; ACM SIGOPS runs it since
  2026 (Hong Kong, November 2026); nothing for 2027 yet.


## 2.2 For the verification (3)

* **NFM 2027 (Houston, 11 to 13 May 2027)**: abstract 4 January, paper 11
  January 2027; regular 16 pages, short 8 for tool papers or case studies
  of real systems with public artifacts (LNCS). No fee.
* **CAV 2027 (Amsterdam, 21 to 23 July 2027)**: 20 January 2027.
  Application, Industrial Experience and Case Study papers, 10 pages,
  single-blind, artifact evaluation optional. The best fit: a real engine,
  machine-checked recovery, conformance of the code.
* **ITP 2027**: host and dates not set (NV); ITP 2026's deadline was in
  February; 16 pages regular, 6 short (LIPIcs); the formalization must be
  submitted.
* **CPP 2028** (at POPL): about September 2027 (NV); 12 pages. CPP 2027
  has passed.
* **Lean Together 2027**: not announced (NV); if like 2026, online in
  January with talk abstracts due about 1 December 2026. Free, recorded,
  software verification in scope.
* **Journal of Automated Reasoning**, "Proof Pearls" articles, for a short
  piece (section 4).
* AI and mathematics workshops (MATH-AI at NeurIPS, AI for Math at ICML,
  AITP) are past for 2026 and non-archival.


## 2.3 For the transactions (6) and other short pieces

* **PaPoC 2027** (at EuroSys, Rabat; NV about late January 2027): 6-page
  short papers, transactions in scope, not anonymous.
* **MPLR 2027** (at SPLASH, Prague; about 11 June 2027, marked TBC): 6-page
  work-in-progress or industry papers on managed runtimes.
* **Onward! Essays** (SPLASH; NV about mid-May 2027): essays, single-blind.
* **DBTest 2027** (at SIGMOD; NV about March 2027): testing database
  systems, research or experience; a fit for the trace conformance.


## 2.4 Practice, talks and preprints

* **ACM Queue**: by invitation only. **CACM Practice**: a newer call
  seems to take unsolicited articles of about 6,000 words (NV: the page
  could not be read). **USENIX ;login:** has ended (2025). **InfoQ**: a
  proposal with five key takeaways to its editors.
* **Jfokus 2027** (Stockholm, February 2027): the call has closed; Jfokus
  2028's about August to October 2027 (NV). JavaZone's call about January
  to April (NV). Devoxx Belgium about June to July (NV).
* **HPTS**: every two years; the next about 2028 (NV); a one-page position
  paper by one author.
* **arXiv**: since 21 January 2026 an institutional address no longer
  gives automatic endorsement; a first-time submitter needs a personal
  endorsement from an established cs author
  (https://info.arxiv.org/help/endorsement.html). Since 31 October 2025
  review and position papers in cs must be peer-reviewed first; a
  technical report is fine. Significant use of generative AI must be
  reported.
* **Artifacts**: a Zenodo release (a DOI per version) and a Software
  Heritage identifier for the repository; ACM's artifact badges.


## 2.5 Rules on AI that matter for BergDB's papers

* ACM (SIGMOD, CPP, MPLR, ICFP): AI cannot be an author; AI used in the
  research (code, data, figures) is described in the paper; venues add
  their own sections (ICFP's "AI Use", Middleware's "Generative AI
  Usage"). The 2025 revision could not be read on acm.org (NV).
* IEEE (ICDE): AI-generated text, figures and code are disclosed in the
  acknowledgements, with the sections and the level of use.
* USENIX (OSDI): text largely generated by AI is fraud; coding agents are
  allowed with disclosure in the implementation section.
* Springer LNCS (CAV, NFM) and LIPIcs (ITP): not checked.

For BergDB the safe course: the paper's text written by Frans, or
rewritten by him until it is his; the role of the agents in the code, the
Lean proofs and the tests described in the method or implementation
section; for the verification paper, the AI's role is part of the
contribution and is described in full.


# 3. What every option needs first

* **A public artifact.** PVLDB requires code and data at a public archival
  place; CAV and NFM value public artifacts; a blog post wants links. This
  depends on 017-01's decision on publishing the repository and its
  licence.
* **An arXiv endorser**, for the technical report: someone Frans knows who
  publishes in cs.DB or cs.LO.
* **A reader from the field**, ideally a co-author for the systems paper:
  someone who knows Berkeley DB JE, LeanStore and the MVBT line and can
  say how reviewers will read the claims. Candidates to think about, not
  contacted: Tore Risch (asked in 2012, 011-01, Q12), the authors of the
  2026 cMVBT paper (Seeger's group, whose next step is external storage),
  someone of the LeanStore group.
* **The evaluation** (self-indexed-streams.md, section 5), for candidates
  2 and 5: an item of its own, size L, on F53 and s1.


# 4. My suggestions

Marked as mine; none is in 017-02's text.

1. **A storage position paper first** (HotStorage 2027, 5 pages, NV about
   June 2027): "a database in one append-only stream, for zoned and
   object storage". Self-indexed streams need only appends and front
   cuts, which is what zoned SSDs (ZNS), SMR disks, append-only object
   storage and WORM storage give; the search found no database for them
   with one stream and lazy index writes (literature.md, zoned storage).
   Cheap, gets expert feedback a year before the full paper.
2. **The traces and the model as an artifact.** A Zenodo release of the
   Lean model, the trace checker, the conformance trace sets (small,
   medium, large) and the trace format (docs/trace-format.md), described
   so that others can check another implementation. With the C clone it
   is already used that way.
3. **Two implementations, one stream.** The C clone (012) reads and
   writes the same stream as Java byte for byte, and each opens the
   other's databases; with the model, three descriptions of one method
   that agree on checked traces. A strong paragraph in the systems paper
   (evidence that the method and the format are fully specified), and a
   possible DBTest paper with the trace conformance.
4. **An experience report on AI agents in the work.** The Lean model,
   about 52,000 lines in `lean/` on 2026-11-04, written by Frans with AI
   agents in about three and a half weeks since 2026-10-12; the C clone's Core in 13.5
   hours of unattended work (012-16, section 1); the unattended night and
   the coordinator (013-01, 013-02); what failed and what the model found
   (the vpos case of Rule R, sis-model.md, section 6.2). Fits CAV's
   experience track (as part of candidate 3), Onward! Essays, or a blog
   series; honest numbers matter more than the venue. The AI rules of
   section 2.5 apply with extra force.
5. **A proof pearl.** The heart of T1 for the abstract method only (Rule
   A, Rule R, "writing a node does not dirty its ancestors"), without
   BergDB's bookkeeping: a few hundred lines of Lean, for JAR's Proof
   Pearls or an ITP short paper. It would also be the clearest
   explanation of why the method works.
6. **The revival as a story.** A design of 2009 to 2012, code of 2012 to
   2017, stopped by bugs, revived in 2026: formalised, fixed, extended
   with reclaim, eviction and handles, and cloned in C. A blog post or an
   essay, and the opening of the technical report.
7. **A blog series**, in this order: (a) what a self-indexed stream is,
   with one figure; (b) a payment in eight lines of Java, and how it
   compares with FoundationDB and Convex (transactions.md); (c) proving a
   storage engine in Lean with AI agents; (d) startup that does not grow
   with the database, with the measurements.
8. **An isolation theorem** for the code-only transactions (transactions.md,
   section 6): small, and it turns the weakest candidate into a
   checkable result; with phantom-safe range reads it could be a PaPoC
   paper.


# 5. Order, and a tentative recommendation

Tentative, for Frans to change:

1. **Now to December 2026.** 017-01's decision on the public repository.
   Blog post (a). The technical report's draft: the method, the model and
   proofs, the measurements that exist, the related work. Find an arXiv
   endorser. Possibly a Lean Together 2027 talk, if its call opens with a
   deadline about 1 December (NV).
2. **January 2027.** The verification as a case study: NFM 2027 (11
   January, 8 pages) or CAV 2027 (20 January, 10 pages). CAV is the
   stronger venue; NFM the easier. The material exists, so this is the
   first peer-reviewed paper within reach. Post the technical report on
   arXiv before or with it.
3. **February to June 2027.** The evaluation item (Berkeley DB JE first).
   Blog posts (b) to (d). Optionally the HotStorage position paper
   (suggestion 1) and a PaPoC paper on the transactions (suggestion 8).
4. **From about mid-2027.** The systems paper on self-indexed streams to
   PVLDB (monthly; the first deadline after the evaluation), or SIGMOD
   2028's later rounds (NV), or FAST '29 (NV). BergDB as a whole to CIDR 2028
   (about August 2027, NV), if Frans wants the vision paper too.
5. **Talks along the way**: Jfokus 2028 (call about August to October
   2027, NV) and JavaZone 2027.

How they support each other: the technical report gives the others a
citation and a date; the verification paper makes the systems paper's
correctness claims citable and lets it spend its pages on the
evaluation; the blog posts and talks find readers, a co-author and
perhaps users; the systems paper is the one that settles the novelty
question with reviewers.


# 6. Questions for Frans

1. What do you want most from publishing: recognition of the ideas in the
   research community, users of BergDB, or paid work? It decides between
   papers first and blog posts and talks first (017-01 has the business
   side).
2. Will the repository be public before a paper, and under which licence?
   PVLDB and most artifact tracks need a public archive.
3. Would you want a co-author from the field, or a reader before
   submission? Is Tore Risch, or someone else you know, a possibility? Do
   you know someone who could endorse an arXiv submission?
4. How should the AI agents' part be described: you as the only author,
   the agents' work disclosed in the method section? Do you want the AI
   experience itself to be a publication (suggestion 4)?
5. Is an evaluation item against Berkeley DB JE, LMDB and RocksDB (size L,
   F53 and s1) worth its time now, against the 015 todos and the next
   release?
6. Keep the name "self-indexed streams"? It is yours since 2012 and not
   used by anyone else found; the literature's nearest terms are
   "log-structured" and "the log is the database".
7. For the transactions: should range reads in `RwEnvironment`, safe
   against phantoms, and an isolation proof become 015 entries, or is a
   blog post enough?
8. Of the venues: are you willing to travel (Amsterdam for CAV, Athens for
   VLDB, Houston for NFM), or do you prefer venues with remote
   presentation or journals?
