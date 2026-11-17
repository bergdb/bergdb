# 025-02's files: the cleanup's tools and the name map

The tools of 025-02 (section 4), written by its planning agent on 2026-11-14 and run by the
provers from /Users/f/fl/bench/2026-11-14/cleanup/tools/, copied here by step 5 (close) as
they ran. Their headers name that directory; run them with the paths changed. The base of
the cleanup is `b8517e8a`.

- **names.md**: the name map, old name to new name for every declaration of lean/SIS/Tree
  that an item cites and that the cleanup renamed or removed (025-02, section 10).
  Written by names.py, last by step 5: `python3 names.py REPO prune-report.txt
  superseded.txt renames.txt dups-renames.txt`, REPO the repo after step 4.
- **Reach.lean**: every declaration of SIS/Tree, its lines, whether a root reaches it
  through proof terms and definitions, and what it uses (`lake env lean` on a built tree).
  **roots.txt**: its roots besides every module outside SIS/Tree (the top theorem by its
  name at the base, `mergeParamsOK_java`, `theta_java`).
- **prune.py**: from Reach.lean's output, what may go, and with `--apply` cuts it. This is
  the copy that step 1 ran: it also cuts a cut declaration's doc comment.
  **macros.py**: step 1's rule for macros, which no proof term names: a macro stays when
  its keyword is in the text that stays.
- **keep.txt**: the plan's 46 names kept although no root reaches them (025-02, section 2).
  **prune-keep.txt**: the KEEP that step 1 applied: those 46 and 373 macros.
  **prune-report.txt**: the report of the applied prune (FILE, TOTAL, DECLS and DEAD lines:
  1,576 DEAD lines, of which 8 auxiliary constants with no source text, and 73 files).
- **superseded.txt**: the cited names that the prune removed as earlier versions, each
  with its successor or the reason it was retired.
- **rename.py**: whole-identifier renames over lean/ and lean/README.md, and file renames
  with their imports, by a table; it refuses a clash. **renames.txt**: step 3's table
  (61 declarations, 8 files), with the reason for each choice that is not a plain strip.
  **dups-renames.txt**: step 4's table (33 rows: a removed copy, then the theorem with the
  same statement that its uses now name; 5 rows marked "kept renamed"); no item cites a
  name in it, so names.md gained no row from it.
- **names.py**: writes names.md from the prune's report, superseded.txt and the tables. This
  copy, step 5's, reads several tables in order and maps a name renamed twice to its last
  name; the tools' copy took one.
- **Guard.lean**: no axiom of ours and no `sorryAx`; the axioms of the theorems in
  **audit.txt** (006-26's 23 theorems, among them the top theorem and Java's parameters;
  the top theorem by its name at the base, which gate.sh replaces by its TOP); the trusted
  closure's fingerprint; the top theorem's statement and its premises' names.
- **Dups.lean**: groups of theorems with the same statement (step 4).
- **gate.sh**: the gate that every cleanup commit passed before it landed (025-02,
  section 7). **land.sh**: the landing, a fast-forward of main and a push.
- **lines.sh**: lines and files of lean/ per area.
- **stale.py**: step 5's check of lean/README.md's backquoted names and file paths, and
  of the names of removed declarations in lean/'s comments.
