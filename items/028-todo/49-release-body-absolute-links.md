028-49. Fix: the release scripts make the GitHub release's body with absolute links
===================================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-24 by Frans Lundberg.

What: the release of 2026.6 was made on GitHub with
`gh release create ... --notes-file releases/2026.6/readme.md` (026,
"How the release is made"; `commit-b.sh` in 026-27's
`27-release-plan/` prints the command). The notes' links are
relative to `releases/2026.6/` in the repository, such as
`../../items/033-bugs/readme.md` and `../2026.5/readme.md`; on the
release's page they resolve against `github.com/bergdb/bergdb/releases/`
and give 404.

Why: a review of release 2026.6 (2026-11-24, finding 1) found six broken
links on the page of `release-2026.6`. A body for it was made by hand,
for `gh release edit`: a copy of the notes whose relative links are made
absolute (`https://github.com/bergdb/bergdb/blob/main/...`). The page of 2026.5
has a short body with absolute links. The next release's scripts, copied
from 026-27's, would make the same fault.

Frans: none.

Done when: the release scripts that the next release uses make a body
file from `releases/V/readme.md` with every relative link made absolute
(`https://github.com/bergdb/bergdb/blob/main/` and the path the link
resolves to from `releases/V/`), print the `gh release create` command
with `--notes-file` of that file, and check that every link of the body
answers 200 (`curl -sIL`) once the commit that holds the linked files is
on the public `main`; a test of the conversion on the notes of 2026.6,
whose result has no relative link and the same text otherwise. The body
is the whole notes, their section "After the release" included (033,
Rules, "Where they are published"); when an entry is added to that
section, the body is made again from the notes and set with
`gh release edit`.

First step: read 034-01 (steps 10 and 12, section 6) and `commit-b.sh`
in `items/034-releases/scripts/` (026-27's scripts, moved there on
2026-11-24); the body made by hand for 2026.6 (the page of
`release-2026.6`) is the expected result of the conversion.


Log
---

2026-11-24. Registered by an agent of lead-1124, from finding 1 of the
review of release 2026.6, for the release scripts of 2026.7 (031).

2026-11-24. Done when: the body includes the notes' section "After the
release" and is set again with `gh release edit` when an entry is added
(Frans, 2026-11-24, 12:58; 033's rule).

2026-11-24. The release scripts moved to `items/034-releases/scripts/`
(034), made release-independent; the fix goes there. Until it is done,
`commit-b.sh` prints the GitHub release's command with a body file made
by hand (034-01, step 12).

2026-11-24. In progress: an agent of lead-1124.

2026-11-24. Done (lead-1124). `items/034-releases/scripts/body.sh V`
makes the body, `R/out/body-V.md`, from `MAIN`'s `releases/V/readme.md`,
the whole notes with their section "After the release": each relative
link outside code (inline, image, reference definition) made
`https://github.com/bergdb/bergdb/blob/main/` and the path it resolves to
from `releases/V/`, a link text equal to its target made that path; it
refuses a target outside the repository or not in its tree, and a
relative link left. With `CHECK=1` every http(s) link must answer 200
(`curl -sIL`). `commit-b.sh` makes the body from B's notes before its
gate (COMMIT B FAILED if body.sh refuses), and prints, after the tag's
push, the check `CHECK=1 sh body.sh V` and `gh release create ...
--notes-file R/out/body-V.md`. After the release, when an entry is
added, `CHECK=1 sh body.sh V` makes it again and prints `gh release edit
release-V --notes-file BODY` (034-01, section 5). The test, `sh body.sh
test`, converts the notes of 2026.6 and 2026.5 and checks them link by
link, independently of the conversion: the same file in the repository
(`os.path.samefile`), the fragment and text kept or the path, the text
outside the links the same, no relative link left: BODY TEST OK
(2026.6, 2026.5: 10 of 10 links each). The bodies of 2026.6 and 2026.5
are the same text as those set on their GitHub releases on 2026-11-24
(`gh release view`, but for one final empty line), and with `CHECK=1` every link answers 200. Smoke run on scratch
repositories as 034-01 says (section 6, its record): RELEASE OK with the
body's lines, COMMIT B FAILED on a link to a file not in the tree. 034-01
(steps 12, sections 5 and 6), 034-02 and 034's readme updated. No change
to `java/`; no gate needed beyond the smoke run (034-01, step 6).
