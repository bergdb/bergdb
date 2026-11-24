028-49. Fix: the release scripts make the GitHub release's body with absolute links
===================================================================================

Status: open. Kind: Fix. Frans: none.
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
whose result has no relative link and the same text otherwise.

First step: read 026, "How the release is made", and `commit-b.sh` in
`items/026-release-2026-6/27-release-plan/`; the body made by hand for
2026.6 (the page of `release-2026.6`) is the expected result of the
conversion.


Log
---

2026-11-24. Registered by an agent of lead-1124, from finding 1 of the
review of release 2026.6, for the release scripts of 2026.7 (031).
