# 034-02. The checklist of a release

Created 2026-11-24 by Frans Lundberg. Status: open, maintained: kept
current, a change dated here.

Everything to check or update at and after a release of version V, one
line each with how it is checked: by a script's line, or by hand. The
steps are 034-01's. The release plan takes this list as it is and
records each line as done, with its evidence, in its log.

Why a list: on 2026-11-24, after release 2026.6, several of these were
found missing only afterwards. The review of release 2026.6 (2026-11-24;
026's log) found the GitHub release's body with six broken links
(finding 1), the Javadoc naming `bergdb-2026.4.jar` and a source zip
(finding 3), 030-26 calling 2026.6 "the coming release" (finding 5), no
`SHA256SUMS` among the release's assets (finding 15), 033's entries
"fixed on main for 2026.6" (finding 16), 026's readme not saying where
its moved work went (finding 17), and the statuses of 024 (release
2026.5) and 030-38 still open (finding 18); and 026-14, the versioning
rule and 026-13's option B were carried or registered only after Frans
asked (006-34, 11:20). Each such line says "missing in 2026.6".


## Before the tag

* **No known bug** (Frans, 2026-11-24, 13:12; 034-01, section 1): 033
  has no open entry for the code being released, unless Frans's
  exception, recorded in the release item, names it; 028's Open table has
  no entry of a fault in it. By hand.
* **033 current**: `git log release-PREV..A -- java/src` read for fixes
  of faults that a released version has; each has its RB entry; the
  counts agree. By hand, recorded in 033's log (034-01, step 4).
* **The proofs' statement** (030-26) says what A proves and tests, its
  counts from GATE OK's line; the guarantee list, if the release makes
  one, reviewed and its findings closed. By hand.
* **The release runs**: NIGHT OK and WEEK OK in their reports,
  `timing.sh`'s figures in the notes, on commits near A. By hand.
* **The notes complete**: `releases/next.md` has no `[[` marker
  (`notes.sh`: NOTES OK, not NOTES NEED EDITS; `stage-b.sh` refuses a
  marker), and Frans has read them (`release.sh` stops at RELEASE
  WAITS).


## Commit A

* **`BuildInfo`** says V, its int and `V.YYMMDD.HHMM`:
  `set-buildinfo.sh` (BUILDINFO SET); `to-main.sh`, `release.sh` and
  `build-a.sh` refuse an A that says a `-dev` version; `build-a.sh`
  checks what the jar prints (BUILD A OK).
* **The Javadoc's overview** names the jar `bergdb-V.jar`: `build-a.sh`
  (BUILD A FAILED if it names another release's jar). Missing in 2026.6.
* **Other release names in the Javadoc**, such as a release said to have
  no encryption: by hand, `grep -rn '20[0-9][0-9]\.[0-9]'
  java/src/overview-pub.html java/src/bergdb/pub/` read. Missing in
  2026.6.
* **A's gate** in a new clone: BEFORE COMMIT OK, `lake build`, GATE OK,
  the axioms check, StreamDigest's differing configurations each named
  in the notes; the extra checks (jcstress, the jar's tests on s1). By
  hand, from their lines, in the `news.md` entry.


## Commit B

* **`releases/V/readme.md` and `SHA256SUMS`**, and nothing else there:
  `stage-b.sh` (STAGE B OK) and `commit-b.sh` (the two files only;
  `SHA256SUMS` checks against `R/out`'s jar and Javadoc zip).
* **`releases/next.md` emptied**, its introduction kept and saying
  "after V": `stage-b.sh`.
* **`BuildInfo`** the next version, `YYYY.(N+1)-dev`: `stage-b.sh`
  (BUILDINFO SET), checked by `commit-b.sh`.
* **`docs/log.md`'s entry** of the release: `stage-b.sh` (the default
  entry, or `LOGENTRY` with the theme); read by hand in `R/B` before the
  second call's push.
* **README.md's Status**: the latest release, its date and its tag,
  "the latest release, V (DATE, tag `release-V`)", and no longer PREV:
  `release.sh`'s step 1 and `stage-b.sh`. How V was tested: by hand, the
  lead's text (`READMEMD`), read by Frans; two corrections of 2026.6's
  were made after the release.
* **B's gate**: BEFORE COMMIT OK, by `commit-b.sh`.


## The tag and the GitHub release

* **The tag** `release-V` on A, pushed: by hand, `git ls-remote origin
  'refs/tags/release-V^{}'` gives A.
* **The GitHub release's assets**: the jar, the Javadoc zip and
  `SHA256SUMS` (`gh release view release-V --json assets`), checked by
  download: `commit-b.sh`'s printed check (`cmp` with the repository's
  `SHA256SUMS`, then `shasum -a 256 -c SHA256SUMS` OK). `SHA256SUMS`
  missing in 2026.6 (added after the review).
* **The GitHub release's body**: the notes with every relative link made
  absolute; every link answers 200 (`curl -sIL`): `commit-b.sh` (BODY
  OK, the body made from B's notes) and the printed `CHECK=1 sh body.sh
  V` (BODY OK, every link 200) before `gh release create`. Missing in
  2026.6 (six links gave 404).
* **The tag's archive builds**: by hand, `java/build.sh` in the unpacked
  archive; `BuildInfo` prints release V.


## After the release, the same day

* **bergdb.org** (the repository `bergdb/bergdb.github.io`,
  `index.html`): Status (the latest release, its date, its tag, how it
  was tested, the link to its notes), Get it (the release's link), the
  jar's name in Try it (`bergdb-V.jar`); `404.html`'s style block copied
  if the style changed. By hand: `grep -n '20[0-9][0-9]\.[0-9]'
  index.html` read, the page's links checked, pushed.
* **033**: the entries that V fixes say "fixed in V", not "on main for
  V"; the counts tables get V's rows. By hand. Missing in 2026.6.
* **The proofs' statement** (030-26) speaks of V as released. By hand.
  Missing in 2026.6.
* **The release item**: status done with its log line; each subitem's
  status set from its records; what it does not finish carried to the
  next release item, or registered in 028, and each proposal's fate
  written where it is proposed. By hand. Missing in 2026.6 (026-14, the
  versioning rule, 026-13's option B).
* **The release plan** (the release item's subitem) done, and the
  release's guarantee list, if any, kept as its record. By hand. Missing
  in 2026.6 (030-38).
* **The previous release item** done, if it is not. By hand. Missing in
  2026.6 (024, release 2026.5, open in its readme and the index).
* **The items index**, `items/readme.md`: the release item's line with
  its status. By hand.
* **The 028 entries the release takes**: each done, or carried to the
  next release item with a line there. By hand, the release item's list
  against 028's Open table.
* **The next release item**: it exists, says that it follows 034, and
  lists what was carried to it. By hand.


## Later

* **"After the release"** in `releases/V/readme.md`, added with its
  first entry, appended only (034-01, section 5; 033, Rules); the
  GitHub release's body made again and set with `gh release edit`:
  `CHECK=1 sh body.sh V` once the entry is pushed (BODY OK), then the
  `gh release edit` it prints, by hand.
* **A released bug found after the release**: its 033 entry, a bullet in
  the latest release's notes, a pointer bullet in an older release's
  notes that has it (033, Rules). By hand.


## Log

2026-11-24. Written (Frans, 13:05), with the lines missing in 2026.6
from the review of release 2026.6 and 006-34; the line on known bugs
(Frans, 13:12).

2026-11-24. The body's lines checked by `body.sh` (028-49).
