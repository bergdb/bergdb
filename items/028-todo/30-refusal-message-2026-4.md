028-30. Investigate: release 2026.4's refusal message names a release that cannot help
======================================================================================

Status: done. Kind: Investigate. Frans: none.
Created 2026-11-19 by Frans Lundberg.

What: Release 2026.4, refusing a database of a newer format, says to read it
with release 2026.5, which a user of 2026.4's database cannot do in the
way the message suggests (noted by the user apps' work, 028-23). 2026.4
is released, so its message cannot change; what can change is what the
release notes and the documentation tell a user who meets it.

Why: A refusal must tell the user what to do (the refusals' messages, 028-15
for 2026.6).

Frans: none.

Done when: The message's exact text and the case that shows it are written down;
the notes of the next release, or 2026.4's Known issues, say what a user
who meets it should do; no code change unless a current message has the
same fault.

First step: Find the message in release 2026.4's code (its tag) and the case in
which it appears.


Result
------

2026-11-20, by tx of coord-1120. The message that names 2026.5 is not
release 2026.4's: no message of 2026.4's code (tag `release-2026.4`)
names 2026.5. It is main's, of 028-15 (2026-11-18), met when the
development build for 2026.6 starts a database of release 2026.4: the
user app Upgrade (a7, `java/stress/apps.sh`) does that, and printed it in
week.sh's run 2026-11-19-1514 (`apps-quick`), with "NOTE the message
does not name 2026.4":

    Cannot read meta block with version 154. Version supported: 155.
    Version 154 is a database written by BergDB release 2026.5 or
    earlier, which this release does not open: its startup distance is
    in its meta blocks, and this release keeps it elsewhere (bergdb
    028-15). To keep its data, make the database again: read it with
    release 2026.5 and put the data into a new database with this
    release. The start has written nothing.

(`RecoverableStream.versionRefused`.) The fault: release 2026.5 does not
open a database of 2026.4 (record format 6; 2026.5 reads format 7), so
a user of 2026.4 cannot do what the message says. Databases of every
release up to 2026.5 have the meta version 154; release 2026.4's are of
record format 6, 2026.3's and earlier of format 5.

What each release says, from jars built from the tags and main's
build at 9f6f7888, each opening a database the others made (Pub API,
`open().start()`):

* 2026.5 on a database of 2026.4: "Cannot parse stored transaction of
  format version 6; this version of BergDB reads format 7 only. A
  smaller number is a database written by an older version of BergDB,
  which this version cannot open: format 6 was written by release
  2026.4, which opens it [...]". Right: it names 2026.4.
* 2026.4 on a database of 2026.5: "Cannot parse stored transaction of
  format version 7; this version of BergDB reads format 6 only. A larger
  number is a database written by a newer version of BergDB." Right.
* 2026.4 and 2026.5 on a database of main (meta version 155): "Cannot
  read meta block with version 155. Version supported: 154". Terse, but
  not wrong, and the files are unchanged.
* main on a database of 2026.4 or 2026.5: the message above.

Changed, as main's message has the fault:

* `RecoverableStream.versionRefused`: "read it with the release that
  wrote it (release 2026.5 opens a database of 2026.5, not one of 2026.4
  or earlier) and put the data into a new database with this release,
  for example with two programs, one on each release's jar"; its test,
  `testReadMetaBlockVersion154Refused`, checks "the release that wrote
  it". With it, Upgrade's message names 2026.4.
* The Javadoc of `DatabaseBuilder.start` and `Db.start`, 027-03, section
  6, and `releases/next.md` (The stream, the first point) say what a user
  does: read the database with the release that wrote it, 2026.4's with
  2026.4, and put the data into a new database with the next release.

Not a released bug (033's rules): the fault is in code of no published
release. 028-15 landed on main on 2026-11-18, after release 2026.5
(2026-11-13); the refusals of 2026.4 and 2026.5 do what their notes say.
2026.4's Known issues need nothing.


Log
---

2026-11-19. Registered by coord-1118 from a report of the day's work.

2026-11-20. Taken by tx of coord-1120, on the branch `028-30-31-texts`.

2026-11-20. Done by tx of coord-1120 (Result): main's message, not
2026.4's; fixed, with the Javadoc, 027-03 and the next release's notes;
not a released bug.
