# 027-10. The self-indexed stream

Created 2026-11-13 by Frans Lundberg. Status: stub.

Part 6 of 027's outline (027-04, section 2.3; levels: 2). BergDB's central
idea: the data P, the dirty set D and the stream S; versions and
references; good and dirty; marking (T13) and the still-dirty test (Rule
A, BergDB's conservative test and what it costs); what a record holds (the
transaction, the index nodes taken, the got-dirty ids, the startup pos,
topPos); the virtual root; the take (the share in proportion to the stream
added, the deadline at twice the startup distance, the dither, the integer
rule, a decrease of the setting); T1, T2 and T3 (`T3_take`,
`T3_take_decrease`) in plain words, what they leave out (the record limit,
the meta blocks), and T4, open.

Not written yet: the outline's order of writing is 027-04, section 5.1.
Each part follows the template of 027-04, section 2.2.


Log
===

2026-11-13. Created as a stub (Frans, 11:09, 027-04's Q3: "as
recommended").
