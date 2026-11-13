# 027-07. The key tree: structure and reads

Created 2026-11-13 by Frans Lundberg. Status: stub.

Part 3 of 027's outline (027-04, section 2.3; levels: 0). The multiversion
map as a tree: keys cut into segments of 7 bytes, and segment trees; key
nodes made of klongs, and the klongs' types; value nodes; the top node and
its skip pointers; node ids; the searches; a get at a lookup time; a scan
with its end key and R9's amortized bound; the keys' shape and its cost in
heap (MEM, SEG; 024-08, 024-15).

Not written yet: the outline's order of writing is 027-04, section 5.1.
Each part follows the template of 027-04, section 2.2.


Log
===

2026-11-13. Created as a stub (Frans, 11:09, 027-04's Q3: "as
recommended").
