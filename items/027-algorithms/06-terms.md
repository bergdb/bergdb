# 027-06. Terms

Created 2026-11-13 by Frans Lundberg. Status: stub.

Part 2 of 027's outline (027-04, section 2.3; levels: all). One list of
BergDB's terms, each with its definition, and with its Lean name and its
Java name where they differ: key, value, KV, segment, key node, top node,
value node, klong, node id; time, lookup time (requested and actual),
first available time; transaction, record, version, reference; startup
distance, startup pos, startup section; D, got-dirty, canonical object,
handle; memory pointer and stream pointer ("pointer i of x"; "slot" is the
Lean model's word only); retain duration, iteration, step, cut; the
writer's terms since record format 8 (026-25): PE, plan and emit, a
planned node and its final list, kept, appended and new nodes, a join, a
cut of a list into parts and the cut size (not reclaim's cut), a root
collapsed or raised, the short way; and the terms of the old writer that
older items use (split, time split, space split, merge, upward unlink,
take-back, rule O), each marked as gone with format 8.

Not written yet: the outline's order of writing is 027-04, section 5.1.
Each part follows the template of 027-04, section 2.2.


Log
===

2026-11-13. Created as a stub (Frans, 11:09, 027-04's Q3: "as
recommended").

2026-11-19. The writer's terms of PE (026-25) added to the list. By an
agent of coord-1118, on the branch `027-pe`.
