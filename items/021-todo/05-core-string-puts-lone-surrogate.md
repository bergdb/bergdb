021-05. Fix: the Core's String puts write '?' for a lone surrogate
================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-07 by Frans Lundberg.

What: the Core's String conveniences encode with `String.getBytes`,
which writes '?' in place of a lone surrogate, silently:
`Trans.Builder.put(String, String)` (its value with
`StringUtil.toBytes`, its key with `Keys.toBytes`), and `Keys.toBytes`
itself, which every Core call that takes a String key uses
(`Trans.Builder.delete(String)`, `keyRead(String)`,
`Keys.toSegments(String)`). A Core user's key "a" U+D800 is the key "a?",
and its value read back holds other characters (021-04, section 3.1).

Why: 021-04's decision (Frans, 2026-11-07, 09:33, option 1): every string
in a BergDB stream is a sequence of Unicode scalar values stored as
well-formed UTF-8, and a writer refuses a string it cannot store so, one
rule for keys, values and objects. The Pub API refuses (015-49, 019-44,
021-04); the Core's String puts did not. 021-04, "Two questions remain",
the first.

Frans: none. Frans, 2026-11-07, 09:34: ""Two problems found". Yes, add
entries." The default (021-04): refuse, as option (1) says, with
`IllegalArgumentException` before anything is written. The Core stays
independent of the layers above it (bergdb 006-08): its check is in
`bergdb.common` (`StringUtil.hasLoneSurrogate`), which the Pub layer's
`PubKeys.hasLoneSurrogate` now calls.

Done when: `Keys.toBytes(String)` and `Trans.Builder.put(String, String)`
refuse a lone surrogate with `IllegalArgumentException`; tests that fail
before the change; `BEFORE COMMIT OK`; a line in `releases/next.md`.

First step: `Keys.toBytes` and `Trans.Builder.put(String, String)`.


Log
---

2026-11-07. Registered by agent u04 of coord-1107 (006-14) from 021-04's
"Two questions remain" paragraph and section 3.1, at Frans's word
(09:34, quoted above).

2026-11-07. Taken by agent u04 of coord-1107 (006-14), with 021-04: a
small change.

2026-11-07. Done by agent u04 of coord-1107 (006-14):

* `StringUtil.hasLoneSurrogate` in `bergdb.common`, the check that was
  `PubKeys.hasLoneSurrogate`'s, which now calls it; the Core does not
  depend on `pubimp` (`deps.py`: "all as package.html allows").
* `Keys.toBytes(String)` refuses a lone surrogate with
  `IllegalArgumentException`. It scans the chars only when the UTF-8
  bytes hold a '?', which the encoder writes for each lone surrogate: no
  cost for a key without '?', on the get path too.
* `Trans.Builder.put(String, String)` refuses a value with one (its key
  through `Keys.toBytes`); Javadoc on both.
* Tests: `Keys.testLoneSurrogate`, `Trans.testLoneSurrogateRefused` (both
  throw "no exception" on `HEAD`'s code, which wrote '?'),
  `StringUtil.testHasLoneSurrogate`.
* `releases/next.md`: a Core API bullet. The Core's `key-encoding.md`
  names `Keys.toBytes`'s refusal.

`BEFORE COMMIT OK (121 s)` (2026-11-07, 09:54; 1266 unit tests, 87
f-tests), with 021-04's changes.
