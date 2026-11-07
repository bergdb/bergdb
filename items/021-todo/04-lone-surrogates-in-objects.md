021-04. Decide: a lone surrogate in a String inside an object
=============================================================

Status: open. Kind: Decide. Frans: decision.
Created 2026-11-07 by Frans Lundberg.

What: a String inside an object (the object code, `DbObject`, experimental
in 2026.3, 018-01, D6) is stored with '?' in place of a lone surrogate,
silently: the object read back holds other characters than the one put.
`DbObjectTester.testLoneSurrogates` (005-26) requires it. A String key
(015-49) and a String value (019-44) refuse a lone surrogate with
`IllegalArgumentException`.

Background:

* A Java `String` is a sequence of 16-bit `char` code units in UTF-16
  (JLS, section 3.1; the Javadoc of `String` and `Character`). A
  character above U+FFFF is two chars, a surrogate pair: a high
  surrogate (U+D800 to U+DBFF) and then a low one (U+DC00 to U+DFFF).
  `String` does not check that pairs are whole: `"a\uD800b"` is a legal
  String. A surrogate without its partner is a lone surrogate.
* Unicode: U+D800 to U+DFFF are not characters, not Unicode scalar
  values (the Unicode Standard, chapter 3); UTF-16 with a lone surrogate
  is ill-formed. UTF-8 encodes scalar values only, and RFC 3629 forbids
  encoding U+D800 to U+DFFF: standard UTF-8 cannot hold a lone
  surrogate.
* `String.getBytes(UTF_8)`, which BergDB's `StringUtil.toBytes` uses,
  "always replaces malformed-input ... with this charset's default
  replacement", '?' for UTF-8. That is where the '?' comes from. A
  `CharsetEncoder` set to report would throw instead.
* How one gets into an application's data: a String cut by char count
  (`s.substring(0, 100)`, a field of at most 100 chars) through a pair;
  JSON input with `"\ud800"` (a legal escape; JavaScript, Jackson and
  Gson decode it to a lone surrogate); Windows file names; code that
  works char by char (a reversal, `(char) n`); fuzzers and random test
  data. Rare, but real.

| Where the String is                     | Lone surrogate                               |
|-----------------------------------------|----------------------------------------------|
| A key                                   | refused, `IllegalArgumentException` (015-49) |
| A String value                          | refused, `IllegalArgumentException` (019-44) |
| A String inside an object               | stored as '?', silently (005-26)             |

Why: a database that returns other data than was put is the worst kind
of fault; 2026.4's theme is "bug-free" (020). Found by 019-44 (agent f44
of 006-13), left for 2026.4 since the object code is experimental in
2026.3; 006-13, section 5, "For Frans to decide (in the morning)",
point 2.

Frans: decision. Frans, 2026-11-07, 08:10: "Add the "Point b, lone
surrogates" as a to decide todo item. Need to think about it."

The options:

* **(1) Refuse** (coord-1106's recommendation). `DbObject.toDbObject`
  throws `IllegalArgumentException` naming the field (and the index of
  an array element), with `PubKeys.hasLoneSurrogate`. One rule for keys,
  values and objects; the stream stays valid UTF-8; the application
  decides what to do with such a String (repair it, or refuse its own
  input). Simple (010-P13). Cost: one scan of each String at a put, as
  keys and values have now; `testLoneSurrogates` changes to expect the
  refusal; a line in `releases/next.md`. Fits 020's work on objects
  (020-01, F1's closed list of types).
* **(2) Store it faithfully.** Encode a lone surrogate in a non-standard
  way, as WTF-8 or Java's modified UTF-8 do (three bytes, `ED A0 80` for
  U+D800), so that the String read back equals the one put. Then the
  stream's Strings are no longer plain UTF-8: every reader must know the
  encoding (the C clone, 012, any tool), `utf8Size` and the encoder
  change, and keys and values should then follow the same rule, or the
  rules differ by where a String is. More code and a format question.
* **(3) Keep '?'.** No change; document it in the object code's Javadoc.
  The silent change of data stays.

Done when: Frans has chosen; the choice is made in the object code (or
documented, for 3) with a test that fails before it, `BEFORE COMMIT OK`,
and a line in `releases/next.md`.

First step: Frans's choice. Then `DbObject.toDbObject`'s String paths and
`DbObjectTester.testLoneSurrogates`.


Log
---

2026-11-07. Registered by coord-1106 from 006-13's morning list, point 2,
at Frans's word (08:10), with the explanation given in the chat at 08:02.
