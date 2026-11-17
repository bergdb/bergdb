021-04. Decide: a lone surrogate in a String inside an object
=============================================================

Status: done. Kind: Decide. Frans: decision.
Created 2026-11-07 by Frans Lundberg.

What: a String inside an object (the object code, `DbObject`, experimental
in 2026.3, 018-01, D6) is stored with '?' in place of a lone surrogate,
silently: the object read back holds other characters than the one put.
`DbObjectTester.testLoneSurrogates` (005-26) requires it. A String key
(015-49) and a String value (019-44) refuse a lone surrogate with
`IllegalArgumentException`.

Since Frans's word of 08:32 (below) the question is wider. BergDB's stream
is meant to be read and written in many languages (010-02, "One stream
format, every platform"), so the decision is what a string is in BergDB's
format and what every language's binding promises about it, for keys,
values and objects alike, not only what Java does. Sections 1 to 6 hold
the study: languages, formats and databases, what BergDB has today, the
consequences of each option across languages, the programs run, and the
sources.

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
* Other languages (section 1): JavaScript, C# and Kotlin strings are
  UTF-16 like Java's and hold lone surrogates; a Python `str` holds any
  code point, surrogates too; Rust's and Swift's strings and the
  WebAssembly Component Model's `string` hold Unicode scalar values only
  and cannot hold one; C and Go strings are bytes, where the counterpart
  of a lone surrogate is a byte sequence that is not well-formed UTF-8.
  Encoding a lone surrogate to UTF-8 gives '?' in Java, U+FFFD in
  JavaScript, C#, Go and Kotlin, and an exception in Python.

| Where the String is                     | Lone surrogate                               |
|-----------------------------------------|----------------------------------------------|
| A key                                   | refused, `IllegalArgumentException` (015-49) |
| A String value                          | refused, `IllegalArgumentException` (019-44) |
| A String inside an object               | stored as '?', silently (005-26)             |

Why: a database that returns other data than was put is the worst kind
of fault; 2026.4's theme is "bug-free" (020). Found by 019-44 (agent f44
of 006-13), left for 2026.4 since the object code is experimental in
2026.3; 006-13, section 5, "For Frans to decide (in the morning)",
point 2. Frans (08:32) calls it important, and the rule chosen is one of
BergDB's format, which every language's binding must keep.

Frans: decision. Frans, 2026-11-07, 08:10: "Add the "Point b, lone
surrogates" as a to decide todo item. Need to think about it." And at
08:32: "Lone surrogates. This is important. Study this further with a
subagent at XHigh effort. Check how this works in other languages
including Rust, Python, JavaScript, WebAssembly, C. Add to the document,
make no code changes. Note that BergDB is design for multi-langage
support. So, decisions like this are not specific to Java only."

Frans, 2026-11-07, 09:33, the decision: "021-04, good study. Yes, option
1, absolutely. Document this, ensure it is clear in the Javadoc API
comments."

The options:

Each option is a rule for every string the stream holds: the text of a
key, a String value, a string field of an object, an index name; and
for what a binding in another language does at a put and at a get. A
"lone surrogate" stands for its counterpart in C and Go too: bytes given
as a string that are not well-formed UTF-8. Labels such as J2 or PY7 are
lines of the programs' outputs (section 5); "docs" marks what comes from
documentation or source code only.

* **(1) Refuse: a BergDB string is Unicode text, stored as well-formed
  UTF-8** (coord-1106's recommendation, and this study's). The rule: a
  string is a sequence of Unicode scalar values (Unicode, D76), stored
  as well-formed UTF-8 (RFC 3629; Unicode, D92). A writer refuses a
  string it cannot store so, before anything is written: in Java,
  JavaScript, C# and Kotlin a string with a lone surrogate; in C and Go
  bytes that are not well-formed UTF-8. In Java, `DbObject.toDbObject`
  throws `IllegalArgumentException` naming the field (and the index of
  an array element), with `PubKeys.hasLoneSurrogate`, as keys and values
  do now. Consequences:
  * The round trip: every string that is taken reads back equal, in
    every language, and every language can read every stored string
    into its own string type (section 4.1).
  * The check, per language (section 4.3): a scan of each string in
    UTF-16 languages (Java has it at keys and values; JavaScript has
    `isWellFormed()`, ES2024; C# a `UTF8Encoding` that throws); it can
    be the encoding itself (a `CharsetEncoder` with `REPORT` encodes and
    checks in one pass, J4). Python's encoder refuses by default (PY2),
    Rust's and Swift's strings cannot hold one: no cost there. C and Go
    validate UTF-8 once (the C clone's runner has such a function, 012-05,
    section 6.1).
  * The stream: no format change. Java's encoder has only ever written
    well-formed UTF-8 ('?' is ASCII), so every existing database already
    holds well-formed UTF-8 in its strings; its old '?'s stay as they
    are and read as before.
  * Readers may rely on it. A reader that finds ill-formed UTF-8 where a
    string should be (another writer's fault, or damage) would report it,
    in Java with `DataFormatException`, rather than repair it silently as
    Java does today, so that two keys read as one (section 4.4; a later
    entry).
  * The application decides what to do with such a string: repair it
    (JavaScript's `toWellFormed()` puts U+FFFD in place of each lone
    surrogate, JS6), refuse its own input, or store it as data that is
    not text: a `byte[]`, or in an object a `char[]`, which the object
    code stores as integers and reads back exactly (OB2, OB3).
  * The C clone (012) needs no change: it stays at release 2026.2 and
    has no Pub layer or objects. A later port checks ikeys in
    `bergdb_ikey_to_bkey`, which takes any bytes but 0xFE and 0xFF today
    (CK1 to CK5).
  * In Java: `DbObject.toDbObject`'s String paths, `testLoneSurrogates`
    changed to expect the refusal, a line in `releases/next.md`. The
    Core's own String puts (`Trans.Builder.put(String, String)`,
    `Keys.toBytes`) still write '?' (section 3.1): a follow-up entry.
  * Simple (010-P13): one rule for keys, values and objects, the same in
    every language, and the rule of the formats made for many languages
    (section 2). Fits 020's work on objects (020-01, F1's closed list of
    types).
* **(2) Store it faithfully: a BergDB string is a sequence of UTF-16
  code units, stored as WTF-8.** The rule: a string is what a Java,
  JavaScript or C# string can hold, any sequence of 16-bit code units;
  in Unicode terms, code points with surrogates only where they do not
  form a pair. It is stored as WTF-8 (section 6, [WTF-8]): UTF-8, and a
  lone surrogate as the three bytes UTF-8 would give its number (U+D800
  as `ED A0 80`), a pair always as four bytes. Java's modified UTF-8 is
  a near relative: it also writes NUL as `C0 80` and a character above
  U+FFFF as two 3-byte halves (J5). Consequences:
  * The round trip is exact only between UTF-16 languages whose bindings
    have a WTF-8 encoder and decoder. No platform has one: Java's UTF-8
    decoder reads `ED A0 80` as one U+FFFD (J6), JavaScript's, Go's,
    Swift's and Python's lenient decoders as three (JS3, GO2, SW3, PY8),
    the strict ones refuse it (J7, JS4, PY6, PL8, GL2). Every binding
    writes its own codec, and `utf8Size`, the encoder and the decoder
    change in Java.
  * Readers in scalar-value languages cannot hold such a string: a Rust
    `String` is always valid UTF-8 (docs), Swift's `String` repairs it
    (SW3) or refuses it (SW4), the Component Model traps when it lifts it
    (docs; PY22, PY23). Each such binding must refuse it, repair it (so
    the round trip is lost in that direction), or offer a second string
    type, as Rust's `OsString` does on Windows (docs).
  * "Faithful" differs by language. In Python a lone surrogate is often a
    byte that could not be decoded (PEP 383: `b'\xff'` reads as U+DCFF,
    PY9, PY16), and its faithful form is that byte, not WTF-8. A Python
    `str` can also hold the two halves of a pair as two code points,
    which `surrogatepass` writes as six bytes (PY20), a form WTF-8
    forbids; the binding must join them first.
  * The format: the stream's strings are no longer UTF-8. The spec and
    every tool (a dump, an export to JSON, the C clone) must know WTF-8,
    whose own spec says it "must not be used to represent text in a file
    format or for transmission over the Internet" ([WTF-8], section 1).
    No format of section 2 uses it for strings.
  * Keys and values should follow, or the rule differs by where a string
    is: 015-49's and 019-44's refusals are undone; keys with a lone
    surrogate sort between U+D7FF and U+E000; an index's sort keys
    (`string/unicode`, ICU) meet ill-formed text.
  * Cost: a codec in every binding, a format change (Frans approves such
    changes, 018-01, section 2), more tests. Against 010-P13.
* **(3) Keep '?'.** No change; document it in the object code's
  Javadoc. Consequences:
  * No round trip for such a string, in any language: the object read
    back holds other characters, silently.
  * Java's choice only: '?' is what `String.getBytes(UTF_8)` writes
    (J2). JavaScript, Go, C#, Kotlin and Rust's lossy conversions write
    U+FFFD (JS2, GO3, docs), Python raises (PY2). A binding in another
    language must copy Java's encoder to write the same bytes (012's
    rule: the same stream, byte for byte).
  * It is an encoder's habit, not a rule of the format: it says nothing
    of bytes that a C or Go writer gives, so the stream can still get
    ill-formed UTF-8 (section 4.4).
  * Keys and values refuse, objects change the data: two rules in one
    database. A '?' cannot be told from a real '?' (two keys that
    differed only there were one key, S2-F24, 015-49).
  * Against 2026.4's theme: a known silent change of data.
* **(4) Replace with U+FFFD.** As (3), but with the Unicode replacement
  character (`EF BF BD`) in place of each lone surrogate, documented.
  Consequences:
  * It is what most platforms do when they are lenient: JavaScript's
    `TextEncoder` and `toWellFormed()` (JS2, JS6), Go (GO3, GO8), Rust's
    `from_utf16_lossy`, .NET's `UTF8Encoding`, Kotlin's
    `encodeToByteArray()` (docs), and at a JavaScript-to-WebAssembly
    boundary wasm-bindgen and jco (WA1; docs). Java needs a step of its
    own (its default is '?').
  * The data still changes silently, as in (3), but the change shows (the
    replacement character is drawn as a mark) and is the same in every
    binding that follows its platform.
  * Two strings that differ only there are still one: "a" + U+D800 and
    "a" + U+FFFD. Keys must go on refusing, so keys and objects differ,
    as in (3).
  * As (3), a habit of encoders, not a rule for bytes from C or Go.
* **(5) Refuse by default, with an opt-in to replace.** As (1), and a
  setting (a `DatabaseBuilder` option, or a flag per put) that makes the
  writer put U+FFFD in place of a lone surrogate instead. Consequences:
  * A second error model in every binding, to document and test (010-P10,
    few settings; P13). The application can replace by itself in one
    call (JavaScript's `toWellFormed()`; in Java a few lines, which
    BergDB could offer as a static helper, without a setting).
* **(6) A separate type for data that is not text.** As (1) for strings,
  and a type that holds any 16-bit code units for applications that need
  them exactly. Consequences:
  * It exists already: `byte[]` values and `b` fields hold any bytes; a
    `char[]` field holds any UTF-16 code units, stored as an array of
    integers, and reads back exactly (OB3; a `char` field too, OB2). A
    reader in any language gets numbers or bytes, never a broken string.
  * A new object type (a "UTF-16 string") would make it explicit, but
    every scalar-value language would map it to something other than its
    string type: more format for little gain over `char[]`. Not
    recommended as a new type; naming `char[]` in the object code's
    Javadoc as the way to keep such data is enough.

**Recommendation: (1)** for every string of the stream, keys, values and
objects alike, with (6)'s existing types as the documented way to store
what is not text. The rule, as the format would state it: every string
in a BergDB stream is a sequence of Unicode scalar values stored as
well-formed UTF-8 (RFC 3629); a writer refuses a string it cannot store
so, a reader may rely on it, and strings compare and sort by their bytes,
which is code point order. The reasons:

1. It is the one rule every language can keep in both directions. The
   scalar-value strings are what every language can hold: a well-formed
   Java, JavaScript or C# string, a Rust or Swift `String`, a Python
   `str` without surrogates, a Go string that is valid UTF-8, the
   Component Model's `string`. Any string taken reads back equal in any
   language (section 4.1); with (2), (3) or (4) some do not.
2. It is what the formats made for many languages chose, and the lenient
   ones show the cost (section 2): CBOR calls invalid UTF-8 invalid,
   proto3 and I-JSON require well-formed text, the Component Model traps,
   PostgreSQL refuses; where it is left open, the libraries part ways:
   @msgpack/msgpack writes different bytes for the same lone surrogate by
   the string's length (JSL1, JSL2), protobufjs writes bytes that it then
   cannot read (JSL10, JSL11), SQLite promises "Garbage-In, Garbage-Out".
3. It is BergDB's rule already for keys (015-49), values (019-44) and
   index names: one rule, no exception for objects (010-P13). And it is
   the model of the original design: a string is "a sequence of Unicode
   characters" (Frans, 2008-08-07, 010-02's sources), keys are UTF-8 and
   "any valid UTF-8 ikey can be converted" ([F1-007], 2013-key-encoding).
4. No format change: every stream Java has written holds only well-formed
   UTF-8, and the bytes of every string taken stay the same.
5. It costs little: one pass per string at a put, which keys and values
   pay already, and which can be the encoding pass itself.

Two questions remain with (1), for later entries (not for this
decision): the Core's String puts that still write '?' (section 3.1),
and the read side, a key or a string that is not well-formed UTF-8 in a
stream made by another writer (section 4.4). The defaults: a 021 entry
for each, the second with 020-01's object spec (F1, question 5). They are
021-05 and 021-06 (Frans, 2026-11-07, 09:34: ""Two problems found". Yes,
add entries.").

Done when: Frans has chosen; the choice is made in the object code (or
documented, for 3) with a test that fails before it, `BEFORE COMMIT OK`,
and a line in `releases/next.md`; and the rule is written once for keys,
values and objects, in the Pub API's Javadoc of the puts, and in the
object format's spec when 020-01 (F1) writes it.

First step: Frans's choice. Then `DbObject.toDbObject`'s String paths and
`DbObjectTester.testLoneSurrogates`.


## 1. Languages

What each language's string is, whether it can hold a lone surrogate,
what its standard library does when it encodes one to UTF-8 and when it
decodes the WTF-8 bytes of one (`61 ED A0 80 62`, "a", U+D800, "b"), and
how that is known: "run J" means the J lines of section 5, "docs" the
documentation or source of section 6.

| Language | A string is | Lone surrogate | To UTF-8 | `ED A0 80` read as | Known |
|---|---|---|---|---|---|
| Java       | UTF-16 code units | yes   | '?'; or throws      | 1 U+FFFD; or throws    | run J  |
| JavaScript | UTF-16 code units | yes   | U+FFFD              | 3 U+FFFD; or throws    | run JS |
| C#/.NET    | UTF-16 code units | yes   | U+FFFD; or throws   | U+FFFD; or throws      | docs   |
| Kotlin     | UTF-16 code units | yes   | replaced; or throws | as Java (JVM)          | docs   |
| Python 3   | code points       | yes   | raises (or WTF-8)   | raises (or 3 U+FFFD)   | run PY |
| Rust       | scalar values     | no    | cannot occur        | `Err`; lossy U+FFFD    | docs   |
| Swift      | scalar values     | no    | cannot occur        | 3 U+FFFD; or `nil`     | run SW |
| Go         | bytes             | bytes | U+FFFD              | kept; runes 3 U+FFFD   | run GO |
| C          | bytes; code units | yes   | `wcrtomb` EILSEQ    | kept; `mbrtowc` EILSEQ | run C  |

Notes, one line or two each:

* **Java** (and Kotlin on the JVM): `getBytes(UTF_8)` writes '?' (J2); a
  `CharsetEncoder` with `REPORT` throws (J4); UTF-16 (`UTF_16BE`)
  replaces it with U+FFFD too (J8); `DataOutputStream.writeUTF` (modified
  UTF-8) keeps it, `ED A0 80` (J5). Lone surrogates come from `substring`
  through a pair and char-by-char code (J9, J11).
* **JavaScript**: a string is "a sequence of 16-bit unsigned integer
  values" with no restriction on their relations ([ECMA-262], 6.1.4).
  `TextEncoder` takes a `USVString`, so a lone surrogate becomes U+FFFD
  (JS2; [Encoding], 7.4); `isWellFormed()` and `toWellFormed()` (ES2024,
  22.1.3.10 and 22.1.3.31; JS5, JS6); `JSON.stringify` escapes it as
  `\ud800` since ES2019 (JS7) and `JSON.parse` gives it back (JS8);
  `encodeURIComponent` throws (JS9). Node and Deno agree (two outputs).
  String comparison is by UTF-16 code unit, not code point (JS13).
* **C#/.NET**: a `string` is "logically a sequence of 16-bit values" and
  may be ill-formed ([.NET encoding], "Well-formed encoding");
  `UTF8Encoding` replaces with U+FFFD both ways, or throws if made with
  `throwOnInvalidBytes` ([.NET UTF8Encoding], `SetDefaultFallbacks`);
  `Rune` is a scalar value and refuses a lone surrogate. Not run.
* **Kotlin**: on the JVM, Java's `String`; `encodeToByteArray()`
  replaces "any malformed char sequence", or throws
  `CharacterCodingException` with `throwOnInvalidSequence` ([Kotlin]).
  Not run.
* **Python 3**: a `str` is a sequence of code points, surrogates
  included (PY1). Strict UTF-8 raises (PY2, PY6); `surrogatepass` writes
  and reads WTF-8-like bytes (PY3, PY7); `replace` writes '?' (PY4) and
  reads three U+FFFD (PY8); `surrogateescape` (PEP 383) turns each
  undecodable byte into U+DC80 to U+DCFF and back (PY9, PY10, PY16).
  `json` escapes a lone surrogate (PY13) and reads `\ud800` (PY15);
  `sqlite3` refuses it (PY17). Two halves are not the pair (PY19).
* **Rust**: "`String`s are always valid UTF-8" ([Rust String], "UTF-8"),
  and a `char` is a Unicode scalar value; `String::from_utf16` returns
  `Err` for a lone surrogate, `from_utf16_lossy` gives U+FFFD, `from_utf8`
  returns `Err` ([Rust String]). `OsString` on Windows holds ill-formed
  UTF-16 in "a less-strict variant of UTF-8" (WTF-8 inside the standard
  library) and converts to `String` only if valid ([Rust OsString]).
  serde_json refuses `"\ud800"` into a `String` ("lone leading surrogate
  in hex escape") and keeps it as WTF-8 only into a byte string
  ([serde_json]). Not run (no rustc on F53).
* **Swift**: a `String` holds scalar values (grapheme clusters on top);
  `Unicode.Scalar(0xD800)` is `nil` (SW2); decoding repairs with U+FFFD
  (SW1, SW3) or `String(validating:)` gives `nil` (SW4). An `NSString`
  holds a lone surrogate (SW5); bridged to `String` it reads as U+FFFD
  (SW6), and `data(using: .utf8)` gives `nil` (SW8).
* **Go**: a string is "a (possibly empty) sequence of bytes" ([Go spec]);
  any bytes, `ED A0 80` too, are kept (GO1, GO11); `range` and `[]rune`
  give U+FFFD per bad byte (GO2, GO10); `string(rune(0xD800))` and
  `utf16.Decode` give U+FFFD (GO3, GO6); `encoding/json` writes U+FFFD
  for bad bytes and reads `\ud800` as U+FFFD (GO7, GO8).
* **C**: a `char*` is bytes and takes `ED A0 80` (C1); a 16-bit array
  holds 0xD800 (C2); the C library, in a UTF-8 locale, refuses U+D800
  both ways with `EILSEQ` (C4 to C6). macOS has no `<uchar.h>`
  (`char16_t`, `c16rtomb`): the program's first build failed on it. C11
  forbids `\uD800` in source (C11, 6.4.3; C7).
* **Others not run**: Kotlin/Native and Kotlin/JS follow Kotlin's
  library above; Dart, Qt's `QString` and Win32 (`wchar_t`) are UTF-16
  like Java and can hold lone surrogates (not checked further).

**WebAssembly** has no string of its own; what a string is depends on
the layer:

| Layer | A string is | A lone surrogate | Known |
|---|---|---|---|
| Core Wasm                 | bytes in linear memory      | what the language put | spec       |
| Component Model `string`  | scalar values               | traps when lifted     | spec, PY22 |
| JS to a component (jco)   | JS string, then encoded     | U+FFFD                | source     |
| JS to Rust (wasm-bindgen) | JS string, then UTF-8       | U+FFFD                | docs, WA1  |
| JS String Builtins (3.0)  | JS string as `externref`    | kept, as code units   | run WA2    |
| stringref (phase 1)       | scalars and lone surrogates | trap, U+FFFD or WTF-8 | proposal   |

* The Component Model: `char` is a Unicode scalar value and `string`
  is a specialization of `list<char>` ([CM Explainer], "Fundamental
  value types", "Specialized value types"); lifting a string decodes
  with a strict codec and traps on any error ([CM Canonical ABI],
  "Loading", `load_string_from_range`), PY22 and PY23 run the same
  calls. So a component can never receive a lone surrogate.
* jco, which runs components in JavaScript: from JS, "Unpaired surrogates
  are replaced, as when converting to a `USVString`"; to JS, a
  `TextDecoder` with `fatal: true` ([jco]). wasm-bindgen: "it will
  replace the unpaired surrogates with U+FFFD"; `JsString` keeps them
  ([wasm-bindgen]); WA1 shows the copy into Wasm memory.
* JS String Builtins (`wasm:js-string`, a finished proposal, Wasm 3.0
  [Wasm proposals]): Wasm code works on JS strings as "a sequence of
  16-bit code units"; WA2 reads U+D800 from one in Node 26. Its UTF-8
  builtins are future work and "use the replacement character for
  unpaired surrogates" ([JS String Builtins], "Future extensions").
* stringref (phase 1, [Wasm proposals]): "a sequence of unicode scalar
  values and isolated surrogates"; `string.encode_utf8` traps on one,
  `encode_lossy_utf8` writes U+FFFD, `encode_wtf8` keeps it
  ([stringref]).

Who can produce a lone surrogate, who can hold one after a decode:

* Produce one in an ordinary string: Java, Kotlin, JavaScript, C#,
  Python; C and Go as bytes (or 16-bit arrays). Not Rust, Swift, the
  Component Model, except through a second type (`OsString`, `NSString`,
  `JsString`, `Vec<u16>`).
* Hold one after reading WTF-8: Python with `surrogatepass` (PY7); Java,
  JavaScript, C# only with a decoder of their own (their UTF-8 decoders
  replace, J6, JS3); Go and C as bytes; not Rust's `String`, Swift's
  `String`, the Component Model.
* Replace: with '?' Java's `getBytes` (J2) and Python's `replace` on
  encode (PY4); with U+FFFD JavaScript, C#, Go, Kotlin, Rust's lossy
  calls, Swift, wasm-bindgen, jco; on decode, Java gives one U+FFFD for
  `ED A0 80` (J6), the others three (JS3, PY8, GO2, SW3), as Unicode
  recommends ([Unicode], 3.9.6). Throw: Python strict, the strict modes
  of Java, JavaScript, C#, Kotlin, Rust's `from_utf16` and `from_utf8`,
  C's `wcrtomb`; trap: the Component Model.


## 2. Formats and databases

| Format or database | Its rule for a string | Known |
|---|---|---|
| JSON, RFC 8259     | `"\ud800"` passes; "unpredictable" (8.2)      | RFC, run     |
| I-JSON, RFC 7493   | no surrogates, escaped or not (2.1)           | RFC          |
| CBOR, RFC 8949     | UTF-8; else "well-formed but invalid" (3.1)   | RFC, run     |
| Protobuf, proto3   | "must always contain UTF-8"; VERIFY           | docs, run    |
| MessagePack        | UTF-8, "may contain invalid byte sequence"    | spec, run    |
| BSON 1.1           | "zero or more UTF-8 encoded characters"       | spec, run    |
| SQLite             | bytes as given: "Garbage-In, Garbage-Out"     | docs, run    |
| PostgreSQL         | valid UTF-8 (a UTF8 database); `jsonb` strict | docs, source |
| Component Model    | Unicode scalar values; a lift traps           | spec         |
| WTF-8              | inside one system only, not in a file format  | spec         |
| Java's own formats | modified UTF-8 (class files, serialization)   | run J5       |

What the libraries do with a lone surrogate (write) and with `ED A0 80`
in a string (read):

| Library | Writes a lone surrogate | Reads `ED A0 80` | Run |
|---|---|---|---|
| JSON: JS, Python      | escapes it                    | `\ud800` as U+D800      | JS7-8, PY13-15 |
| JSON: Jackson, Gson   | escapes it, or raw            | `\ud800` as U+D800      | JL4-JL9        |
| JSON: Go              | (bad bytes) U+FFFD            | `\ud800` as U+FFFD      | GO7, GO8       |
| CBOR: cbor2 (Python)  | refuses                       | refuses                 | PL1, PL2       |
| CBOR: cbor-x (JS)     | `ED A0 80`                    | 3 U+FFFD                | JSL8, JSL9     |
| CBOR: fxamacker (Go)  | the bytes                     | refuses                 | GL3-GL5        |
| Protobuf: Java        | '?', silently                 | refuses                 | JL1-JL3        |
| Protobuf: Python, Go  | refuses                       | refuses                 | PL7-8, GL1-2   |
| Protobuf: protobufjs  | `ED A0 80`                    | refuses (its own bytes) | JSL10-11       |
| MessagePack: Python   | refuses                       | refuses; by option kept | PL3-PL6        |
| MessagePack: @msgpack | `ED A0 80`, or U+FFFD if long | U+D800                  | JSL1-JSL4      |
| BSON: pymongo         | refuses                       | refuses                 | PL9, PL10      |
| BSON: js-bson         | U+FFFD                        | refuses                 | JSL5-JSL7      |
| SQLite                | (Python: refuses)             | kept as given           | PY17, SQ1-7    |
| PostgreSQL            | -                             | refuses                 | source         |

* **JSON**: the grammar lets any `\uXXXX` through, and RFC 8259, 8.2,
  says that with an unpaired surrogate "the behavior of software that
  receives JSON texts containing such values is unpredictable"; I-JSON
  (RFC 7493, 2.1) forbids it: "\uDEAD" is invalid. JSON is how a lone
  surrogate most often reaches an application (JS8, PY15, JL6, JL9).
* **CBOR**: a text string is UTF-8; "A string containing an invalid
  UTF-8 sequence is well-formed but invalid" (RFC 8949, 3.1); a decoder
  "might or might not" check (5.3.1). The libraries part ways (table).
* **Protocol Buffers**: proto3's `string` "must always contain UTF-8
  encoded or 7-bit ASCII text" ([proto3], "Scalar Value Types");
  `features.utf8_validation` is `VERIFY` for proto3 and editions, `NONE`
  for proto2, where "Parsers may handle this type of field in an
  unpredictable way" ([protobuf features]). Java writes '?' with no
  warning seen (JL1), as Java's `getBytes`; protobufjs writes WTF-8 and
  then refuses to read it (JSL10, JSL11).
* **MessagePack**: "String extending Raw type represents a UTF-8 string"
  and "String objects may contain invalid byte sequence", "the behavior
  of a deserializer depends on the actual implementation" ([MessagePack],
  "Type system"). @msgpack/msgpack 3.1.3 shows what that leads to: the
  same lone surrogate is `ED A0 80` in a short string and `EF BF BD` in a
  long one (JSL1, JSL2), since it encodes strings of up to 50 chars with
  its own code and longer ones with `TextEncoder` (its `utils/utf8`).
* **BSON** (MongoDB): strings are UTF-8 ([BSON]); the drivers refuse
  ill-formed UTF-8 when reading by default (PL10, JSL6); the Node driver
  writes U+FFFD (JSL5), Python refuses (PL9).
* **SQLite**: "SQLite does not try to enforce UTF formatting rules" and
  "makes no guarantees about what text you might get back out"
  ([SQLite], sections 1 to 3). `char(0xD800)` and `json_extract` of
  `"\ud800"` make `ED A0 80` (SQ3, SQ5); the bytes sort and compare as
  bytes (SQ2).
* **PostgreSQL**: a UTF8 database refuses `ED A0 80`
  (`pg_utf8_islegal`, [PostgreSQL wchar.c]); `jsonb` "insists that any
  use of Unicode surrogate pairs ... be correct", while `json` keeps the
  text, checking only the escape's syntax ([PostgreSQL], 8.14).
* **Why the formats chose so**: a format read by many languages can only
  promise what every reader can hold. Those that state a rule (CBOR,
  proto3, I-JSON, the Component Model, PostgreSQL) chose Unicode scalar
  values, well-formed UTF-8. Those that left it open (JSON's grammar,
  MessagePack, proto2, SQLite) leave each library to choose, and the
  libraries choose differently, even one library with itself (JSL1,
  JSL2, JSL10, JSL11). WTF-8 and modified UTF-8 are used inside one
  system (Rust's `OsString`, Java's class files and serialization), not
  as a format between languages.


## 3. What BergDB has today

### 3.1 In Java

* Keys: `PubKeys.u2i` and `udir2idir` refuse a lone surrogate since
  015-49 (S2-F24), and `IndexManager.checkIndexName` an index name.
  String values: `RwEnvironmentImp.put` since 019-44. Both with
  `PubKeys.hasLoneSurrogate`, one scan of the chars.
* Objects: `DbString.write` uses `StringUtil.toBytes`, `getBytes`: '?'
  (OB1). `StringUtil.utf8Size` counts a lone surrogate as one byte to
  match (005-26). A `char` and a `char[]` field are stored as integers
  (type `i`, and an array of them) and read back exactly (OB2, OB3).
  Field names come from the class's fields: javac refuses a lone
  surrogate in a name (J12), though a generated class file could hold
  one; `DbObject.Builder` takes any name (internal use). The rule covers
  names too.
* The Core's String conveniences: `Trans.Builder.put(String, String)`
  and `Keys.toBytes(String)` use `getBytes`, so a Core user's lone
  surrogate becomes '?' there, in a key or a value; the Core's own
  strings are ASCII (reclaim's table, `/#i/` keys).
* Reads: `StringUtil.toString` (`new String(bytes, "UTF-8")`) repairs
  ill-formed UTF-8 with U+FFFD, for String values, an object's `s`
  fields and keys (`Keys.bkey2ikey`). An index's `string/unicode` sort
  key is the UTF-8 of the value, each byte + 2 (`UnicodeCollator`).

### 3.2 In the format and the C clone (012)

* A key is a byte string, a bkey; the Pub layer's text keys are UTF-8,
  each `/` as 1 and every other byte + 2 (012-02, section 7). The
  original note on it ([F1-007], 2013-key-encoding): "The bytes 0xFE and
  0xFF do not appear in valid UTF-8 bytes, so any valid UTF-8 ikey can
  be converted this way" and "An arbitrary bkey cannot, in general, be
  converted to an ikey".
* A String value is its UTF-8 bytes (012-03, section 6.4); the object
  format is not specified for other languages yet (020-01, F1, question
  5), and C reads objects only as bytes.
* The C clone's `bergdb_ikey_to_bkey` takes any bytes but 0xFE and 0xFF,
  "The bytes are not checked to be UTF-8" (`include/bergdb.h`): it takes
  `ED A0 80`, `EF BF BD`, `C0 80` (CK1 to CK4). Java reads the first two
  as one String, and `Keys.toBytes` of it gives the second bkey, so the
  first key's value cannot be got by its key from Java (JR1 to JR5).
* The C clone already does what option (1) asks where it reads text: the
  cross harness takes only valid UTF-8 keys (`valid_utf8` in
  `c/tools/run.c`, "Strict UTF-8, as Java's decoder with REPORT"; 012-05,
  section 6.1). And it shows the cost of Java's UTF-16 in the format:
  reclaim's table order needs `String.hashCode()` over UTF-16 code units,
  computed in C from UTF-8 (`c/src/strmap.h`), and directory order
  differs between Java's `compareTo` and bytes (`c/src/plat.h`).

### 3.3 In the principles and the old notes

* 010-02, "One stream format, every platform": "NOT java dependent,
  should work with many languages with a language-independent data
  object model" (2008-08-07); "There is only *one* DB stream format for
  all supported devices, operating systems and programming languages"
  (by 2013-06-06).
* The same note of 2008-08-07 ([F1-007], `log-old/2008-2011-log.txt`):
  "string: A built-in string type is absolutely required. It is a
  sequency of Unicode characters. In Java the String class is used.
  Internally, the string may be stored using UTF-8 or UTF-16BE or
  whatever encoding that is suitable." Characters, not code units.
* 2009-11-01 (the same log): keys are strings, "sorted according to
  Unicode. Stored as UTF-8"; 2013-key-encoding: "Sorting the bytes should
  sort the keys in alphabetical order according to Unicode". UTF-8's byte
  order is code point order; UTF-16's is not (JS13).
* 010-01: P2 (a deterministic stream), P10 (few settings), P13 (KISS:
  "Important that the database user understands the error model"). 012's
  rule that Java and C write the same stream, byte for byte; and 005-79
  (012-16, "Next steps"): integers instead of doubles "so that every
  language and target gives the same bytes".


## 4. Consequences across languages

### 4.1 A put in one language, a get in another

| Writer to reader | (1) refuse | (2) WTF-8 | (3) or (4) |
|---|---|---|---|
| UTF-16 to UTF-16 (Java to JS)   | refused at put | exact, own codecs   | replaced |
| UTF-16 to scalar (Java to Rust) | refused at put | refused or repaired | replaced |
| Python to Java                  | refused at put | PEP 383 bytes lost  | replaced |
| scalar to any (Rust to Java)    | exact          | exact               | exact    |
| bytes to any (C or Go to Java)  | refused at put | some bytes taken    | no rule  |

* With (1) every cell is "exact" for every string that is taken; the
  refused ones never reach the stream.
* With (2), a UTF-16 writer and a scalar reader disagree on what the
  stream holds; every scalar binding needs a policy of its own.
* (3) and (4) are rules for Java's encoder only: they leave open what
  a C or Go writer may give, so readers meet ill-formed UTF-8 anyway
  (4.4).

### 4.2 Scalar-value writers

A Rust, Swift or Component Model writer can only give scalar values: its
strings are well-formed under every option, and every reader gets them
exactly. The options differ only for UTF-16 writers (Java, JavaScript, C#,
Kotlin), Python, and byte-string writers (C, Go).

### 4.3 The cost of the check under (1), per language

* Java: `PubKeys.hasLoneSurrogate`, one scan of the chars; or a
  `CharsetEncoder` with `REPORT` that encodes and checks at once (J4).
* JavaScript: `s.isWellFormed()`, native (JS5); Node's and the browsers'
  `TextEncoder` cannot report, it replaces (JS2).
* C#: a `UTF8Encoding(false, true)`, which throws; `Rune` for scalars.
* Kotlin: `encodeToByteArray(throwOnInvalidSequence = true)`.
* Python: none; `str.encode('utf-8')` raises (PY2); a binding reports it
  as BergDB's error. PEP 383 data (`surrogateescape`) is refused too,
  as Python's own strict encoder refuses it.
* Rust, Swift, Component Model: none; the type holds only scalar values.
  A Rust reader validates with `String::from_utf8` (fast, and needed for
  memory safety); it cannot trust the stream blindly.
* Go: `utf8.ValidString` (GO1). C: a validator of about 40 lines, as
  `valid_utf8` in 012's `c/tools/run.c`.
* A JavaScript application that calls a BergDB component through jco or
  wasm-bindgen gets U+FFFD put in silently at that boundary, before
  BergDB sees the string; the JavaScript binding must check first
  (`isWellFormed()`), else option (1) turns into (4) there.

### 4.4 The read side

Every Java-written stream holds well-formed UTF-8, but a C writer may put
any key bytes (CK1 to CK4), and the Core API takes any bytes. Java's
reader repairs with one U+FFFD (J6) where other languages give three
(JS3, PY8, GO2, SW3), so two readers of one stream disagree on such a
string, and two keys can read as one (JR4). Under (1) a reader that finds
ill-formed UTF-8 in a string reports it (`DataFormatException`, "data in
the database has an illegal format"); a key from the Core that is not
UTF-8 is a bkey without an ikey, as 2013-key-encoding says. A question
for a later entry (the recommendation's last paragraph).

### 4.5 Order and equality

BergDB sorts keys by their bytes. For well-formed UTF-8 that is code
point order in every language; Java's `compareTo` and JavaScript's `<`
compare UTF-16 code units, which differ for characters above U+FFFF
against U+E000 to U+FFFF (JS13; 012's `plat.h`). A binding in a UTF-16
language compares by code point, not with its native comparison. No
option changes this, but (2) adds surrogates to the order (between
U+D7FF and U+E000). Equality is by bytes: no normalization (NFC, NFD) in
any option.


## 5. The programs and their results

Programs and outputs in `/Users/f/fl/bench/006-14/021-04/` (its
`readme.txt` lists how to run each), run on F53 on 2026-11-07. Every
line below was seen in an output; the rest of this entry marked "docs"
was not run.

* `java/Lone.java` (JDK 27): J1 a String holds U+D800; J2 `getBytes`
  gives `61 3F 62`; J3 reads back "a?b"; J4 `REPORT` throws
  `MalformedInputException`; J5 `writeUTF` gives `61 ED A0 80 62 C0 80`;
  J6 `ED A0 80` decodes to one U+FFFD; J7 `REPORT` refuses it; J8
  `UTF_16BE` replaces with U+FFFD; J9 `substring(0, 3)` of two U+1F600
  ends with a lone high surrogate; J11 a char-by-char reversal makes two;
  J12 javac refuses `\uD800` in a field name (`Ident.java`).
* `python/lone.py` (3.14.7): PY2 strict raises "surrogates not allowed";
  PY3 `surrogatepass` gives `61 ED A0 80 62`; PY4 `replace` gives '?';
  PY6 strict decode raises; PY7 `surrogatepass` gives U+D800; PY8
  `replace` gives three U+FFFD; PY9, PY10, PY16 PEP 383 maps `FF` to
  U+DCFF and back; PY13 `json.dumps` escapes; PY14 with
  `ensure_ascii=False` the text cannot be encoded; PY15 `json.loads`
  gives U+D800; PY17 `sqlite3` refuses; PY19 two halves are not the
  pair; PY20 they encode as six bytes `ED A0 BD ED B8 80`; PY22, PY23
  the Canonical ABI's strict decodes raise.
* `js/lone.mjs` (Node 26.9.0, Deno 2.9.7, the same results): JS2
  `TextEncoder` gives `61 EF BF BD 62`; JS3 three U+FFFD; JS4 `fatal`
  throws `TypeError`; JS5 `isWellFormed()` false; JS6 `toWellFormed()`
  gives "a" U+FFFD "b"; JS7 `JSON.stringify` gives `"a\ud800b"`; JS8
  `JSON.parse` gives U+D800; JS9 `encodeURIComponent` throws `URIError`;
  JS13 U+FF61 < U+1F600 is false; JS14, JS15 Node's `Buffer` as
  `TextEncoder` and `TextDecoder`; WA1 `encodeInto` a `WebAssembly.Memory`
  gives `61 EF BF BD 62`; WA2 a hand-made module with `wasm:js-string`
  `charCodeAt` reads `61 D800 62`.
* `go/lone.go` (1.27.0): GO1 the bytes are a string, not valid; GO2
  three U+FFFD by `range`; GO3, GO5 U+D800 encodes as `EF BF BD`; GO6
  `utf16.Decode` U+FFFD; GO7 `json.Marshal` three U+FFFD; GO8
  `json.Unmarshal` of `\ud800` U+FFFD; GO11 bytes round-trip.
* `c/lone.c` (Apple clang 21): C1 bytes kept; C2 a 16-bit array holds
  it; C4 `wcrtomb(0xD800)` and C5 `mbrtowc` of `ED A0 80` and C6
  `mbstowcs` give `EILSEQ`; C7 `"\uD800"` in a C11 source is an error
  (`ucn.c`). `<uchar.h>` is missing on macOS.
* `swift/lone.swift` (Swift 6.4): SW1 U+FFFD from UTF-16; SW2 no scalar
  for 0xD800; SW3 three U+FFFD from UTF-8; SW4 `validating` gives `nil`;
  SW5 `NSString` holds it; SW6 bridged it reads as U+FFFD; SW8 its UTF-8
  data is `nil`.
* `sqlite/lone.sql` (3.54.0): SQ2 `ED A0 80`, `EF BF BD` and '?' stored
  as three keys, as given; SQ3 `char(0xD800)` gives `ED A0 80`; SQ4
  `json_valid('"\ud800"')` is 1; SQ5 `json_extract` gives `ED A0 80`;
  SQ7 `unicode()` of it is 65533.
* `cclone/` (012's `keys.c`, and the jar of 2026-11-05): CK1 to CK4 the
  C clone takes `ED A0 80`, `EF BF BD`, '?' and `C0 80` in an ikey, CK5
  refuses 0xFF; JR1, JR2 Java reads CK1's and CK2's bkeys as the same
  String (JR4), and JR5 that String's bkey is CK2's.
* `objprobe/` (the same jar): OB1 a String field "a" U+D800 "b" reads
  back "a?b"; OB2 a `char` field and OB3 a `char[]` field read back
  U+D800.
* `formats/` (libraries downloaded for this, versions in the outputs):
  PL1 to PL10 (cbor2 6.2.1, msgpack 1.2.4, protobuf 7.36.2, pymongo
  4.19.0), JSL1 to JSL11 (@msgpack/msgpack 3.1.3, bson 7.3.4, cbor-x
  1.6.9, protobufjs 8.8.1), GL1 to GL5 (fxamacker/cbor 2.10.0,
  google.golang.org/protobuf 1.36.12), JL1 to JL9 (protobuf-java 4.36.2,
  jackson-core 2.22.4, gson 2.15.0); the second table of section 2.

Not run: Rust, C#, Kotlin, wasmtime and PostgreSQL (no toolchain on
F53); for them the documentation or the source is cited. The cost of the
check was not measured.


## 6. Sources

Read on 2026-11-07; copies of those marked "copy" are in the bench
directory's `sources/`.

* [Unicode] The Unicode Standard, Version 18.0.0, chapter 3: D76
  (Unicode scalar value), D91 (UTF-16: "isolated UTF-16 code units in
  the range D800..DFFF are ill-formed"), D92 (UTF-8: "any UTF-8 byte
  sequence that would otherwise map to code points U+D800..U+DFFF is
  ill-formed"), 3.9.6 (U+FFFD Substitution of Maximal Subparts).
  https://www.unicode.org/versions/Unicode18.0.0/core-spec/chapter-3/
  (copy).
* [RFC 3629] UTF-8, section 3: "The definition of UTF-8 prohibits
  encoding character numbers between U+D800 and U+DFFF".
  https://www.rfc-editor.org/rfc/rfc3629.html
* [WTF-8] Simon Sapin, The WTF-8 encoding (2022-02-23), section 1
  (intended audience: "must not be used to represent text in a file
  format or for transmission over the Internet"), section 3 ("Surrogate
  pair byte sequences are ill-formed in WTF-8"), section 6.5
  (concatenation). https://wtf-8.codeberg.page/
* [RFC 8259] JSON, sections 7 and 8.2.
  https://www.rfc-editor.org/rfc/rfc8259.html
* [RFC 7493] I-JSON, section 2.1.
  https://www.rfc-editor.org/rfc/rfc7493.html
* [RFC 8949] CBOR, sections 1.2, 3.1 (major type 3) and 5.3.1.
  https://www.rfc-editor.org/rfc/rfc8949.html
* [proto3] Protocol Buffers, proto3 language guide, "Scalar Value
  Types". https://protobuf.dev/programming-guides/proto3/
* [protobuf features] Editions feature settings,
  `features.utf8_validation`. https://protobuf.dev/editions/features/
* [MessagePack] MessagePack specification, "Type system".
  https://github.com/msgpack/msgpack/blob/master/spec.md
* [BSON] BSON specification version 1.1, `string` and `cstring`.
  https://bsonspec.org/spec.html
* [SQLite] SQLite, "Invalid UTF Policy", sections 1 to 3.
  https://www.sqlite.org/invalidutf.html
* [PostgreSQL] PostgreSQL 18 documentation, section 8.14, JSON Types.
  https://www.postgresql.org/docs/current/datatype-json.html
* [PostgreSQL wchar.c] `pg_utf8_islegal` in `src/common/wchar.c`
  (master). https://github.com/postgres/postgres/blob/master/src/common/wchar.c
  (copy).
* [ECMA-262] ECMAScript, section 6.1.4 The String Type; 22.1.3.10
  `isWellFormed`, 22.1.3.31 `toWellFormed`. https://tc39.es/ecma262/
  (copy of the data types page).
* [Encoding] WHATWG Encoding Standard, 7.2 `TextDecoder`, 7.4
  `TextEncoder` (takes a `USVString`), 8.1.1 UTF-8 decoder.
  https://encoding.spec.whatwg.org/
* [.NET encoding] Introduction to character encoding in .NET, "The
  string and char types", "Well-formed encoding".
  https://learn.microsoft.com/en-us/dotnet/standard/base-types/character-encoding-introduction
* [.NET UTF8Encoding] dotnet/runtime, `UTF8Encoding.cs`,
  `SetDefaultFallbacks` (U+FFFD, or throw), main at 5ccf61b
  (2026-11-07). https://github.com/dotnet/runtime/blob/main/src/libraries/System.Private.CoreLib/src/System/Text/UTF8Encoding.cs
  (copy).
* [Kotlin] `encodeToByteArray`, kotlin.text.
  https://kotlinlang.org/api/core/kotlin-stdlib/kotlin.text/encode-to-byte-array.html
* [Rust String] `std::string::String`: "A UTF-8–encoded, growable
  string", the section "UTF-8", `from_utf16`, `from_utf16_lossy`,
  `from_utf8`, `from_utf8_lossy`.
  https://doc.rust-lang.org/std/string/struct.String.html
* [Rust OsString] `std::ffi::OsString`, the Windows and Unix
  representations, `into_string`, `to_string_lossy`.
  https://doc.rust-lang.org/std/ffi/struct.OsString.html
* [serde_json] `src/read.rs`, `parse_unicode_escape`, and `src/error.rs`,
  master at 8c535a2 (2026-10-16). https://github.com/serde-rs/json
  (copy).
* [Go spec] The Go Programming Language Specification, "String types",
  "Conversions to and from a string type", "For statements with range
  clause"; `encoding/json`. https://go.dev/ref/spec
* [Python] The Python Standard Library, `codecs`, "Error Handlers"
  (`surrogatepass`, `surrogateescape`); PEP 383.
  https://docs.python.org/3/library/codecs.html#error-handlers,
  https://peps.python.org/pep-0383/
* [CM Explainer] WebAssembly Component Model, `design/mvp/Explainer.md`,
  "Fundamental value types" (`char`: Unicode Scalar Values),
  "Specialized value types" (`string ↦ (list char)`).
  https://github.com/WebAssembly/component-model (copy).
* [CM Canonical ABI] `design/mvp/CanonicalABI.md`, "Loading",
  `load_string_from_range` (`except UnicodeError: trap()`) (copy).
* [jco] bytecodealliance/jco, `crates/js-component-bindgen/src/
  intrinsics/string.rs`, main at 7cddbbd (2026-11-07).
  https://github.com/bytecodealliance/jco (copy).
* [wasm-bindgen] The wasm-bindgen Guide, Supported Types, `str`.
  https://rustwasm.github.io/docs/wasm-bindgen/reference/types/str.html
* [JS String Builtins] WebAssembly/js-string-builtins,
  `proposals/js-string-builtins/Overview.md`, "JS String Builtin API",
  "Future extensions". https://github.com/WebAssembly/js-string-builtins
* [stringref] WebAssembly/stringref, `proposals/stringref/Overview.md`,
  "What's a string?", "Encodings and views".
  https://github.com/WebAssembly/stringref
* [Wasm proposals] WebAssembly/proposals: `finished-proposals.md` (JS
  String Builtins, spec version 3.0) and `README.md` (stringref in phase
  1). https://github.com/WebAssembly/proposals (copy of the README).
* [F1-007] Frans's design notes, read-only:
  `f1/a/007-bergdb-261012/bergdb/doc/log-old/2008-2011-log.txt`
  (2008-08-07, "Types"; 2009-11-01, "sorted according to Unicode.
  Stored as UTF-8") and `doc/2013/2013-key-encoding.txt` (the ikey to bkey
  conversion and its "UTF-8" section).


Log
---

2026-11-07. Registered by coord-1106 from 006-13's morning list, point 2,
at Frans's word (08:10), with the explanation given in the chat at 08:02.

2026-11-07. Studied across languages by agent s04 of coord-1107 (006-14),
at Frans's word (08:32): the options rewritten as rules for every
language, three added ((4) U+FFFD, (5) refuse with an opt-in, (6) a
separate type), the recommendation (1) with its reasons, and sections 1
to 6: Java, JavaScript, C#, Kotlin, Python, Rust, Swift, Go, C and
WebAssembly; JSON, CBOR, Protobuf, MessagePack, BSON, SQLite, PostgreSQL;
BergDB today, the C clone included; the consequences across languages;
the programs, run in `/Users/f/fl/bench/006-14/021-04/`; the sources. No
code changed. Status stays open: Frans decides.

2026-11-07. Taken by agent u04 of coord-1107 (006-14), after Frans's
decision (09:33): option (1).

2026-11-07. Done by agent u04 of coord-1107 (006-14), option (1) as Frans
decided (09:33):

* The object code: `DbString`'s constructor refuses a String with a lone
  surrogate (`PubKeys.hasLoneSurrogate`), and `DbObject`'s field (its
  `DbField`) a field name with one, with `DbString.LoneSurrogateException`,
  an `IllegalArgumentException`; `DbObject.toDbObject` and
  `DbValue.createDbArray` add each field's name and array index on the
  way out, so the message names the place: "The string at
  'inner.names[1]' has a lone surrogate ...". That covers every String
  path into an object: fields, `Object` fields, arrays at any depth, an
  array put as an object, `DbObject.Builder`. A string read from bytes is
  not checked again (a private constructor). Not covered: a `DbObject`
  made from bytes (`new DbObject(byte[])`), put as it is; 021-06.
* The test: `DbObjectTester.testLoneSurrogates` now expects the refusal
  at six places (a field, an array element, an `Object` field, a nested
  object's array, nested arrays, an array put as an object), from the
  Builder for a value and a field name, and a pair stored and a `char[]`
  with lone surrogates read back exactly. On `HEAD`'s code (cd9e2df) it
  fails: "AssertionError: no exception, 'names[1]'".
* The rule in the Javadoc: in full in the package doc of `bergdb.pub`,
  section "Strings" (what, for which strings, what is refused, why, that
  a reader may rely on it, `byte[]` and `char[]` for data that is not
  text, option 6); linked from the overview, `Connection` (class doc and
  `put`), `WBuilder.put` (both) and `RwEnvironment.put` (both), with their
  `@throws`. `DbObject`'s and `DbString`'s class docs (in `pubimp`, not in
  the Pub Javadoc) state it for objects.
* The format: the Core's `doc-files/key-encoding.md` ("Conversion ikey
  --> bkey") states it for every string of the stream. No other kept-up
  format description names how strings are stored: `stream-format.txt`
  and `docs/trace-format.md` do not; 012's format notes (012-02, section
  7; 012-03, section 6.4) are a finished item's, not updated; the object
  format's spec does not exist yet (020-01, F1, question 5), and 021-06
  carries the rule there. 020-01, section 4, still says that a lone
  surrogate in an object is stored as '?': an inventory read at
  `2b8ef00`, not updated.
* `releases/next.md`: a Pub API bullet (objects) and a Documentation
  bullet (the rule).
* The two questions became 021-05 (the Core's String puts, done the same
  day) and 021-06 (the read side, open).

`JAVADOC PUB OK`. `BEFORE COMMIT OK (121 s)` (2026-11-07, 09:54; 1266 unit
tests, 87 f-tests), on the tree with 021-04's and 021-05's changes.
