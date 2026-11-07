Notes for the next release
==========================

What the release notes of the next release after 2026.3 must say, collected
here as the changes are made, so that the release does not have to find them
again. The release folds them into its `releases/VERSION/readme.md`, as
[2026.3](2026.3/readme.md) has them under its changes, and
empties this file. A change of the stream's bytes, within the format,
names the StreamDigest configurations whose digests changed and the entry
that keeps its digests before and after (bergdb 018-01, section 2).

Emptied at release 2026.3 (2026-11-07), whose notes hold what was there.


### Pub API

* **`Time.utc` and `Time.resolve` refuse a null with
  `IllegalArgumentException`** (bergdb 021-01; 2026-11-07). `Time.utc(null)`
  and `Time.resolve(zone, null)` threw a `NullPointerException`, and
  `Time.resolve(zone, null, s)` (a null current time) too; each now throws
  `IllegalArgumentException`, as `resolve(zone, now, null)` and a null zone
  did.
* **A string with a lone surrogate inside an object is refused** (bergdb
  021-04; Frans, 2026-11-07, option 1) with `IllegalArgumentException` at
  the put, before anything is written, as keys (015-49) and String values
  (019-44) are: it was stored with `?` in its place, silently, and the
  object read back held other characters. It covers every string of an
  object: a field's value, an array's element, at any depth, and a field's
  name; the message names the field and an array element's index
  (`inner.names[3]`). `DbObject.toDbObject`, `DbObject.Builder` and
  `DbString` refuse it. A `char[]` field keeps any chars and reads back
  exactly; a `byte[]` keeps any bytes. The stream is unchanged: Java has
  only ever written well-formed UTF-8, and old `?`s read as before.
* **A stored value that is not a well-formed object is refused at a get
  with `ObjectCreationException`** (bergdb 021-07; 2026-11-07), from the
  object reader's `BadFormatException`, inside `rw()` and outside, and the
  database goes on; an index update that reads such a previous value
  throws `DataFormatException`. A nested object of size −1, which no
  writer writes, gave an `AssertionError` (with `-ea`), which failed the
  database inside `rw()`; a bad length, a bad field type byte or bytes
  that end inside a field gave a `NegativeArraySizeException`, an
  `IllegalArgumentException`, an `IndexOutOfBoundsException` or, for a
  length near 2^31, an `OutOfMemoryError`; and `Z` after an array's
  element ended the array silently. `DbObject.Builder`'s add methods
  refuse a null name or value with `IllegalArgumentException`:
  `addString` stored a null string, the others gave an `AssertionError`
  or a `NullPointerException`. Well-formed objects are read and written
  as before; the stream is unchanged.


### Core API

* **The Core's String puts refuse a lone surrogate** (bergdb 021-05;
  2026-11-07) with `IllegalArgumentException`, as the Pub API does:
  `Trans.Builder.put(String, String)`, in its key and its value, and
  `Keys.toBytes(String)`, and so every Core call that takes a String key.
  They wrote `?` in its place, so that two keys were one. The check scans
  a key's chars only when its UTF-8 bytes hold a `?`.


### Documentation

* **BergDB's rule for strings is stated once, in the Pub API's Javadoc**
  (bergdb 021-04; 2026-11-07): every string BergDB stores, a key, a String
  value, each string in an object and an index name, is a sequence of
  Unicode scalar values stored as well-formed UTF-8 (RFC 3629), in every
  language; a writer refuses a string it cannot store so (in Java, a
  String with a lone surrogate), and a reader may rely on it. The package
  `bergdb.pub`, section "Strings", holds it in full, with why and what to
  do with data that is not text (a `byte[]`, or a `char[]` in an object);
  the overview, `Connection`, `WBuilder.put` and `RwEnvironment.put` link
  to it, and the Core's `key-encoding.md` states it for keys.
* **The Pub API's Javadoc says what is, not how it was** (bergdb 021-01;
  2026-11-07). The sentences on how a method or an exception behaved before
  a change, and their dates, are gone from `Database`, `DatabaseBuilder`,
  `CryptoKey`, `DbException`, `DbFailedException`, `DatabaseMissingException`,
  `DatabaseNotCreatedException` and `SyncLevel`; the release notes keep the
  history. `DataFormatException` says that it belongs to the object code
  and the user indexes, experimental in 2026.3 (bergdb 018-01, D6), and
  where it is thrown. `Time.utc` and both `Time.resolve` document
  `BadFormatException` for a bad time string and `IllegalArgumentException`
  for a null argument.
