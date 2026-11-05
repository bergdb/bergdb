019-03. Decide: a get that always copies a byte[] value
=======================================================

Status: waiting (for Frans, "for another time"). Kind: Decide. Frans:
decision.
Created 2026-11-05 by Frans Lundberg.

What: since 015-47's option (c) (Frans, 2026-11-05, 12:00), a get of a
`byte[]` value returns the database's own array, zero-copy, and the
Javadoc says that it must not be changed; the put copies the caller's
array. Should the Pub API also offer a get that always returns a copy?

Why: Frans, 2026-11-05, 12:00, choosing the zero-copy gets: "For another
time, we could discuss supporting get operations that always copy the
byte arrays. That should be doable, right? Some getAndCopy() methods or
something. Or just some setting possibly. Not sure. But this is for
another time." It is doable: the copy is one `clone()` at the edge of the
Pub API, where 015-47's first fix (39cbbec) had it.

Frans: decision. The options:

* **(a) No new API.** A caller that wants its own array copies it:
  `byte[] b = c.get(key, byte[].class).clone();`. The Javadoc of the gets
  shows this line. Nothing to add or test (P11); the cost is paid only
  where a copy is wanted.
* **(b) A copying method**, such as `getCopy(key)` on `ReadInterface`
  (and so on `Connection` and `RwEnvironment`), returning a fresh array.
  One more method of each read interface, with its tests and Javadoc; it
  does what (a)'s line does.
* **(c) A setting on the connection**, such as
  `Connection.setCopyOnGet(true)`, so that every get of that connection
  copies. A program can then hand arrays to code it does not trust
  without changing each call; but it is a setting (P10), and a reader of
  a get cannot tell from the call whether its array may be changed.
* **(d) A read-only view**, such as `get(key, ByteBuffer.class)`
  returning `asReadOnlyBuffer()`: no copy and safe, but a new form of get,
  worth it only if a program needs large values without copies and
  without trust.

Recommended: (a), with the line in the Javadoc; (b) or (d) when a program
needs them.

Done when: Frans has chosen; the choice is made in `java/` with its
tests, or the entry is closed with (a).

First step: wait for Frans; nothing to investigate first.


Log
---

2026-11-05. Registered by session bergdb-e8, from Frans's words of 12:00
on 015-47.
