021-10. Fix: a '.' in a directory's name makes no key there an object key
=========================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-08 by Frans Lundberg.

What: `Entries.suffix` takes the last '.' of the whole key, not of its
last part. In a directory with a '.' in its name, such as "/v1.2/", every
key gets a suffix ("2/k"), so no key there is an object key, and a put of
an object there is refused as "Bad key". Found by the agent of 020-10's
step I0 (coord-1108's night of 2026-11-08), from the code; not probed.

Why: a directory's name is the user's choice; an object key's rule must
look at the key's own name only (020-01, F1, N4: the kind of a value).

Done when: the suffix is taken from the key's last part only, with tests
of a '.' in a directory and in the name; 020-07 and 020-09 agree with it;
`BEFORE COMMIT OK`; a line in `releases/next.md`. With 020-08's steps
(the objects agent owns `Entries` tonight).

2026-11-09. Done with 020-08's step 3, by the objects' agent of
coord-1108's night (006-15).

* `Entries.suffix` takes the suffix of the key's last part, after its
  last '/': a '.' in a directory's name is no suffix, so "/v1.2/k" is an
  object key; a part that starts with its only '.' has no suffix, as
  before. Its callers (`isObjectKey`, with ukeys and ikeys) are
  unchanged.
* Tests: `Entries.testSuffixOfTheLastPart` ("/v1.2/k", "/v1.2/k.txt",
  "/a.b/c.d/k.obj", "/a.b/", as ukeys and ikeys); the existing suffix
  tests unchanged.
* 020-07 and 020-09 say nothing of suffixes (020-07, section 2.1: which
  keys hold objects is outside the format), so they agree.
* `releases/next.md`: left to the coordinator.

`BEFORE COMMIT OK`, with 020-08's step 3.
