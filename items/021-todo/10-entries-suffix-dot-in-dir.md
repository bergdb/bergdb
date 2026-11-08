021-10. Fix: a '.' in a directory's name makes no key there an object key
=========================================================================

Status: open. Kind: Fix. Frans: none.
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
