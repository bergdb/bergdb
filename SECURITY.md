Security
========

How to report a vulnerability
-----------------------------

Do not open a public issue. Report it privately, in one of two ways:

* On GitHub: the repository's **Security** tab, **Report a
  vulnerability**.
* By e-mail to SECURITY-ADDRESS (TO CHECK, Frans: the address).

Say which release or commit, which JDK and which operating system, what
an attacker can do, and how to reproduce it. A short program helps most.

BergDB is maintained by one person. You get an answer as soon as Frans
can give one, normally within a week (TO CHECK, Frans: the time). Please
give him time to fix the vulnerability before you publish it; he will
say when a fix is out and, if you wish, name you in the release notes.


Supported versions
------------------

BergDB is a preview. Fixes go into the `main` branch and the next
release; earlier releases get no fixes.


What BergDB protects, and what it does not
------------------------------------------

BergDB is a library that runs inside the application's own process. It
trusts the application that calls it, and it trusts its storage: the
stream's files must not be writable by an attacker. Its checks of damaged
bytes in those files are a best effort. It has no encryption, no users
and no access control.

TO CHECK (Frans): whether a crash or a hang on a crafted or damaged
stream file counts as a vulnerability, or as an ordinary bug to report in
an issue.
