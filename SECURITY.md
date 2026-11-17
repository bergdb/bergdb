Security
========

How to report a vulnerability
-----------------------------

Do not open a public issue. Report it privately on GitHub: the
repository's **Security** tab, **Report a vulnerability**.

Say which release or commit, which JDK and which operating system, what
an attacker can do, and how to reproduce it. A short program helps most.

BergDB is maintained by one person. You get an answer as soon as Frans
can give one, normally within a week. Please
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

A crash or a hang on a crafted or damaged stream file, or on other
input, is an ordinary bug: report it in a public issue. A vulnerability
is a file or an input that makes BergDB do more than crash or hang: for
example read or write outside its stream, or run code. Report that
privately, as above.
