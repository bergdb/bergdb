key-encoding.md
===============

Based on doc/2013-key-encoding.txt. Added to src-dev/bergdb/dev/doc-files, March 2016.

How to encode keys. Formats: ukey, ikey, bkey, skey.

Our basic requirements are:

* To be able to represent nearly any string. 
* To only have 0000 and '/' as special chars. Follows ext3 and ext4 filesystems.
* Sorting the bytes should sort the keys in alphabetical order according to 
  Unicode. Special sorting for dirs vs files and IKP (internal key prefix) is allowed.
* The encoding must integrate with the binary key index entries in IKP/i/.
  We must be able to iterate the index entries (possibly with special Core 
  tools).
* The encoding should work with the byte[] -> byte[] mapping exposed to the 
  Core layer.


Terms and definitions
---------------------

ukey
    User string key. String used as database key by the Pub Layer user.
ikey
    Internal string key. After conversion.
    Not visible to Pub user, but possible to use by internal code.
bkey
    Byte key. A byte array, unrestricted values, any values allowed, but not
    all bkeys has a corresponding ikey (or ukey).
    A bkey can be created directly by a Core user, or from an ikey.
skey
    Segmented key. The byte array (bkey) stored in a long[] array.


Want 1: internal key prefix, IKP
--------------------------------

We want a special directory prefix for internal data that is not visible to the
user of the database, but visible and accessible to internal code. 
We would like the same code to be used for accessing the IKP data as the 
ordinary data. Possibly a cast to a specific implementation / subclass can
achieve this followed by a call to a method that does not check the key the
same way.


Want 2: efficiently list files in a directory
---------------------------------------------

Consider the files:

    a/note1.txt
    a/note2.txt
    a/sub/s1.dat
    a/sub/s2.dat
          ...
    a/sub/s1000000.dat
    a/t1.txt
    a/t2.txt

To list the files in a/ not including subdirectories, we would iterate
the primary index forward from "a/" exclusive. We would need to go through 
all 1 million files in a/sub/ before we get to t1.txt and t2.txt. How to improve
this to enable us to list files in a directory without large subdirectories 
interfering with the process?


Want 3: efficiently list items in a directory
---------------------------------------------

Want 3 is a stronger requirement than Want 2. We want to be able to list both 
files and the names of the subdirectories (like "ls") without the need
to go through millions of subdirectory items.

This Want is significantly harder than Want 2, but is very useful if BergDB data
is to be exposed as a filesystem. Want 3 is not an immediate concern, by will
likely be addressed in the future.


Solution
========

Based on strings for KISS, easy debug and works better than bytes for current
code base. "ukey" = user string key used from the Pub Layer.
'/' have special meaning; the only char with special meaning.
A ukey is converted to an ikey first and then to bytes.

ukey validity rules:

    * Must start with /
    * Must not end with /
    * Two consecutive slashes (//) is not allowed in a ustring.

NOTE, a start / makes conversion simpler and makes more sense if root dir is
considered to be the empty string. Also it allows us more flexibility for the
future. For example, the option of enabling key replace (${transactionTime})
could be put in the ukey string before the first '/'.


### Conversion ukey --> ikey ###

How a ukey is converted to an ikey. Every ukey has a single mapping to
exactly one ikey (a pure function). Not every ikey has a corresponding 
ukey, however.

    /a/customer/c0.obj   -->  /da/dcustomer/-c0.obj
    /b.obj               -->  /-b.obj
    
Assume a valid ukey, the conversion to ikey is done by prepending 'd' 
to directory names ("customer") and "-" to filenames ("c0.obj", "b.obj").
The character following a / will always be d or - for all ikeys that were
created from a ukey.

The algorithm is simple, the last occurence of "/" is replaced with "/-"
and the other occurrences of "/", if any, is replaced with "/d".

Sort order (/ sorted first):  /, -, d.


### IKP ###

An ikey can be created directly by internal code. Then the char '#' can
also be used after a '/'. This functions like 'd', but is sorted first. It is
used for IKP, internal data prefix. The IKP ikey is:

    /#i/

Example internal data (ikey)

    /#i/di/-indexEntry1     -- index entry, binary data at the end.

    /#i/dii/-indexA.obj     -- index info for "indexA"

    /#i/dreclaim/-table.txt -- reclaim information, see core.Reclaim.


### Conversion ikey --> bkey ###

First convert ikey to UTF-8 bytes: well-formed UTF-8 (RFC 3629). Every
string in a BergDB stream, a key, a String value, a string in an object,
is a sequence of Unicode scalar values stored as well-formed UTF-8, in
every language; a writer refuses a string it cannot store so, and a reader
may rely on it (bergdb 021-04). In Java, a String with a lone surrogate (a
char of U+D800 to U+DFFF not part of a surrogate pair) is refused with
IllegalArgumentException, by the Pub API and by `Keys.toBytes` (bergdb
021-05); a writer in C or Go refuses bytes that are not well-formed UTF-8
(the C clone, bergdb 012, at release 2026.2, does not yet; bergdb 021-06).
Then for each byte
    if b == '/', res = 1
    else res = b + 2

0 is reserved (not used), 1 is for '/' and 2 is used for char \u0000.

The bytes 0xFE and 0xFF do not appear in valid UTF-8 bytes, so any valid
UTF-8 ikey can be converted this way.

Be careful not to use ikey-to-bkey conversion when the key is binary already.


### Conversion bkey --> ikey ###

For each byte b
    if b == 1, res = '/'
    else if b == 0 --> fail, bkey cannot be converted to an ikey
    else res = b - 2
Then convert res bytes to a String with UTF-8.

NOTE, there are bytes sequences that are not valid UTF-8 bytes.
An arbitrary bkey cannot, in general, be converted to an ikey.


### Implementation ###

Conversions can be made in core.Keys. public static methods work fine.
We could have classes too. The benefit is better typing, but it adds a little
bit of overhead. Typing to differentiate between ukey and ikey could be good 
however.

### Want 1 ###

Satisfied with the special IKP ikey. Not a ukey.

### Want 2 ###

With d/- prefixes for directories and files, directories are always sorted 
before files. So, to find all files in u:a/dir1/, we iterate from i:a/ddir/- 
exclusive with i:a/ddir/- as prefix.

### Want 3 ###

Want 3 is not handled now. We would need special "mkdir" functionality.
For example to be able to represent an empty directory. This is something to
be introduced later, if at all. However, the current approach supports inserting
dir keys with n prefix. Dirnames would be listed separately.
The n-prefix entries would be the directory information entries.
Not possible to read from Pub Layer (no ukey converts to those ikeys).

    /a/dir1/f1
    /a/dir1/sub/f2

    i:/da/ddir1/dsub/-f2
    i:/da/ddir1/nsub
    i:/da/ddir1/-f1
    i:/da/ndir1
    i:/na


--------------------------------------------------------------------------------

Facts
=====


UTF-8
-----

According to http://en.wikipedia.org/wiki/UTF-8#Invalid_code_points, 
the bytes 0xFE and 0xFF do not appear in valid UTF-8 bytes.
This is confirmed by the table in http://en.wikipedia.org/wiki/UTF-8#Description
and by RFC 3629. Actually, RFC 3629 removed 5- and 6-byte sequences. 

And The Unicode Standard, Version 6.0, says (D93, page 94): 
    As a consequence of the well-formedness conditions specified in Table 3-7, 
    the following byte values are disallowed in UTF-8: C0–C1, F5–FF.

Disallowed: F5 - FF.
Max value from 4-byte UTF-8 figure would be: 11110xxx, 11110111 = F7, 
but not all scalar values are allowed.

Conclusion:
    * It is safe to use at least byte values: F8, F9, FA, FB, FC, FD, FE, FF 
      for special stuff.
    * It is "especially safe" to use FE and FF - works even for UTF-8 with 5 
      and 6 bytes (which is not allowed by current standards).

Ext3/4
------

Internally in the filesystem, all bytes except for 0 (NUL) and (byte) '/' 
are allowed in a filename. This includes ASCII control characters.

ASCII
-----

Part of ASCII / Unicode table.

Hex     
00      NUL
08      BS - backspace
09      TAB - horizontal tab
0A      NL - new line '\n'
0D      CR - carriage return - '\r'
20      SPACE - ' '.
21      '!'
22      '"'
23      '#'
2E      '.'
2F      '/'
30      '0'
41      'A'
61      'a'
