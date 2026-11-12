
About
=====

Author: Frans Lundberg, 2016-04-01.

For: my understanding. Possibly base for cooperation / publishing.

Scope: startup, startup algo proof, memory vs stream pointers, 
storing general data structures (graphs) append-only.

Anti-scope: cache eviction, cache details, space reclamation,
serialization details, BergDB implementation.

This document is about making large data structures persistent 
and storing them to disk. Focus is to prove that the startup 
algorithm works.

This document contains an example of an evolving database. 
Data structures: Mem, Dirty, Stream. 
Mem and Dirty are stored in memory, while Stream is the database 
stream stored to disk.

## pandoc ##

This document was generated with pandoc from a markdown (startup.md) 
file. style.css is included the HTML output when --self-contained is used.

    pandoc --startup.md -o startup.html
    pandoc --number-sections startup.md -o startup.html
    pandoc --number-sections startup.md -s -c style.css -o startup.html
    pandoc --number-sections --self-contained startup.md -s -c style.css -o startup.html
    pandoc --toc --number-sections --self-contained startup.md -s -c style.css -o startup.html

## Publish / cooperation notes ##

I would love to publish my work. Or at least talk to someone about it.

Title: *Storing persistent data structures*

Title: *Storing large persistent data structures*

Title: *Storing a large data structure append-only*

Title: *Making data structures persistant and storing them append-only*

Title: *Making data structures persistant and storing them*

Imaging being able to publish this :-). The conference ICDT 
http://icdt.tu-dortmund.de/ 
(ICDT: the International Conference on Database Theory) seems 
like a good alternative.

The [Making] paper is seminal for my work. 

**Tarjan**. Maybe contact Robert Tarjan about my work. Maybe write paper 
*Making Data Structures Persistant and Storing Them*.
https://en.wikipedia.org/wiki/Robert_Tarjan
He is still active at Princeton. Got Turing price :-)
See [https://en.wikipedia.org/wiki/Robert_Tarjan].

**DANIEL D. SLEATOR**. See [https://en.wikipedia.org/wiki/Daniel_Sleator].

**Driscoll**. ? Not found. **Neil Sarnak**, no website. Worked for IBM, UBS.



Intro
=====

Let us consider how to store a large, evolving data structure, D, 
on a computer. D is larger than the memory of the computer 
(volatile random-access memory) and must survive computer restarts.
Thus, we need to store D on disk. For performance reasons, we also
store part of D in memory.

In addition to storing the last state of D, a requirement is to store
all [Foot1] previous states of the data structure. In other words, we consider
the topic on how to create a database that supports *historic queries*,
not only *last-state queries*. The paper [Making] studies how, in general, 
to convert an ordinary *ephemeral data structure* to a *persistant data structure* 
that supports historic queries. This paper focuses on how, in general,
to convert a large [Foot2] ephemeral data structure to a partially persistant
data structure and how to store it to disk. We also require D to be stored
in to disk *append-only*. (Motivate the append-only requirement).
(say something about *partially* persistant).

This paper is a study of how to convert a large ephemeral data structure 
to a historic data structure and how to store it append-only.

Since "persistant" is ambigous in this context, the term 
*historic data structure* is used as a synonym for *partially persistent 
data structure* as defined in [Making].

A *data structure*, in this context, is a directed acyclic graph (DAG) 
of nodes and pointers. Each node has a set of data fields and a set of 
pointers to other nodes. One node is the *root node* [FootRoot]. 
All nodes are reachable from the root node through a path of length 
O(log(size(D)).

The data structure supports read and write operations. 
A read operation is performed by following pointers
from the root node to other nodes computing a result while doing so. 
A read operation does not change the data structure. A read 
operation never affects the result of other read operations.
D evolves by executing a sequence of transactions. A transaction describes
the atomic change of D from one state to the next.

**Foot1**: We will later look at how to store the last n states rather
then all previous states.

**Foot2**: Larger than memory.

**FootRoot**: This is not a limitation because...

**Ref Making**: Making Data Structures Persistant, 1989]



Technical
=========

(Defining D in detail, notation)

**D**. The ephemeral data structure. D(t) = the ephemeral data structure
at time t. size(D) = number of nodes of D.

**H**. The historic data structure. H(t) = the historic data structure at 
time t. It includes all previous states. So: H(t1) subof H(t2) if t2 > t1.
(We would need to define subof operation more precisely.)

Defining D:

* Directed acyclic graph.
* One root node.

Storing D:

* Nodes are stored in memory or in stream.
* Pointers are to to stream locations (stream pointer) or to memory locations
  (memory pointer). A stream pointer is stored in a memory node or a stream node.
  A memory pointer is stored in a memory node.
  

## Initial state ##

Root node only. Historic node R.

    Memory: R
    Stream: R
    Dirty: R

After that, H evolves through a sequence of transactions requested by 
the database user.

## Read operation ##

A read operation computes an *accessed set* consisting of accessed nodes. 
At the beginning of the operation the accessed set is empty. 
The operation consists of a sequence of *access steps*, each of which adds one
node to the accessed set. This node must either be the root node or a node
that is accessed through a pointer in a previously accessed node. 
The time taken by a read operation is defined to be the number of access 
steps performed.

## Write operation ##

A write operation consists of an intermixed sequence of access and 
*update steps*. The access steps compute a set of accessed nodes 
exactly as in an access operation. The update steps change the data structure.
An update step consists either of creating a new node, which is added to the
accessed set, or changing a single field in an accessed node.
The pointer of a field changed must indicate a node in the accessed set or be null.
The total time taken by a write operation is defined to be the total number 
of access and update steps; the update time is the number of update steps.

(some text stolen from [Making])

## Ephemeral node ##

A node has a set of fields. A field is a 3-tuple: name, data, pointer.
Name could be implicit (id = position index) or explicit. Human-readable or not.
Data can be any data (bytes). Pointer is null or not.

(note: we choose to not differentiate between data fields and pointer fields
like [Making] does, we will see if that is a good choice)

    Ephemeral node, A
    
    f1 
    f2: d2, p2
    f3: d3, p3
    
## Historic node ##

Our goal is to store H, not D, so we need to extend how nodes are stored.
An ephemeral node goes through a sequence of states as it gets modified
by write operations. An ephemeral node at a particular time has a corresponding
historic node that encodes the current state of the node and (typically) 
previous states too.

    Historic node, B
    
    t0: n1 -> p1
    t0: n2 -> p2
    t0: n3 -> p2
    
    t1: n1 -> p4
    
    t2: n2 -> p5
    t2: n3 -> p6
    
A historic node can become full. Further update steps would be done by
by creating a copy of B (B'). The predecessor would create a pointer to
B'. Note, B' only contains the *last state* of B. Historic queries with 
a lookup time less than the transaction time would still access node
B, not B'.

The details of how this is chieved is explained in [Making].
(It is a solved problem. Just summarize in this paper.)



Evolving D example
==================

D is the large ephemeral data structure that we want to:

1. store to disk,
2. partly cache in memory,
3. convert to an a partially persistent data structure to support historic queries.

H is the corresponding partially persistant data structure.


## Initial state, t0 ##

The initial state, after the implicit *primordial transaction*, t0.

    == Mem ==
    
    A
    t0: created
    
    == Dirty ==
    
    t0: A
    
    == Stream ==
    
    t0:
    * op: create A (the implicit primordial transaction)
    * dirty: A

After that, the database state evolves through a sequence of transactions
requested by the database user and transactions requested by the database
itself (internal transactions).


## Transaction t1 ##

Transaction adding two nodes forming a tree with three nodes.
Resulting ephemeral data structure (D):
    
    A
    |-> B 
    |-> C

Note that D is not stored explicitely. What is stored on the computer
is the *Mem*, and *Dirty* data structures in memory, and the *Stream*
data structure in the append-only database stream.

    == Mem ==
    
    A
    t0: created
    t1: k1 --> B
    t2: k2 --> C
    
    B
    t1: v = "valB"
    
    C
    t1: v = "valC"
    
    == Dirty ==
    
    t0: A
    t1: B, C
    
    == Stream ==
    
    t0:
    * op: create A (the implicit primordial transaction)
    * dirty: A
    
    t1:
    * op: create B with B.v = "valB"
    * op: create C with C.v = "valC"
    * dirty: B, C

The resulting data structure is a tree. It can be viewed as a key-value
database storing two entries: (k1, valB), (k2, valC).


## Transaction t2 ##

Transaction t2 adds two more nodes: D, E.
Node D replaces Node C.
Resulting ephemeral data structure:
    
    A
    |-> B 
    |-> D
    |-> E

Memory, Dirty, Stream:
    
    == Mem ==
    
    A
    t0: created
    t1: k1 --> B
    t1: k2 --> C
    t2: k2 --> D
    t2: k3 --> E
    
    B
    t1: v = "valB"
    
    C
    t1: v = "valC"
    
    D
    t2: v = "valD"
    
    E
    t2: v = "valE"
    
    == Dirty ==
    
    t0: A
    t1: B, C
    t2: D, E
    
    == Stream ==
    
    t0:
    * op: create A (the implicit primordial transaction)
    * dirty: A
    
    t1:
    * op: put (k1, valB)
    * op: put (k2, valC) 
    * dirty: B, C
    
    t2:
    * op: put (k2, valD)
    * op: put (k3, valE)
    * dirty: D, E
    
The resulting ephemeral data structure can be viewed as a key-value
database storing three entries: (k1, valB), (k2, valD), (k3, valE).
The resulting historic data structure also stores the (k2, valC) 
key-value entry as it was after Transaction t2. Nothing is overwritten.


## Transaction t3 ##

Transaction t3 adds Node F.
    
    A
    |-> B
    |-> D
    |-> E
    |-> F

Memory, Dirty, Stream:
    
    == Mem ==
    
    A
    t0: created
    t1: k1 --> B
    t1: k2 --> C
    t2: k2 --> D
    t2: k3 --> E
    t3: k4 --> F
    
    B
    t1: v = "valB"
    
    C
    t1: v = "valC"
    
    D
    t2: v = "valD"
    
    E
    t2: v = "valE"
    
    F
    t3: v = "valF"
    
    == Dirty ==
    
    t0: A
    t1: B, C
    t2: D, E
    t3: F
    
    == Stream ==
    
    t0:
    * op: create A (the implicit primordial transaction)
    * dirty: A
    
    t1:
    * op: put (k1, valB)
    * op: put (k2, valC) 
    * dirty: B, C
    
    t2:
    * op: put (k2, valD)
    * op: put (k3, valE)
    * dirty: D, E
    
    t3:
    * op: put (k4, valF)
    * dirty: F
    
To startup the database after t4, one must rerun transactions t0, .., t3 to 
recreate the in-memory data structures: Memory and Dirty.
This startup algorithm is naive. The *startup time* grows indefinitely
since all data that was ever written to Stream must be read before the
database can execute new operations to serve its users.

The transactions t0-t3 are *user transactions*. They describe the updates
to D in some exact and reproducible way. 
These *transaction descriptions* can be a set of key-value entries to 
be added to a database, for example. It can also be a description
of the function that takes D from D(t_i-1) to D(t_i). SQL or JavaScript
could be used to express the *transaction function*.

The remedy for an ever increasing Stream is to introduce *internal transactions*
that do not change the state of the database as visible to a database user, 
but they reduce the startup time since only the last part of Stream need to 
be read to startup the database.


## Transaction t4 (internal) ##

The internal transaction t4 increases the startup time from t0 to t2.

    == Mem ==
    
    No changes.
    
    == Dirty ==
    
    t2: D, E
    t3: F
    t4: A
    
    == Stream ==
    
    t0:
    * op: create A (the implicit primordial transaction)
    * dirty: A
    
    t1:
    * op: put (k1, valB)
    * op: put (k2, valC) 
    * dirty: B, C
    
    t2:
    * op: put (k2, valD)
    * op: put (k3, valE)
    * dirty: D, E
    
    t3:
    * op: put (k4, valF)
    * dirty: F
    
    t4 (internal):
    * store: A, B, C
    * dirty: A
    * start: t2
    
Transaction t4 increases the startup position from t0 to t2. 
It stores all nodes that got dirty during transactions t0, t1 
(transactions before t2). The beginning of Dirty is removed.
t4 also writes the index (or stream position) of the new 
startup transaction (t2) to the Stream representation of t4.

Now, we can startup the database to state t4 by reading only *the end* 
of Stream, from t2 till the end. The state before t2 (State t1) is 
recreated from nodes A, B, C stored in the stream.

t2 is created from A(t1), B(t1), C(t1). This is possible since nodes
know their history. After Start t1 is recreated, user transactions t2, t3
are *rerun* to recreate the last state of the database (State t4).

The startup algorithm:

* Read the last internal transaction in Stream (t4). 
  Find the startup transaction (t_start = t2).
  
* Read the end of the stream starting from t_start = t2.
  Store nodes in memory.

* Recreate Memory as it was before t2.

* Update Memory by rerunning user transactions t2, t3.

* Recreate Dirty from node ids stored in Stream.

Note! Transaction t4 makes Node A dirty. It stores nodes A, B, C to 
stream, but A is still dirty because is has at least one pointer to 
a dirty node; it has a pointer to F which is dirty.

A node that points to a dirty node is itself also dirty.
In t4, nodes A, B, C are first cleaned (dirty flag set to false).
Then each of those nodes are checked; is it still dirty?
If it has a dirty child it is still dirty.
In general, this is recursive, making a node stored to Stream 
in an internal transaction dirty could make another node in the transaction 
node set dirty.



Startup proof idea
==================

How can we prove that the startup algorithm works?

We want to prove that the database can be started from data in the
startup section of the stream.


Inductive proof idea
--------------------

The startup algorithm according to the example in this document obviously 
works for the primordial database state, B(0) = (Memory(0), Dirty(0), Stream(0)).
Let us prove the inductive step.

Assume that startup algo works for B(i-1), prove that it works for B(i).

We have two cases:

1. t(i) is a user transaction, and
2. t(i) is an internal transaction.

These are treated below. It turned out that inducation is not
needed to prove the case of internal transactions.


Inductive step for a user transaction
-------------------------------------

This is simple. Assume that startup algo works for 

    B(i-1) = (Mem(i-1), Dirty(i-1), Stream(i-1))
    
we want to prove that it works for

    B(i) = B(i-1) * tu
    
where tu = t(i) is a user transaction.

If Mem(i-1) can be recreated during startup (as assumed), we can also 
recreate Mem(i) during startup by executing transaction t(i) on Mem(i-1). 
That is:

    Mem(i) = Mem(i-1) * tu
    
The changes to Mem are fully described in the user transaction tu
and transactions are required to be deterministic, so we will always get
a the same result.

Likewise, if Dirty(i-1) can be recreated during startup (as assumed), we
can also recreate Dirty(i) when executing transaction tu.

    Dirty(i) = Dirty(i-1) * tu
    
The change to Dirty is deterministic and given by the transaction 
description tu and the in-memory state (Mem(i-1), Dirty(i-1)).

Stream(i) is obvious, it is there already. This is the input to the 
startup algorithm.

    Stream(i) = Stream(i-1) * tu
    
So, if the startup algo works for B(i-1), it also works for
B(i) = B(i-1) * tu where tu is a user transaction.


Inductive step for a user transaction (2)
-----------------------------------------

An alternative way to express this (intuitivly) is that running 
transaction tu on database state B(i-1) affects Mem(i-1) identically 
when this is done during the ordinary online phase of the database and
during startup.
The only difference is that no data is added to Stream when running tu 
during startup and the Dirty DS does not need to be changed.

The change to Mem(i-1) is identical.


Proof for an internal transaction
---------------------------------

We want to prove that the startup algorithm works for

    B(i) = B(i-1) * ti
    
where ti = t(i) is an arbitrary internal transaction.

Let 

    s(i) = the index of the startup transaction of B(i).
    
ti changes the startup transaction from t(s(i-1)) to t(s(i)).

Consider the essence of the startup algorithm for state B(i):

1. Recreate Mem(s(i-1)). That is: the state of Mem before transaction s(i).

2. Update Mem by running the user transactions in the *startup section*.
   That is, the user transactions in s(i), s(i)+1, ..., i.

3. Create Dirty(i) from node IDs stored in the transactions of the
   startup section.

Step 3 trivially works and thus not further discussed.
Step 2 works. This has been shown in the section that proves the 
that the startup algorithm works for a user transaction.

This leaves us with proving that Step 1 works.

Mem(i-1) can be recreated. The Clean Rule implies that all nodes in 
the stream are clean for t = s(i-1).
So for a lookup time t LT s(i-1), any lookup operation will succeed.

To restart:

1. Read all nodes in the startup section that was created before 
   transaction s(i) to memory [FootReadNodes1], [FootReadNodes2].

1. Find the root node. There should be exactly one instance of 
   the root node in the startup section.
   
1. Recreate each node's state as it was before transaction s(i) was run.
   This is possible since nodes are persistent.
   
1. Re-run the user transactions from s(i) till the end of the stream.
   While doing this, do not change Stream, nor Dirty.

1. Done. The database is now ready to execute read and write operations
   at the request of the database user.
   
The Dirty DS is idential to its state before the restart. 
The Stream DS is obviously identical to its state before the 
restart since it is not modified during startup.

The Mem DS is equivalent to the Mem DS before the restart 
if the cache state of nodes are not considered. 
The newly started Mem DS may not have as many nodes in memory as the 
Mem DS had before the restart. Node may or may not be stored in memory.
This is a caching issue and not treated in any detail in this text.


**FootReadNodes1**: In the general case, we only need to read the internal
transactions here. If internal transactions and user transactions 
(write ahead log) are separate, the startup time possibly be reduced.
For the BergDB, we do not need to read the value nodes because they
will never change and have no outbound pointers.

**FootReadNodes1**: Nodes created by transaction s(i) or later are not
of interest, we want to recreate that state before transaction s(i).


Dirty nodes and the Clean Rule
==============================

The Dirty data structure stores a collection of all dirty nodes and
information about when they got dirty.

Definition of dirty:

    A memory node *is dirty* iff it has never been stored or if it *has changed*
    since the last time it was stored.
    
Definition of *has-changed*:

    We say that a node, A, *has changed* after time t1, if a field has been added 
    to A after t1 or if A points to a node that has changed after t1.
    
Intuitively, a node, A, has changed after a field has been added to it.
However, here we will deal with the stream representation of A.
Consider a pointer from A to another node, C. If C is stored, 
the in-memory version of A will not need to be changed as long
as it still points to the same in-memory node B. The in-memory pointer
to B stays the same. However, the stream representation of A *does change*.
The pointer to B changes in the stream representation
of A since the latest version of B now has a new stream position and
the pointer to B should use this new stream position.

We will extend the above definition to define a node that *is dirty
at time t*.

Definition of *dirty at time t*:

    A memory node *is dirty at time t* iff it has never been stored 
    before t or if it *has changed* in a transaction before t and
    after the last time it was stored before t.
    
Definition of *clean*:

    A node is *clean* if it is not dirty.
    
Definition of *clean at time t*:

    A node is *clean at time t* if it is not dirty at time t.
    
The Clean Rule (important!):

    A node written to the stream in transaction i, must be clean at time st(i)-1.
    
st(i) is the startup time of transaction i. 

The purpose of the Dirty DS is to enforce this rule.

A node in Mem (a memory node) can *get dirty* because a user transaction 
or an internal transaction.

## Rules of dirtiness ##

Properties, laws, of dirty nodes.

Derived: 

    A node is dirty if any of its descendends is dirty.

Derived:

    All ancestors of a dirty node are dirty.

Derived:

    A node that is stored causes all its ancestors to become dirty
    if they are not already dirty.
        
Derived:

    A node is clean (not dirty) if 1. no field has been added to
    it after it was last stored, and 2. all its descendents are clean.
    
Becoming dirty:

    A node becomes dirty when:
    1. it is created,
    2. a field is added to it, 
    3. a node it points to becomes dirty, 
    4. a node it points to is written to stream, or
    5. after being written to stream it points to a dirty node.

    When a node becomes dirty, it is marked as dirty and added to 
    the Dirty DS.

Becoming clean:

    A node becomes clean if it is written to stream and after that
    has no pointer to a dirty node.

    When a node is written to stream in transaction i, it is guaranteed
    to be clean at startupTime(i-1). However, this does not necessarily mean
    that it is clean at the current time.

