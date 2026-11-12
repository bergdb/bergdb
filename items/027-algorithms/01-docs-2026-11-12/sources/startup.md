
About
=====

About this text.

Author: Frans Lundberg, 2016-05-05.

For: my understanding, generic algos, base for publication?

Scope: algorithms with proof, theoretical and general

Compared to startup-1604.md, this text is more general, no examples, more
theoretical. Closer to a real proof for the general case.

The HTML output can be generated with pandoc:

    pandoc --toc --number-sections --self-contained startup.md -s -c style.css -o startup.html
    
    
    
Frans's notes
=============


## Notation ##

Functional, object-oriented, notation. Good for software and little need 
for advanced typesetting. Just about everything of DB could be described 
as functions. Data structures have capital letters, function names use
lower-case-first camel-case.


## Compact summary ##

    G = ephemeral data structure (abstract)
    P = persistent version of G (memory + disk)
    D = collection of dirty nodes (memory)
    S = database stream (disk)
    DB = <P, D, S>
    DB(i) = DB(i-1).exe(T(i))
    
    User transaction
    P(i) = P(i-1).exe(T(i))
    D(i) = D(i-1).add(gd(i))
    S(i) = S(i-1).appendU(T(i), gd(i).ids())
    
    Internal transaction
    P(i) = P(i-1)
    D(i) = D(i-1).take(gdr(s(i-1)+1, s(i))).add(gd(i))
    S(i) = S(i-1).appendI(gdr(s(i-1)+1, s(i)), gd(i).ids(), s(i))

    gd(i)       -- the nodes that got dirty during transaction i.
    gd(i).ids() -- IDs of nodes in gd(i)
    gdr(j, k)   -- the nodes that got dirty during transactions j, j+1, ... k.


## Thoughts ##

160405: Consider "Clean Rule". It is definition (property enforced), or something
derived?

160405: Idea of describing database with a focus on data structures 
(P, Dirty, Stream) and functions. Examples: execute, read, take(Dirty), 
add(Dirty), ... Or even object-oriented: Stream.append(T(i)).
Dirty.takeBetween(s(i-1)+1, s(i)).



Introduction
============

Let us study how to store a large evolving data structure, G, 
on a computer; or equivalently *how to create a database*, DB.

We have the following requirements:

1. DB must handle the case when G is much larger than the memory of the computer.

2. DB must support *historic queries*.

3. DB must store its state purely append-only to *the database stream*, S.

4. The startup time of DB must be O(1), or at least not greater than 
   O(log(G.size())).

The paper [Making] studies how, in general, to convert an ordinary 
*ephemeral data structure* to a *persistant data structure* 
that supports historic queries. This text focuses on how, in general,
to store such a persistent data structure on disk. The scope of the study
is limited to *partially persistent* data structures, that is, data structures
that has one single version evolving with time. Branches are not supported.

To limit the scope of this text, we do not consider read caching in 
any detail.

Also, storing a partial history (last X days) is not covered; the database 
stream grows forever and all previous states are available for historic 
queries. A real implementation will also consider a limited retention time
of historic states.


Database
========

The proposed database, DB, is a tuple of three elements:

    DB = <P, D, S>
    
*P* is the persistent version of G. P is a directed acylic graph 
of nodes and pointers. P has a single root node. All other nodes can 
be reached by following pointers (graph edges) from the root node.
Note that, when we speak about a *node* in P, we mean a node in the 
persistent data structure. Each such node is itself persistent; it remembers 
its history.

Definitions:

    G.size() = number of nodes of G
    P.size() = number of nodes of P
    
The longest path from the root node to any other node in G is assumed to 
be within O(log(G.size()). A typical example of G is a rooted tree,
or, in particular, a B-tree.

The database receives requests from the database user to perform read 
and write operations on it. A read operation does not change the state of DB, 
but returns a result to the database user.

A write operation is *a transaction*. The database evolves from one state
to the next by executing a sequence of transactions:

    T(0), T(1), ..., T(i)

that results in database states:

    DB(0), DB(1), ..., DB(i)

respectively. T(0) is a special implicit transaction that creates the 
initial state of the database, DB(0). After T(0), transactions are 
executed to evolve the database state.

There are two types of transactions: *user transactions* initiated by the
database user, and *internal transactions* initiated by the database itself.
When a transaction is run, it can cause nodes to become *dirty*.
When a node becomes dirty, it is added to *D* -- an in-memory 
collection of all dirty nodes.

The data stream, S, is the long-term, non-volatile storage
of the database. Data is written to S in a purely append-only fashion. 
Once data has been appended to the stream, it is never modified.


Transactions
============

When a transaction is run, it changes the state of DB.

A user transaction is a description of how the externally visible 
database state should change. It is a request for a change. 
The transaction specification (the *trans spec*) can, for example, be in 
the form of a set of key-value elements, some SQL code, or some JavaScript code.
The exact form of a user transaction specification is not important for the 
algoritms in this paper.

A trans spec for T(i) describes how G should change from G(i) to G(i+1). 
A trans spec must be deterministic; running a transaction based on 
its spec must always yield the same result.


Algo: user transaction
----------------------

This algorithm describes how to execute an arbitrary user transaction, T(i), 
to change the database state from DB(i-1) to DB(i).

    * Read the trans spec of T(i) from the database user.

    * Update P according to the trans spec. We write:
    
        P(i) = P(i-1).exe(T(i))
      
    * While doing this, record the nodes that *got dirty* during T(i)
      and add this information to Dirty. We write:
      
        D(i) = D(i-1).add(gd(i))
      
    * Append T(i) to Stream. We write:
    
        S(i) = S(i-1).appendU(T(i), gd(i).ids())
        
      The second argument to the appendU function is a set of node IDs. 
      The whole nodes of gd(i) are not stored, just their IDs.
      
T(i) is stored to S in such detail that the execution of it
can be performed again. This is required by the startup algorithm.

The definition of a *dirty node* and how a node gets dirty is crucial 
and will be discussed in another section of this document.


Algo: internal transaction
--------------------------

This algorithm describes how to run an arbitrary internal transaction, T(i),
to change the database state from DB(i-1) to DB(i). An internal transaction 
does not modify the external database state as visible to a database user.
Instead an internal transaction stores a set of nodes to S to reduce the 
part of S that needs to be read to start the database.

Let s(i) denote the state index of the *startup state* of DB(i).
The *startup state* is a state of P that must be recreated during 
database startup. This is P(s(i)).

The *startup section* of S at time i consists of the transactions
with the following indexes: s(i), s(i)+1, ..., i.

The purpose of the internal transaction T(i) is to increase the startup 
state index, s, to reduce the size of the startup section and thus 
reduce the time it takes to start the database.
This is done to fullfill Requirement 4.

Algorithm:

    * Decide to increase the startup state index from s(i-1) to s(i).
    
    * From D, retrieve and remove the set of nodes that *got dirty* 
      during transactions s(i-1)+1, s(i-1)+2, ..., s(i).
      We write
      
        oldDirtyNodes = D(i-1).take(gdr(s(i-1)+1, s(i)))
        
    * The nodes of oldDirtyNodes are made *provisionally clean*
      and are stored to stream. Each node of oldDirtyNodes may become
      dirty again (the gd(i) nodes) and thus readded to D.
      A provisionally clean node becomes dirty again iff it has a 
      dirty child (recursively applied).
      
      We summarize the effect of T(i):
      
        P(i) = P(i-1)
        D(i) = D(i-1).take(gdr(s(i-1)+1, s(i))).add(gd(i))
        S(i) = S(i-1).appendI(gdr(s(i-1)+1, s(i)), gd(i).ids(), s(i))       

How s(i) is chosen in the first step will not be discussed in detail.
Typically this is a setting of the database. For example, the 
database may allow a startup section of S that is around 20 MB long.

____________________

**Note**: Consider a particular oldDirtyNode, B. When B is stored in 
internal transaction T, its stream position changes and its ancestors 
all *become dirty*! How to handle this?

Answer: This *never happens*. No ancestor of B will become dirty
during T.

Proof: Consider an arbitrary current ancestor, A, of B. When B got dirty, 
we know that either A was dirty already or got dirty in the same transaction.
This is true since any current ancestor of a dirty node is itself dirty. 
If B got dirty in T(i), A must be dirty at state i, since B is a 
descendent of A.

If A and B got dirty in the same transaction, T(i), they will be written to 
stream in the same internal transaction, T(j). T(j) is the internal 
transaction that increases s (the startup state index) from an 
index LT s(i) to an index GTE s(i). Since A and B are written to stream 
in the same transaction, A does not get dirty when B is written to stream.

Thus, we just need to consider descendents of B to know whether B 
should be readded to D or not. Good!

____________________


Startup
=======

The startup algorithm and proof that is works.


Algo: startup
-------------

The startup algorithm, starting the database. Assume the last transaction
in S is T(i). The purpose of the startup algo is thus to recreate
DB(i) from S(i). That is, we want to recreate P(i) and D(i) from S(i).

This is the startup algorithm:

    * Read the last internal transaction of S.
      Read the startup time from it, s(i).
      
    * Read the transactions of the startup section of the stream;
      transactions s(i), s(i)+1, ..., i-1, i.

    * Recreate P as it was at time s(i). Find root node at time s(i)
      and recreate the state of each P node at that time.

    * Update P by rerunning all user transactions in:
      s(i)+1, s(i)+2, ..., i. While executing those transactions, 
      populate D based on the node indexes (gd(i).ids()) stored in S.
      
      So, for j = s(i)+1, s(i)+2, ..., i, we have:
      
        P(j) = P(j-1).exe(T(i))
        D(j) = D(j-1).add(gd(i))
        S(j) = S(i)
        
        where
        
        P(s(i)) has been recreated in the previous step.
        D(s(i)) is the empty set

No change is made to S during startup.


Startup proof
=============


Inductive proof idea
--------------------

The startup algorithm according the algorithms in this document obviously 
works for the primordial database state, DB(0) = (P(0), Dirty(0), Stream(0)).
Let us prove the inductive step.

Assume that startup algorithm works for DB(i-1), prove that it works for 
DB(i) = DB(i-1) * T(i).

We have two cases:

1. T(i) is a user transaction, and
2. T(i) is an internal transaction.

These are treated separately.


Inductive step for a user transaction
-------------------------------------

This is the simple case. Assume that startup algorithm works for DB(i-1).
We want to prove that it works for

    DB(i) = DB(i-1).exe(T(i))
    
where T(i) is a user transaction.

If P(i-1) can be recreated during startup (as assumed), we can also 
recreate P(i) during startup by running T(i) on P(i-1). 
That is:

    P(i) = P(i-1).exe(T(i))
    
The changes to P are fully described in the trans spec of T(i) and transactions
must be deterministic, so we will always get the same result.

Likewise, if D(i-1) can be recreated during startup (as assumed), we
can also recreate D(i) when executing running T(i). We write:

    D(i) = D(i-1).add(gd(i))
    
This is possible since gd(i).ids() is stored in the stream with user 
transaction T(i).
    
So, if the startup algo works for DB(i-1), it also works for DB(i)
when T(i) is a user transaction.


Inductive step for an internal transaction
------------------------------------------

Assume: Every current node in S(i-1) is clean for t = s(i-1).
Prove:  Every current node in S(i) is clean for t = s(i).

Edit 160416:
  What we really say is that the *last* version of every node
  in S is clean for state s(i-1).
  Maybe we should define "reconcilable" for state s(i-1) or
  something. Pointer reconciliation is required.

When that is proved, it follows that the whole startup works.

Let T(i) be an internal transaction that increases startup index from 
s(i-1) to s(i).

From D, we known what nodes that got dirty during transactions
s(i-1)+1, s(i-1)+2, ..., s(i). Those dirty nodes are stored in 
transaction T(i).

Since every node in S(i-1) is clean for state s(i-1) (as assumed) 
and we store all nodes that got dirty in transactions 
s(i-1)+1, s(i-1)+2, ..., s(i) in transaction T(i), we know that all 
current nodes in S(i) are clean for state s(i).

Note the Clean Rule: A node written to stream in transaction i, 
must be clean for state s(i).

If all nodes are clean for state s(i), we can recreate the startup 
state, P(s(i)), and rerun user transactions in s(i)+1, s(i)+2, ..., i-1, i
to recreate the state P(i).

The IDs of the got-dirty nodes are stored in the transactions
of the startup section. Therefore, we can recreate D(i) during startup.

S(i) does not need any changes, it is there when we start.



Dirty nodes and the Clean Rule
==============================

The D data structure is a collection of all dirty nodes and
information about in which transaction they got dirty.

Definition of dirty:

    A node *is dirty* iff it has never been stored or if it was last
    stored in T(i) and *has changed* in a transaction, T(j), 
    for which j > i.
    
Definition of *has-changed*:

    A node *has changed* in transaction T if a field was added to the node 
    or to any of its descendents during the execution of T.
    
Intuitively, a node, A, has changed after a field has been added to it.
However, here we will consider the stream representation of A.
Consider a pointer from A to another node, B. If B is stored, 
the in-memory version of A will not need to be changed as long
as it still points to the same in-memory representation of B. 
The in-memory pointer to B stays the same. However, the stream 
representation of A *does change*.
The pointer to B changes in the stream representation
of A since the latest version of B now has a new stream position and
the pointer to B should use this new stream position.

Let us define a node that is dirty for a specific database state.

    A node *is dirty for database state i* iff it was never stored in or before
    T(i) or it was last stored in T(j) where j < i and it has changed
    in a transaction, T(k), where j < k <= i.
    
Definition of *clean*:

    A node is *clean* if it is not dirty.
    
Definition of *clean at time t*:

    A node is *clean at time t* if it is not dirty at time t.
    
The Clean Rule (important!):

    A node written to the stream in transaction i, must be clean at time s(i).
    
s(i) is the startup time index, that is, the index to the first transaction
of the current startup section.

The purpose of D is to enforce this rule.

A node can *get dirty* due to a user transaction or an internal transaction.


## Rules of dirtiness ##

Properties, laws, of dirty nodes.

Derived: 

    A node is dirty if any of its descendends is dirty.

Derived:

    All current ancestors of a dirty node are dirty.

Derived:

    A node that is stored causes all its ancestors to become dirty
    if they are not already dirty.
        
Derived:

    A node is clean (not dirty) if 1. no field has been added to
    it after it was last stored, and 2. all its descendents are clean.
    
Becoming dirty:

    A node *becomes dirty* in a user transaction when:
    1. it is created,
    2. it is not dirty and a field is added to it, 
    3. it is not dirty and node it points to becomes dirty, 
    
    A node *becomes dirty* in an internal transaction, T, when:
    after being written to stream, it has a dirty descendent
    not written to stream in the same transaction.

    When a node becomes dirty, it is marked as dirty and added to D.

Becoming clean:

    A node *becomes clean* for state s(i) when it is stored
    in internal transation T(i). If the node, after being stored, has any
    dirty descendent, it *got dirty* during T(i) and is readded to D
    (with a new got-dirty transaction index).
    

