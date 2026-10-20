EDITS = [
("java/src/bergdb/common/Pair.java",
""" * Immutable 2-tuple implementation.
 * This class and Triplet forms a very simple tuple library for BergDB. 
 * If we need more, we could switch to http://www.javatuples.org/.
 * 
 * @see Triplet
 * @author Frans Lundberg""",
""" * Immutable 2-tuple implementation.
 * If we need more, we could switch to http://www.javatuples.org/.
 * 
 * @author Frans Lundberg"""),
("java/src/bergdb/core/Pack.java", """        Cache2.class,
""", ""),
("java/src/bergdb/dag/Pack.java", """        DagChecksum.class,
""", ""),
("java/src-dev/bergdb/test/Concurrency2.java",
""" * Simpler version of Concurrency.""",
""" * Simpler version of the Concurrency test of 2013 (removed in bergdb 005-10)."""),
("docs/level4-plan.md",
"""The old [Cache2.java](../java/src/bergdb/core/Cache2.java) implements""",
"""The old Cache2.java (removed in bergdb 005-10; `git show
0597329:java/src/bergdb/core/Cache2.java`) implements"""),
]
