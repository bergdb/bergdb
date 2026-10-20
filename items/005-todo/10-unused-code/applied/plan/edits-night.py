EDITS = [
("README.md",
"""    java/stress/level4.sh          # eviction             (about 16 minutes; quick: 4)
    cd lean && lake build          # checks all proofs

Each level script prints `LEVEL n OK` when it passes. All four must pass
before a change to the Java code is committed.""",
"""    java/stress/level4.sh          # eviction             (about 16 minutes; quick: 4)
    java/stress/night.sh           # the night tests      (about 4.5 minutes)
    cd lean && lake build          # checks all proofs

Each level script prints `LEVEL n OK` when it passes. All four must pass
before a change to the Java code is committed. `night.sh` runs the
long-running tests of 2013 to 2015 that no level script runs and prints
`NIGHT OK`; it is not a gate."""),
("README.md",
"""`NIGHT OK`; it is not a gate. Set `JAVAC` and `JAR` if the
JDK tools are not on the path.""",
"""`NIGHT OK`; it is not a gate. Set `JAVAC` and `JAR` if the JDK tools are
not on the path."""),
]
