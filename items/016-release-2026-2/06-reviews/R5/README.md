R5 review attachments
=====================

Base: abe7785. The five patches add regression tests only; R5-F5 also
registers its new tester in storage/Pack. No production fix is included.
Each patch applies to BASE. Applied together, they reproduce the six
changed Java files in the review clone exactly (checked with git apply).

On a clean checkout of BASE, apply the desired patches from its root with
`git apply /absolute/path/to/R5-Fn.diff`, then build once:

    cd java
    sh build.sh

R5-F1.txt through R5-F5.txt give single-test commands and the expected
assertion failures on BASE. R5-F6.txt through R5-F8.txt give the three
finding probes' commands and output; all run on BASE without a test patch.
Read Nano's FAILURE/SUCCESS line: its process exits 0 on an assertion failure. Every added test releases and closes its streams
or databases, including on assertion failure.

checks.txt records the 26 selected existing test methods that passed and
the main-only group/ring probe's commands and compact output. To compile
and run that probe from repo/java:

    mkdir -p ../../out/R5/classes
    javac --release 17 -cp build/bergdb.jar -d ../../out/R5/classes ../../out/R5/R5MainOnlyProbe.java
    java -ea -cp ../../out/R5/classes:build/bergdb.jar bergdb.core.R5MainOnlyProbe

Use one JVM at a time. The probe has finite latch/join waits; its ring
close can also wait for the configured timer, remaining under one minute.

R5CloseErrorProbe.java is the sixth finding's probe. Its program asserts
the BASE symptom and then cleans up; it is a reproducer, not a fixed-code
regression test. Compile/run it with the commands in R5-F6.txt. The
consumer's uncaught exception is captured by a handler so the output stays
small and the test can cleanly interrupt its otherwise stranded sync.

R5PendingCutProbe.java is the seventh finding's controlled cut/flush
interleaving. Its commands and compact output are in R5-F7.txt. It also
asserts the BASE symptom and releases and closes the buffer before exit.

R5ReadEofProbe.java is the eighth finding's exception-subtype check. Its
commands and output are in R5-F8.txt; it closes the buffer in finally.
