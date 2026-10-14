# Exploratory reference model

The theory proposal is [reference-theory.md](../../docs/reference-theory.md).
This model is separate from the existing proved SIS algorithm and is not
part of the default `lake build` target.

From the repository root:

```sh
sh lean/References/check.sh
```

To also rebuild the existing SIS library in isolation and check the
historical-reference trace under its current algorithm:

```sh
sh lean/References/check.sh --sis
```

The script uses `lean/lean-toolchain`, copies the two source files to a
temporary directory, compiles the model, checks the executable examples and
prints selected theorem axiom dependencies. It does not change the shared
SIS build directory or add dependencies. The installed pinned toolchain
must be available.

`--sis` also checks [SISCase.lean](SISCase.lean), whose finite trace passes
the existing executable assumption, recovery and restart checks. It keeps
one current parent per node yet requires a newer address for a dead
historical edge after that child's write has left the recent suffix.
This is a trace in the abstract SIS model, not a Java Dag reproduction.
The file also constructs one record retaining the complete older anchor
and checks recovery from that stream; it does not implement or prove a
general alternative writer.

Read [Model.lean](Model.lean) for the trusted definitions and statements;
read [Examples.lean](Examples.lean) for the constructed cases and negative
controls. The model proves cache/cut agreement for exactly backed immutable
images and retained concrete paths. It does not prove dirty writer loading,
reclaim scheduling, availability of every query, restart, Java publication,
resource bounds or production Level 4 correctness. The theory document
explains these premises and the next refinement obligations.
