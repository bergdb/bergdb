#!/bin/sh
# Writes lean/contract/statements.pin (bergdb 030-15): the files a reader of the
# contract package must trust, each with its SHA-256, as `shasum -a 256` writes
# them, paths from the repository's root. gate.sh checks the pins; run this after a
# change of a pinned file, and commit the pin file with the change, so that a
# change of a statement shows in review.
#
# The files: those of the trusted closure of the main theorems (Statements.lean
# prints them: the theorems of Axioms.lean but the examples, and every definition
# their statements rest on, in lean/contract/ and in the old package lean/); the
# list of theorems and the closure's tool (Axioms.lean, Statements.lean); the
# checkers' main files, which turn a verdict into an exit status (ContractCheck.lean,
# BridgeCheck.lean); the gate (gate.sh); and the Lean version and the libraries
# (lean-toolchain, lakefile.toml and lake-manifest.json of the three packages:
# lean/, lean/contract/ and lean/contractcheck/, which builds the checkers from
# lean/contract/'s files without Mathlib, bergdb 028-24).
#
# Beside the closure, files that are no statement but whose change must show in
# review the same way (bergdb 030-28): the tree checker's writer
# lean/SIS/Tree/Pe.lean, a copy of the proved writer (Contract/PeWriter.lean) that
# the level scripts compare Java with; pecmp, which compares the two writers on
# Java's traces (lean/pecmp/: PeCmp.lean, check.sh and its package's files); and
# pins.sh, the check of these pins without a build. Pinning them changes no
# statement.
#
# Usage: lean/contract/pin.sh. Needs lake build in lean/contract/.
cd "$(dirname "$0")"
FILES=$(lake env lean Statements.lean 2>&1 | grep '^lean/')
[ -n "$FILES" ] || { echo "pin.sh: no files from Statements.lean"; lake env lean Statements.lean 2>&1 | head -5; exit 1; }
EXTRA="lean/contract/Axioms.lean lean/contract/Statements.lean lean/contract/ContractCheck.lean
lean/contract/BridgeCheck.lean lean/contract/gate.sh lean/contract/lean-toolchain
lean/contract/lakefile.toml lean/contract/lake-manifest.json lean/lean-toolchain
lean/lakefile.toml lean/lake-manifest.json lean/contractcheck/lean-toolchain
lean/contractcheck/lakefile.toml lean/contractcheck/lake-manifest.json
lean/SIS/Tree/Pe.lean lean/pecmp/PeCmp.lean lean/pecmp/check.sh lean/pecmp/lakefile.toml
lean/pecmp/lean-toolchain lean/pecmp/lake-manifest.json lean/contract/pins.sh"
cd ../..
{
    echo "$FILES"
    echo "$EXTRA" | tr ' ' '\n'
} | grep -v '^$' | sort -u | xargs shasum -a 256 > lean/contract/statements.pin
echo "pin.sh: $(wc -l < lean/contract/statements.pin | tr -d ' ') files pinned in lean/contract/statements.pin"
