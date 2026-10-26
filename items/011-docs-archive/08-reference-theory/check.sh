#!/bin/sh
# Check this exploratory model without changing the shared SIS build directory.
set -eu

if [ "$#" -gt 1 ]; then
    printf '%s\n' 'Usage: sh lean/References/check.sh [--sis]' >&2
    exit 2
fi
case "${1:-}" in
    ''|--sis) ;;
    *) printf '%s\n' 'Usage: sh lean/References/check.sh [--sis]' >&2; exit 2 ;;
esac

reference_source_dir=$(CDPATH= cd "$(dirname "$0")" && pwd)
reference_check_dir=$(mktemp -d "${TMPDIR:-/tmp}/bergdb-references.XXXXXX")
trap 'rm -rf "$reference_check_dir"' EXIT HUP INT TERM

mkdir "$reference_check_dir/References"
cp "$reference_source_dir/Model.lean" "$reference_check_dir/References/Model.lean"
cp "$reference_source_dir/Examples.lean" "$reference_check_dir/References/Examples.lean"
cp "$reference_source_dir/../lean-toolchain" "$reference_check_dir/lean-toolchain"

cd "$reference_check_dir"
LEAN_PATH="$reference_check_dir${LEAN_PATH:+:$LEAN_PATH}" \
    lean -o References/Model.olean References/Model.lean
LEAN_PATH="$reference_check_dir${LEAN_PATH:+:$LEAN_PATH}" \
    lean References/Examples.lean

if [ "${1:-}" = --sis ]; then
    cp "$reference_source_dir/SISCase.lean" References/SISCase.lean
    cp "$reference_source_dir/../lakefile.toml" lakefile.toml
    cp "$reference_source_dir/../SIS.lean" SIS.lean
    cp -R "$reference_source_dir/../SIS" SIS
    lake build
    lake env lean References/SISCase.lean
fi
