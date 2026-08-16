#!/bin/sh
# Capture the compiler's externally visible type-dependent output.
#
# Two artifacts, both derived from the corpus:
#
#   lean.snap  the generated Lean for every `corpus/verifies`, `corpus/tests`,
#              and `corpus/test-fails` subject, which contains every mangled
#              declaration name, every emitted Lean type, and every obligation
#              statement;
#   diag.snap  the rendered diagnostic for every `corpus/must-fail` subject,
#              which contains every type name the compiler prints.
#
# A change to how types are represented that is meant to preserve behavior
# leaves both byte-identical. `Ty::name` is compositional, so a type spelled
# differently in the representation still prints the same string — which is
# what makes an empty diff evidence about the whole grammar rather than about
# the shapes some test happened to mention.
#
# Usage: type-snapshot.sh <sable-binary> <output-dir>
set -eu

binary=$1
outdir=$2
root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)

mkdir -p "$outdir"

: > "$outdir/lean.snap"
for dir in verifies tests test-fails; do
    for subject in "$root"/corpus/"$dir"/*.sable; do
        printf '===== %s\n' "${subject#"$root"/}" >> "$outdir/lean.snap"
        "$binary" check --emit-lean -M "$root/corpus/verifies" "$subject" \
            >> "$outdir/lean.snap" 2>&1 || true
    done
done

: > "$outdir/diag.snap"
for subject in "$root"/corpus/must-fail/*.sable; do
    printf '===== %s\n' "${subject#"$root"/}" >> "$outdir/diag.snap"
    "$binary" check -M "$root/corpus/must-fail/mods" -M "$root/corpus/verifies" \
        "$subject" >> "$outdir/diag.snap" 2>&1 || true
done

wc -l "$outdir/lean.snap" "$outdir/diag.snap"
