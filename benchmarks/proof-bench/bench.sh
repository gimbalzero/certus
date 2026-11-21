#!/usr/bin/env bash
# Reproduce the Lean vs Metamath benchmark. Needs: Lean 4.36 on PATH (lean, leanexport, nanoda_bin), cc, curl, python3.
set -euo pipefail
cd "$(dirname "$0")"
N=${N:-1000}

echo "== Lean: single file"; (cd lean && /usr/bin/time -p lean Sum.lean)

for style in auto explicit; do
  echo "== Lean: $N generated proofs ($style)"
  (cd lean && python3 ../scripts/gen_lean.py "$N" "$style" > "Gen_${style}_$N.lean" \
     && /usr/bin/time -p lean "Gen_${style}_$N.lean" > "prof_${style}_$N.txt" \
     && python3 ../scripts/profile_summary.py < "prof_${style}_$N.txt")
done

echo "== Kernel-only recheck with nanoda (Rust)"
mkdir -p lean/olean lean/export
for m in Empty "Gen_auto_$N" "Gen_explicit_$N"; do
  [ -f "lean/$m.lean" ] || echo "" > lean/Empty.lean
  (cd lean && lean -o "olean/$m.olean" "$m.lean" > /dev/null \
     && LEAN_PATH="$(dirname "$(dirname "$(command -v lean)")")/lib/lean:olean" leanexport "$m" > "export/$m.ndjson")
  cat > "lean/export/$m.json" <<J
{"export_file_path": "$m.ndjson", "permitted_axioms": ["propext","Classical.choice","Quot.sound","Lean.trustCompiler"],
 "unpermitted_axiom_hard_error": false, "nat_extension": true, "string_extension": true, "num_threads": 8, "print_success_message": true}
J
  echo "-- $m"; (cd lean/export && /usr/bin/time -p nanoda_bin "$m.json" | head -1)
done

echo "== Metamath"
if [ ! -x metamath/metamath ]; then
  mkdir -p metamath/src
  curl -sL https://github.com/metamath/metamath-exe/archive/refs/heads/master.tar.gz | tar -xzf - -C metamath/src --strip-components 1
  cc -O2 -o metamath/metamath metamath/src/src/*.c
fi
[ -f metamath/set.mm ] || curl -sL -o metamath/set.mm https://raw.githubusercontent.com/metamath/set.mm/develop/set.mm
(cd metamath && /usr/bin/time -p ./metamath "set scroll continuous" "read set.mm" "verify proof *" \
   "show trace_back arisum /count_steps" exit | grep -E "verified|steps")
