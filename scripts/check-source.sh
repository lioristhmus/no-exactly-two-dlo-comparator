#!/usr/bin/env bash
set -euo pipefail

script_dir="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
project_dir="$(CDPATH= cd -- "$script_dir/.." && pwd -P)"
cd "$project_dir"

if [[ "$(grep -c '^import ' Challenge.lean)" -ne 1 ]] ||
    ! grep -qx 'import Mathlib' Challenge.lean; then
  echo "Challenge.lean must import exactly Mathlib" >&2
  exit 1
fi
if [[ "$(grep -c '^import ' Solution.lean)" -ne 1 ]] ||
    ! grep -qx 'import NoExactlyTwoDlo.FO.Main2' Solution.lean; then
  echo "Solution.lean must import exactly the pinned exact-two endpoint module" >&2
  exit 1
fi
if [[ "$(grep -Ec '^[[:space:]]*by sorry[[:space:]]*$' Challenge.lean)" -ne 1 ]]; then
  echo "Challenge.lean must contain exactly one trusted theorem hole" >&2
  exit 1
fi
if grep -Eq '^[[:space:]]*(axiom|unsafe)[[:space:]]|^[[:space:]]*by admit[[:space:]]*$' \
    Challenge.lean; then
  echo "Challenge.lean contains an extra trusted or unsafe declaration" >&2
  exit 1
fi
if grep -Eq 'sorry|admit|^[[:space:]]*(axiom|unsafe)[[:space:]]' Solution.lean; then
  echo "Solution.lean contains a placeholder, local axiom, or unsafe declaration" >&2
  exit 1
fi

python3 - <<'PY'
import json

def reject_duplicate_keys(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise SystemExit(f"duplicate key in config.json: {key!r}")
        result[key] = value
    return result

with open("config.json", encoding="utf-8") as source:
    config = json.load(source, object_pairs_hook=reject_duplicate_keys)

expected = {
    "challenge_module": "Challenge",
    "solution_module": "Solution",
    "theorem_names": ["ExactTwoDLO.Comparator.derivable"],
    "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
    "enable_nanoda": False,
}
if config != expected:
    raise SystemExit(f"config.json differs from the fail-closed certificate config:\n{config!r}")
PY
python3 scripts/check-challenge-surface.py
python3 scripts/check-project-pins.py
lake build Challenge
lake build Solution
