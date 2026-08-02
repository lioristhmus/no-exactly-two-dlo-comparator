#!/usr/bin/env bash
set -euo pipefail

if [[ "$#" -ne 1 ]]; then
  echo "usage: $0 /absolute/path/to/new-tools-directory" >&2
  exit 2
fi

tools_root="$1"
if [[ "$tools_root" != /* ]]; then
  echo "tools directory must be an absolute path" >&2
  exit 2
fi
if [[ -e "$tools_root" ]]; then
  echo "refusing to overwrite existing path: $tools_root" >&2
  exit 2
fi

script_dir="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
comparator_commit="2a00b30df5e9173e70c4e4ec669fdf03da3163b9"
landrun_commit="811cfff51ceaf3d9843708aa6d22e9b84ccac8b4"
lean4export_commit="6f4e21dd70c3c11d7fbd07d39e3192792c657448"
lean4checker_commit="b7398199245524275543dec6113229c9bb4902e5"

mkdir -p "$tools_root/bin"

git clone --no-checkout https://github.com/leanprover/comparator.git "$tools_root/comparator"
git -C "$tools_root/comparator" checkout --detach "$comparator_commit"
git -C "$tools_root/comparator" apply "$script_dir/comparator-v4.29.1.patch"

manifest_export_commit="$(
  sed -n '/"url": "https:\/\/github.com\/leanprover\/lean4export"/,/"configFile"/p' \
    "$tools_root/comparator/lake-manifest.json" |
    sed -n 's/^[[:space:]]*"rev": "\([0-9a-f]*\)",/\1/p'
)"
if [[ "$manifest_export_commit" != "$lean4export_commit" ]]; then
  echo "unexpected lean4export manifest commit: $manifest_export_commit" >&2
  exit 1
fi

(
  cd "$tools_root/comparator"
  lake build comparator lean4export
)

materialized_export_commit="$(
  git -C "$tools_root/comparator/.lake/packages/lean4export" rev-parse HEAD
)"
if [[ "$materialized_export_commit" != "$lean4export_commit" ]]; then
  echo "unexpected materialized lean4export commit: $materialized_export_commit" >&2
  exit 1
fi

materialized_checker_commit="$(
  git -C "$tools_root/comparator/.lake/packages/Lean4Checker" rev-parse HEAD
)"
if [[ "$materialized_checker_commit" != "$lean4checker_commit" ]]; then
  echo "unexpected materialized Lean4Checker commit: $materialized_checker_commit" >&2
  exit 1
fi

git clone --no-checkout https://github.com/Zouuup/landrun.git "$tools_root/landrun"
git -C "$tools_root/landrun" checkout --detach "$landrun_commit"
(
  cd "$tools_root/landrun"
  go mod verify
  go build -trimpath -o "$tools_root/bin/landrun" ./cmd/landrun
)

ln -s "$tools_root/comparator/.lake/build/bin/comparator" "$tools_root/bin/comparator"
ln -s "$tools_root/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export" \
  "$tools_root/bin/lean4export"

test "$(git -C "$tools_root/comparator" rev-parse HEAD)" = "$comparator_commit"
test "$(git -C "$tools_root/landrun" rev-parse HEAD)" = "$landrun_commit"
test -x "$tools_root/bin/comparator"
test -x "$tools_root/bin/lean4export"
test -x "$tools_root/bin/landrun"

echo "Comparator tools built in $tools_root/bin"
echo "Comparator commit: $(git -C "$tools_root/comparator" rev-parse HEAD)"
echo "lean4export commit: $materialized_export_commit"
echo "Lean4Checker commit: $materialized_checker_commit"
echo "Landrun commit: $(git -C "$tools_root/landrun" rev-parse HEAD)"
