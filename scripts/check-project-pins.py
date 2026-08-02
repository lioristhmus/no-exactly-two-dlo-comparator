#!/usr/bin/env python3
"""Check locked package metadata and materialized Git HEADs fail closed."""

from __future__ import annotations

import json
import subprocess
from pathlib import Path


EXPECTED = {
    "NoExactlyTwoDlo": (
        "https://github.com/lioristhmus/no-exactly-two-dlo-lean.git",
        "162ef5991f6548b62776eb9abbbda1c9aaf81fb9",
        False,
    ),
    "NoExactlyThreeDlo": (
        "https://github.com/lioristhmus/no-exactly-three-dlo-lean.git",
        "ca5d9488552e68fd64ffb0da05912c3fa68d78c9",
        True,
    ),
    "mathlib": (
        "https://github.com/leanprover-community/mathlib4.git",
        "5e932f97dd25535344f80f9dd8da3aab83df0fe6",
        False,
    ),
    "plausible": (
        "https://github.com/leanprover-community/plausible",
        "83e90935a17ca19ebe4b7893c7f7066e266f50d3",
        True,
    ),
    "LeanSearchClient": (
        "https://github.com/leanprover-community/LeanSearchClient",
        "c5d5b8fe6e5158def25cd28eb94e4141ad97c843",
        True,
    ),
    "importGraph": (
        "https://github.com/leanprover-community/import-graph",
        "48d5698bc464786347c1b0d859b18f938420f060",
        True,
    ),
    "proofwidgets": (
        "https://github.com/leanprover-community/ProofWidgets4",
        "4dd0959c44d1af0462bd604d0f87c5781307d709",
        True,
    ),
    "aesop": (
        "https://github.com/leanprover-community/aesop",
        "7152850e7b216a0d409701617721b6e469d34bf6",
        True,
    ),
    "Qq": (
        "https://github.com/leanprover-community/quote4",
        "707efb56d0696634e9e965523a1bbe9ac6ce141d",
        True,
    ),
    "batteries": (
        "https://github.com/leanprover-community/batteries",
        "756e3321fd3b02a85ffda19fef789916223e578c",
        True,
    ),
    "Cli": (
        "https://github.com/leanprover/lean4-cli",
        "7802da01beb530bf051ab657443f9cd9bc3e1a29",
        True,
    ),
}


def reject_duplicate_keys(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise SystemExit(f"duplicate key in lake-manifest.json: {key!r}")
        result[key] = value
    return result


def git_head(path: Path) -> str:
    completed = subprocess.run(
        ["git", "-C", str(path), "rev-parse", "HEAD"],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    return completed.stdout.strip()


def main() -> None:
    project = Path(__file__).resolve().parents[1]
    manifest_path = project / "lake-manifest.json"
    with manifest_path.open(encoding="utf-8") as source:
        manifest = json.load(source, object_pairs_hook=reject_duplicate_keys)

    if manifest.get("name") != "NoExactlyTwoDloComparator":
        raise SystemExit(f"unexpected manifest package name: {manifest.get('name')!r}")

    packages = manifest.get("packages")
    if not isinstance(packages, list):
        raise SystemExit("lake-manifest.json packages must be a list")
    by_name = {}
    for package in packages:
        name = package.get("name")
        if name in by_name:
            raise SystemExit(f"duplicate package entry in lake-manifest.json: {name!r}")
        by_name[name] = package

    if set(by_name) != set(EXPECTED):
        raise SystemExit(
            "manifest package set differs from the certificate lock:\n"
            f"expected={sorted(EXPECTED)!r}\nactual={sorted(by_name)!r}"
        )

    packages_dir = project / manifest.get("packagesDir", ".lake/packages")
    for name, (url, revision, inherited) in EXPECTED.items():
        package = by_name[name]
        actual = (package.get("url"), package.get("rev"), package.get("inherited"))
        expected = (url, revision, inherited)
        if actual != expected:
            raise SystemExit(
                f"unexpected manifest lock for {name}: expected={expected!r}, actual={actual!r}"
            )
        if name in {"NoExactlyTwoDlo", "NoExactlyThreeDlo", "mathlib"} and \
                package.get("inputRev") != revision:
            raise SystemExit(
                f"critical inputRev/rev mismatch for {name}: "
                f"inputRev={package.get('inputRev')!r}, rev={revision!r}"
            )

        materialized = packages_dir / name
        if materialized.is_symlink():
            raise SystemExit(f"refusing symlinked package root: {materialized}")
        if not materialized.exists():
            raise SystemExit(f"package is not materialized: {materialized}")
        if not materialized.is_dir():
            raise SystemExit(f"package root is not a directory: {materialized}")
        actual_head = git_head(materialized)
        if actual_head != revision:
            raise SystemExit(
                f"materialized HEAD mismatch for {name}: expected={revision}, actual={actual_head}"
            )

    print("project pins ok: 11 manifest locks and materialized Git HEADs")


if __name__ == "__main__":
    main()
