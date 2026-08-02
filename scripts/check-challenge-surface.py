#!/usr/bin/env python3
"""Fail closed unless Challenge.lean exposes the intended 54 definitions."""

from __future__ import annotations

import re
from pathlib import Path


EXPECTED = {
    "ExactThreeDLO.FO": [
        "memRel",
        "Lmem",
        "memF",
        "extAx",
        "pairAx",
        "unionAx",
        "powerAx",
        "infAx",
        "sepAx",
        "Zsep",
        "bv0",
        "sub0",
        "ofSentAux",
        "ofSent",
        "vEq",
        "vMem",
        "Deriv",
        "theoryHyp",
        "Provable",
        "lastSplit",
        "fMem",
        "fEq",
        "fAnd",
        "fNot",
        "fOr",
        "fImp",
        "fIff",
        "fComp",
        "fAll",
        "fEx",
        "fClose",
        "fEqOpair",
        "fOpairMem",
        "fLt",
        "fMemProd",
        "fEqApp",
        "fIsFunc",
        "fIsInj",
        "fIsOnto",
        "fIsSLO",
        "fDense",
        "fNoLeast",
        "fNoGreatest",
        "fIsDLO",
        "fOrdClause",
        "fIsOrderIso",
        "fOrderIsom",
        "fPairIso",
        "fSpec3Body",
        "fSpecGe3",
    ],
    "ExactTwoDLO.FO": [
        "fSpec2Body",
        "fSpecGe2",
        "fSpecEq2",
        "spec2Sentence",
    ],
}

DECLARATION = re.compile(
    r"^(?:(?:noncomputable|protected)\s+)?(?:inductive|def|abbrev)\s+([A-Za-z0-9_]+)\b"
)
NAMESPACE = re.compile(r"^namespace\s+([A-Za-z0-9_.]+)\s*$")
END = re.compile(r"^end(?:\s+([A-Za-z0-9_.]+))?\s*$")


def main() -> None:
    source = Path(__file__).resolve().parents[1] / "Challenge.lean"
    stack: list[str] = []
    actual = {namespace: [] for namespace in EXPECTED}

    for raw_line in source.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if match := NAMESPACE.match(line):
            stack.append(match.group(1))
            continue
        if END.match(line):
            if not stack:
                raise SystemExit(f"unmatched namespace end in {source}: {raw_line!r}")
            stack.pop()
            continue
        if match := DECLARATION.match(line):
            namespace = ".".join(stack)
            if namespace in actual:
                actual[namespace].append(match.group(1))

    if stack:
        raise SystemExit(f"unclosed namespace stack in {source}: {stack!r}")

    if actual != EXPECTED:
        raise SystemExit(
            "Challenge.lean definition surface differs from the exact-two certificate contract:\n"
            f"expected={EXPECTED!r}\nactual={actual!r}"
        )

    count = sum(map(len, actual.values()))
    if count != 54:
        raise SystemExit(f"internal contract error: expected 54 definitions, found {count}")
    print("challenge surface ok: 50 shared/exact-three + 4 exact-two definitions")


if __name__ == "__main__":
    main()
