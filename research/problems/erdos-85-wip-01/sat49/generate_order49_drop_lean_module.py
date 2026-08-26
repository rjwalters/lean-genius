#!/usr/bin/env python3
"""Connect four generated stratum theorems to the checked order-49 drop."""

from __future__ import annotations

import argparse
import os
import re
from pathlib import Path


LEAN_NAME = re.compile(
    r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
)


def render(inputs: list[tuple[str, str]]) -> str:
    modules = list(dict.fromkeys(module for module, _ in inputs))
    h1, h3, h5, h7 = (theorem for _, theorem in inputs)
    lines = [f"import {module}" for module in modules]
    lines.extend([
        "import Proofs.Erdos85FiniteDropWitnesses", "",
        "/-! GENERATED checked order-48/order-49 strict-drop endpoint. -/", "",
        "namespace Erdos85", "",
        "theorem not_c4FreeMinDegreeWitness_fortyNine_seven_of_generatedCertificates :",
        "    ¬ C4FreeMinDegreeWitness 49 7 :=",
        "  not_c4FreeMinDegreeWitness_fortyNine_seven_of_strata",
        f"    {h1} {h3} {h5} {h7}", "",
        "theorem minDegreeForC4_fortyEight_fortyNine_exact_of_generatedCertificates :",
        "    minDegreeForC4 48 = 8 ∧ minDegreeForC4 49 = 7 :=",
        "  minDegreeForC4_fortyEight_fortyNine_exact_checked",
        "    not_c4FreeMinDegreeWitness_fortyNine_seven_of_generatedCertificates", "",
        "theorem minDegreeForC4_fortyNine_lt_fortyEight_of_generatedCertificates :",
        "    minDegreeForC4 49 < minDegreeForC4 48 :=",
        "  minDegreeForC4_fortyNine_lt_fortyEight_checked",
        "    not_c4FreeMinDegreeWitness_fortyNine_seven_of_generatedCertificates", "",
        "end Erdos85", "",
    ])
    return "\n".join(lines)


def atomic_write(path: Path, source: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.tmp.{os.getpid()}")
    try:
        temporary.write_text(source)
        os.replace(temporary, path)
    except BaseException:
        if temporary.exists():
            temporary.unlink()
        raise


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    for stratum in ("h1", "h3", "h5", "h7"):
        parser.add_argument(f"--{stratum}-module", required=True)
        parser.add_argument(f"--{stratum}-theorem", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    inputs = []
    for stratum in ("h1", "h3", "h5", "h7"):
        module = getattr(args, f"{stratum}_module")
        theorem = getattr(args, f"{stratum}_theorem")
        if not LEAN_NAME.fullmatch(module) or not LEAN_NAME.fullmatch(theorem):
            parser.error(f"--{stratum}-module/theorem must be Lean identifiers")
        inputs.append((module, theorem))
    atomic_write(args.output, render(inputs))
    print(f"WROTE {args.output.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
