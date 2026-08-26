#!/usr/bin/env python3
"""Emit the complete checked-bank aggregate for exact-v2 H1 certificates."""

from __future__ import annotations

import argparse
import re
from pathlib import Path

from generate_h1_v2_lean_stubs import (
    PROFILE_NAMES,
    IndexRow,
    atomic_write,
    read_index,
    read_inventory,
)


LEAN_MODULE = re.compile(
    r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
)


def validate_complete(rows: list[IndexRow], profiles: list[list[str]]) -> None:
    expected = sum(map(len, profiles))
    if len(rows) != expected:
        raise ValueError(
            f"aggregate requires all {expected} inventory rows; index has {len(rows)}"
        )
    cursor = 0
    for profile, tags in enumerate(profiles):
        for local_index, tag in enumerate(tags):
            row = rows[cursor]
            if (row.profile, row.local_index, row.orbit) != (
                profile, local_index, tag
            ):
                raise ValueError(
                    "index does not exactly cover authoritative inventory at "
                    f"profile={profile} localIndex={local_index}: "
                    f"found {(row.profile, row.local_index, row.orbit)}"
                )
            if not row.stub_ready:
                raise ValueError(f"{row.orbit}: aggregate row is not stub_ready")
            cursor += 1


def stub_stem(row: IndexRow) -> str:
    return f"h1V2P{row.profile}I{row.local_index:05d}"


def validate_stub_sources(rows: list[IndexRow], stub_dir: Path) -> None:
    for row in rows:
        module = f"Erdos85H1V2CertP{row.profile}I{row.local_index:05d}.lean"
        path = stub_dir / module
        if not path.is_file():
            raise ValueError(f"missing generated Lean stub: {path}")
        source = path.read_text()
        stem = stub_stem(row)
        declarations = (
            f"theorem {stem}Checked :",
            f"def {stem}Entry : OneHighFamilyV2CheckedEntry {row.profile}",
        )
        if any(declaration not in source for declaration in declarations):
            raise ValueError(f"generated Lean stub has wrong declarations: {path}")


def aggregate_source(rows: list[IndexRow], stub_module_prefix: str) -> str:
    imports = [
        f"import {stub_module_prefix}.Erdos85H1V2CertP{row.profile}I{row.local_index:05d}"
        for row in rows
    ]
    lines = imports + [
        "", "/-! GENERATED complete exact-v2 H1 checked-certificate banks. -/", "",
        "namespace Erdos85", "",
    ]
    by_profile = [[], [], [], [], []]
    for row in rows:
        by_profile[row.profile].append(row)
    for profile, profile_rows in enumerate(by_profile):
        lines.extend([
            f"def h1V2CheckedBank{profile} :",
            f"    List (OneHighFamilyV2CheckedEntry {profile}) := [",
        ])
        for index, row in enumerate(profile_rows):
            comma = "," if index + 1 < len(profile_rows) else ""
            lines.append(f"  {stub_stem(row)}Entry{comma}")
        lines.extend([
            "]", "",
            f"theorem h1V2CheckedBank{profile}_covers :",
            "    oneHighFamilyV2CheckedBankTables "
            f"h1V2CheckedBank{profile} =",
            f"      oneHighInventoryTables ({profile} : Fin 5) := by",
            "  native_decide", "",
            f"theorem h1V2InventoryProfile{profile}_checked :",
            f"    ∀ table ∈ oneHighInventoryTables ({profile} : Fin 5),",
            f"      OneHighFamilyV2CheckedUnsat {profile} table :=",
            "  oneHighFamilyV2Checked_of_bank_tables_eq_inventory",
            f"    ({profile} : Fin 5) h1V2CheckedBank{profile} "
            f"h1V2CheckedBank{profile}_covers", "",
        ])
    lines.extend([
        "theorem orderFortyNineStratumExcluded_one_of_completeV2Certificates :",
        "    OrderFortyNineStratumExcluded 1 := by",
        "  apply orderFortyNineStratumExcluded_one_of_inventory_checked",
        "  intro profile", "  fin_cases profile",
    ])
    for profile in range(5):
        lines.append(f"  · exact h1V2InventoryProfile{profile}_checked")
    lines.extend(["", "end Erdos85", ""])
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--index", type=Path, required=True)
    parser.add_argument("--inventory", type=Path, required=True)
    parser.add_argument("--stub-dir", type=Path, required=True)
    parser.add_argument("--stub-module-prefix", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if not LEAN_MODULE.fullmatch(args.stub_module_prefix):
        parser.error("--stub-module-prefix must be a qualified Lean identifier")
    profiles = read_inventory(args.inventory)
    rows = read_index(args.index)
    validate_complete(rows, profiles)
    validate_stub_sources(rows, args.stub_dir)
    atomic_write(args.output, aggregate_source(rows, args.stub_module_prefix))
    print(f"WROTE {args.output.resolve()} ({len(rows)} checked entries)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
