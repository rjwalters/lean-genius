#!/usr/bin/env python3
"""Emit a hierarchical checked-bank aggregate for exact-v2 H1 certificates."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path

from generate_h1_v2_lean_stubs import IndexRow, atomic_write, read_index, read_inventory


LEAN_MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
PROFILE_WORDS = ("zero", "one", "two", "three", "four")
DEFAULT_BANK_SIZE = 128


@dataclass(frozen=True)
class Bank:
    profile: int
    index: int
    rows: tuple[IndexRow, ...]

    @property
    def stem(self) -> str:
        return f"Erdos85H1V2Profile{self.profile}Bank{self.index:03d}"

    @property
    def theorem(self) -> str:
        return f"h1V2InventoryProfile{self.profile}Bank{self.index:03d}_checkedAt"


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
            if (row.profile, row.local_index, row.orbit) != (profile, local_index, tag):
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
        raw_table_definition = (
            f"def {stem}Table : OneHighMissTable :=\n"
            f"  (oneHighInventoryTables ({row.profile} : Fin 5)).get\n"
            f"    ⟨{row.local_index}, by native_decide⟩"
        )
        declarations = (
            raw_table_definition,
            f"theorem {stem}Checked :",
            f"def {stem}Entry : OneHighFamilyV2CheckedEntry {row.profile}",
        )
        if any(declaration not in source for declaration in declarations):
            raise ValueError(f"generated Lean stub has wrong declarations: {path}")


def partition_banks(rows: list[IndexRow], bank_size: int) -> list[list[Bank]]:
    if bank_size <= 0:
        raise ValueError("bank_size must be positive")
    by_profile: list[list[IndexRow]] = [[] for _ in PROFILE_WORDS]
    for row in rows:
        by_profile[row.profile].append(row)
    return [
        [
            Bank(profile, start // bank_size, tuple(profile_rows[start:start + bank_size]))
            for start in range(0, len(profile_rows), bank_size)
        ]
        for profile, profile_rows in enumerate(by_profile)
    ]


def bank_source(bank: Bank, stub_module_prefix: str) -> str:
    rows = list(bank.rows)
    if not rows:
        raise ValueError("cannot render an empty bank")
    lo = rows[0].local_index
    hi = rows[-1].local_index + 1
    imports = [
        f"import {stub_module_prefix}.Erdos85H1V2CertP{row.profile}I{row.local_index:05d}"
        for row in rows
    ]
    lines = imports + [
        "", "/-! GENERATED exact-v2 H1 leaf bank. -/", "", "namespace Erdos85", "",
        "set_option maxHeartbeats 0 in", "set_option maxRecDepth 1000000 in",
        f"theorem {bank.theorem}",
        f"    (i : Nat) (hlo : {lo} ≤ i) (hhi : i < {hi}) :",
        f"    OneHighFamilyV2CheckedUnsat {bank.profile}",
        f"      ((oneHighInventoryTables ({bank.profile} : Fin 5)).get",
        "        ⟨i, by",
        f"          rw [oneHighInventoryTables_length_{PROFILE_WORDS[bank.profile]}]",
        "          omega⟩) := by", "  interval_cases i",
    ]
    lines.extend(f"  · exact {stub_stem(row)}Checked" for row in rows)
    lines.extend(["", "end Erdos85", ""])
    return "\n".join(lines)


def _dispatch_lines(profile: int, banks: list[Bank]) -> list[str]:
    if not banks:
        raise ValueError(f"profile {profile} has no banks")
    if len(banks) == 1:
        return [f"  exact {banks[0].theorem} i (by omega) (by omega)"]
    first = banks[0]
    first_hi = first.rows[-1].local_index + 1
    lines = [
        f"  by_cases h : i < {first_hi}",
        f"  · exact {first.theorem} i (by omega) h",
    ]
    indent = "  "
    for bank in banks[1:-1]:
        hi = bank.rows[-1].local_index + 1
        lines.append(f"{indent}· by_cases h : i < {hi}")
        indent += "  "
        lines.append(f"{indent}· exact {bank.theorem} i (by omega) h")
    lines.append(f"{indent}· exact {banks[-1].theorem} i (by omega) (by omega)")
    return lines


def profile_source(profile: int, banks: list[Bank], aggregate_module_prefix: str) -> str:
    imports = [f"import {aggregate_module_prefix}.{bank.stem}" for bank in banks]
    lines = imports + [
        "", "/-! GENERATED exact-v2 H1 profile bank. -/", "", "namespace Erdos85", "",
        "set_option maxHeartbeats 0 in", "set_option maxRecDepth 1000000 in",
        f"theorem h1V2InventoryProfile{profile}_checkedAt",
        f"    (i : Fin (oneHighInventoryTables ({profile} : Fin 5)).length) :",
        f"    OneHighFamilyV2CheckedUnsat {profile}",
        f"      ((oneHighInventoryTables ({profile} : Fin 5)).get i) := by",
        "  rcases i with ⟨i, hi⟩",
        f"  rw [oneHighInventoryTables_length_{PROFILE_WORDS[profile]}] at hi",
    ]
    lines.extend(_dispatch_lines(profile, banks))
    lines.extend([
        "", f"theorem h1V2InventoryProfile{profile}_checked :",
        f"    ∀ table ∈ oneHighInventoryTables ({profile} : Fin 5),",
        f"      OneHighFamilyV2CheckedUnsat {profile} table :=",
        "  oneHighFamilyV2Checked_of_inventory_get",
        f"    ({profile} : Fin 5) h1V2InventoryProfile{profile}_checkedAt",
        "", "end Erdos85", "",
    ])
    return "\n".join(lines)


def top_source(aggregate_module_prefix: str) -> str:
    imports = [
        f"import {aggregate_module_prefix}.Erdos85H1V2Profile{profile}"
        for profile in range(len(PROFILE_WORDS))
    ]
    lines = imports + [
        "", "/-! GENERATED complete exact-v2 H1 checked-certificate dispatch. -/", "",
        "namespace Erdos85", "",
        "theorem orderFortyNineStratumExcluded_one_of_completeV2Certificates :",
        "    OrderFortyNineStratumExcluded 1 := by",
        "  apply orderFortyNineStratumExcluded_one_of_inventory_checked",
        "  intro profile", "  fin_cases profile",
    ]
    lines.extend(
        f"  · exact h1V2InventoryProfile{profile}_checked"
        for profile in range(len(PROFILE_WORDS))
    )
    lines.extend(["", "end Erdos85", ""])
    return "\n".join(lines)


def file_identity(path: Path) -> dict[str, object]:
    content = path.read_bytes()
    return {
        "path": str(path.resolve()),
        "bytes": len(content),
        "sha256": hashlib.sha256(content).hexdigest(),
    }


def validate_layout_manifest(manifest: dict[str, object], rows: list[IndexRow],
                             source_by_file: dict[str, str]) -> None:
    modules = manifest["modules"]
    if not isinstance(modules, list):
        raise ValueError("aggregate manifest modules must be a list")
    files = [module["file"] for module in modules]
    if len(files) != len(set(files)):
        raise ValueError("aggregate manifest has duplicate module files")
    leaf_members: list[tuple[int, int, str]] = []
    for module in modules:
        source = source_by_file[module["file"]]
        source_bytes = source.encode()
        if module["source_bytes"] != len(source_bytes) or module["source_sha256"] != hashlib.sha256(source_bytes).hexdigest():
            raise ValueError(f"{module['file']}: manifest/source identity mismatch")
        expected_module = (
            f"{manifest['prefixes']['aggregate_modules']}."
            f"{Path(module['file']).stem}"
        )
        if module["module"] != expected_module:
            raise ValueError(f"{module['file']}: qualified module mismatch")
        theorem = module["theorem"]
        if not isinstance(theorem, str) or f"theorem {theorem.removeprefix('Erdos85.')}" not in source:
            raise ValueError(f"{module['file']}: theorem/source mismatch")
        imports = [line.removeprefix("import ") for line in source.splitlines()
                   if line.startswith("import ")]
        if imports != module["direct_imports"]:
            raise ValueError(f"{module['file']}: manifest/source import mismatch")
        if len(imports) != module["direct_import_count"]:
            raise ValueError(f"{module['file']}: direct import count mismatch")
        if module["kind"] == "leaf-bank":
            if len(imports) > manifest["bank_size"]:
                raise ValueError(f"{module['file']}: leaf fan-in exceeds bank size")
            for member, imported in zip(module["members"], imports, strict=True):
                leaf_module = (
                    f"{manifest['prefixes']['leaf_modules']}."
                    f"Erdos85H1V2CertP{member['profile']}I{member['local_index']:05d}"
                )
                leaf_theorem = (
                    f"Erdos85.h1V2P{member['profile']}I{member['local_index']:05d}Checked"
                )
                if member["module"] != leaf_module or imported != leaf_module:
                    raise ValueError(f"{module['file']}: leaf module/member mismatch")
                if member["theorem"] != leaf_theorem or leaf_theorem.removeprefix("Erdos85.") not in source:
                    raise ValueError(f"{module['file']}: leaf theorem/member mismatch")
                leaf_members.append(
                    (member["profile"], member["local_index"], member["tag"])
                )
        elif module["members"] or any("Erdos85H1V2Cert" in item for item in imports):
            raise ValueError(f"{module['file']}: upper bank directly references leaves")
    expected = [(row.profile, row.local_index, row.orbit) for row in rows]
    if leaf_members != expected or len(set(leaf_members)) != len(expected):
        raise ValueError("aggregate manifest leaf membership is not an exact bijection")
    members = [
        member for module in modules if module["kind"] == "leaf-bank"
        for member in module["members"]
    ]
    members_bytes = json.dumps(members, sort_keys=True, separators=(",", ":")).encode()
    if manifest["leaf_members_sha256"] != hashlib.sha256(members_bytes).hexdigest():
        raise ValueError("aggregate manifest leaf-members hash mismatch")
    top = [module for module in modules if module["kind"] == "top-bank"]
    if len(top) != 1 or top[0]["direct_import_count"] != len(PROFILE_WORDS):
        raise ValueError("aggregate manifest must have one five-profile top bank")
    if manifest["top_module"] != top[0]["module"]:
        raise ValueError("aggregate manifest top-module mismatch")


def write_hierarchy(rows: list[IndexRow], output_dir: Path,
                    stub_module_prefix: str, aggregate_module_prefix: str,
                    bank_size: int, *, inventory_identity: dict[str, object],
                    index_identity: dict[str, object]) -> list[Path]:
    banks_by_profile = partition_banks(rows, bank_size)
    rendered: list[tuple[Path, str]] = []
    module_records: list[dict[str, object]] = []
    for profile, banks in enumerate(banks_by_profile):
        for bank in banks:
            path = output_dir / f"{bank.stem}.lean"
            source = bank_source(bank, stub_module_prefix)
            rendered.append((path, source))
            module_records.append({
                "file": path.name,
                "module": f"{aggregate_module_prefix}.{bank.stem}",
                "kind": "leaf-bank",
                "theorem": f"Erdos85.{bank.theorem}",
                "direct_imports": [
                    f"{stub_module_prefix}.Erdos85H1V2CertP{row.profile}I{row.local_index:05d}"
                    for row in bank.rows
                ],
                "members": [
                    {"profile": row.profile, "local_index": row.local_index,
                     "tag": row.orbit,
                     "module": (
                         f"{stub_module_prefix}.Erdos85H1V2CertP"
                         f"{row.profile}I{row.local_index:05d}"
                     ),
                     "theorem": (
                         f"Erdos85.h1V2P{row.profile}I"
                         f"{row.local_index:05d}Checked"
                     )}
                    for row in bank.rows
                ],
            })
        stem = f"Erdos85H1V2Profile{profile}"
        path = output_dir / f"{stem}.lean"
        source = profile_source(profile, banks, aggregate_module_prefix)
        rendered.append((path, source))
        module_records.append({
            "file": path.name,
            "module": f"{aggregate_module_prefix}.{stem}",
            "kind": "profile-bank",
            "theorem": f"Erdos85.h1V2InventoryProfile{profile}_checked",
            "direct_imports": [
                f"{aggregate_module_prefix}.{bank.stem}" for bank in banks
            ],
            "members": [],
        })
    top_path = output_dir / "Erdos85H1V2Complete.lean"
    rendered.append((top_path, top_source(aggregate_module_prefix)))
    module_records.append({
        "file": top_path.name,
        "module": f"{aggregate_module_prefix}.Erdos85H1V2Complete",
        "kind": "top-bank",
        "theorem": (
            "Erdos85.orderFortyNineStratumExcluded_one_of_completeV2Certificates"
        ),
        "direct_imports": [
            f"{aggregate_module_prefix}.Erdos85H1V2Profile{profile}"
            for profile in range(len(PROFILE_WORDS))
        ],
        "members": [],
    })
    expected = {path.name for path, _ in rendered}
    existing = (
        {path.name for path in output_dir.glob("Erdos85H1V2Profile*.lean")}
        | ({"Erdos85H1V2Complete.lean"}
           if (output_dir / "Erdos85H1V2Complete.lean").exists() else set())
    )
    stale = sorted(existing - expected)
    if stale:
        raise ValueError(
            "aggregate output directory contains stale generated modules: "
            + ", ".join(stale)
        )
    for path, source in rendered:
        atomic_write(path, source)
    source_by_file = {path.name: source for path, source in rendered}
    for record in module_records:
        source = source_by_file[str(record["file"])]
        record["source_bytes"] = len(source.encode())
        record["source_sha256"] = hashlib.sha256(source.encode()).hexdigest()
        record["direct_import_count"] = len(record["direct_imports"])
    members = [
        member
        for record in module_records
        for member in record["members"]
    ]
    members_bytes = json.dumps(members, sort_keys=True, separators=(",", ":")).encode()
    manifest = {
        "schema": "erdos85-h1-v2-aggregate-layout-v1",
        "bank_size": bank_size,
        "leaf_count": len(rows),
        "leaf_members_sha256": hashlib.sha256(members_bytes).hexdigest(),
        "inputs": {"inventory": inventory_identity, "index": index_identity},
        "prefixes": {
            "leaf_modules": stub_module_prefix,
            "aggregate_modules": aggregate_module_prefix,
        },
        "profile_bank_counts": [len(banks) for banks in banks_by_profile],
        "modules": module_records,
        "top_module": f"{aggregate_module_prefix}.Erdos85H1V2Complete",
    }
    validate_layout_manifest(manifest, rows, source_by_file)
    manifest_path = output_dir / "aggregate-layout.json"
    manifest_text = json.dumps(manifest, sort_keys=True, indent=2) + "\n"
    atomic_write(manifest_path, manifest_text)
    manifest_hash_path = output_dir / "aggregate-layout.sha256"
    manifest_hash = hashlib.sha256(manifest_text.encode()).hexdigest()
    atomic_write(manifest_hash_path, f"{manifest_hash}  aggregate-layout.json\n")
    return [path for path, _ in rendered] + [manifest_path, manifest_hash_path]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--index", type=Path, required=True)
    parser.add_argument("--inventory", type=Path, required=True)
    parser.add_argument("--stub-dir", type=Path, required=True)
    parser.add_argument("--stub-module-prefix", required=True)
    parser.add_argument("--aggregate-module-prefix", required=True)
    parser.add_argument("--bank-size", type=int, default=DEFAULT_BANK_SIZE)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    for option in ("stub_module_prefix", "aggregate_module_prefix"):
        if not LEAN_MODULE.fullmatch(getattr(args, option)):
            parser.error(f"--{option.replace('_', '-')} must be a qualified Lean identifier")
    if args.bank_size <= 0:
        parser.error("--bank-size must be positive")
    profiles = read_inventory(args.inventory)
    rows = read_index(args.index)
    validate_complete(rows, profiles)
    validate_stub_sources(rows, args.stub_dir)
    written = write_hierarchy(rows, args.output_dir, args.stub_module_prefix,
                              args.aggregate_module_prefix, args.bank_size,
                              inventory_identity=file_identity(args.inventory),
                              index_identity=file_identity(args.index))
    print(f"WROTE {len(written) - 2} Lean modules + manifest ({len(rows)} entries)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
