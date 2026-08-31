#!/usr/bin/env python3
"""Generate the provenance-bound H1 wrapper endpoint adapter."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent


def imported(name: str, filename: str):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


STUBS = imported("h1_stubs", "generate_h1_v2_lean_stubs.py")
_previous_stubs = sys.modules.get("generate_h1_v2_lean_stubs")
try:
    sys.modules["generate_h1_v2_lean_stubs"] = STUBS
    AGGREGATE = imported("h1_aggregate", "generate_h1_v2_lean_aggregate.py")
finally:
    if _previous_stubs is None:
        del sys.modules["generate_h1_v2_lean_stubs"]
    else:
        sys.modules["generate_h1_v2_lean_stubs"] = _previous_stubs
SCHEMA = "erdos85-h1-post-aggregate-adapter-generation-v1"
LEAF_INDEX_SCHEMA = "erdos85-h1-leaf-module-index-v1"
REINDEX_SCHEMA = "erdos85-h1-v2-capacity-reindex-v1"
LAYOUT_SCHEMA = "erdos85-h1-v2-aggregate-layout-v1"
SOURCE_MODULE = "Proofs.Generated.Erdos85OrderFortyNineOneHighCertificates"
SOURCE_REPO_PATH = "proofs/Proofs/Generated/Erdos85OrderFortyNineOneHighCertificates.lean"
OUTPUT_THEOREM = "Erdos85.orderFortyNineStratumExcluded_one_of_generatedCertificates"
INPUT_THEOREM = "Erdos85.orderFortyNineStratumExcluded_one_of_completeV2CapacityCertificates"
PROFILE_COUNTS = (1485, 3617, 4717, 2693, 839)
SHA256 = re.compile(r"[0-9a-f]{64}")
LEAN_MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+")


def canonical(value: object) -> bytes:
    return (json.dumps(value, ensure_ascii=True, allow_nan=False,
                       sort_keys=True, separators=(",", ":")) + "\n").encode("ascii")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def require_file(path: Path, pin: str, label: str) -> None:
    if not path.is_absolute() or path.is_symlink() or not path.is_file():
        raise ValueError(f"{label} must be an absolute regular non-symlink file")
    if not isinstance(pin, str) or SHA256.fullmatch(pin) is None or sha256(path) != pin:
        raise ValueError(f"{label} SHA mismatch")


def read_canonical(path: Path, pin: str, label: str) -> dict:
    require_file(path, pin, label)
    raw = path.read_bytes()
    value = json.loads(raw)
    if not isinstance(value, dict) or raw != canonical(value):
        raise ValueError(f"{label} must be canonical JSON")
    return value


def read_pretty(path: Path, pin: str, label: str) -> dict:
    require_file(path, pin, label)
    raw = path.read_bytes()
    value = json.loads(raw)
    expected = (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()
    if not isinstance(value, dict) or raw != expected:
        raise ValueError(f"{label} must be canonical indented JSON")
    return value


def file_identity(path: Path) -> dict[str, object]:
    return {"path": str(path), "bytes": path.stat().st_size, "sha256": sha256(path)}


def module_path(repo: Path, module: str) -> Path:
    if LEAN_MODULE.fullmatch(module) is None:
        raise ValueError("invalid qualified module path")
    return repo / "proofs" / Path(*module.split(".")).with_suffix(".lean")


def require_repo_path(repo: Path, path: Path, label: str) -> None:
    if not path.is_absolute() or path!=path.resolve(): raise ValueError(f"{label} is not canonical real path")
    try: parts=path.relative_to(repo).parts
    except ValueError as error: raise ValueError(f"{label} escapes repo") from error
    current=repo
    for part in parts:
        current=current/part
        if current.is_symlink(): raise ValueError(f"{label} traverses a symlink")


def render(top_module: str) -> str:
    if LEAN_MODULE.fullmatch(top_module) is None:
        raise ValueError("layout top module is not a qualified Lean module")
    return "\n".join([
        f"import {top_module}", "", "/-! GENERATED reviewed H1 aggregate endpoint adapter. -/",
        "", "namespace Erdos85", "",
        "theorem orderFortyNineStratumExcluded_one_of_generatedCertificates :",
        "    OrderFortyNineStratumExcluded 1 :=",
        "  orderFortyNineStratumExcluded_one_of_completeV2CapacityCertificates",
        "", "end Erdos85", "",
    ])


def validate(repo: Path, layout_path: Path, layout_sha256: str,
             aggregate_root: Path, index_path: Path, index_sha256: str,
             reindex_path: Path, reindex_sha256: str,
             leaf_index_path: Path, leaf_index_sha256: str) -> tuple[str, dict, list[Path]]:
    if not repo.is_absolute() or repo.is_symlink() or not repo.is_dir() or repo!=repo.resolve():
        raise ValueError("repo must be an absolute real directory")
    top=subprocess.run(["git","rev-parse","--show-toplevel"],cwd=repo,check=True,
                       text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE).stdout.strip()
    if Path(top)!=repo: raise ValueError("repo is not the canonical git root")
    if not aggregate_root.is_absolute() or aggregate_root.is_symlink() or not aggregate_root.is_dir():
        raise ValueError("aggregate source root must be an absolute real directory")
    layout = read_pretty(layout_path, layout_sha256, "aggregate layout")
    layout_fields = {"bank_size", "inputs", "inventory_contract", "leaf_count",
        "leaf_members_sha256", "modules", "prefixes", "profile_bank_counts",
        "schema", "top_module"}
    if set(layout) != layout_fields or layout.get("schema") != LAYOUT_SCHEMA:
        raise ValueError("aggregate layout schema mismatch")
    require_file(index_path, index_sha256, "capacity index")
    rows = STUBS.read_index(index_path)
    require_file(index_path, index_sha256, "capacity index")
    if len(rows) != sum(PROFILE_COUNTS) or any(not row.stub_ready for row in rows):
        raise ValueError("capacity index is not the complete 13,351 stub-ready bank")
    AGGREGATE.validate_capacity_shape(rows)
    layout_index = layout.get("inputs", {}).get("index")
    if layout_index != file_identity(index_path):
        raise ValueError("aggregate layout does not bind the capacity index")

    reindex = read_pretty(reindex_path, reindex_sha256, "capacity reindex receipt")
    reindex_fields = {"capacity_total", "dropped_outside_capacity_tags", "emitted_rows",
        "indexes", "inventory", "inventory_sha256", "output", "output_sha256",
        "require_complete", "schema"}
    layout_inventory = layout.get("inputs", {}).get("inventory")
    if (set(reindex) != reindex_fields or reindex.get("schema") != REINDEX_SCHEMA
            or reindex.get("capacity_total") != sum(PROFILE_COUNTS)
            or reindex.get("emitted_rows") != sum(PROFILE_COUNTS)
            or reindex.get("dropped_outside_capacity_tags") != []
            or reindex.get("require_complete") is not True
            or reindex.get("output") != str(index_path)
            or reindex.get("output_sha256") != index_sha256
            or not isinstance(layout_inventory, dict)
            or reindex.get("inventory") != layout_inventory.get("path")
            or reindex.get("inventory_sha256") != layout_inventory.get("sha256")):
        raise ValueError("capacity reindex receipt mismatch")
    inventory_path = Path(reindex["inventory"])
    require_file(inventory_path, reindex["inventory_sha256"], "capacity inventory")
    if layout_inventory != file_identity(inventory_path):
        raise ValueError("aggregate layout inventory identity mismatch")
    source_indexes = reindex.get("indexes")
    if (not isinstance(source_indexes, list) or not source_indexes
            or any(not isinstance(item, dict) or set(item) != {"path", "sha256"}
                   for item in source_indexes)):
        raise ValueError("capacity reindex source indexes malformed")
    source_index_paths=[]
    for item in source_indexes:
        path=Path(item["path"])
        require_file(path,item["sha256"],"capacity reindex source index")
        source_index_paths.append(path)
    resolved_sources=[path.resolve() for path in source_index_paths]
    forbidden_sources={index_path.resolve(),inventory_path.resolve(),reindex_path.resolve()}
    if (len(resolved_sources)!=len(set(resolved_sources))
            or any(path in forbidden_sources for path in resolved_sources)):
        raise ValueError("capacity reindex source indexes are duplicated or alias outputs")
    modules = layout.get("modules")
    if not isinstance(modules, list):
        raise ValueError("aggregate layout modules missing")
    aggregate_prefix=layout.get("prefixes",{}).get("aggregate_modules")
    expected_aggregate_root=repo/"proofs"/Path(*aggregate_prefix.split("."))
    if aggregate_root!=expected_aggregate_root:
        raise ValueError("aggregate root is not the canonical repo module directory")
    require_repo_path(repo,aggregate_root,"aggregate root")
    if layout_path!=aggregate_root/"aggregate-layout.json":
        raise ValueError("aggregate layout is outside its canonical source root")
    source_by_file: dict[str, str] = {}
    aggregate_paths: list[Path] = []
    aggregate_identities = []
    module_fields = {"direct_import_count", "direct_imports", "file", "kind",
                     "members", "module", "source_bytes", "source_sha256", "theorem"}
    for record in modules:
        if (not isinstance(record, dict) or set(record) != module_fields
                or not isinstance(record.get("file"), str)):
            raise ValueError("aggregate layout module record malformed")
        path = module_path(repo,record["module"])
        if path!=aggregate_root/record["file"]: raise ValueError(f"{record['file']}: noncanonical module path")
        require_file(path, str(record.get("source_sha256")), record["file"])
        if path.stat().st_size != record.get("source_bytes"):
            raise ValueError(f"{record['file']}: source byte count mismatch")
        source_by_file[record["file"]] = path.read_text()
        aggregate_paths.append(path)
        aggregate_identities.append({"repo_path":str(path.relative_to(repo)),
            "bytes":path.stat().st_size,"sha256":sha256(path)})
    actual_names = {path.name for path in aggregate_root.iterdir() if path.is_file() and path.suffix == ".lean"}
    if actual_names != {record["file"] for record in modules}:
        raise ValueError("aggregate source root has a stale/missing Lean module")
    AGGREGATE.validate_layout_manifest(layout, rows, source_by_file)
    top = next(record for record in modules if record["kind"] == "top-bank")
    if (layout.get("top_module") != top.get("module")
            or top.get("theorem") != INPUT_THEOREM):
        raise ValueError("aggregate top endpoint mismatch")

    leaf_index = read_canonical(leaf_index_path, leaf_index_sha256, "leaf module index")
    leaf_fields = {"capacity_index_sha256", "leaf_count", "modules", "schema"}
    leaf_rows = leaf_index.get("modules")
    expected_leaf_fields = {"local_index", "orbit", "packed_lrat_sha256", "profile",
                            "source_bytes", "source_module", "source_path", "source_sha256"}
    if (set(leaf_index) != leaf_fields or leaf_index.get("schema") != LEAF_INDEX_SCHEMA
            or leaf_index.get("capacity_index_sha256") != index_sha256
            or leaf_index.get("leaf_count") != len(rows)
            or not isinstance(leaf_rows, list) or len(leaf_rows) != len(rows)):
        raise ValueError("leaf module index header mismatch")
    leaf_paths: list[Path] = []
    seen_leaf_paths: set[Path] = set()
    for row, entry in zip(rows, leaf_rows, strict=True):
        if (not isinstance(entry, dict) or set(entry) != expected_leaf_fields
                or (entry["profile"], entry["local_index"], entry["orbit"],
                    entry["packed_lrat_sha256"]) !=
                   (row.profile, row.local_index, row.orbit, row.packed_sha)):
            raise ValueError("leaf module index is not the exact capacity bijection")
        expected_module = f"{layout['prefixes']['leaf_modules']}.Erdos85H1V2CertP{row.profile}I{row.local_index:05d}"
        path = Path(entry["source_path"])
        theorem = f"h1V2P{row.profile}I{row.local_index:05d}Checked"
        expected_path=module_path(repo,expected_module)
        if (entry["source_module"] != expected_module or path!=expected_path
                or path in seen_leaf_paths):
            raise ValueError(f"{row.orbit}: leaf module identity mismatch")
        require_repo_path(repo,path,f"{row.orbit} leaf source")
        require_file(path, entry["source_sha256"], f"{row.orbit} leaf source")
        if path.stat().st_size != entry["source_bytes"]:
            raise ValueError(f"{row.orbit}: leaf source byte count mismatch")
        if f"theorem {theorem} :" not in path.read_text():
            raise ValueError(f"{row.orbit}: leaf source theorem mismatch")
        seen_leaf_paths.add(path)
        leaf_paths.append(path)
    receipt_core = {
        "aggregate_layout_path": str(layout_path), "aggregate_layout_sha256": layout_sha256,
        "aggregate_source_root": str(aggregate_root),
        "aggregate_sources_identity_sha256": hashlib.sha256(canonical(aggregate_identities)).hexdigest(),
        "capacity_index_path": str(index_path), "capacity_index_sha256": index_sha256,
        "capacity_reindex_receipt_path": str(reindex_path),
        "capacity_reindex_receipt_sha256": reindex_sha256,
        "input_top_module": top["module"], "input_top_path": str(aggregate_root / top["file"]),
        "input_top_repo_path":str((aggregate_root/top["file"]).relative_to(repo)),
        "input_top_sha256": top["source_sha256"], "input_top_theorem": INPUT_THEOREM,
        "leaf_count": len(rows), "leaf_module_index_path": str(leaf_index_path),
        "leaf_module_index_sha256": leaf_index_sha256,
        "repo":str(repo),
    }
    return render(top["module"]), receipt_core, [layout_path, index_path, inventory_path,
                                                   *source_index_paths, reindex_path,
                                                   leaf_index_path, *aggregate_paths, *leaf_paths]


def publish(repo: Path, output: Path, source: str, receipt_core: dict,
            captured: dict[str, str]) -> None:
    expected = repo / SOURCE_REPO_PATH
    receipt_path = Path(str(output) + ".receipt.json")
    if output != expected or output.is_symlink() or output.exists() or receipt_path.exists() or receipt_path.is_symlink():
        raise ValueError("output must be the absent canonical H1 endpoint path")
    if not output.parent.is_dir() or output.parent.is_symlink():
        raise ValueError("output parent must be an existing real directory")
    if any(sha256(Path(path)) != pin for path, pin in captured.items()):
        raise ValueError("input drift before publication")
    source_raw = source.encode()
    with output.open("xb") as stream:
        stream.write(source_raw); stream.flush(); os.fsync(stream.fileno())
    if (sha256(output) != hashlib.sha256(source_raw).hexdigest()
            or any(sha256(Path(path)) != pin for path, pin in captured.items())):
        raise ValueError("input drift before receipt")
    receipt = {**receipt_core,
        "generator_sha256": captured[str(Path(__file__).resolve())],
        "generator_source": "research/problems/erdos-85-wip-01/sat49/generate_h1_post_aggregate_adapter.py",
        "output_bytes": len(source_raw), "output_path": str(output),
        "output_sha256": hashlib.sha256(source_raw).hexdigest(),
        "output_source_module": SOURCE_MODULE, "output_theorem": OUTPUT_THEOREM,
        "schema": SCHEMA}
    with receipt_path.open("xb") as stream:
        stream.write(canonical(receipt)); stream.flush(); os.fsync(stream.fileno())
    descriptor = os.open(output.parent, os.O_RDONLY)
    try: os.fsync(descriptor)
    finally: os.close(descriptor)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--aggregate-layout", type=Path, required=True)
    parser.add_argument("--aggregate-layout-sha256", required=True)
    parser.add_argument("--aggregate-source-root", type=Path, required=True)
    parser.add_argument("--capacity-index", type=Path, required=True)
    parser.add_argument("--capacity-index-sha256", required=True)
    parser.add_argument("--capacity-reindex-receipt", type=Path, required=True)
    parser.add_argument("--capacity-reindex-receipt-sha256", required=True)
    parser.add_argument("--leaf-module-index", type=Path, required=True)
    parser.add_argument("--leaf-module-index-sha256", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    source, core, paths = validate(args.repo, args.aggregate_layout,
        args.aggregate_layout_sha256, args.aggregate_source_root, args.capacity_index,
        args.capacity_index_sha256, args.capacity_reindex_receipt,
        args.capacity_reindex_receipt_sha256, args.leaf_module_index,
        args.leaf_module_index_sha256)
    captured = {str(path.resolve()): sha256(path) for path in [Path(__file__), *paths]}
    publish(args.repo, args.output, source, core, captured)
    print(f"WROTE {args.output} leaf_count=13351")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
