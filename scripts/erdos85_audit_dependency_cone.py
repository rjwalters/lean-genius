#!/usr/bin/env python3
"""Audit the exact Lean declaration cone of an Erdős-85 drop theorem.

The driver asks Lean itself for the transitive declaration graph, restricts the
reported theorem inventory to project ``Proofs.*`` modules, emits literal
``#print axioms`` commands for every theorem, and checks all transitive axioms
and direct native-decision roots against a reviewed JSON allowlist.

No default target is provided deliberately: the final composed drop theorem
does not exist yet, and silently auditing an older conditional socket would be
the wrong completion gate.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from datetime import datetime, timezone


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PROOFS = ROOT / "proofs"
DEFAULT_ALLOWLIST = (
    ROOT / "research/problems/erdos-85-wip-01/drop_axiom_allowlist.json"
)


@dataclass(frozen=True)
class ConeTheorem:
    name: str
    module: str
    direct_axioms: tuple[str, ...]
    transitive_axioms: tuple[str, ...]


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def run_lean(proofs_dir: Path, source: str) -> subprocess.CompletedProcess[str]:
    # The temporary source must live below the Lake package root so imports and
    # path diagnostics have the same semantics as a checked-in audit module.
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", prefix="erdos85-cone-", dir=proofs_dir,
        encoding="utf-8", delete=False
    ) as handle:
        handle.write(source)
        temp_path = Path(handle.name)
    try:
        return subprocess.run(
            ["lake", "env", "lean", str(temp_path)],
            cwd=proofs_dir,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
    finally:
        temp_path.unlink(missing_ok=True)


def build_audit_helper(proofs_dir: Path) -> None:
    result = subprocess.run(
        ["lake", "build", "Proofs.Erdos85DependencyConeAudit"],
        cwd=proofs_dir,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if result.returncode != 0:
        raise RuntimeError(f"audit input build failed (rc={result.returncode})\n{result.stdout}")


def discover(proofs_dir: Path, module: str, target: str) -> tuple[list[ConeTheorem], str]:
    source = (
        f"import {module}\n"
        "import Proofs.Erdos85DependencyConeAudit\n\n"
        f"#erdos85_dependency_cone {target}\n"
    )
    result = run_lean(proofs_dir, source)
    if result.returncode != 0:
        raise RuntimeError(f"dependency discovery failed (rc={result.returncode})\n{result.stdout}")
    theorems: list[ConeTheorem] = []
    summary_seen = False
    for line in result.stdout.splitlines():
        if line.startswith("ERDOS85_CONE\t"):
            fields = line.split("\t")
            if len(fields) != 5:
                raise RuntimeError(f"malformed discovery line: {line}")
            direct = tuple(filter(None, fields[3].split(",")))
            transitive = tuple(filter(None, fields[4].split(",")))
            theorems.append(ConeTheorem(fields[1], fields[2], direct, transitive))
        elif line.startswith("ERDOS85_CONE_SUMMARY\t"):
            summary_seen = True
    if not summary_seen or not theorems:
        raise RuntimeError(f"Lean returned no dependency inventory\n{result.stdout}")
    unique = {theorem.name: theorem for theorem in theorems}
    if len(unique) != len(theorems):
        raise RuntimeError("Lean dependency inventory contains duplicate theorem names")
    return sorted(theorems, key=lambda theorem: theorem.name), result.stdout


def render_axiom_source(module: str, theorems: list[ConeTheorem]) -> str:
    lines = [f"import {module}", ""]
    for theorem in theorems:
        # Delimiters make the captured output attributable while leaving the
        # actual `#print axioms` output byte-for-byte as Lean printed it.
        lines.append(f'#eval IO.println "ERDOS85_AXIOM_BEGIN\\t{theorem.name}"')
        lines.append(f"#print axioms {theorem.name}")
        lines.append(f'#eval IO.println "ERDOS85_AXIOM_END\\t{theorem.name}"')
    lines.append("")
    return "\n".join(lines)


def load_allowlist(path: Path) -> dict:
    data = json.loads(path.read_text(encoding="utf-8"))
    required = {
        "schema", "allowed_axioms", "native_axiom_regex", "native_families"
    }
    missing = sorted(required - data.keys())
    if missing:
        raise ValueError(f"allowlist missing keys: {', '.join(missing)}")
    if data["schema"] != 1:
        raise ValueError(f"unsupported allowlist schema {data['schema']!r}")
    re.compile(data["native_axiom_regex"])
    for family in data["native_families"]:
        if not {"id", "module_regex", "declaration_regex"} <= family.keys():
            raise ValueError(f"malformed native family: {family!r}")
        re.compile(family["module_regex"])
        re.compile(family["declaration_regex"])
    return data


def classify_native_root(theorem: ConeTheorem, families: list[dict]) -> str | None:
    matches = [
        family["id"]
        for family in families
        if re.fullmatch(family["module_regex"], theorem.module)
        and re.fullmatch(family["declaration_regex"], theorem.name)
    ]
    if len(matches) > 1:
        raise ValueError(f"native root {theorem.name} matches multiple families: {matches}")
    return matches[0] if matches else None


def validate(theorems: list[ConeTheorem], allowlist: dict) -> tuple[list[dict], list[str]]:
    allowed_axioms = set(allowlist["allowed_axioms"])
    native_axiom = re.compile(allowlist["native_axiom_regex"])
    errors: list[str] = []
    roots: list[dict] = []
    for theorem in theorems:
        unexpected = sorted(
            axiom for axiom in set(theorem.transitive_axioms)
            if axiom not in allowed_axioms and native_axiom.fullmatch(axiom) is None
        )
        if unexpected:
            errors.append(f"{theorem.name}: unexpected axioms {unexpected}")
        for direct_axiom in theorem.direct_axioms:
            if native_axiom.fullmatch(direct_axiom) is None:
                continue
            family = classify_native_root(theorem, allowlist["native_families"])
            if family is None:
                errors.append(
                    f"{theorem.name}: direct native root {direct_axiom} "
                    "is not in a disclosed family"
                )
            roots.append(
                {
                    "theorem": theorem.name,
                    "module": theorem.module,
                    "axiom": direct_axiom,
                    "family": family,
                }
            )
    return roots, errors


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--module", required=True, help="Lean module importing the target")
    parser.add_argument("--target", required=True, help="fully-qualified final theorem name")
    parser.add_argument("--proofs-dir", type=Path, default=DEFAULT_PROOFS)
    parser.add_argument("--allowlist", type=Path, default=DEFAULT_ALLOWLIST)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument(
        "--inventory-only", action="store_true",
        help="discover and validate the cone but skip the literal #print axioms pass",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    proofs_dir = args.proofs_dir.resolve()
    allowlist_path = args.allowlist.resolve()
    output_dir = args.output_dir.resolve()
    if not (proofs_dir / "lakefile.toml").is_file():
        print(f"error: not a Lean package: {proofs_dir}", file=sys.stderr)
        return 2
    try:
        allowlist = load_allowlist(allowlist_path)
        # The final target must already have passed the independent clean build
        # gate.  Rebuilding it here would conflate that gate with the audit and
        # can mask which artifact failed.  We build only the small audit helper.
        build_audit_helper(proofs_dir)
        theorems, discovery_log = discover(proofs_dir, args.module, args.target)
        native_roots, errors = validate(theorems, allowlist)
    except (OSError, ValueError, RuntimeError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2

    output_dir.mkdir(parents=True, exist_ok=True)
    discovery_path = output_dir / "dependency-cone.log"
    discovery_path.write_text(discovery_log, encoding="utf-8")
    inventory_path = output_dir / "dependency-cone.json"
    inventory = {
        "schema": 1,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "git_commit": subprocess.run(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True,
            stdout=subprocess.PIPE, check=True
        ).stdout.strip(),
        "module": args.module,
        "target": args.target,
        "allowlist_path": str(allowlist_path.relative_to(ROOT)),
        "allowlist_sha256": sha256(allowlist_path),
        "theorem_count": len(theorems),
        "native_roots": native_roots,
        "theorems": [theorem.__dict__ for theorem in theorems],
    }
    inventory_path.write_text(json.dumps(inventory, indent=2) + "\n", encoding="utf-8")

    axiom_log_path: Path | None = None
    if not args.inventory_only:
        result = run_lean(proofs_dir, render_axiom_source(args.module, theorems))
        axiom_log_path = output_dir / "print-axioms.log"
        axiom_log_path.write_text(result.stdout, encoding="utf-8")
        if result.returncode != 0:
            errors.append(f"literal #print axioms pass failed with rc={result.returncode}")
        begin_count = result.stdout.count("ERDOS85_AXIOM_BEGIN\t")
        end_count = result.stdout.count("ERDOS85_AXIOM_END\t")
        if begin_count != len(theorems) or end_count != len(theorems):
            errors.append(
                "literal output delimiter mismatch: "
                f"begin={begin_count}, end={end_count}, expected={len(theorems)}"
            )

    receipt = {
        "schema": 1,
        "status": "PASS" if not errors else "FAIL",
        "target": args.target,
        "theorem_count": len(theorems),
        "native_root_count": len(native_roots),
        "native_family_counts": {
            family["id"]: sum(root["family"] == family["id"] for root in native_roots)
            for family in allowlist["native_families"]
        },
        "errors": errors,
        "artifacts": {
            "dependency_cone": inventory_path.name,
            "dependency_cone_sha256": sha256(inventory_path),
            "discovery_log": discovery_path.name,
            "discovery_log_sha256": sha256(discovery_path),
            "print_axioms_log": axiom_log_path.name if axiom_log_path else None,
            "print_axioms_log_sha256": sha256(axiom_log_path) if axiom_log_path else None,
        },
    }
    (output_dir / "audit-receipt.json").write_text(
        json.dumps(receipt, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(receipt, indent=2))
    return 0 if not errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
