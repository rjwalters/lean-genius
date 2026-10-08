"""Prepare four varied H3 timing inputs without running Lean or finite searches.

Reconstructs the current literal census set operations and representative tables.
The generated Lean membership/identity checks remain unverified until compiled.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re

PACKAGE = Path(__file__).resolve().parent
RESEARCH = PACKAGE.parent
REPO = RESEARCH.parents[2]
SELECTION = [("full", 3, 3), ("full", 54, 20),
             ("deficient", 26, 2), ("deficient", 369, 11)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    provenance = {}

    def read(path):
        provenance[str(path.relative_to(REPO))] = hashlib.sha256(path.read_bytes()).hexdigest()
        return path.read_text()

    def literal(text, name, vector=False):
        pattern = r"!\[([\d,\s]+)\]" if vector else r"\{([\d,\s]+)\}"
        match = re.search(r"^def " + name + r"\b[^\n]*:=\s*" + pattern, text, re.M)
        if not match:
            raise ValueError(f"No supported literal definition: {name}")
        return [int(x) for x in match[1].split(",") if x.strip()]

    def formula(text, name, expected):
        match = re.search(r"^def " + name + r"\b.*?:=\s*(.*?)(?=\n(?:theorem|def)\b)", text, re.M | re.S)
        if not match or "".join(match[1].split()) != "".join(expected.split()):
            raise ValueError(f"Census formula changed: {name}")

    full = read(RESEARCH / "full_orbit_pruning/Pruning.lean")
    blocks = read(RESEARCH / "full_block_orbits/Certificate.lean")
    block_pruning = read(RESEARCH / "full_block_pruning/Reduction.lean")
    terminal = read(RESEARCH / "full_terminal_pruning/TerminalReduction.lean")
    capacity = read(RESEARCH / "full_capacity_pruning/CapacityReduction.lean")
    subset = read(RESEARCH / "full_subset_capacity/SubsetCapacityBatch.lean")
    deficient = read(RESEARCH / "deficient_orbit_pruning/Pruning.lean")
    degrees = read(REPO / "proofs/Proofs/Erdos85ThreeHighSecondaryDegreeClasses.lean")
    codes = {n: set(map(int, re.search(r"threeHighSecondaryDegreeCodes " + str(n) +
             r" = \{([^}]+)\}", degrees)[1].split(","))) for n in (6, 8)}
    formula(full, "remainingPairs", r"((Finset.univ \ triangleCodes).product (threeHighSecondaryDegreeCodes 8)) \ (farColorCodes.product farRCodes)")
    formula(block_pruning, "remainingPairs", "FullUOrbitPruning.remainingPairs.filter (fun rq => rq.1 ∈ FullUBlockOrbits.targets)")
    formula(terminal, "remainingPairs", "FullUBlockPruning.remainingPairs.erase (1,14)")
    formula(capacity, "remainingPairs", r"(FullTerminalPruning.remainingPairs \ SubsetCapacityBatch.pairs).erase (32,14)")
    formula(subset, "pairs", "Finset.univ.image pair")
    formula(deficient, "excludedCodes", "lowCodes ∪ triangleCodes ∪ pairCodes ∪ externalCodes")
    formula(deficient, "conditionalCodes", "farCodes ∪ adjacentCodes ∪ signedCodes")
    formula(deficient, "remainingPairs", r"((Finset.univ \ excludedCodes).product (threeHighSecondaryDegreeCodes 6)) \ (conditionalCodes.product farRCodes)")
    full_pairs = {(r, q) for r in range(55) for q in codes[8]
                  if r not in literal(full, "triangleCodes") and not
                  (r in literal(full, "farColorCodes") and q in literal(full, "farRCodes"))}
    assert len(full_pairs) == 565
    targets = set(literal(blocks, "targets"))
    assert targets == set(literal(blocks, "target", True))
    full_pairs = {p for p in full_pairs if p[0] in targets}
    assert len(full_pairs) == 276
    removed = {tuple(map(int, p)) for p in re.findall(r"\((\d+),(\d+)\)",
               re.search(r"^def pair .*:= !\[(.*)\]$", subset, re.M)[1])}
    assert len(removed) == 13
    full_pairs -= removed | {(1, 14), (32, 14)}
    assert len(full_pairs) == 261
    excluded = set().union(*(literal(deficient, x + "Map", True)
                            for x in ("low", "triangle", "pair", "external")))
    conditional = set().union(*(literal(deficient, x + "Map", True)
                               for x in ("far", "adjacent", "signed")))
    for x in ("low", "triangle", "pair", "external", "far", "adjacent", "signed"):
        formula(deficient, x + "Codes", "Finset.univ.image " + x + "Map")
    deficient_pairs = {(r, q) for r in range(370) for q in codes[6]
                       if r not in excluded and not
                       (r in conditional and q in literal(deficient, "farRCodes"))}
    assert len(deficient_pairs) == 1554
    tables = {}
    for branch, file, size in (("full", "Full_3_3", 55), ("deficient", "Deficient_3_3_0", 370)):
        text = read(RESEARCH / f"compact_u_orbits/{branch}_coverage/{file}.lean")
        names = ["repA", "repB", "repP"] + (["repD"] if branch == "deficient" else [])
        columns = [literal(text, n, True) for n in names]
        assert all(len(c) == size for c in columns)
        tables[branch] = list(zip(*columns))
    secondary = read(REPO / "proofs/Proofs/Erdos85ThreeHighSecondaryOrbitTable.lean")
    secondary_codes = re.findall(r"threeHighSecondaryCode (\d+) (\d+) (\d+) (true|false)", secondary)
    assert len(secondary_codes) == 21
    files, cases = {}, []
    memberships = {b: [] for b in ("full", "deficient")}
    for branch, r, q in SELECTION:
        assert (r, q) in (full_pairs if branch == "full" else deficient_pairs)
        code = tables[branch][r]
        tag = f"{branch.title()}U{r}R{q}"
        module = "Erdos85ThreeHighPilot" + tag
        ns = "Erdos85.VariedPilot." + tag
        if branch == "full":
            union = f"threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode {' '.join(map(str, code))}))"
        else:
            union = f"threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed (threeBlockDeficientCompactCode {' '.join(map(str, code))}))"
        files[module + "Inputs.lean"] = f"""import Proofs.Erdos85ThreeBlockCompactCodes
import Proofs.Erdos85ThreeHighSecondaryOrbitTable
import Proofs.Erdos85ThreeHighNativePairSearch

namespace {ns}
open Erdos85
def U : Fin 15 → Fin 15 → Bool := {union}
def R : Fin 8 → Fin 8 → Bool :=
  threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative {q})
end {ns}
"""
        files[module + "Certificate.lean"] = f"""import Proofs.{module}Inputs

/-! Unverified timing-sample rejection; no stratum exclusion. -/
namespace {ns}
open Erdos85
set_option maxRecDepth 100000 in
theorem rejected : threeHighNativePairSearch U R = false := by native_decide
end {ns}
#print axioms {ns}.rejected
"""
        files[module + "Consumer.lean"] = f"""import Proofs.{module}Certificate

namespace {ns}
open Erdos85
attribute [local irreducible] threeHighCrossDomain
theorem no_joint (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain U R)
    (he : encodedExternalBlockCap (threeHighEmptyAdj U R cross)
      threeHighCanonicalRow = true) :
    ¬ ThreeHighDistinctJointWitness (threeHighEmptyAdj U R cross) :=
  threeHighNativePairSearch_no_joint U R rejected cross hc he
end {ns}
#print axioms {ns}.no_joint
"""
        representative = "FullURestrictedAssembly.representative" if branch == "full" else "DeficientUOrbitPruning.representative"
        census = "FullCapacityPruning.remainingPairs" if branch == "full" else "DeficientUOrbitPruning.remainingPairs"
        membership_defs = (
            "FullCapacityPruning.remainingPairs, FullTerminalPruning.remainingPairs, "
            "FullUBlockPruning.remainingPairs, FullUOrbitPruning.remainingPairs"
            if branch == "full" else "DeficientUOrbitPruning.remainingPairs")
        memberships[branch].append((module, f"""theorem {tag}_mem : ({r},{q}) ∈ {census} := by
  simp only [{membership_defs}, Finset.mem_erase, Finset.mem_sdiff,
    Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
  decide
theorem {tag}_input : {representative} {r} = {ns}.U := by rfl
#print axioms {tag}_mem
#print axioms {tag}_input
"""))
        cases.append({"branch": branch, "u_index": r, "r_index": q, "compact_code": list(code),
                      "secondary_code": list(secondary_codes[q]), "module_prefix": module,
                      "namespace": ns, "source_census_member": True})
    for branch, entries in memberships.items():
        files[branch.title() + "Membership.lean"] = (
            "import " + ("CapacityReduction" if branch == "full" else "Pruning") + "\n" +
            "".join(f"import Proofs.{m}Inputs\n" for m, _ in entries) +
            "\nset_option maxRecDepth 100000\nset_option maxHeartbeats 10000000\n" +
            "\n".join(body for _, body in entries))
    manifest = {"status": "SOURCE_ONLY_NOT_COMPILED", "selection": "Diagnostic diversity, not a random or representative sample.",
                "census_counts": {"full": len(full_pairs), "deficient": len(deficient_pairs)},
                "cases": cases, "input_source_sha256": provenance,
                "generated_source_sha256": {n: hashlib.sha256(s.encode()).hexdigest() for n, s in files.items()}}
    if args.write:
        for name, text in files.items():
            (PACKAGE / name).write_text(text)
        (PACKAGE / "PLAN.json").write_text(json.dumps(manifest, indent=2) + "\n")
    else:
        for name, text in files.items():
            assert (PACKAGE / name).read_text() == text, name
        assert json.loads((PACKAGE / "PLAN.json").read_text()) == manifest
    print(json.dumps({"status": manifest["status"], "cases": cases, "generated_modules": len(files)}, indent=2))


if __name__ == "__main__":
    main()
