"""Small metadata inventory and deterministic Lean source emitter; no search."""
import hashlib
from pathlib import Path
import re
PACKAGE = Path(__file__).resolve().parent
RESEARCH = PACKAGE.parent
REPO = RESEARCH.parents[2]


def inventory():
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
    return {"full": sorted(full_pairs), "deficient": sorted(deficient_pairs)}, tables, secondary_codes, provenance


def case(branch, u, r, code, secondary):
    tag = f"{branch.title()}U{u}R{r}"
    return {"id": f"{branch}-u{u:03d}-r{r:02d}", "branch": branch,
            "u_index": u, "r_index": r, "compact_code": list(code),
            "secondary_code": list(secondary), "tag": tag,
            "namespace": "Erdos85.TripleCampaign." + tag,
            "module_prefix": "Erdos85ThreeHighCampaign" + tag}


def sources(c):
    branch, u, r = c['branch'], c['u_index'], c['r_index']
    ns, module = c['namespace'], c['module_prefix']
    code = ' '.join(map(str, c['compact_code']))
    union = (f'threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode {code}))'
             if branch == 'full' else f'threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed (threeBlockDeficientCompactCode {code}))')
    representative = 'FullURestrictedAssembly.representative' if branch == 'full' else 'DeficientUNormalizedAssembly.representative'
    census = 'FullCapacityPruning.remainingPairs' if branch == 'full' else 'DeficientUOrbitPruning.remainingPairs'
    definitions = ('FullCapacityPruning.remainingPairs, FullTerminalPruning.remainingPairs, FullUBlockPruning.remainingPairs, FullUOrbitPruning.remainingPairs'
                   if branch == 'full' else 'DeficientUOrbitPruning.remainingPairs')
    census_import = 'CapacityReduction' if branch == 'full' else 'Pruning'
    inputs = f"""import Proofs.Erdos85ThreeBlockCompactCodes
import Proofs.Erdos85ThreeHighSecondaryOrbitTable
import Proofs.Erdos85ThreeHighNativePairSearch
namespace {ns}
open Erdos85
def U : Fin 15 → Fin 15 → Bool := {union}
def R : Fin 8 → Fin 8 → Bool :=
  threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative {r})
end {ns}
"""
    membership = f"""import {census_import}
import Proofs.{module}Inputs
namespace {ns}
open Erdos85
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem member : ({u},{r}) ∈ {census} := by
  simp only [{definitions}, Finset.mem_erase, Finset.mem_sdiff,
    Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
  decide
theorem input_identity : {representative} {u} = U := by rfl
#print axioms {ns}.member
#print axioms {ns}.input_identity
end {ns}
"""
    certificate = f"""import Proofs.{module}Inputs
namespace {ns}
open Erdos85
set_option maxRecDepth 100000 in
theorem rejected : threeHighNativePairSearch U R = false := by native_decide
end {ns}
#print axioms {ns}.rejected
"""
    consumer = f"""import {module}Membership
import Proofs.{module}Certificate
namespace {ns}
open Erdos85
attribute [local irreducible] threeHighCrossDomain
theorem representative_rejected :
    threeHighNativePairSearch ({representative} {u})
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative {r})) = false := by
  rw [input_identity]
  exact rejected
theorem no_joint (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain ({representative} {u})
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative {r})))
    (he : encodedExternalBlockCap (threeHighEmptyAdj ({representative} {u})
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative {r})) cross)
      threeHighCanonicalRow = true) :
    ¬ ThreeHighDistinctJointWitness (threeHighEmptyAdj ({representative} {u})
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative {r})) cross) :=
  threeHighNativePairSearch_no_joint _ _ representative_rejected cross hc he
end {ns}
#print axioms {ns}.representative_rejected
#print axioms {ns}.no_joint
"""
    return {module + suffix + '.lean': text for suffix, text in
            [('Inputs', inputs), ('Membership', membership), ('Certificate', certificate), ('Consumer', consumer)]}


def source_hashes(c):
    return {name: hashlib.sha256(text.encode()).hexdigest() for name, text in sources(c).items()}
