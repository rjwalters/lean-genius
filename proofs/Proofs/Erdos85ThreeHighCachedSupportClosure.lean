import Proofs.Erdos85ThreeHighSeparatedJointSearch

namespace Erdos85

abbrev ThreeHighTripleTable := Vector (List (Finset (Fin 24))) 3

private theorem tripleTable_get_ofFn (D : Fin 3 → List (Finset (Fin 24))) :
    (Vector.ofFn D).get = D := by
  funext i
  simp

/-- Return a concrete table, so compilation cannot defer its construction to lookup. -/
def threeHighSupportTableUntilStable (B : Fin 24 → Fin 24 → Bool) :
    Nat → ThreeHighTripleTable → ThreeHighTripleTable
  | 0, D => D
  | n+1, D =>
    let E := Vector.ofFn (threeHighTripleSupportPass B D.get)
    if E.get = D.get then D else threeHighSupportTableUntilStable B n E

theorem threeHighSupportTableUntilStable_eq (B : Fin 24 → Fin 24 → Bool)
    (n : Nat) (D : ThreeHighTripleTable) :
    (threeHighSupportTableUntilStable B n D).get =
      threeHighTripleSupportUntilStable B n D.get := by
  induction n generalizing D with
  | zero => rfl
  | succ n ih =>
    simp only [threeHighSupportTableUntilStable, threeHighTripleSupportUntilStable,
      tripleTable_get_ofFn]
    by_cases h : threeHighTripleSupportPass B D.get = D.get
    · simp only [h, ite_true]
    · simp only [h, ite_false, ih, tripleTable_get_ofFn]

def threeHighSupportTableClosure (B : Fin 24 → Fin 24 → Bool)
    (D : Fin 3 → List (Finset (Fin 24))) : ThreeHighTripleTable :=
  let initial := Vector.ofFn D
  threeHighSupportTableUntilStable B (threeHighTripleSupportSize initial.get) initial

theorem threeHighSupportTableClosure_eq (B : Fin 24 → Fin 24 → Bool)
    (D : Fin 3 → List (Finset (Fin 24))) :
    (threeHighSupportTableClosure B D).get = threeHighTripleSupportClosure B D := by
  simp only [threeHighSupportTableClosure, threeHighSupportTableUntilStable_eq,
    tripleTable_get_ofFn, threeHighTripleSupportClosure]

/-- Store adjacency and domain tables as values inside the Boolean search. -/
def threeHighCachedSeparatedJointSearch (B : Fin 24 → Fin 24 → Bool) : Bool :=
  let adjacency := Vector.ofFn (fun i => Vector.ofFn (B i))
  let cachedB := fun i j => (adjacency.get i).get j
  let table := threeHighSupportTableClosure cachedB
    (fun k => (threeHighCanonicalTripleShapes k).filter (threeHighTripleNoCommonNeighbor cachedB))
  let D := table.get
  threeHighListedCoverGate D threeHighCanonicalResidual &&
    ((List.finRange 3).all (fun k => threeHighSeparatedGate (D k) (threeHighCanonicalResidual k))) &&
    threeHighListedJointSearch cachedB D threeHighCanonicalResidual

theorem threeHighCachedSeparatedJointSearch_eq (B : Fin 24 → Fin 24 → Bool) :
    threeHighCachedSeparatedJointSearch B = threeHighSeparatedJointSearch B := by
  have hb : (fun i j => ((Vector.ofFn (fun i => Vector.ofFn (B i))).get i).get j) = B := by
    funext i j
    simp
  simp only [threeHighCachedSeparatedJointSearch, hb, threeHighSupportTableClosure_eq,
    threeHighSeparatedJointSearch]

theorem threeHighCachedSeparatedJointSearch_sound :
    ThreeHighTerminalSound threeHighCachedSeparatedJointSearch := by
  intro B h
  rw [threeHighCachedSeparatedJointSearch_eq]
  exact threeHighSeparatedJointSearch_sound B h

end Erdos85
#print axioms Erdos85.threeHighSupportTableUntilStable_eq
#print axioms Erdos85.threeHighSupportTableClosure_eq
#print axioms Erdos85.threeHighCachedSeparatedJointSearch_eq
#print axioms Erdos85.threeHighCachedSeparatedJointSearch_sound
