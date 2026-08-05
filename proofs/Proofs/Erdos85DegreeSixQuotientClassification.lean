import Proofs.Erdos85SecondOrderQuotient

/-!
# Certified degree-six component-quotient classification

This file mirrors the exact finite backtracking search in
`degree6_quotient_classification.py`.  All search spaces are generated inside
Lean; `native_decide` is therefore only an evaluator for a closed decidable
proposition, not a trusted external certificate.
-/

namespace Erdos85
namespace DegreeSixQuotient

abbrev Row := List Nat
abbrev Quotient := List Row
abbrev Candidate := List Nat × Quotient × List Nat

/-- Weak compositions of `total` into exactly `parts` entries. -/
def weakCompositions : (parts total : Nat) → List Row
  | 0, total => if total = 0 then [[]] else []
  | parts + 1, total =>
      (List.range (total + 1)).flatMap fun x =>
        (weakCompositions parts (total - x)).map (x :: ·)

theorem mem_weakCompositions_iff {parts total : Nat} {xs : Row} :
    xs ∈ weakCompositions parts total ↔
      xs.length = parts ∧ xs.sum = total := by
  induction parts generalizing total xs with
  | zero =>
      constructor
      · intro h
        simp [weakCompositions] at h
        rcases h with ⟨rfl, rfl⟩
        simp
      · intro h
        have hx : xs = [] := List.length_eq_zero_iff.mp h.1
        subst xs
        have ht : total = 0 := by simpa using h.2.symm
        subst total
        simp [weakCompositions]
  | succ parts ih =>
      simp only [weakCompositions, List.mem_flatMap, List.mem_range,
        List.mem_map]
      constructor
      · rintro ⟨x, hx, tail, htail, rfl⟩
        have ht := (ih.mp htail)
        simp only [List.length_cons, List.sum_cons]
        constructor
        · omega
        · omega
      · intro h
        cases xs with
        | nil => simp at h
        | cons x tail =>
            simp only [List.length_cons, List.sum_cons] at h
            have hx : x < total + 1 := by omega
            refine ⟨x, hx, tail, ih.mpr ?_, rfl⟩
            constructor <;> omega

/-- Nondecreasing partitions of `total` into `parts` entries, each at least
`lower`. -/
def partitionsAux : (parts total lower : Nat) → List (List Nat)
  | 0, total, _ => if total = 0 then [[]] else []
  | parts + 1, total, lower =>
      (List.range (total + 1)).filter (fun x =>
        lower ≤ x) |>.flatMap fun x =>
          (partitionsAux parts (total - x) x).map (x :: ·)

theorem mem_partitionsAux_iff {parts total lower : Nat} {xs : List Nat} :
    xs ∈ partitionsAux parts total lower ↔
      xs.length = parts ∧ xs.sum = total ∧
        (∀ x ∈ xs, lower ≤ x) ∧ xs.Pairwise (· ≤ ·) := by
  induction parts generalizing total lower xs with
  | zero =>
      constructor
      · intro h
        simp [partitionsAux] at h
        rcases h with ⟨rfl, rfl⟩
        simp
      · intro h
        have hx : xs = [] := List.length_eq_zero_iff.mp h.1
        subst xs
        have ht : total = 0 := by simpa using h.2.1.symm
        subst total
        simp [partitionsAux]
  | succ parts ih =>
      simp only [partitionsAux, List.mem_flatMap, List.mem_filter,
        List.mem_range, decide_eq_true_eq, List.mem_map]
      constructor
      · rintro ⟨x, ⟨hxrange, hxlower⟩, tail, htail, rfl⟩
        have ht := ih.mp htail
        simp only [List.length_cons, List.sum_cons, List.pairwise_cons]
        refine ⟨by omega, by omega, ?_, ⟨ht.2.2.1, ht.2.2.2⟩⟩
        intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact hxlower
        · exact le_trans hxlower (ht.2.2.1 y hy)
      · intro h
        cases xs with
        | nil => simp at h
        | cons x tail =>
            simp only [List.length_cons, List.sum_cons,
              List.pairwise_cons] at h
            have hxrange : x < total + 1 := by omega
            have hxlower : lower ≤ x := h.2.2.1 x (by simp)
            refine ⟨x, ⟨hxrange, hxlower⟩, tail, ih.mpr ?_, rfl⟩
            refine ⟨by omega, by omega, ?_, h.2.2.2.2⟩
            intro y hy
            exact h.2.2.2.1 y hy

def componentPartitions (count : Nat) : List (List Nat) :=
  partitionsAux count 33 3

def reverseEntry (lengths row : List Nat) (i j : Nat) : Nat :=
  lengths.getD i 0 * row.getD j 0 / lengths.getD j 1

def rowAdmissible (lengths : List Nat) (i : Nat) (row : Row) : Bool :=
  let k := lengths.length
  row.length = k && row.sum = 6 &&
    (List.range k).all (fun j =>
      lengths.getD j 0 ∣ lengths.getD i 0 * row.getD j 0) &&
    ((List.range k).map (fun j =>
      row.getD j 0 * reverseEntry lengths row i j)).sum =
      lengths.getD i 0 + 3

def rowDomain (lengths : List Nat) (i : Nat) : List Row :=
  (weakCompositions lengths.length 6).filter (rowAdmissible lengths i)

theorem mem_rowDomain_iff {lengths row : List Nat} {i : Nat} :
    row ∈ rowDomain lengths i ↔
      row.length = lengths.length ∧ row.sum = 6 ∧
        rowAdmissible lengths i row := by
  rw [rowDomain, List.mem_filter, mem_weakCompositions_iff]
  aesop

def lookupRow (chosen : List (Nat × Row)) (i : Nat) : Row :=
  (chosen.find? (fun p => p.1 = i)).map (fun p => p.2) |>.getD []

def compatibleWithChosen (lengths : List Nat) (i : Nat) (row : Row)
    (chosen : List (Nat × Row)) : Bool :=
  chosen.all fun p =>
    lengths.getD i 0 * row.getD p.1 0 =
      lengths.getD p.1 0 * p.2.getD i 0

def assembleMatrix (k : Nat) (chosen : List (Nat × Row)) : Quotient :=
  (List.range k).map (lookupRow chosen)

def squareEntry (q : Quotient) (i j : Nat) : Nat :=
  (List.range q.length).map (fun t =>
    (q.getD i []).getD t 0 * (q.getD t []).getD j 0) |>.sum

def offDiagonalSquareOK (lengths : List Nat) (q : Quotient) : Bool :=
  (List.range lengths.length).all fun i =>
    (List.range lengths.length).all fun j =>
      i = j || squareEntry q i j = lengths.getD j 0

/-- Backtracking over row domains, ordered by increasing domain size. -/
def chooseRows (lengths : List Nat) :
    List (Nat × List Row) → List (Nat × Row) → Nat → List Quotient
  | [], chosen, diagonalTrace =>
      if diagonalTrace = 6 then
        let q := assembleMatrix lengths.length chosen
        if offDiagonalSquareOK lengths q then [q] else []
      else []
  | (i, domain) :: rest, chosen, diagonalTrace =>
      domain.flatMap fun row =>
        let nextTrace := diagonalTrace + row.getD i 0
        if nextTrace ≤ 6 && compatibleWithChosen lengths i row chosen then
          chooseRows lengths rest ((i, row) :: chosen) nextTrace
        else []

def quotientMatrices (lengths : List Nat) : List Quotient :=
  let indexed := (List.range lengths.length).map fun i => (i, rowDomain lengths i)
  chooseRows lengths indexed [] 0

def handshakeParityOK (lengths : List Nat) (q : Quotient) : Bool :=
  (List.range lengths.length).all fun i =>
    (lengths.getD i 0 * (q.getD i []).getD i 0) % 2 = 0

def colorMaskAdmissible (lengths : List Nat) (q : Quotient)
    (mask : Nat) : Bool :=
  let coloredOrder := (List.range lengths.length).map (fun i =>
    if mask.testBit i then lengths.getD i 0 else 0) |>.sum
  coloredOrder % 3 = 0 &&
    (List.range lengths.length).all (fun i =>
      !mask.testBit i ||
        (5 ≤ lengths.getD i 0 && 2 ≤ (q.getD i []).getD i 0))

/-- An antipodal defect 5-cycle cannot have internal quotient degree two:
the forced complementary 5-cycle gives consecutive defect vertices an
internal common neighbor. -/
def antipodalFiveLocalOK (lengths : List Nat) (q : Quotient)
    (mask : Nat) : Bool :=
  (List.range lengths.length).all fun i =>
    lengths.getD i 0 != 5 || mask.testBit i ||
      (q.getD i []).getD i 0 != 2

def admissibleColorMasks (lengths : List Nat) (q : Quotient) : List Nat :=
  if handshakeParityOK lengths q then
    (List.range (2 ^ lengths.length)).filter fun mask =>
      colorMaskAdmissible lengths q mask && antipodalFiveLocalOK lengths q mask
  else []

def cycleParityOK (lengths : List Nat) : Bool :=
  (lengths.filter fun r => r % 2 = 0).length % 2 = 0

/-- Necessary condition coming from the full block relation `AD=DA`, beyond
the constant-vector quotient equation.  A block from a cycle of order `r_i`
to one of order `r_j` has rows periodic by the target order `r_j` (reduced
modulo `r_i`).  Hence two vertices of component `i` at that separation already
have all `q_ij` target neighbors in common; the total cannot exceed one in a
`C₄`-free graph.  This target-order form already eliminates every classified
case. -/
def periodicCommonNeighborOK (lengths : List Nat) (q : Quotient) : Bool :=
  (List.range lengths.length).all fun i =>
    (List.range (lengths.getD i 0)).all fun shift =>
      shift < 2 || shift + 1 = lengths.getD i 0 ||
        (((List.range lengths.length).filter (fun j => j != i &&
            lengths.getD j 0 % lengths.getD i 1 = shift)).map
          (fun j => (q.getD i []).getD j 0)).sum ≤ 1

def classify (count : Nat) : List Candidate :=
  (componentPartitions count).filter cycleParityOK |>.flatMap fun lengths =>
    (quotientMatrices lengths).filterMap fun q =>
      let masks := admissibleColorMasks lengths q
      if masks.isEmpty then none else some (lengths, q, masks)

def classifyWithPeriodicity (count : Nat) : List Candidate :=
  (classify count).filter fun candidate =>
    periodicCommonNeighborOK candidate.1 candidate.2.1

theorem classifyWithPeriodicity_three_empty : classifyWithPeriodicity 3 = [] := by
  native_decide

theorem classifyWithPeriodicity_five_empty : classifyWithPeriodicity 5 = [] := by
  native_decide

theorem classify_three_count : (classify 3).length = 2 := by native_decide

theorem classify_one_count : (classify 1).length = 1 := by native_decide

end DegreeSixQuotient
end Erdos85
