import Proofs.Erdos85SignedSRGSAT

/-!
# Bridge from finite relations to the verified signing SAT certificate
-/

namespace Erdos85

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- Filtering a two-element finset by opposite truth values leaves exactly
one element. -/
theorem card_filter_eq_one_of_card_eq_two_of_xor
    {V : Type*} [DecidableEq V] (C : Finset V) (p : V → Prop)
    [DecidablePred p] (hcard : C.card = 2)
    (hxor : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → Xor (p u) (p v)) :
    (C.filter p).card = 1 := by
  rcases Finset.card_eq_two.mp hcard with ⟨u, v, huv, rfl⟩
  have huvxor := hxor u (by simp) v (by simp) huv
  rcases huvxor with ⟨hu, hv⟩ | ⟨hv, hu⟩
  · have heq : Finset.filter p {u, v} = {u} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hz | hz, hp⟩
        · exact hz
        · subst z
          exact (hv hp).elim
      · intro hz
        subst z
        exact ⟨Or.inl rfl, hu⟩
    rw [heq]
    simp
  · have heq : Finset.filter p {u, v} = {v} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hz | hz, hp⟩
        · subst z
          exact (hu hp).elim
        · exact hz
      · intro hz
        subst z
        exact ⟨Or.inr rfl, hv⟩
    rw [heq]
    simp

/-- Package a Boolean relation on `Fin 16` as a row-major bit matrix. -/
def matrixBV (r : Fin 16 → Fin 16 → Bool) : BitVec 256 :=
  (BitVec.ofBoolListLE (List.ofFn fun i : Fin 256 =>
    r ⟨i.val / 16, by omega⟩ ⟨i.val % 16, Nat.mod_lt _ (by omega)⟩)).cast (by
      rw [List.length_ofFn])

/-- Matrix packaging preserves every entry. -/
theorem bitAdj_matrixBV (r : Fin 16 → Fin 16 → Bool) (x y : Fin 16) :
    bitAdj256 (matrixBV r) x y = r x y := by
  simp only [bitAdj256, matrixBV, BitVec.getLsbD_cast,
    BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn]
  have hlt : x.val * 16 + y.val < 256 := by omega
  simp only [hlt, ↓reduceDIte, Option.getD_some]
  congr 2 <;> omega

/-- Looking up bit `y` of row `x` is matrix entry `(x,y)`. -/
theorem row256_getLsbD (a : BitVec 256) (x y : Fin 16) :
    (row256 a x).getLsbD y = bitAdj256 a x y := by
  simp [row256, bitAdj256]

theorem row256_matrixBV_getLsbD
    (r : Fin 16 → Fin 16 → Bool) (x y : Fin 16) :
    (row256 (matrixBV r) x).getLsbD y = r x y := by
  rw [row256_getLsbD, bitAdj_matrixBV]

/-- On a 16-bit row, population count is the cardinality of the set bits. -/
theorem cpop16_eq_filter_card : ∀ v : BitVec 16,
    v.cpop.toNat =
      (Finset.univ.filter fun i : Fin 16 => v.getLsbD i).card := by
  native_decide

/-- Relation-level form of the `(16,6,2,2)` constraints. -/
def BoolSRG1622 (a : Fin 16 → Fin 16 → Bool) : Prop :=
  (∀ x, a x x = false) ∧
  (∀ x y, a x y = a y x) ∧
  (∀ x, (Finset.univ.filter fun y => a x y).card = 6) ∧
  (∀ x y, x ≠ y →
    (Finset.univ.filter fun z => a x z && a y z).card = 2)

/-- Packaging a Boolean SRG relation produces the bit-vector SRG
constraints consumed by the SAT theorem. -/
theorem bvSRG1622_matrixBV {a : Fin 16 → Fin 16 → Bool}
    (ha : BoolSRG1622 a) : bvSRG1622 (matrixBV a) := by
  rcases ha with ⟨hloop, hsym, hdegree, hcommon⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    simpa only [bitAdj_matrixBV] using hloop x
  · intro x y
    simpa only [bitAdj_matrixBV] using hsym x y
  · intro x
    apply BitVec.eq_of_toNat_eq
    rw [cpop16_eq_filter_card]
    simp only [row256_matrixBV_getLsbD]
    simpa using hdegree x
  · intro x y hxy
    apply BitVec.eq_of_toNat_eq
    rw [cpop16_eq_filter_card]
    simp only [BitVec.getLsbD_and, row256_matrixBV_getLsbD]
    simpa using hcommon x y hxy

/-- Relation-level compact negative-signing constraints. -/
def BoolNegativeCompact1622
    (a s : Fin 16 → Fin 16 → Bool) : Prop :=
  (∀ x y, s x y = s y x) ∧
  ∀ x y, x ≠ y →
    (Finset.univ.filter fun z =>
      (a x z && a y z) && (s x z ^^ s y z)).card = 1

/-- Packaging preserves the compact negative-signing constraints. -/
theorem bvNegativeCompact1622_matrixBV
    {a s : Fin 16 → Fin 16 → Bool}
    (hneg : BoolNegativeCompact1622 a s) :
    bvNegativeCompact1622 (matrixBV a) (matrixBV s) := by
  rcases hneg with ⟨hsym, hparity⟩
  refine ⟨?_, ?_⟩
  · intro x y
    simpa only [bitAdj_matrixBV] using hsym x y
  · intro x y hxy
    apply BitVec.eq_of_toNat_eq
    rw [cpop16_eq_filter_card]
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor,
      row256_matrixBV_getLsbD]
    simpa using hparity x y hxy

/-- Relation-level consequence of the normalized SAT certificate. -/
theorem not_boolNegativeCompact1622_of_normalizedCycle
    (a s : Fin 16 → Fin 16 → Bool)
    (ha0 : row256 (matrixBV a) 0 = 0x007e)
    (hs0 : row256 (matrixBV s) 0 = 0)
    (ha12 : a 1 2 = true) (ha23 : a 2 3 = true)
    (ha34 : a 3 4 = true) (ha45 : a 4 5 = true)
    (ha56 : a 5 6 = true) (ha61 : a 6 1 = true)
    (ha : BoolSRG1622 a) :
    ¬ BoolNegativeCompact1622 a s := by
  intro hneg
  exact no_bvNegativeCompact1622_of_normalizedCycle
    (matrixBV a) (matrixBV s) ha0 hs0
    (by simpa only [bitAdj_matrixBV] using ha12)
    (by simpa only [bitAdj_matrixBV] using ha23)
    (by simpa only [bitAdj_matrixBV] using ha34)
    (by simpa only [bitAdj_matrixBV] using ha45)
    (by simpa only [bitAdj_matrixBV] using ha56)
    (by simpa only [bitAdj_matrixBV] using ha61)
    (bvSRG1622_matrixBV ha) (bvNegativeCompact1622_matrixBV hneg)

/-- Boolean adjacency matrix of a decidable graph on `Fin 16`. -/
def graphBool (H : SimpleGraph (Fin 16)) [DecidableRel H.Adj] :
    Fin 16 → Fin 16 → Bool := fun x y => decide (H.Adj x y)

/-- Boolean matrix of a decidable propositional signing. -/
def signingBool (s : Fin 16 → Fin 16 → Prop) [DecidableRel s] :
    Fin 16 → Fin 16 → Bool := fun x y => decide (s x y)

/-- The graph part of an abstract negative signing gives the Boolean SRG
constraints directly. -/
theorem boolSRG1622_graphBool
    (H : SimpleGraph (Fin 16)) [DecidableRel H.Adj]
    (hreg : ∀ x : Fin 16, H.degree x = 6)
    (hcommon : ∀ x y : Fin 16, x ≠ y →
      (H.neighborFinset x ∩ H.neighborFinset y).card = 2) :
    BoolSRG1622 (graphBool H) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    simp [graphBool]
  · intro x y
    simp only [graphBool, decide_eq_decide]
    exact H.adj_comm x y
  · intro x
    simpa [graphBool, SimpleGraph.degree, SimpleGraph.neighborFinset] using hreg x
  · intro x y hxy
    rw [show (Finset.univ.filter fun z => graphBool H x z && graphBool H y z) =
        H.neighborFinset x ∩ H.neighborFinset y by
      ext z
      simp [graphBool]]
    exact hcommon x y hxy

/-- The pathwise `Xor` formulation of a negative signing is exactly the
compact population-one formulation after Boolean conversion. -/
theorem boolNegativeCompact1622_of_pathXor
    (H : SimpleGraph (Fin 16)) [DecidableRel H.Adj]
    (s : Fin 16 → Fin 16 → Prop) [DecidableRel s]
    (hcommon : ∀ x y : Fin 16, x ≠ y →
      (H.neighborFinset x ∩ H.neighborFinset y).card = 2)
    (hsym : ∀ x y, s x y ↔ s y x)
    (hneg : ∀ {x y u v : Fin 16}, x ≠ y → u ≠ v →
      H.Adj x u → H.Adj u y → H.Adj x v → H.Adj v y →
      Xor (s x u ↔ s u y) (s x v ↔ s v y)) :
    BoolNegativeCompact1622 (graphBool H) (signingBool s) := by
  refine ⟨?_, ?_⟩
  · intro x y
    simp only [signingBool, decide_eq_decide]
    exact hsym x y
  · intro x y hxy
    let C := H.neighborFinset x ∩ H.neighborFinset y
    let p : Fin 16 → Prop := fun z => Xor (s x z) (s y z)
    have hcard : C.card = 2 := hcommon x y hxy
    have hpairs : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → Xor (p u) (p v) := by
      intro u hu v hv huv
      have hu' : u ∈ H.neighborFinset x ∧ u ∈ H.neighborFinset y := by
        simpa [C] using hu
      have hv' : v ∈ H.neighborFinset x ∧ v ∈ H.neighborFinset y := by
        simpa [C] using hv
      have hxu : H.Adj x u := by
        simpa using hu'.1
      have hyu : H.Adj y u := by
        simpa using hu'.2
      have hxv : H.Adj x v := by
        simpa using hv'.1
      have hyv : H.Adj y v := by
        simpa using hv'.2
      have hn := hneg hxy huv hxu hyu.symm hxv hyv.symm
      have su := hsym u y
      have sv := hsym v y
      simp only [p, Xor] at hn ⊢
      tauto
    have hone := card_filter_eq_one_of_card_eq_two_of_xor C p hcard hpairs
    rw [← hone]
    congr 1
    ext z
    have hboolxor :
        (decide (s x z) ^^ decide (s y z)) = true ↔ Xor (s x z) (s y z) := by
      by_cases hx : s x z <;> by_cases hy : s y z <;> simp [hx, hy, Xor]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, C, p,
      Finset.mem_inter, SimpleGraph.mem_neighborFinset, graphBool, signingBool,
      decide_eq_true_eq, Bool.and_eq_true, hboolxor]

end Erdos85
