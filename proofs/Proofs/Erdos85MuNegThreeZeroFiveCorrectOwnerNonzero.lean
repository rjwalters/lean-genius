import Proofs.Erdos85MuNegThreeZeroFiveCorrectOwnerCnf
import Proofs.Erdos85DimacsSatBridge

/-! # Structural nonzero-literal proof for the honest 88-owner h305 CNFs -/

namespace Erdos85

open Std Sat

private theorem mem_lit_of_mem_exactlyTwo {lits clause : List Int} {lit : Int}
    (hc : clause ∈ muNegOneExactlyTwo lits) (hl : lit ∈ clause) :
    lit ∈ lits ∨ -lit ∈ lits := by
  simp only [muNegOneExactlyTwo, List.mem_append, List.mem_map,
    List.mem_flatMap, List.mem_filter, List.mem_range] at hc
  rcases hc with ⟨x, hx, rfl⟩ | ⟨i, hi, j, ⟨hj, hij⟩, k, ⟨hk, hjk⟩, rfl⟩
  · exact Or.inl (List.mem_of_mem_filter hl)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · right
      simp only [neg_neg]
      rw [getElem!_pos lits i hi]
      exact List.getElem_mem _
    · right
      simp only [neg_neg]
      rw [getElem!_pos lits j hj]
      exact List.getElem_mem _
    · right
      simp only [neg_neg]
      rw [getElem!_pos lits k hk]
      exact List.getElem_mem _

private theorem mem_lit_of_mem_exactlyThree {lits clause : List Int}
    {lit : Int} (hc : clause ∈ muNegThreeExactlyThree lits)
    (hl : lit ∈ clause) : lit ∈ lits ∨ -lit ∈ lits := by
  simp only [muNegThreeExactlyThree, List.mem_append, List.mem_flatMap,
    List.mem_filter, List.mem_range, List.mem_map, List.mem_singleton] at hc
  rcases hc with ⟨i, hi, j, ⟨hj, hij⟩, rfl⟩ | rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · left
      rw [getElem!_pos lits i hi]
      exact List.getElem_mem _
    · left
      rw [getElem!_pos lits j hj]
      exact List.getElem_mem _
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hl
    exact Or.inr (by simpa using hx)

private theorem dvar_map_nonzero (js : List Nat) (f g : Nat → Nat) :
    ∀ lit ∈ (js.map fun j => Int.ofNat (muNegOneDVar (f j) (g j))),
      lit ≠ 0 := by
  intro lit hlit
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hlit
  apply Int.ofNat_ne_zero.mpr
  unfold muNegOneDVar
  omega

private theorem crossRow_nonzero (sigma : Bool) :
    ∀ clause ∈ muNegThreeZeroFiveCrossRowClauses sigma,
      DimacsClauseNonzero clause := by
  intro clause hc lit hlit
  simp only [muNegThreeZeroFiveCrossRowClauses, List.mem_flatMap,
    List.mem_range, List.mem_append] at hc
  obtain ⟨i, hi, hc | hc⟩ := hc
  · rcases mem_lit_of_mem_exactlyTwo hc hlit with h | h
    · exact dvar_map_nonzero _ (fun _ => i) id lit h
    · intro hz
      exact dvar_map_nonzero _ (fun _ => i) id (-lit) h (by omega)
  · rcases mem_lit_of_mem_exactlyThree hc hlit with h | h
    · exact dvar_map_nonzero _ (fun _ => i) id lit h
    · intro hz
      exact dvar_map_nonzero _ (fun _ => i) id (-lit) h (by omega)

private theorem crossCol_nonzero (sigma : Bool) :
    ∀ clause ∈ muNegThreeZeroFiveCrossColClauses sigma,
      DimacsClauseNonzero clause := by
  intro clause hc lit hlit
  simp only [muNegThreeZeroFiveCrossColClauses, List.mem_flatMap,
    List.mem_range, List.mem_append] at hc
  obtain ⟨j, hj, hc | hc⟩ := hc
  · rcases mem_lit_of_mem_exactlyTwo hc hlit with h | h
    · exact dvar_map_nonzero _ id (fun _ => j) lit h
    · intro hz
      exact dvar_map_nonzero _ id (fun _ => j) (-lit) h (by omega)
  · rcases mem_lit_of_mem_exactlyThree hc hlit with h | h
    · exact dvar_map_nonzero _ id (fun _ => j) lit h
    · intro hz
      exact dvar_map_nonzero _ id (fun _ => j) (-lit) h (by omega)

private theorem sumEq_nonzero {a b c d : Int}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    ∀ clause ∈ muNegOneSumEq a b c d, DimacsClauseNonzero clause := by
  intro clause hclause lit hlit
  simp only [muNegOneSumEq, List.mem_cons, List.not_mem_nil,
    or_false] at hclause
  rcases hclause with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlit <;>
    rcases hlit with rfl | rfl | rfl <;> simp_all

private theorem intertwine_nonzero :
    ∀ clause ∈ muNegOneIntertwineClauses,
      DimacsClauseNonzero clause := by
  intro clause hc
  simp only [muNegOneIntertwineClauses, List.mem_flatMap,
    List.mem_range] at hc
  obtain ⟨i, hi, j, hj, hc⟩ := hc
  refine sumEq_nonzero ?_ ?_ ?_ ?_ clause hc <;>
    apply Int.ofNat_ne_zero.mpr
  all_goals unfold muNegOneDVar; omega

private theorem correctXVar_pos {pairs : List (Nat × Nat)} {a b x : Nat}
    (hx : muNegThreeZeroFiveCorrectXVar? pairs a b = some x) : 0 < x := by
  simp only [muNegThreeZeroFiveCorrectXVar?, Option.map_eq_some_iff] at hx
  obtain ⟨k, _, rfl⟩ := hx
  omega

private theorem correctXLit_nonzero {pairs : List (Nat × Nat)}
    {a b : Nat} {lit : Int}
    (hx : muNegThreeZeroFiveCorrectXLit? pairs a b = some lit) : lit ≠ 0 := by
  simp only [muNegThreeZeroFiveCorrectXLit?, Option.map_eq_some_iff] at hx
  obtain ⟨x, hx, rfl⟩ := hx
  exact Int.ofNat_ne_zero.mpr (Nat.ne_of_gt (correctXVar_pos hx))

private theorem correctGuard_pos {os : List (Nat × Nat)} {a g : Nat}
    (hg : muNegThreeZeroFiveCorrectGuard? os a = some g) : 0 < g := by
  unfold muNegThreeZeroFiveCorrectGuard? at hg
  dsimp only at hg
  split at hg <;> simp_all [muNegOneDVar] <;> omega

private theorem correctHitActivity_nonzero (os pairs : List (Nat × Nat)) :
    ∀ clause ∈ muNegThreeZeroFiveCorrectHitActivityClauses os pairs,
      DimacsClauseNonzero clause := by
  intro clause hc lit hlit
  simp only [muNegThreeZeroFiveCorrectHitActivityClauses,
    List.mem_flatMap] at hc
  obtain ⟨pr, _, hc⟩ := hc
  split at hc <;> rename_i x hx
  · simp only [List.mem_append] at hc
    rcases hc with hc | hc
    · split at hc
      · rename_i g hg
        simp only [List.mem_singleton] at hc
        subst clause
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hlit
        rcases hlit with rfl | rfl
        · intro hz
          exact Int.ofNat_ne_zero.mpr
            (Nat.ne_of_gt (correctXVar_pos hx)) (neg_eq_zero.mp hz)
        · intro hz
          exact Int.ofNat_ne_zero.mpr
            (Nat.ne_of_gt (correctGuard_pos hg)) (neg_eq_zero.mp hz)
      · simp at hc
    · split at hc
      · rename_i g hg
        simp only [List.mem_singleton] at hc
        subst clause
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hlit
        rcases hlit with rfl | rfl
        · intro hz
          exact Int.ofNat_ne_zero.mpr
            (Nat.ne_of_gt (correctXVar_pos hx)) (neg_eq_zero.mp hz)
        · intro hz
          exact Int.ofNat_ne_zero.mpr
            (Nat.ne_of_gt (correctGuard_pos hg)) (neg_eq_zero.mp hz)
      · simp at hc
  · simp at hc

private theorem correctService_nonzero (os pairs : List (Nat × Nat)) :
    ∀ clause ∈ muNegThreeZeroFiveCorrectServiceClauses os pairs,
      DimacsClauseNonzero clause := by
  intro clause hc lit hlit
  simp only [muNegThreeZeroFiveCorrectServiceClauses, List.mem_flatMap,
    List.mem_range] at hc
  obtain ⟨a, ha, w, hw, hc⟩ := hc
  let pre : List Int :=
    match muNegThreeZeroFiveCorrectGuard? os a with
    | some g => [Int.ofNat g]
    | none => []
  let lits := (List.range os.length).filterMap fun b =>
    if b != a && muNegOnePairMem (os[b]!) w then
      muNegThreeZeroFiveCorrectXLit? pairs a b
    else none
  have hlits : ∀ x ∈ lits, x ≠ 0 := by
    intro x hx
    dsimp [lits] at hx
    simp only [List.mem_filterMap] at hx
    obtain ⟨b, _, hb⟩ := hx
    split at hb <;> simp_all
    exact correctXLit_nonzero hb
  change clause ∈ [pre ++ lits] ++ muNegOnePairsOf lits pre at hc
  simp only [List.mem_append, List.mem_singleton] at hc
  rcases hc with rfl | hc
  · simp only [List.mem_append] at hlit
    rcases hlit with hp | hl
    · dsimp [pre] at hp
      split at hp
      · rename_i g hg
        simp only [List.mem_singleton] at hp
        subst lit
        exact Int.ofNat_ne_zero.mpr
          (Nat.ne_of_gt (correctGuard_pos hg))
      · simp at hp
    · dsimp [lits] at hl
      simp only [List.mem_filterMap] at hl
      obtain ⟨b, _, hb⟩ := hl
      split at hb <;> simp_all
      exact correctXLit_nonzero hb
  · simp only [muNegOnePairsOf, List.mem_flatMap, List.mem_map,
      List.mem_filter, List.mem_range] at hc
    obtain ⟨i, hi, j, ⟨hj, hij⟩, rfl⟩ := hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hlit
    rcases hlit with hlit | rfl | rfl
    · dsimp [pre] at hlit
      split at hlit
      · rename_i g hg
        simp only [List.mem_singleton] at hlit
        subst lit
        exact Int.ofNat_ne_zero.mpr
          (Nat.ne_of_gt (correctGuard_pos hg))
      · simp at hlit
    · intro hz
      rw [getElem!_pos lits i hi] at hz
      exact hlits _ (List.getElem_mem hi) (neg_eq_zero.mp hz)
    · intro hz
      rw [getElem!_pos lits j hj] at hz
      exact hlits _ (List.getElem_mem hj) (neg_eq_zero.mp hz)

private theorem correctC4_nonzero (os pairs : List (Nat × Nat)) :
    ∀ clause ∈ muNegThreeZeroFiveCorrectC4Clauses os pairs,
      DimacsClauseNonzero clause := by
  intro clause hc lit hlit
  simp only [muNegThreeZeroFiveCorrectC4Clauses, List.mem_flatMap,
    List.mem_range, List.mem_filter] at hc
  obtain ⟨a, ha, b, ⟨hb, hab⟩, hc⟩ := hc
  split at hc
  · simp only [List.mem_filterMap] at hc
    obtain ⟨g, _, hclause⟩ := hc
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hclause
    obtain ⟨x, hx, y, hy, hxy⟩ := hclause
    change some [-x, -y] = some clause at hxy
    simp only [Option.some.injEq] at hxy
    subst clause
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlit
    rcases hlit with rfl | rfl
    · exact fun hz => correctXLit_nonzero hx (by omega)
    · exact fun hz => correctXLit_nonzero hy (by omega)
  · simp only [List.mem_flatMap, List.mem_range, List.mem_filter,
      List.mem_filterMap] at hc
    obtain ⟨gi, hgi, hi, ⟨hhi, hgihi⟩, hclause⟩ := hc
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hclause
    obtain ⟨xag, hxag, xbg, hxbg, xah, hxah, xbh, hxbh, heq⟩ := hclause
    change some [-xag, -xbg, -xah, -xbh] = some clause at heq
    simp only [Option.some.injEq] at heq
    subst clause
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlit
    rcases hlit with rfl | rfl | rfl | rfl
    · exact fun hz => correctXLit_nonzero hxag (by omega)
    · exact fun hz => correctXLit_nonzero hxbg (by omega)
    · exact fun hz => correctXLit_nonzero hxah (by omega)
    · exact fun hz => correctXLit_nonzero hxbh (by omega)

theorem muNegThreeZeroFiveCorrectOwnerDimacsClauses_nonzero_of_mem
    (uTri vTri sigma : Bool) :
    ∀ clause ∈ muNegThreeZeroFiveCorrectOwnerDimacsClauses uTri vTri sigma,
      DimacsClauseNonzero clause := by
  intro clause hc
  simp only [muNegThreeZeroFiveCorrectOwnerDimacsClauses, List.mem_toArray,
    List.mem_append] at hc
  rcases hc with ((((hrow | hcol) | hintertwine) | hactivity) | hservice) | hc4
  · exact crossRow_nonzero sigma clause hrow
  · exact crossCol_nonzero sigma clause hcol
  · exact intertwine_nonzero clause hintertwine
  · exact correctHitActivity_nonzero _ _ clause hactivity
  · exact correctService_nonzero _ _ clause hservice
  · exact correctC4_nonzero _ _ clause hc4

end Erdos85

#print axioms Erdos85.muNegThreeZeroFiveCorrectOwnerDimacsClauses_nonzero_of_mem
