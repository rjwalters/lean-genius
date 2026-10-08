import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalHighSymmetryRowKey
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalHsbGen
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptyCubeOrbitExtraClauses

/-! # Soundness of the high-side symmetry-breaking clauses (`hsb`)

For every cube `(F, i)` and every list of generator entries, the clauses
whose witness passes `SevenHighT0Hsb.check` are orbit-sound: every completion
graph of the cube yields a completion graph of the same cube (the one with
lexicographically minimal row keys) whose edge valuation satisfies all of
them.  This is the obligation `hrep` of
`sevenHighT0CanonicalExtraClausesOrbitSound_of_edgeOnly_representative`.

The statement is uniform in the entry list, so it covers
`SevenHighT0Hsb.clauses depth mask` for every depth without evaluating the
generator; no `native_decide` is used.
-/

namespace Erdos85

open Std Sat SimpleGraph

namespace SevenHighT0Hsb

/-! ## Numeric vertices versus canonical indices -/

/-- Outside index of a numeric vertex `14..48`. -/
def outOfFin (v : Fin 49) : SevenHighT0OutsideIndex :=
  match sevenHighT0CanonicalIndexOfFin v with
  | Sum.inr (Sum.inr x) => x
  | _ => Sum.inl (0, 0)

/-- Numeric vertex of an outside index. -/
def numO : SevenHighT0OutsideIndex → ℕ
  | Sum.inl q => 14 + 2 * q.1.1 + q.2.1
  | Sum.inr key => 28 + pairIdx key.1.1.1 key.1.2.1

def outOfNat (v : ℕ) : SevenHighT0OutsideIndex :=
  outOfFin ⟨v % 49, Nat.mod_lt _ (by decide)⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem indexOfFin_outside : ∀ v : Fin 49, 14 ≤ v.1 →
    sevenHighT0CanonicalIndexOfFin v =
      Sum.inr (Sum.inr (outOfFin v)) := by
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem numO_outOfFin : ∀ v : Fin 49, 14 ≤ v.1 →
    numO (outOfFin v) = v.1 := by
  decide

set_option maxHeartbeats 0 in
theorem indexOfFin_empty : ∀ j : Fin 7,
    sevenHighT0CanonicalIndexOfFin ⟨7 + j.1, by omega⟩ =
      Sum.inr (Sum.inl j) := by
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem lowEdgeId_eq_edgeVar : ∀ (j : Fin 7) (v : Fin 49), 14 ≤ v.1 →
    sevenHighT0CanonicalLowEdgeId (7 + j.1) v.1 = edgeVar j.1 v.1 + 1 := by
  decide

set_option maxHeartbeats 0 in
theorem edgeVar_lt : ∀ (j : Fin 7) (v : Fin 49), edgeVar j.1 v.1 < 861 := by
  decide

theorem pairOf_pairIdx : ∀ key : SevenHighT0PairIndex,
    pairOf (pairIdx key.1.1.1 key.1.2.1) = (key.1.1.1, key.1.2.1) := by
  decide

theorem labelPairs_idxOf : ∀ l r : Fin 7, l ≠ r →
    sevenHighT0CanonicalLabelPairs.idxOf (min l.1 r.1, max l.1 r.1) =
      pairIdx (min l.1 r.1) (max l.1 r.1) := by
  decide

theorem outOfNat_eq (v : ℕ) (h : v < 49) : outOfNat v = outOfFin ⟨v, h⟩ := by
  have hfin : (⟨v % 49, Nat.mod_lt _ (by decide)⟩ : Fin 49) = ⟨v, h⟩ :=
    Fin.ext (Nat.mod_eq_of_lt h)
  unfold outOfNat
  rw [hfin]

theorem numO_outOfNat (v : ℕ) (h14 : 14 ≤ v) (h49 : v < 49) :
    numO (outOfNat v) = v := by
  rw [outOfNat_eq v h49]
  exact numO_outOfFin ⟨v, h49⟩ h14

/-- The SAT variable of the edge `(7 + j, v)` reads the adjacency of empty
`j` with the outside index of `v`. -/
theorem edgeVal_edgeVar
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (j : Fin 7) (v : ℕ) (h14 : 14 ≤ v) (h49 : v < 49) :
    satAssignmentOfDimacs (sevenHighT0CanonicalEdgeVal H) (edgeVar j.1 v) =
      decide (H.Adj (sevenHighT0HsbEmptyVertex j)
        (sevenHighT0HsbOutsideVertex (outOfNat v))) := by
  have hj := j.2
  have hid : sevenHighT0CanonicalLowEdgeId (7 + j.1) v = edgeVar j.1 v + 1 :=
    lowEdgeId_eq_edgeVar j ⟨v, h49⟩ h14
  have hne : (⟨7 + j.1, by omega⟩ : Fin 49) ≠ ⟨v, h49⟩ := by
    intro h
    have hv : 7 + j.1 = v := congrArg Fin.val h
    omega
  have hedge : sevenHighT0CanonicalEdgeVal H
      (sevenHighT0CanonicalLowEdgeId (7 + j.1) v) =
      sevenHighT0CanonicalAdjBool H ⟨7 + j.1, by omega⟩ ⟨v, h49⟩ :=
    sevenHighT0CanonicalEdgeVal_edge H ⟨7 + j.1, by omega⟩ ⟨v, h49⟩
      (Nat.le_add_right 7 j.1) (le_trans (by decide) h14) hne
  have hsat : satAssignmentOfDimacs (sevenHighT0CanonicalEdgeVal H)
      (edgeVar j.1 v) =
      sevenHighT0CanonicalEdgeVal H (edgeVar j.1 v + 1) := rfl
  rw [hsat, ← hid, hedge, outOfNat_eq v h49]
  unfold sevenHighT0CanonicalAdjBool
  rw [indexOfFin_empty j, indexOfFin_outside ⟨v, h49⟩ h14]

/-! ## The group element of a witness -/

/-- Copy swaps selected by the bits of `flips`. -/
def flipOf (flips : ℕ) : Fin 7 → Equiv.Perm (Fin 2) := fun l =>
  if flips.testBit l.1 then Equiv.swap 0 1 else Equiv.refl _

theorem swap_val : ∀ c : Fin 2, ((Equiv.swap (0 : Fin 2) 1) c).1 = 1 - c.1 := by
  decide

theorem flipOf_val (flips : ℕ) (l : Fin 7) (c : Fin 2) :
    (flipOf flips l c).1 =
      if flips.testBit l.1 then 1 - c.1 else c.1 := by
  unfold flipOf
  by_cases h : flips.testBit l.1 = true
  · rw [if_pos h, if_pos h]
    exact swap_val c
  · rw [if_neg h, if_neg h]
    rfl

theorem pairPerm_fst (σ : Equiv.Perm (Fin 7)) (key : SevenHighT0PairIndex) :
    (sevenHighT0PairIndexPerm σ key).1.1 = σ key.1.1 ⊓ σ key.1.2 := rfl

theorem pairPerm_snd (σ : Equiv.Perm (Fin 7)) (key : SevenHighT0PairIndex) :
    (sevenHighT0PairIndexPerm σ key).1.2 = σ key.1.1 ⊔ σ key.1.2 := rfl

/-- The numeric `vmap` is the high-side action on outside indices. -/
theorem vmap_numO (sig : ℕ → ℕ) (flips : ℕ) (σ : Equiv.Perm (Fin 7))
    (hσ : ∀ i : Fin 7, sig i.1 = (σ i).1) (x : SevenHighT0OutsideIndex) :
    vmap sig flips (numO x) =
      numO (sevenHighT0OutsideHighPerm σ (flipOf flips) x) := by
  rcases x with q | key
  · obtain ⟨l, c⟩ := q
    have hl := l.2
    have hc := c.2
    have h1 : (14 + 2 * l.1 + c.1 - 14) / 2 = l.1 := by omega
    have h2 : (14 + 2 * l.1 + c.1 - 14) % 2 = c.1 := by omega
    have hlt : 14 + 2 * l.1 + c.1 < 28 := by omega
    have hrhs : numO (sevenHighT0OutsideHighPerm σ (flipOf flips)
        (Sum.inl (l, c))) =
        14 + 2 * (σ l).1 + (flipOf flips l c).1 := rfl
    have hlhs : numO (Sum.inl (l, c)) = 14 + 2 * l.1 + c.1 := rfl
    rw [hrhs, hlhs, flipOf_val]
    unfold vmap
    rw [if_pos hlt, h1, h2, hσ l]
  · have hp := pairOf_pairIdx key
    have hge : ¬ 28 + pairIdx key.1.1.1 key.1.2.1 < 28 := by omega
    have hsub : 28 + pairIdx key.1.1.1 key.1.2.1 - 28 =
        pairIdx key.1.1.1 key.1.2.1 := by omega
    have hrhs : numO (sevenHighT0OutsideHighPerm σ (flipOf flips)
        (Sum.inr key)) =
        28 + pairIdx (sevenHighT0PairIndexPerm σ key).1.1.1
          (sevenHighT0PairIndexPerm σ key).1.2.1 := rfl
    have hlhs : numO (Sum.inr key) =
        28 + pairIdx key.1.1.1 key.1.2.1 := rfl
    have h1 : sig (pairOf (pairIdx key.1.1.1 key.1.2.1)).1 =
        (σ key.1.1).1 := by
      rw [hp]
      exact hσ key.1.1
    have h2 : sig (pairOf (pairIdx key.1.1.1 key.1.2.1)).2 =
        (σ key.1.2).1 := by
      rw [hp]
      exact hσ key.1.2
    rw [hrhs, hlhs, pairPerm_fst, pairPerm_snd]
    unfold vmap
    rw [if_neg hge, hsub, h1, h2]
    rcases le_total (σ key.1.1) (σ key.1.2) with h | h
    · have h' : (σ key.1.1).1 ≤ (σ key.1.2).1 := h
      rw [inf_of_le_left h, sup_of_le_right h, Nat.min_eq_left h',
        Nat.max_eq_right h']
    · have h' : (σ key.1.2).1 ≤ (σ key.1.1).1 := h
      rw [inf_of_le_right h, sup_of_le_left h, Nat.min_eq_right h',
        Nat.max_eq_left h']

theorem exists_perm_of_sigOk (sig : List ℕ) (h : sigOk sig = true) :
    ∃ σ : Equiv.Perm (Fin 7), ∀ i : Fin 7, sigOf sig i.1 = (σ i).1 := by
  unfold sigOk at h
  rw [List.all_eq_true] at h
  have hlt : ∀ i : Fin 7, sigOf sig i.1 < 7 := by
    intro i
    have hi := h i.1 (List.mem_range.mpr i.2)
    rw [Bool.and_eq_true] at hi
    exact of_decide_eq_true hi.1
  have hinj : Function.Injective
      (fun i : Fin 7 => (⟨sigOf sig i.1, hlt i⟩ : Fin 7)) := by
    intro i j hij
    have hv : sigOf sig i.1 = sigOf sig j.1 := congrArg Fin.val hij
    have hi := h i.1 (List.mem_range.mpr i.2)
    rw [Bool.and_eq_true, List.all_eq_true] at hi
    have hj := hi.2 j.1 (List.mem_range.mpr j.2)
    rw [Bool.or_eq_true] at hj
    rcases hj with hj | hj
    · exact Fin.ext (eq_of_beq hj)
    · rw [hv] at hj
      simp at hj
  exact ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj),
    fun i => rfl⟩

/-! ## Mask degree -/

theorem maskAdj_eq (mask : ℕ) (l r : Fin 7) :
    sevenHighT0CanonicalEmptySemanticMaskAdj mask l.1 r.1 =
      maskAdj mask l.1 r.1 := by
  unfold maskAdj sevenHighT0CanonicalEmptySemanticMaskAdj
  by_cases hlr : l = r
  · subst hlr
    simp
  · rw [labelPairs_idxOf l r hlr]

theorem maskDeg_eq_card (mask : ℕ) (j : Fin 7) :
    (Finset.univ.filter fun f : Fin 7 =>
      sevenHighT0CanonicalEmptySemanticMaskAdj mask j.1 f.1 = true).card =
      maskDeg mask j.1 := by
  rw [Finset.card_filter, Fin.sum_univ_seven]
  simp only [maskAdj_eq mask j]
  rfl

/-! ## Reading the Boolean checks -/

theorem rowOk_spec {mask j : ℕ} {row : List ℕ} (h : rowOk mask j row = true) :
    (∀ v ∈ row, 14 ≤ v ∧ v < 49) ∧ row.Nodup ∧
      row.length + maskDeg mask j = 7 := by
  unfold rowOk at h
  rw [Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨fun v hv => ?_, of_decide_eq_true h.1.2, of_decide_eq_true h.2⟩
  have hv' := h.1.1 v hv
  rw [Bool.and_eq_true] at hv'
  exact ⟨of_decide_eq_true hv'.1, of_decide_eq_true hv'.2⟩

theorem check_spec {mask : ℕ} {rows : List (List ℕ)} {sig : List ℕ}
    {flips : ℕ} (h : check mask rows sig flips = true) :
    0 < rows.length ∧ rows.length ≤ 7 ∧ sigOk sig = true ∧
      ∀ j, j < rows.length →
        rowOk mask j (rows.getD j []) = true ∧
        (if j + 1 = rows.length then
          decide (key ((rows.getD j []).map (vmap (sigOf sig) flips)) <
            key (rows.getD j []))
        else
          decide (key ((rows.getD j []).map (vmap (sigOf sig) flips)) =
            key (rows.getD j []))) = true := by
  unfold check at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    List.all_eq_true] at h
  refine ⟨of_decide_eq_true h.1.1.1, of_decide_eq_true h.1.1.2, h.1.2, ?_⟩
  intro j hj
  have hjr := h.2 j (List.mem_range.mpr hj)
  rw [Bool.and_eq_true] at hjr
  exact hjr

/-- DIMACS-order weight on outside indices. -/
def weightO (x : SevenHighT0OutsideIndex) : ℕ := weight (numO x)

theorem key_map_outOfNat (row : List ℕ)
    (hrow : ∀ v ∈ row, 14 ≤ v ∧ v < 49) :
    ((row.map outOfNat).map weightO).sum = key row := by
  unfold key
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro v hv
  show weight (numO (outOfNat v)) = weight v
  rw [numO_outOfNat v (hrow v hv).1 (hrow v hv).2]

theorem key_map_vmap (row : List ℕ)
    (hrow : ∀ v ∈ row, 14 ≤ v ∧ v < 49)
    (sig : ℕ → ℕ) (flips : ℕ) (σ : Equiv.Perm (Fin 7))
    (hσ : ∀ i : Fin 7, sig i.1 = (σ i).1) :
    ((row.map outOfNat).map fun x =>
      weightO (sevenHighT0OutsideHighPerm σ (flipOf flips) x)).sum =
      key (row.map (vmap sig flips)) := by
  unfold key
  rw [List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro v hv
  show weight (numO (sevenHighT0OutsideHighPerm σ (flipOf flips)
    (outOfNat v))) = weight (vmap sig flips v)
  rw [← vmap_numO sig flips σ hσ, numO_outOfNat v (hrow v hv).1 (hrow v hv).2]

theorem nodup_map_outOfNat (row : List ℕ)
    (hrow : ∀ v ∈ row, 14 ≤ v ∧ v < 49) (hnodup : row.Nodup) :
    (row.map outOfNat).Nodup := by
  apply List.Nodup.map_on _ hnodup
  intro u hu v hv huv
  have h := congrArg numO huv
  rw [numO_outOfNat u (hrow u hu).1 (hrow u hu).2,
    numO_outOfNat v (hrow v hv).1 (hrow v hv).2] at h
  exact h

/-! ## One clause -/

/-- A clause whose witness passes `check` holds in every completion of the
cube that no high-side relabeling makes lex-smaller in its row keys. -/
theorem clause_eval_of_check
    {H' : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H'.Adj]
    (hH' : SevenHighT0CanonicalCompletionSemantics H') (mask : ℕ)
    (hmask : sevenHighT0CanonicalEmptySemanticMask H' = mask)
    (hmin : ∀ (σ : Equiv.Perm (Fin 7)) (flip : Fin 7 → Equiv.Perm (Fin 2))
      (k : Fin 7),
      (∀ j, j < k →
        sevenHighT0RowKey weightO
            (sevenHighT0CanonicalHighRelabel σ flip H') j =
          sevenHighT0RowKey weightO H' j) →
      ¬ sevenHighT0RowKey weightO
            (sevenHighT0CanonicalHighRelabel σ flip H') k <
          sevenHighT0RowKey weightO H' k)
    (rows : List (List ℕ)) (sig : List ℕ) (flips : ℕ)
    (hcheck : check mask rows sig flips = true) :
    CNF.Clause.eval
      (satAssignmentOfDimacs (sevenHighT0CanonicalEdgeVal H'))
      (clause rows) = true := by
  obtain ⟨hpos, hle7, hsig, hrows⟩ := check_spec hcheck
  obtain ⟨σ, hσ⟩ := exists_perm_of_sigOk sig hsig
  let k : Fin 7 := ⟨rows.length - 1, by omega⟩
  let L : Fin 7 → List SevenHighT0OutsideIndex :=
    fun j => (rows.getD j.1 []).map outOfNat
  have hjlt : ∀ j : Fin 7, j ≤ k → j.1 < rows.length := by
    intro j hj
    have hj' : j.1 ≤ rows.length - 1 := hj
    omega
  have hspec : ∀ j : Fin 7, j ≤ k →
      (∀ v ∈ rows.getD j.1 [], 14 ≤ v ∧ v < 49) ∧
      (rows.getD j.1 []).Nodup ∧
      (rows.getD j.1 []).length + maskDeg mask j.1 = 7 :=
    fun j hj => rowOk_spec (hrows j.1 (hjlt j hj)).1
  obtain ⟨j, hjk, x, hx, hnadj⟩ :=
    sevenHighT0HsbWitness_excludes weightO mask hH' hmask σ (flipOf flips)
      (hmin σ (flipOf flips)) k L
      (fun j hj => nodup_map_outOfNat _ (hspec j hj).1 (hspec j hj).2.1)
      (fun j hj => by
        show _ + ((rows.getD j.1 []).map outOfNat).length = 7
        rw [maskDeg_eq_card, List.length_map]
        have := (hspec j hj).2.2
        omega)
      (fun j hj => by
        show (((rows.getD j.1 []).map outOfNat).map fun x =>
          weightO (sevenHighT0OutsideHighPerm σ (flipOf flips) x)).sum =
          (((rows.getD j.1 []).map outOfNat).map weightO).sum
        have hj' : j.1 < rows.length - 1 := hj
        have hcmp := (hrows j.1 (hjlt j (le_of_lt hj))).2
        rw [if_neg (by omega)] at hcmp
        rw [key_map_vmap _ (hspec j (le_of_lt hj)).1 (sigOf sig) flips σ hσ,
          key_map_outOfNat _ (hspec j (le_of_lt hj)).1]
        exact of_decide_eq_true hcmp)
      (by
        show (((rows.getD k.1 []).map outOfNat).map fun x =>
          weightO (sevenHighT0OutsideHighPerm σ (flipOf flips) x)).sum <
          (((rows.getD k.1 []).map outOfNat).map weightO).sum
        have hk : k.1 + 1 = rows.length := by
          show rows.length - 1 + 1 = rows.length
          omega
        have hcmp := (hrows k.1 (hjlt k (le_refl k))).2
        rw [if_pos hk] at hcmp
        rw [key_map_vmap _ (hspec k (le_refl k)).1 (sigOf sig) flips σ hσ,
          key_map_outOfNat _ (hspec k (le_refl k)).1]
        exact of_decide_eq_true hcmp)
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
  have hbounds := (hspec j hjk).1 v hv
  have hmem : (edgeVar j.1 v, false) ∈ clause rows := by
    unfold clause
    rw [List.mem_flatMap]
    exact ⟨j.1, List.mem_range.mpr (hjlt j hjk),
      List.mem_map.mpr ⟨v, hv, rfl⟩⟩
  unfold CNF.Clause.eval
  rw [List.any_eq_true]
  refine ⟨(edgeVar j.1 v, false), hmem, ?_⟩
  show (satAssignmentOfDimacs (sevenHighT0CanonicalEdgeVal H')
    (edgeVar j.1 v) == false) = true
  rw [edgeVal_edgeVar H' j v hbounds.1 hbounds.2, decide_eq_false hnadj]
  rfl

theorem clause_var_lt {mask : ℕ} {rows : List (List ℕ)} {sig : List ℕ}
    {flips : ℕ} (hcheck : check mask rows sig flips = true)
    (lit : ℕ × Bool) (hlit : lit ∈ clause rows) : lit.1 < 861 := by
  obtain ⟨_, hle7, _, hrows⟩ := check_spec hcheck
  unfold clause at hlit
  rw [List.mem_flatMap] at hlit
  obtain ⟨j, hj, hlit⟩ := hlit
  have hjlt := List.mem_range.mp hj
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hlit
  have hb := (rowOk_spec (hrows j hjlt).1).1 v hv
  exact edgeVar_lt ⟨j, by omega⟩ ⟨v, hb.2⟩

/-! ## The CNF and its soundness -/

/-- CNF of the entries whose witness passes `check`. -/
def cnfOfEntries (mask : ℕ) (es : List Entry) : CNF ℕ :=
  ⟨(clausesOfEntries mask es).toArray⟩

/-- The `hsb<depth>` CNF of a mask (`gen_pilot.py --facts hsb<depth>`). -/
def cnf (depth mask : ℕ) : CNF ℕ := cnfOfEntries mask (entries depth mask)

theorem cnf_clauses (depth mask : ℕ) :
    (cnf depth mask).clauses = (clauses depth mask).toArray := rfl

theorem mem_clausesOfEntries {mask : ℕ} {es : List Entry}
    {c : List (ℕ × Bool)} (hc : c ∈ clausesOfEntries mask es) :
    ∃ rows sig flips, check mask rows sig flips = true ∧ c = clause rows := by
  unfold clausesOfEntries at hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
  exact ⟨e.rows, e.sig, e.flips, (List.mem_filter.mp he).2, rfl⟩

theorem cnfOfEntries_edgeOnly (mask : ℕ) (es : List Entry) :
    ∀ v, CNF.VarMem v (cnfOfEntries mask es) → v < 861 := by
  rintro v ⟨c, hc, hv⟩
  have hc' : c ∈ clausesOfEntries mask es := List.mem_toArray.mp hc
  obtain ⟨rows, sig, flips, hcheck, rfl⟩ := mem_clausesOfEntries hc'
  rcases hv with hv | hv
  · exact clause_var_lt hcheck _ hv
  · exact clause_var_lt hcheck _ hv

end SevenHighT0Hsb

open SevenHighT0Hsb

/-- **`hrep` for `hsb`.**  Every completion graph of the cube `(F, i)` yields
a completion graph of the same cube whose edge valuation satisfies every
witness-checked `hsb` clause. -/
theorem sevenHighT0CanonicalHsb_representative
    (edgeCount typeIndex : ℕ) (es : List Entry)
    (H : SimpleGraph SevenHighT0CanonicalIndex) (_ : DecidableRel H.Adj)
    (semantics : SevenHighT0CanonicalCompletionSemantics H)
    (hmask : sevenHighT0CanonicalEmptySemanticMask H =
      sevenHighT0CanonicalEmptyRepresentativeMask edgeCount typeIndex) :
    ∃ (H' : SimpleGraph SevenHighT0CanonicalIndex)
      (_ : DecidableRel H'.Adj),
      SevenHighT0CanonicalCompletionSemantics H' ∧
      sevenHighT0CanonicalEmptySemanticMask H' =
        sevenHighT0CanonicalEmptyRepresentativeMask edgeCount typeIndex ∧
      (cnfOfEntries
        (sevenHighT0CanonicalEmptyRepresentativeMask edgeCount typeIndex)
        es).Sat (satAssignmentOfDimacs (sevenHighT0CanonicalEdgeVal H')) := by
  obtain ⟨H', inst, h1, h2, hmin⟩ := semantics.exists_rowKeyMinimal weightO
  refine ⟨H', inst, h1, h2.trans hmask, ?_⟩
  rw [CNF.sat_def]
  unfold CNF.eval
  show (clausesOfEntries _ es).toArray.all _ = true
  rw [List.all_toArray, List.all_eq_true]
  intro c hc
  obtain ⟨rows, sig, flips, hcheck, rfl⟩ := mem_clausesOfEntries hc
  exact @clause_eval_of_check H' inst h1 _ (h2.trans hmask) hmin
    rows sig flips hcheck

/-- The witness-checked `hsb` clauses are orbit-sound for every cube. -/
theorem sevenHighT0CanonicalHsbEntries_orbitSound
    (edgeCount typeIndex : ℕ) (es : List Entry) :
    SevenHighT0CanonicalExtraClausesOrbitSound edgeCount typeIndex
      (cnfOfEntries
        (sevenHighT0CanonicalEmptyRepresentativeMask edgeCount typeIndex)
        es) :=
  sevenHighT0CanonicalExtraClausesOrbitSound_of_edgeOnly_representative
    (cnfOfEntries_edgeOnly _ es)
    (sevenHighT0CanonicalHsb_representative edgeCount typeIndex es)

/-- Orbit soundness of the generated `hsb<depth>` CNF of every cube. -/
theorem sevenHighT0CanonicalHsb_orbitSound
    (depth edgeCount typeIndex : ℕ) :
    SevenHighT0CanonicalExtraClausesOrbitSound edgeCount typeIndex
      (SevenHighT0Hsb.cnf depth
        (sevenHighT0CanonicalEmptyRepresentativeMask edgeCount typeIndex)) :=
  sevenHighT0CanonicalHsbEntries_orbitSound edgeCount typeIndex _

/-- UNSAT of `cube ∧ hsb<depth>` gives the semantic exclusion of the cube. -/
theorem sevenHighT0CanonicalEmptyCubeSemanticExclusion_of_hsbUnsat
    (depth edgeCount typeIndex : ℕ)
    (hunsat : (orderFortyNineSevenHighT0CanonicalEmptyCubeExtraSatCnf
      edgeCount typeIndex
      (SevenHighT0Hsb.cnf depth
        (sevenHighT0CanonicalEmptyRepresentativeMask
          edgeCount typeIndex))).Unsat) :
    SevenHighT0CanonicalEmptyCubeSemanticExclusion edgeCount typeIndex :=
  sevenHighT0CanonicalEmptyCubeSemanticExclusion_of_orbitExtraUnsat
    (sevenHighT0CanonicalHsb_orbitSound depth edgeCount typeIndex) hunsat

end Erdos85

#print axioms Erdos85.SevenHighT0Hsb.clause_eval_of_check
#print axioms Erdos85.sevenHighT0CanonicalHsb_representative
#print axioms Erdos85.sevenHighT0CanonicalHsb_orbitSound
#print axioms Erdos85.sevenHighT0CanonicalEmptyCubeSemanticExclusion_of_hsbUnsat
