import Proofs.SpernerGridBase

/-
# sperner-ndim-oq-02: self-contained unoriented Freudenthal cell machinery

This module is a clean extraction of the `GridSimplex` cell structure and its
chain-coordinate lemmas from `SpernerGrid.lean`'s SECTIONS III–V (plus the
`BaryPoint.transfer` helper of SECTION VI). The parent `SpernerGrid.lean`
additionally bundles the *oriented* `gridAdj` machinery (lines ~600–1556) whose
`boundary_doors_odd` is **false** as stated — the motivating defect of this
problem — and which does not currently compile. Everything reproduced here lives
strictly *before* that broken block and depends only on the clean `BaryPoint`
API from `Proofs.SpernerGridBase` (`import Mathlib` only).

Reproducing it on the compiling foundation makes the cell geometry — the
`d+1`-vertex mass-transfer chain, its `verts_injective`, the `miss`-coordinate
tracking, and the `incDir` complement surjection — available to the "Option C"
*unoriented* `SpernerTriangulation` instance (`sperner-ndim-oq-02`) without
importing the broken file. `GridSimplex` is an **oriented chain** encoding; the
Phase-1 instance quotients out that orientation with a canonicality predicate
(see `SpernerNDimOQ02Cell.lean`).

Namespace is kept as `SpernerGrid` (import-disjoint from the broken file, so no
module ever sees two `SpernerGrid.GridSimplex`). No new axioms or sorries.
-/

open Finset

namespace SpernerGrid

-- ============================================================
-- SECTION III: Grid Simplices
-- ============================================================

structure GridSimplex (d N : ℕ) where
  /-- The d+1 vertices in chain order. -/
  verts : Fin (d + 1) → BaryPoint d N
  /-- Which coordinate increases at step k. -/
  incDir : Fin d → Fin (d + 1)
  /-- The coordinate that decreases at every step. -/
  miss : Fin (d + 1)
  /-- The miss direction is not an increase direction. -/
  miss_ne_inc : ∀ k : Fin d, incDir k ≠ miss
  /-- The increased coordinate goes up by 1. -/
  step_inc : ∀ k : Fin d,
    (verts k.succ).coords (incDir k) =
    (verts k.castSucc).coords (incDir k) + 1
  /-- The miss coordinate goes down by 1. -/
  step_dec : ∀ k : Fin d,
    (verts k.castSucc).coords miss =
    (verts k.succ).coords miss + 1
  /-- All other coordinates are unchanged. -/
  step_same : ∀ (k : Fin d) (j : Fin (d + 1)),
    j ≠ incDir k → j ≠ miss →
    (verts k.succ).coords j =
    (verts k.castSucc).coords j
  /-- The increased directions are all distinct. -/
  inc_injective : Function.Injective incDir

instance gridSimplexDecEq (d N : ℕ) :
    DecidableEq (GridSimplex d N) := by
  intro a b
  by_cases hv : a.verts = b.verts
  · by_cases hi : a.incDir = b.incDir
    · by_cases hm : a.miss = b.miss
      · exact isTrue (by
          cases a; cases b
          simp only at hv hi hm
          subst hv; subst hi; subst hm; rfl)
      · exact isFalse (fun h =>
          hm (by cases h; rfl))
    · exact isFalse (fun h =>
        hi (by cases h; rfl))
  · exact isFalse (fun h =>
      hv (by cases h; rfl))

noncomputable instance gridSimplexFintype (d N : ℕ) :
    Fintype (GridSimplex d N) :=
  Fintype.ofInjective
    (fun s : GridSimplex d N => (s.verts, s.incDir, s.miss))
    (fun a b h => by
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h1; subst h2; subst h3; rfl)

-- SECTION IV: Basic Properties
-- ============================================================

variable {d N : ℕ}

/-- Coordinate incDir(k) is unchanged at step k' ≠ k.
Since incDir is injective, incDir(k') ≠ incDir(k). And
miss ≠ incDir(k) by miss_ne_inc. So step_same applies. -/
theorem GridSimplex.incDir_stable (s : GridSimplex d N)
    (k k' : Fin d) (hne : k ≠ k') :
    (s.verts k'.succ).coords (s.incDir k) =
    (s.verts k'.castSucc).coords (s.incDir k) :=
  s.step_same k' (s.incDir k)
    (fun h => hne (s.inc_injective h))
    (s.miss_ne_inc k)

/-- Coordinate incDir(k) has the same value at vertex m as at
vertex k.succ, for any m ≥ k.succ. This is because the only
step that changes incDir(k) is step k, which occurs before m.

Proved by strong induction on m.val. -/
theorem GridSimplex.incDir_const_after (s : GridSimplex d N)
    (k : Fin d) (m : Fin (d + 1))
    (hm : k.succ ≤ m) :
    (s.verts m).coords (s.incDir k) =
    (s.verts k.succ).coords (s.incDir k) := by
  -- Induction on m.val
  have : ∀ p : ℕ, (hp : p < d + 1) → k.succ.val ≤ p →
      (s.verts ⟨p, hp⟩).coords (s.incDir k) =
      (s.verts k.succ).coords (s.incDir k) := by
    intro p hp hkp
    induction p with
    | zero =>
      -- k.succ.val ≥ 1, so k.succ.val ≤ 0 is impossible
      simp [Fin.succ] at hkp
    | succ p' ih =>
      by_cases hbase : k.succ.val = p' + 1
      · -- k.succ.val = p' + 1
        have hkv : k.val = p' := by
          have := k.isLt; simp [Fin.succ] at hbase; omega
        have heq : (⟨p' + 1, hp⟩ : Fin (d + 1)) = k.succ := by
          apply Fin.ext; simp [Fin.succ]; omega
        rw [show s.verts ⟨p' + 1, hp⟩ = s.verts k.succ from
          congr_arg s.verts heq]
      · -- p' ≥ k.succ.val, so IH applies
        have hp' : p' < d + 1 := by omega
        have hkp' : k.succ.val ≤ p' := by omega
        have ih_val := ih hp' hkp'
        -- Step from p' to p'+1 uses step index ⟨p', _⟩
        have hpd : p' < d := by omega
        let step : Fin d := ⟨p', hpd⟩
        have hstep_ne : k ≠ step := by
          intro heq
          simp [step, Fin.ext_iff] at heq
          simp [Fin.succ] at *; omega
        have hstable := s.incDir_stable k step hstep_ne
        have hsc : step.castSucc = ⟨p', hp'⟩ := by
          ext; simp [step, Fin.castSucc]
        have hss : step.succ = ⟨p' + 1, hp⟩ := by
          ext; simp [step, Fin.succ]
        rw [hss, hsc] at hstable
        rw [hstable, ih_val]
  exact this m.val m.isLt (by exact hm)

/-- Consecutive vertices in a GridSimplex are distinct. -/
theorem GridSimplex.verts_succ_ne (s : GridSimplex d N)
    (k : Fin d) :
    s.verts k.succ ≠ s.verts k.castSucc := by
  intro heq
  have h := s.step_inc k
  rw [show (s.verts k.succ).coords (s.incDir k) =
    (s.verts k.castSucc).coords (s.incDir k) from
    congr_arg (fun v => v.coords (s.incDir k)) heq] at h
  omega

/-- All d+1 vertices of a GridSimplex are pairwise distinct.

With constant miss, coordinate incDir(k) increases exactly
once (at step k) and never changes at other steps. So for
i < j, taking k = ⟨i, _⟩, we get
  v_j(incDir k) = v_i(incDir k) + 1
since the +1 at step k is the only change, proving v_i ≠ v_j. -/
theorem GridSimplex.verts_injective (s : GridSimplex d N) :
    Function.Injective s.verts := by
  intro i j heq
  suffices i.val = j.val from Fin.val_injective this
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · -- i < j: track coordinate incDir(⟨i, _⟩)
    have hid : i.val < d := by omega
    let k : Fin d := ⟨i.val, hid⟩
    -- After step k: incDir(k) has increased by 1
    have h1 := s.step_inc k
    -- k.castSucc = i
    have hkc : k.castSucc = i := Fin.ext (by simp [k, Fin.castSucc])
    -- k.succ ≤ j (since i < j means i+1 ≤ j)
    have hksj : k.succ ≤ j := by
      simp [Fin.le_iff_val_le_val, k, Fin.succ]; omega
    -- By incDir_const_after: verts(j) and verts(k.succ) agree on incDir(k)
    have h2 := s.incDir_const_after k j hksj
    -- So verts(j).coords(incDir k) = verts(i).coords(incDir k) + 1
    rw [hkc] at h1
    have : (s.verts j).coords (s.incDir k) =
        (s.verts i).coords (s.incDir k) + 1 := by
      rw [h2, h1]
    -- But heq says verts i = verts j
    rw [congr_arg (fun v => v.coords (s.incDir k)) heq] at this
    omega
  · -- j < i: symmetric
    have hjd : j.val < d := by omega
    let k : Fin d := ⟨j.val, hjd⟩
    have h1 := s.step_inc k
    have hkc : k.castSucc = j := Fin.ext (by simp [k, Fin.castSucc])
    have hksi : k.succ ≤ i := by
      simp [Fin.le_iff_val_le_val, k, Fin.succ]; omega
    have h2 := s.incDir_const_after k i hksi
    rw [hkc] at h1
    have : (s.verts i).coords (s.incDir k) =
        (s.verts j).coords (s.incDir k) + 1 := by
      rw [h2, h1]
    rw [congr_arg (fun v => v.coords (s.incDir k)) heq] at this
    omega

/-- The vertex set (as a Finset) has cardinality d + 1. -/
theorem GridSimplex.vertex_set_card (s : GridSimplex d N) :
    (univ.image s.verts).card = d + 1 := by
  rw [Finset.card_image_of_injective _ s.verts_injective]
  simp [Fintype.card_fin]

-- ============================================================
-- SECTION V: Coordinate Tracking Lemmas
-- ============================================================

/-- The miss coordinate decreases by exactly 1 at each step,
so at vertex m it equals v₀.coords(miss) - m. -/
theorem GridSimplex.miss_coord_at (s : GridSimplex d N)
    (m : Fin (d + 1)) :
    (s.verts m).coords s.miss =
    (s.verts 0).coords s.miss - m.val := by
  induction m using Fin.induction with
  | zero => simp
  | succ k ih =>
    have hsd := s.step_dec k
    -- step_dec: verts(k.castSucc).coords miss =
    --           verts(k.succ).coords miss + 1
    -- So verts(k.succ).coords miss =
    --    verts(k.castSucc).coords miss - 1
    rw [ih] at hsd
    have hcv : k.castSucc.val = k.val := rfl
    have hsv : k.succ.val = k.val + 1 := rfl
    omega

/-- The base vertex's miss coordinate is at least d
(since it decreases by 1 at each of d steps). -/
theorem GridSimplex.base_miss_ge_d (s : GridSimplex d N) :
    d ≤ (s.verts 0).coords s.miss := by
  induction d with
  | zero => omega
  | succ n ih =>
    -- At step n, coords = base - n, and step_dec says
    -- verts(n.castSucc).coords miss = verts(n.succ).coords miss + 1
    -- so base - n ≥ 1, i.e., base ≥ n + 1.
    have hsd := s.step_dec ⟨n, by omega⟩
    have hmca := s.miss_coord_at ⟨n, by omega⟩
    have : (⟨n, by omega⟩ : Fin (n + 2)).val = n := rfl
    rw [this] at hmca
    -- hmca : verts(⟨n,...⟩).coords miss = base - n
    -- hsd : verts(⟨n,...⟩.castSucc).coords miss = verts(⟨n,...⟩.succ).coords miss + 1
    have hcv : (⟨n, by omega⟩ : Fin (n + 1)).castSucc.val = n := rfl
    have hsv : (⟨n, by omega⟩ : Fin (n + 1)).succ.val = n + 1 := rfl
    -- castSucc and the original Fin (n+2) element have same val
    have : (⟨n, by omega⟩ : Fin (n + 1)).castSucc = (⟨n, by omega⟩ : Fin (n + 2)) := by
      ext; simp
    rw [this] at hsd
    rw [hmca] at hsd
    -- hsd : base - n = verts(⟨n,...⟩.succ).coords miss + 1
    -- This means base - n ≥ 1, so base ≥ n + 1
    omega

/-- At vertex m, the miss coordinate is at least d - m. -/
theorem GridSimplex.miss_coord_ge (s : GridSimplex d N)
    (m : Fin (d + 1)) :
    d - m.val ≤ (s.verts m).coords s.miss := by
  rw [s.miss_coord_at m]
  have := s.base_miss_ge_d
  omega

/-- incDir(k) is the unique complement of miss: incDir gives
a bijection from Fin d to Fin(d+1) \ {miss}. This means
every j ≠ miss is in the range of incDir. -/
theorem GridSimplex.incDir_surj_complement (s : GridSimplex d N)
    (j : Fin (d + 1)) (hj : j ≠ s.miss) :
    ∃ k : Fin d, s.incDir k = j := by
  -- incDir is injective from Fin d to Fin(d+1), avoiding miss.
  -- Since |Fin d| = d = |Fin(d+1)| - 1 = |Fin(d+1) \ {miss}|,
  -- it must be surjective onto the complement.
  by_contra h
  push_neg at h
  -- All d values incDir(k) are in Fin(d+1) \ {miss, j}
  -- which has d+1-2 = d-1 elements. But incDir is injective
  -- with d values, contradiction.
  have hcard : (Finset.univ.image s.incDir).card = d := by
    rw [Finset.card_image_of_injective _ s.inc_injective]
    simp
  have hsub : Finset.univ.image s.incDir ⊆
      (Finset.univ.erase s.miss).erase j := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨k, rfl⟩ := hx
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨h k, s.miss_ne_inc k⟩
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  have hmiss_mem : s.miss ∈ (Finset.univ : Finset (Fin (d + 1))) := Finset.mem_univ _
  have hj_mem : j ∈ (Finset.univ.erase s.miss) := by
    rw [Finset.mem_erase]
    exact ⟨hj, Finset.mem_univ _⟩
  rw [Finset.card_erase_of_mem hj_mem, Finset.card_erase_of_mem hmiss_mem] at hle
  simp at hle
  omega

-- ============================================================
-- SECTION VI: Adjacency
-- ============================================================

/-- Helper: construct a new BaryPoint by transferring one
unit from coordinate `dec` to coordinate `inc`. -/
noncomputable def BaryPoint.transfer {d N : ℕ}
    (v : BaryPoint d N) (inc dec : Fin (d + 1))
    (h_ne : inc ≠ dec) (h_pos : 0 < v.coords dec) :
    BaryPoint d N where
  coords := fun j =>
    if j = inc then v.coords j + 1
    else if j = dec then v.coords j - 1
    else v.coords j
  sum_eq := by
    have hv := v.sum_eq
    have hkey : ∀ (j : Fin (d + 1)), j ∈ Finset.univ →
      (if j = inc then v.coords j + 1
        else if j = dec then v.coords j - 1
        else v.coords j) + (if j = dec then 1 else 0) =
        v.coords j + (if j = inc then 1 else 0) := by
      intro j _; split_ifs <;> simp_all <;> omega
    have hsums := Finset.sum_congr rfl hkey
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsums
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hsums
    omega

@[simp]
theorem BaryPoint.transfer_coords_inc {d N : ℕ}
    (v : BaryPoint d N) (inc dec : Fin (d + 1))
    (h_ne : inc ≠ dec) (h_pos : 0 < v.coords dec) :
    (v.transfer inc dec h_ne h_pos).coords inc =
    v.coords inc + 1 := by
  simp [BaryPoint.transfer]

@[simp]
theorem BaryPoint.transfer_coords_dec {d N : ℕ}
    (v : BaryPoint d N) (inc dec : Fin (d + 1))
    (h_ne : inc ≠ dec) (h_pos : 0 < v.coords dec) :
    (v.transfer inc dec h_ne h_pos).coords dec =
    v.coords dec - 1 := by
  simp [BaryPoint.transfer, Ne.symm h_ne]

@[simp]
theorem BaryPoint.transfer_coords_other {d N : ℕ}
    (v : BaryPoint d N) (inc dec : Fin (d + 1))
    (h_ne : inc ≠ dec) (h_pos : 0 < v.coords dec)
    (j : Fin (d + 1)) (hj_inc : j ≠ inc)
    (hj_dec : j ≠ dec) :
    (v.transfer inc dec h_ne h_pos).coords j =
    v.coords j := by
  simp [BaryPoint.transfer, hj_inc, hj_dec]

end SpernerGrid
