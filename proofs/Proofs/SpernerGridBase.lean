/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Mathlib

/-
# Barycentric Lattice Points for the Freudenthal Grid (clean base)

This file holds the *coordinate primitives* of the concrete Freudenthal grid —
the barycentric lattice point type `SpernerGrid.BaryPoint`, its `onFace`
predicate, and the `IsSperner` boundary condition — factored out of the larger
`SpernerGrid.lean` so they can be reused without pulling in that file's
in-progress `GridSimplex`/`gridAdj`/`boundary_doors_odd` machinery.

The definitions here are byte-for-byte the ones from `SpernerGrid.lean`
(SECTION II, lines 172-223); they are the stable, fully-proved foundation that
the `sperner-ndim-oq-02` "Option C" coordinate bridge (`SpernerNDimOQ02.lean`)
depends on. Keeping them in a dedicated, self-contained file lets the bridge —
and the forthcoming Phase-1 `SpernerTriangulation` instance — build and be
machine-verified independently of the unfinished grid-adjacency proofs.

No axioms, no sorries.
-/

open Finset

namespace SpernerGrid

-- ============================================================
-- Barycentric Lattice Points
-- ============================================================

/-- A barycentric lattice point on the standard d-simplex with
subdivision parameter N: coordinates (b₀, ..., b_d) with
b_i ≥ 0 and ∑ b_i = N. -/
@[ext]
structure BaryPoint (d N : ℕ) where
  coords : Fin (d + 1) → ℕ
  sum_eq : ∑ i, coords i = N

instance (d N : ℕ) : DecidableEq (BaryPoint d N) := by
  intro a b
  by_cases h : a.coords = b.coords
  · exact isTrue (BaryPoint.ext h)
  · exact isFalse (fun hab =>
      h (congr_arg BaryPoint.coords hab))

instance baryPointFintype (d N : ℕ) :
    Fintype (BaryPoint d N) := by
  have equiv : BaryPoint d N ≃
      { f : Fin (d + 1) → Fin (N + 1) //
        ∑ i, (f i).val = N } :=
    { toFun := fun p =>
        ⟨fun i => ⟨p.coords i, by
          have h1 := Finset.single_le_sum
            (f := p.coords) (fun j _ => Nat.zero_le _)
            (Finset.mem_univ i)
          have h2 := p.sum_eq
          omega⟩,
         by simp [p.sum_eq]⟩
      invFun := fun ⟨f, hf⟩ =>
        ⟨fun i => (f i).val, by simpa using hf⟩
      left_inv := fun p => by ext i; simp
      right_inv := fun ⟨f, hf⟩ => by
        ext i; simp }
  exact Fintype.ofEquiv _ equiv.symm

/-- A vertex lies on face k: its k-th barycentric coordinate
is zero. -/
def BaryPoint.onFace {d N : ℕ} (v : BaryPoint d N)
    (k : Fin (d + 1)) : Prop :=
  v.coords k = 0

instance {d N : ℕ} (v : BaryPoint d N)
    (k : Fin (d + 1)) :
    Decidable (v.onFace k) :=
  inferInstanceAs (Decidable (_ = _))

/-- Sperner condition: on face k (where b_k = 0), color k is
forbidden. -/
def IsSperner {d N : ℕ}
    (c : BaryPoint d N → Fin (d + 1)) : Prop :=
  ∀ (v : BaryPoint d N) (k : Fin (d + 1)),
    v.onFace k → c v ≠ k

-- ============================================================
-- SECTION III: Grid Simplices
-- ============================================================
-- (factored verbatim from SpernerGrid.lean SECTION III-V, lines
-- 241-513; these proofs are already machine-checked there and
-- depend only on `BaryPoint` above, so they live here in the
-- clean base to keep the Phase-1 `SpernerTriangulation` instance
-- independent of the unfinished adjacency machinery.)

/-- A d-simplex in the Freudenthal triangulation of Δ_N.

A chain of d+1 barycentric lattice points where each step
transfers one unit of mass from a fixed "miss" coordinate to
a varying "incDir" coordinate. The d increase directions must
be distinct (injective), and miss is not among them.

This means the d+1 directions Fin(d+1) decompose as:
- d directions in range(incDir): each increases exactly once
- 1 direction (miss): decreases at every step

This is the standard Freudenthal/Kuhn construction. -/
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

-- ============================================================
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
-- SECTION VI: Coordinate Reconstruction (new, for Phase-1)
-- ============================================================
-- These characterize every vertex's coordinates purely from the
-- base vertex `verts 0`, `miss`, and `incDir`. They are the
-- arithmetic backbone the Phase-1 canonical-representative
-- predicate (`IsCanon`) and the facet-sharing adjacency need:
-- the whole cell is determined by `(verts 0, miss, incDir)`.

/-- Symmetric counterpart of `incDir_const_after`: coordinate
incDir(k) is unchanged at every vertex m ≤ k.castSucc, since the
only step touching it is step k (at index k, i.e. from
k.castSucc to k.succ). -/
theorem GridSimplex.incDir_const_before (s : GridSimplex d N)
    (k : Fin d) (m : Fin (d + 1))
    (hm : m ≤ k.castSucc) :
    (s.verts m).coords (s.incDir k) =
    (s.verts 0).coords (s.incDir k) := by
  -- Induction on m.val (downward telescoping from 0 up to k.castSucc).
  have : ∀ p : ℕ, (hp : p < d + 1) → p ≤ k.castSucc.val →
      (s.verts ⟨p, hp⟩).coords (s.incDir k) =
      (s.verts 0).coords (s.incDir k) := by
    intro p hp hpk
    induction p with
    | zero => rfl
    | succ p' ih =>
      have hp' : p' < d + 1 := by omega
      have hpk' : p' ≤ k.castSucc.val := by omega
      have ih_val := ih hp' hpk'
      -- Step from p' to p'+1 uses step index ⟨p', _⟩, which is ≠ k
      -- because p' < k.castSucc.val = k.val, so ⟨p',_⟩ ≠ k.
      have hpd : p' < d := by
        have : k.castSucc.val = k.val := rfl
        omega
      let step : Fin d := ⟨p', hpd⟩
      have hstep_ne : k ≠ step := by
        intro heq
        have : k.val = p' := by simpa [step, Fin.ext_iff] using congrArg Fin.val heq
        have hkc : k.castSucc.val = k.val := rfl
        omega
      have hstable := s.incDir_stable k step hstep_ne
      have hsc : step.castSucc = ⟨p', hp'⟩ := by
        ext; simp [step, Fin.castSucc]
      have hss : step.succ = ⟨p' + 1, hp⟩ := by
        ext; simp [step, Fin.succ]
      rw [hss, hsc] at hstable
      rw [hstable, ih_val]
  exact this m.val m.isLt (by simpa using hm)

/-- Every non-miss coordinate `j` increases by exactly 1 across
the whole chain: it equals its base value plus 1 at the last
vertex. (It is incremented exactly once, at the unique step
`k` with `incDir k = j`.) -/
theorem GridSimplex.last_coord_non_miss (s : GridSimplex d N)
    (j : Fin (d + 1)) (hj : j ≠ s.miss) :
    (s.verts (Fin.last d)).coords j =
    (s.verts 0).coords j + 1 := by
  obtain ⟨k, hk⟩ := s.incDir_surj_complement j hj
  subst hk
  -- value at last = value at k.succ (const after), and
  -- value at k.succ = value at k.castSucc + 1 (step_inc), and
  -- value at k.castSucc = value at 0 (const before).
  have hafter : (s.verts (Fin.last d)).coords (s.incDir k) =
      (s.verts k.succ).coords (s.incDir k) :=
    s.incDir_const_after k (Fin.last d) (Fin.le_last _)
  have hbefore : (s.verts k.castSucc).coords (s.incDir k) =
      (s.verts 0).coords (s.incDir k) :=
    s.incDir_const_before k k.castSucc le_rfl
  rw [hafter, s.step_inc k, hbefore]

/-- The miss coordinate decreases by exactly `d` across the whole
chain. (Specialization of `miss_coord_at` to the last vertex.) -/
theorem GridSimplex.last_coord_miss (s : GridSimplex d N) :
    (s.verts (Fin.last d)).coords s.miss =
    (s.verts 0).coords s.miss - d := by
  simpa using s.miss_coord_at (Fin.last d)

-- ============================================================
-- SECTION VII: Full coordinate formula & reconstruction
-- ============================================================
-- `last_coord_non_miss`/`last_coord_miss` above only pin the LAST
-- vertex. Here we give the general per-vertex formula for a
-- non-miss coordinate at an ARBITRARY vertex, and then the
-- reconstruction theorem: a `GridSimplex` is uniquely determined
-- by the triple `(verts 0, miss, incDir)`. This is the arithmetic
-- backbone making the Phase-1 canonical-representative predicate
-- well-posed — per-geometry uniqueness reduces to it.

/-- General formula for a non-miss coordinate at an arbitrary
vertex `m`: coordinate `incDir k` equals its base value, plus one
exactly when step `k` has already occurred (`k.val < m.val`).
Specializes to `last_coord_non_miss` at `m = Fin.last d` (where
`k.val < d` always holds). -/
theorem GridSimplex.coord_incDir_at (s : GridSimplex d N)
    (k : Fin d) (m : Fin (d + 1)) :
    (s.verts m).coords (s.incDir k) =
    (s.verts 0).coords (s.incDir k) + (if k.val < m.val then 1 else 0) := by
  by_cases h : k.val < m.val
  · -- m ≥ k.succ: value = value at k.succ = value at k.castSucc + 1 = base + 1.
    simp only [h, if_true]
    have hge : k.succ ≤ m := by
      rw [Fin.le_def, Fin.val_succ]; omega
    have hafter := s.incDir_const_after k m hge
    have hbefore := s.incDir_const_before k k.castSucc le_rfl
    rw [hafter, s.step_inc k, hbefore]
  · -- m ≤ k.castSucc: coordinate not yet incremented, value = base.
    simp only [h, if_false, Nat.add_zero]
    have hle : m ≤ k.castSucc := by
      rw [Fin.le_def, Fin.coe_castSucc]; omega
    exact s.incDir_const_before k m hle

/-- **Reconstruction theorem.** A `GridSimplex` is uniquely
determined by its base vertex `verts 0`, its `miss` direction, and
its increment-direction function `incDir`: every coordinate of
every vertex is fixed by these three (miss coordinate via
`miss_coord_at`, every other coordinate via `coord_incDir_at`).
This is what makes the Phase-1 canonical-representative predicate
well-posed — distinct canonical encodings of the same geometric
cell are ruled out by reducing to equality of `(verts 0, miss,
incDir)`. -/
theorem GridSimplex.eq_of_base_miss_incDir (s t : GridSimplex d N)
    (hbase : s.verts 0 = t.verts 0)
    (hmiss : s.miss = t.miss)
    (hinc : s.incDir = t.incDir) :
    s = t := by
  have hverts : s.verts = t.verts := by
    funext m
    apply BaryPoint.ext
    funext j
    by_cases hj : j = s.miss
    · -- miss coordinate: determined by `miss_coord_at` + base + miss.
      subst hj
      rw [s.miss_coord_at m, hmiss, t.miss_coord_at m, hbase]
    · -- non-miss coordinate: pick the unique step `k` with `incDir k = j`
      -- and apply the general formula on both sides.
      obtain ⟨k, hk⟩ := s.incDir_surj_complement j hj
      have hL : (s.verts m).coords j
          = (s.verts 0).coords j + (if k.val < m.val then 1 else 0) := by
        rw [← hk]; exact s.coord_incDir_at k m
      have htk : t.incDir k = j := by rw [← hinc]; exact hk
      have hR : (t.verts m).coords j
          = (t.verts 0).coords j + (if k.val < m.val then 1 else 0) := by
        rw [← htk]; exact t.coord_incDir_at k m
      rw [hL, hR, hbase]
  cases s; cases t
  simp only at hverts hmiss hinc
  subst hverts; subst hmiss; subst hinc; rfl

-- ============================================================
-- SECTION VIII: Lexicographic order & canonical representatives
-- ============================================================
-- The `GridSimplex` encoding double-counts each geometric cell:
-- the same vertex *set* admits several `(verts, incDir, miss)`
-- chains (Session-1 d=1 counterexample to `boundary_doors_odd`).
-- To get one representative per geometry — the orientation-free
-- carrier the abstract `SpernerNDim.SpernerTriangulation` needs —
-- we single out the chain whose base vertex `verts 0` is
-- lexicographically minimal among the cell's vertices.
--
-- This section builds the lex order on `BaryPoint`, the
-- canonicality predicate `IsCanon`, their decidability, and the
-- first half of per-geometry uniqueness: two canonical cells with
-- the same vertex set share the same base `verts 0` (the lex
-- order has a unique minimum). With the reconstruction theorem
-- (`eq_of_base_miss_incDir`) above, full uniqueness then reduces
-- to recovering `miss`/`incDir` from `(base, vertex set)` — the
-- next deliverable.

/-- Strict lexicographic order on barycentric points: there is a
coordinate `i` at which `a < b`, with all earlier coordinates
(indices `j < i`) equal. -/
def BaryPoint.lexLT {d N : ℕ} (a b : BaryPoint d N) : Prop :=
  ∃ i : Fin (d + 1),
    (∀ j : Fin (d + 1), j < i → a.coords j = b.coords j) ∧
    a.coords i < b.coords i

/-- Non-strict lexicographic order: equal, or strictly less. -/
def BaryPoint.lexLE {d N : ℕ} (a b : BaryPoint d N) : Prop :=
  a = b ∨ a.lexLT b

instance {d N : ℕ} (a b : BaryPoint d N) : Decidable (a.lexLT b) :=
  inferInstanceAs (Decidable (∃ _, _ ∧ _))

instance {d N : ℕ} (a b : BaryPoint d N) : Decidable (a.lexLE b) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Reflexivity of the non-strict lex order. -/
theorem BaryPoint.lexLE_refl {d N : ℕ} (a : BaryPoint d N) :
    a.lexLE a := Or.inl rfl

/-- The strict lex order is irreflexive. -/
theorem BaryPoint.lexLT_irrefl {d N : ℕ} (a : BaryPoint d N) :
    ¬ a.lexLT a := by
  rintro ⟨i, _, hlt⟩
  exact lt_irrefl _ hlt

/-- The strict lex order is asymmetric: `a < b` and `b < a` is
impossible. (First-differing-coordinate comparison.) -/
theorem BaryPoint.lexLT_asymm {d N : ℕ} {a b : BaryPoint d N}
    (hab : a.lexLT b) (hba : b.lexLT a) : False := by
  obtain ⟨i, hi_eq, hi_lt⟩ := hab
  obtain ⟨i', hi'_eq, hi'_lt⟩ := hba
  rcases lt_trichotomy i i' with h | h | h
  · -- i < i': b's prefix-equality at i contradicts a.coords i < b.coords i
    have := hi'_eq i h
    omega
  · -- i = i': a i < b i and b i < a i
    subst h; omega
  · -- i' < i: a's prefix-equality at i' contradicts b.coords i' < a.coords i'
    have := hi_eq i' h
    omega

/-- Antisymmetry of the non-strict lex order. -/
theorem BaryPoint.lexLE_antisymm {d N : ℕ} {a b : BaryPoint d N}
    (hab : a.lexLE b) (hba : b.lexLE a) : a = b := by
  rcases hab with h | h
  · exact h
  · rcases hba with h' | h'
    · exact h'.symm
    · exact (BaryPoint.lexLT_asymm h h').elim

/-- A `GridSimplex` is *canonical* when its base vertex `verts 0`
is lexicographically minimal among its `d+1` vertices. Each
geometric Freudenthal cell has exactly one canonical encoding (the
lex order has a unique minimum), so the canonical simplices give
one orientation-free representative per cell. -/
def IsCanon {d N : ℕ} (s : GridSimplex d N) : Prop :=
  ∀ k : Fin (d + 1), (s.verts 0).lexLE (s.verts k)

instance {d N : ℕ} (s : GridSimplex d N) : Decidable (IsCanon s) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- **Base uniqueness.** Two canonical `GridSimplex`es with the
same vertex set have the same base vertex. The base is the unique
lex-minimum of the (shared) vertex set, so it is determined by the
geometry alone. This is the first half of per-geometry uniqueness;
combined with the forthcoming `miss`/`incDir` recovery and the
reconstruction theorem `eq_of_base_miss_incDir`, it will show the
canonical encoding is unique per cell. -/
theorem IsCanon.base_unique {d N : ℕ} {s t : GridSimplex d N}
    (hs : IsCanon s) (ht : IsCanon t)
    (hset : Set.range s.verts = Set.range t.verts) :
    s.verts 0 = t.verts 0 := by
  -- t.verts 0 lies in range s.verts, so s.verts 0 ≤ t.verts 0.
  have ht0 : t.verts 0 ∈ Set.range s.verts := by
    rw [hset]; exact ⟨0, rfl⟩
  obtain ⟨j, hj⟩ := ht0
  have h1 : (s.verts 0).lexLE (t.verts 0) := by
    rw [← hj]; exact hs j
  -- s.verts 0 lies in range t.verts, so t.verts 0 ≤ s.verts 0.
  have hs0 : s.verts 0 ∈ Set.range t.verts := by
    rw [← hset]; exact ⟨0, rfl⟩
  obtain ⟨i, hi⟩ := hs0
  have h2 : (t.verts 0).lexLE (s.verts 0) := by
    rw [← hi]; exact ht i
  exact BaryPoint.lexLE_antisymm h1 h2

-- ============================================================
-- SECTION IX: Per-geometry uniqueness (miss/incDir recovery)
-- ============================================================
-- `IsCanon.base_unique` (SECTION VIII) pinned the base vertex of a
-- canonical cell from its vertex set. Here we finish per-geometry
-- uniqueness by recovering the remaining data of the
-- reconstruction triple `(verts 0, miss, incDir)` from the shared
-- geometry, then feeding it to `eq_of_base_miss_incDir`:
--
--   1. `miss_unique`  — `miss` is the unique coordinate at which
--      some vertex dips strictly below the base (every non-`miss`
--      coordinate is non-decreasing along the chain). Needs only
--      the shared base and vertex set.
--   2. `verts_eq`     — with `miss` and base fixed, vertex `m` is
--      the unique cell vertex whose `miss`-coordinate is
--      `base − m` (the `miss`-coordinate is injective in `m`), so
--      the whole vertex *function* is forced.
--   3. `incDir_eq`    — with the vertex function fixed, `incDir k`
--      is the unique coordinate that strictly increases across
--      step `k` (`miss` decreases, all others are unchanged).
--
-- None of the three needs `IsCanon` itself; canonicality enters
-- only through `base_unique`, which supplies the shared base. The
-- payoff `IsCanon.geometry_unique` then says: two canonical cells
-- with the same vertex set are equal — exactly the orientation-free
-- "one representative per geometry" the Phase-1 carrier requires.

/-- **Miss recovery.** Any two `GridSimplex`es sharing their base
vertex and vertex set share their `miss` direction. `miss` is the
unique coordinate at which some vertex of the cell lies strictly
below the base vertex: along the chain the `miss` coordinate
decreases by `d` (down to `base − d`) while every other coordinate
only ever increases (`coord_incDir_at`). For `d = 0` the claim is
vacuous (`miss : Fin 1`). -/
theorem GridSimplex.miss_unique {d N : ℕ} {s t : GridSimplex d N}
    (hbase : s.verts 0 = t.verts 0)
    (hset : Set.range s.verts = Set.range t.verts) :
    s.miss = t.miss := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · -- d = 0: miss lives in `Fin 1`, so both directions are `0`.
    subst hd
    have := s.miss.isLt; have := t.miss.isLt
    exact Fin.ext (by omega)
  · -- d ≥ 1: the last t-vertex dips below the base at coordinate t.miss.
    by_contra hne
    -- t.miss ≠ s.miss, so t.miss = s.incDir k for some step k.
    obtain ⟨k, hk⟩ := s.incDir_surj_complement t.miss (fun h => hne h.symm)
    -- The witness vertex t.verts(last) lies in the shared vertex set.
    have hw : t.verts (Fin.last d) ∈ Set.range s.verts := by
      rw [hset]; exact ⟨Fin.last d, rfl⟩
    obtain ⟨m, hm⟩ := hw
    have hlast : (t.verts (Fin.last d)).coords t.miss
        = (t.verts 0).coords t.miss - d := t.last_coord_miss
    have hbge : d ≤ (t.verts 0).coords t.miss := t.base_miss_ge_d
    -- On the s-side, coordinate s.incDir k = t.miss never drops below base.
    have hge : (s.verts 0).coords (s.incDir k)
        ≤ (s.verts m).coords (s.incDir k) := by
      have hc := s.coord_incDir_at k m
      split_ifs at hc <;> omega
    rw [hk, hbase, hm, hlast] at hge
    omega

/-- **Vertex recovery.** Two `GridSimplex`es sharing their base
vertex, their `miss` direction, and their vertex set share their
whole vertex *function*. With `miss` fixed, the `miss`-coordinate
of vertex `m` is `base − m` (`miss_coord_at`), which is injective
in `m` (the base coordinate is `≥ d`), so each cell vertex is
labelled by a unique chain index. -/
theorem GridSimplex.verts_eq {d N : ℕ} {s t : GridSimplex d N}
    (hbase : s.verts 0 = t.verts 0)
    (hmiss : s.miss = t.miss)
    (hset : Set.range s.verts = Set.range t.verts) :
    s.verts = t.verts := by
  funext m
  -- t.verts m is some s-vertex, say s.verts m'.
  have hmem : t.verts m ∈ Set.range s.verts := by rw [hset]; exact ⟨m, rfl⟩
  obtain ⟨m', hm'⟩ := hmem
  have c1 : (s.verts m').coords s.miss
      = (s.verts 0).coords s.miss - m'.val := s.miss_coord_at m'
  have c2 : (t.verts m).coords t.miss
      = (t.verts 0).coords t.miss - m.val := t.miss_coord_at m
  -- Rewrite c2 entirely onto the s-side via the shared base/miss/vertex.
  rw [← hbase, ← hmiss, ← hm', c1] at c2
  have hbge : d ≤ (s.verts 0).coords s.miss := s.base_miss_ge_d
  have hm1 : m'.val ≤ d := by have := m'.isLt; omega
  have hm2 : m.val ≤ d := by have := m.isLt; omega
  have hval : m.val = m'.val := by omega
  exact (congrArg s.verts (Fin.ext hval)).trans hm'

/-- **Increment-direction recovery.** Two `GridSimplex`es sharing
their vertex function share their `incDir`. At step `k`,
coordinate `incDir k` strictly increases while `miss` decreases and
every other coordinate is unchanged, so `incDir k` is the unique
coordinate that goes up across step `k` — and that is determined by
the (shared) vertices alone (no need to also know `miss` matches:
the `miss`/`step_same` dichotomy is read off each simplex's own
fields). -/
theorem GridSimplex.incDir_eq {d N : ℕ} {s t : GridSimplex d N}
    (hverts : s.verts = t.verts) :
    s.incDir = t.incDir := by
  funext k
  by_contra hne
  -- t increases coordinate (t.incDir k) across step k; phrase it via s.verts.
  have hti := t.step_inc k
  rw [← hverts] at hti
  by_cases hm : t.incDir k = s.miss
  · -- s decreases that coordinate (step_dec) — contradiction.
    have hsd := s.step_dec k
    rw [← hm] at hsd
    omega
  · -- s leaves it unchanged (step_same: ≠ s.incDir k by hne, ≠ s.miss by hm).
    have hss := s.step_same k (t.incDir k) (fun h => hne h.symm) hm
    omega

/-- **Per-geometry uniqueness.** Two canonical `GridSimplex`es with
the same vertex set are equal. The canonical encoding therefore
gives exactly one representative per geometric Freudenthal cell —
the orientation-free carrier the abstract
`SpernerNDim.SpernerTriangulation` needs. Proof: `base_unique`
fixes the base, then `miss_unique`/`verts_eq`/`incDir_eq` recover
the rest of the reconstruction triple, which
`eq_of_base_miss_incDir` turns into equality. -/
theorem IsCanon.geometry_unique {d N : ℕ} {s t : GridSimplex d N}
    (hs : IsCanon s) (ht : IsCanon t)
    (hset : Set.range s.verts = Set.range t.verts) :
    s = t := by
  have hbase : s.verts 0 = t.verts 0 := IsCanon.base_unique hs ht hset
  have hmiss : s.miss = t.miss := GridSimplex.miss_unique hbase hset
  have hverts : s.verts = t.verts := GridSimplex.verts_eq hbase hmiss hset
  have hinc : s.incDir = t.incDir := GridSimplex.incDir_eq hverts
  exact s.eq_of_base_miss_incDir t hbase hmiss hinc

end SpernerGrid
