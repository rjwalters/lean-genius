/-
# Erdős–Ko–Rado, OQ-03: the n = 2k boundary — why the star characterization needs strict n > 2k

The Erdős–Ko–Rado theorem has two halves. The **bound** says an intersecting
family of `k`-subsets of `Fin n` with `n ≥ 2k` has at most `C(n-1, k-1)` members;
the **uniqueness** (or *star characterization*) says that, **when `n > 2k`**, the
only families attaining that bound are the *stars* — all `k`-sets through a fixed
point.

The gallery already covers the bound:
* `ErdosKoRadoOQ01` proves Katona's cyclic-interval lemma (at most `k` pairwise
  intersecting arcs), axiom-free;
* `ErdosKoRadoOQ02` discharges the upper bound `|A| ≤ C(n-1, k-1)` via Mathlib's
  Kruskal–Katona route (`Finset.erdos_ko_rado`) and shows the star **attains** it
  (`IsGreatest`).

What remains for OQ-03 is the *converse* extremal statement: that the maximizer is
**unique** (a star) for `n > 2k`. Mathlib does not have this — the Kruskal–Katona
file lists "Characterise the equality case" as an explicit TODO — and a full Lean
proof of EKR uniqueness is a substantial project (it is strictly harder than the
bound, and at `n = 2k` it is simply *false*).

This entry pins down the part of OQ-03 that is both **sharp and provable**: the
**necessity of the strict inequality `n > 2k`**. We exhibit, at the boundary
`n = 2k` (concretely `n = 4`, `k = 2`), an intersecting family that

  1. attains the EKR maximum `C(n-1, k-1) = 3`, yet
  2. is **not a star** — it has no common element, so it differs from every
     `Star x`.

Hence at `n = 2k` the maximizer is *not* unique: the "triangle" `{01, 12, 02}` and
the star `Star 0 = {01, 02, 03}` are two distinct maximum intersecting families.
This is exactly why the uniqueness half of EKR carries the *strict* hypothesis
`n > 2k`, and it bounds what any future formalization of the full characterization
can claim. The general `n > 2k` uniqueness is recorded as the remaining open target.

## Results (0 sorries, 0 axioms — fully proved)
The EKR bound is re-derived from Mathlib (`Finset.erdos_ko_rado`, as in OQ-02);
the boundary counterexample is verified by `decide` over `Fin 4`.
-/

import Mathlib

open Finset

namespace ErdosKoRadoOQ03

/- ## Definitions (verbatim from the parent / OQ-02 entries) -/

/-- A family of `k`-sets is intersecting if every two members share an element. -/
def IsIntersectingFamily {n : ℕ} (A : Finset (Finset (Fin n))) (k : ℕ) : Prop :=
  (∀ s ∈ A, s.card = k) ∧
  ∀ s t, s ∈ A → t ∈ A → (s ∩ t).Nonempty

/-- The star centered at `x`: all `k`-subsets of `Fin n` containing `x`. -/
def Star {n : ℕ} (x : Fin n) (k : ℕ) : Finset (Finset (Fin n)) :=
  (powersetCard k (univ : Finset (Fin n))).filter (fun s => x ∈ s)

/-- Every member of a star contains its center. -/
theorem mem_Star_imp_mem {n k : ℕ} {x : Fin n} {s : Finset (Fin n)}
    (hs : s ∈ Star x k) : x ∈ s := by
  rw [Star, mem_filter] at hs
  exact hs.2

-- ============================================================
-- PART I: The EKR upper bound (de-axiomatized, as in OQ-02)
-- ============================================================

/-- **The Erdős–Ko–Rado upper bound.** For an intersecting family of `k`-sets in
`Fin n` with `n ≥ 2k`, `|A| ≤ C(n-1, k-1)`.  Bridges the bespoke predicate to
Mathlib's `Set.Intersecting` / `Set.Sized` and invokes `Finset.erdos_ko_rado`.
No cyclic intervals, no axioms. -/
theorem ekr_bound {n k : ℕ} (hn : n ≥ 2 * k)
    (A : Finset (Finset (Fin n))) (hA : IsIntersectingFamily A k) :
    A.card ≤ (n - 1).choose (k - 1) := by
  have hsized : (A : Set (Finset (Fin n))).Sized k := fun s hs => hA.1 s (mem_coe.mp hs)
  have hinter : (A : Set (Finset (Fin n))).Intersecting := by
    intro s hs t ht
    rw [Finset.not_disjoint_iff_nonempty_inter]
    exact hA.2 s t (mem_coe.mp hs) (mem_coe.mp ht)
  have hle : k ≤ n / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    omega
  exact Finset.erdos_ko_rado hinter hsized hle

-- ============================================================
-- PART II: The boundary counterexample at n = 4 = 2·2
-- ============================================================

/-- The "triangle" family of `2`-subsets of `Fin 4`: `{0,1}`, `{1,2}`, `{0,2}`.
Every two of these share a vertex, but the three share no common vertex. -/
def triangle : Finset (Finset (Fin 4)) := {{0, 1}, {1, 2}, {0, 2}}

/-- The triangle is an intersecting family of `2`-sets. -/
theorem triangle_intersecting : IsIntersectingFamily triangle 2 := by
  unfold IsIntersectingFamily; decide

/-- The triangle has three members. -/
theorem triangle_card : triangle.card = 3 := by decide

/-- The EKR maximum value at `n = 4`, `k = 2` is `C(3,1) = 3`. -/
theorem ekr_value : (4 - 1).choose (2 - 1) = 3 := by decide

/-- **The triangle attains the EKR maximum at the boundary `n = 2k = 4`.**
Its size equals the bound `C(3,1) = 3`, and (by `ekr_bound`, valid since
`4 ≥ 2·2`) no intersecting family of `2`-sets in `Fin 4` is larger. -/
theorem triangle_is_maximum :
    triangle.card = (4 - 1).choose (2 - 1) ∧
      ∀ A : Finset (Finset (Fin 4)), IsIntersectingFamily A 2 →
        A.card ≤ triangle.card := by
  refine ⟨by decide, fun A hA => ?_⟩
  rw [triangle_card]
  have h := ekr_bound (n := 4) (k := 2) (by norm_num) A hA
  rw [ekr_value] at h
  exact h

/-- The triangle has no common element. -/
theorem triangle_no_common : ¬ ∃ x : Fin 4, ∀ s ∈ triangle, x ∈ s := by decide

/-- **The triangle is not a star.** It differs from `Star x` for every center `x`,
because a star's members all share the center while the triangle's do not. -/
theorem triangle_ne_star : ∀ x : Fin 4, triangle ≠ Star x 2 := by
  intro x h
  exact triangle_no_common ⟨x, fun s hs => mem_Star_imp_mem (h ▸ hs)⟩

-- ============================================================
-- PART III: Non-uniqueness at n = 2k
-- ============================================================

/-- The star `Star 0` at `n = 4`, `k = 2` also has three members, so it too is a
maximum intersecting family — a *distinct* maximizer from the triangle. -/
theorem star_zero_card : (Star (0 : Fin 4) 2).card = 3 := by decide

/-- The star `Star 0` is intersecting (every member contains `0`). -/
theorem star_zero_intersecting : IsIntersectingFamily (Star (0 : Fin 4) 2) 2 := by
  unfold IsIntersectingFamily; decide

/-- **Main theorem — EKR uniqueness fails at `n = 2k`.**
At the boundary `n = 2k = 4`, `k = 2`, the triangle is a maximum intersecting
family of `2`-sets (it attains the bound `C(3,1) = 3`) that is **not a star**.
Together with the genuine star `Star 0` (also a size-`3` maximizer), this gives
two distinct maximizers, so the EKR maximizer is *not* unique when `n = 2k`.
This is precisely why the star-characterization half of Erdős–Ko–Rado (OQ-03)
requires the **strict** inequality `n > 2k`. -/
theorem ekr_uniqueness_fails_at_2k :
    -- the triangle is a maximum intersecting family ...
    IsIntersectingFamily triangle 2 ∧
      triangle.card = (4 - 1).choose (2 - 1) ∧
      -- ... that is not any star ...
      (∀ x : Fin 4, triangle ≠ Star x 2) ∧
      -- ... while a genuine star is a distinct maximizer of the same size.
      IsIntersectingFamily (Star (0 : Fin 4) 2) 2 ∧
      (Star (0 : Fin 4) 2).card = 3 ∧
      triangle ≠ Star (0 : Fin 4) 2 :=
  ⟨triangle_intersecting, by decide, triangle_ne_star, star_zero_intersecting,
    star_zero_card, triangle_ne_star 0⟩

end ErdosKoRadoOQ03
