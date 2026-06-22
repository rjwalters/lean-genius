/-
# Erdős–Ko–Rado: the double-counting bound, de-axiomatized (OQ-02)

The parent gallery entry `ErdosKoRado` formalizes the Erdős–Ko–Rado theorem via
Katona's cyclic-permutation argument, but it leaves the heart of the proof —
the upper bound

    |𝒜| ≤ C(n-1, k-1)    for an intersecting family of k-sets, n ≥ 2k

— as an `axiom` (`double_counting_bound`), because Katona's double count rests on
a cyclic-interval lemma whose modular bookkeeping resisted a Lean formalization
(see the sibling open question OQ-01, released unsolved).

This file answers OQ-02 by discharging that axiom **completely, with zero axioms**,
taking an entirely different route: Mathlib proves Erdős–Ko–Rado through the
Kruskal–Katona shadow inequality (`Finset.erdos_ko_rado`), sidestepping cyclic
intervals altogether. We

  1. bridge the parent's bespoke predicate `IsIntersectingFamily A k` to Mathlib's
     `Set.Intersecting` together with `Set.Sized k`;
  2. obtain the upper bound `A.card ≤ (n-1).choose (k-1)` axiom-free; and
  3. prove the bound is **sharp** — the star (all k-sets through a fixed point)
     is an intersecting family of size exactly `(n-1).choose (k-1)` — so that the
     maximum is pinned: it `IsGreatest`.

The result is the full extremal statement of Erdős–Ko–Rado for the parent's
predicate, machine-checked with no remaining assumptions.

Self-contained: imports only Mathlib. The definitions `IsIntersectingFamily` and
`Star` are reproduced verbatim from the parent (which is `axiomatized`; importing
it would pull its nine axioms into this file).
-/
import Mathlib

open Finset

namespace ErdosKoRadoOQ02

/- ## Definitions (verbatim from the parent entry) -/

/-- A family of `k`-sets is intersecting if every two members share an element. -/
def IsIntersectingFamily {n : ℕ} (A : Finset (Finset (Fin n))) (k : ℕ) : Prop :=
  (∀ s ∈ A, s.card = k) ∧
  ∀ s t, s ∈ A → t ∈ A → (s ∩ t).Nonempty

/-- The star centered at `x`: all `k`-subsets of `Fin n` containing `x`. -/
def Star {n : ℕ} (x : Fin n) (k : ℕ) : Finset (Finset (Fin n)) :=
  (powersetCard k (univ : Finset (Fin n))).filter (fun s => x ∈ s)

/- ## Bridge to Mathlib's `Set.Intersecting` / `Set.Sized` -/

/-- The parent's uniformity condition is Mathlib's `Set.Sized k`. -/
theorem sized_of_isIntersectingFamily {n k : ℕ} {A : Finset (Finset (Fin n))}
    (hA : IsIntersectingFamily A k) : (A : Set (Finset (Fin n))).Sized k := by
  intro s hs
  exact hA.1 s (mem_coe.mp hs)

/-- The parent's pairwise-nonempty-intersection condition is Mathlib's
`Set.Intersecting`. The translation is `not_disjoint_iff_nonempty_inter`:
two finsets are non-disjoint exactly when their intersection is nonempty. -/
theorem intersecting_of_isIntersectingFamily {n k : ℕ} {A : Finset (Finset (Fin n))}
    (hA : IsIntersectingFamily A k) : (A : Set (Finset (Fin n))).Intersecting := by
  intro s hs t ht
  rw [Finset.not_disjoint_iff_nonempty_inter]
  exact hA.2 s t (mem_coe.mp hs) (mem_coe.mp ht)

/- ## The upper bound, axiom-free -/

/-- **The Erdős–Ko–Rado upper bound (the parent's `double_counting_bound`),
de-axiomatized.** For an intersecting family of `k`-sets in `Fin n` with `n ≥ 2k`,

    |A| ≤ C(n-1, k-1).

Proof: bridge to Mathlib's predicates and invoke `Finset.erdos_ko_rado`, whose
side condition `k ≤ n / 2` follows from `2k ≤ n`. No cyclic intervals, no axioms. -/
theorem ekr_bound {n k : ℕ} (hn : n ≥ 2 * k)
    (A : Finset (Finset (Fin n))) (hA : IsIntersectingFamily A k) :
    A.card ≤ (n - 1).choose (k - 1) := by
  have hle : k ≤ n / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    omega
  exact Finset.erdos_ko_rado (intersecting_of_isIntersectingFamily hA)
    (sized_of_isIntersectingFamily hA) hle

/- ## Sharpness: the star attains the bound -/

/-- The star is an intersecting family of `k`-sets (every member contains the
center, so any two intersect there). -/
theorem star_is_intersecting {n k : ℕ} (_hk : 0 < k) (x : Fin n) :
    IsIntersectingFamily (Star x k) k := by
  unfold IsIntersectingFamily Star
  refine ⟨?_, ?_⟩
  · intro s hs
    simp only [mem_filter, mem_powersetCard_univ] at hs
    exact hs.1
  · intro s t hs ht
    simp only [mem_filter, mem_powersetCard_univ] at hs ht
    exact ⟨x, mem_inter.mpr ⟨hs.2, ht.2⟩⟩

/-- The star has exactly `C(n-1, k-1)` members: deleting the center is a bijection
from `k`-sets through `x` onto `(k-1)`-subsets of the remaining `n-1` points. -/
theorem star_card {n k : ℕ} (hk : 0 < k) (x : Fin n) :
    (Star x k).card = (n - 1).choose (k - 1) := by
  unfold Star
  let target := powersetCard (k - 1) (univ.erase x)
  have h_target_card : target.card = (n - 1).choose (k - 1) := by
    simp only [target, card_powersetCard]
    congr 1
    simp [card_erase_of_mem (mem_univ x)]
  rw [← h_target_card]
  apply Finset.card_bij (fun s _ => s.erase x)
  · intro s hs
    simp only [mem_filter, mem_powersetCard_univ] at hs
    simp only [target, mem_powersetCard]
    refine ⟨?_, ?_⟩
    · intro y hy
      simp only [mem_erase] at hy ⊢
      exact ⟨hy.1, mem_univ y⟩
    · rw [card_erase_of_mem hs.2, hs.1]
  · intro s₁ hs₁ s₂ hs₂ heq
    simp only [mem_filter, mem_powersetCard_univ] at hs₁ hs₂
    have h1 : s₁ = insert x (s₁.erase x) := (insert_erase hs₁.2).symm
    have h2 : s₂ = insert x (s₂.erase x) := (insert_erase hs₂.2).symm
    rw [h1, h2, heq]
  · intro t ht
    simp only [target, mem_powersetCard] at ht
    have hx_notin : x ∉ t := by
      intro hx
      have hmem := ht.1 hx
      rw [mem_erase] at hmem
      exact hmem.1 rfl
    refine ⟨insert x t, ?_, erase_insert hx_notin⟩
    rw [mem_filter, mem_powersetCard_univ]
    refine ⟨?_, mem_insert_self x t⟩
    rw [card_insert_of_notMem hx_notin, ht.2]
    omega

/- ## The exact maximum -/

/-- **The full extremal Erdős–Ko–Rado statement, axiom-free.** Among the sizes of
all intersecting families of `k`-sets in `Fin n` (with `n ≥ 2k`, `k ≥ 1`), the
greatest is exactly `C(n-1, k-1)`: the star achieves it (membership) and nothing
exceeds it (the upper bound). -/
theorem ekr_isGreatest {n k : ℕ} (hn : n ≥ 2 * k) (hk : 0 < k) :
    IsGreatest {c | ∃ A : Finset (Finset (Fin n)), IsIntersectingFamily A k ∧ A.card = c}
      ((n - 1).choose (k - 1)) := by
  have hn0 : 0 < n := by omega
  -- a center exists since `n > 0`
  let x : Fin n := ⟨0, hn0⟩
  refine ⟨⟨Star x k, star_is_intersecting hk x, star_card hk x⟩, ?_⟩
  rintro c ⟨A, hA, rfl⟩
  exact ekr_bound hn A hA

/- ## Concrete instances -/

/-- `n = 6, k = 3`: the maximum intersecting family has `C(5,2) = 10` members. -/
theorem ekr_max_6_3 :
    IsGreatest {c | ∃ A : Finset (Finset (Fin 6)), IsIntersectingFamily A 3 ∧ A.card = c} 10 := by
  have h := ekr_isGreatest (n := 6) (k := 3) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- `n = 4, k = 2`: the maximum intersecting family of pairs has `C(3,1) = 3`
members (the three pairs through a common point). -/
theorem ekr_max_4_2 :
    IsGreatest {c | ∃ A : Finset (Finset (Fin 4)), IsIntersectingFamily A 2 ∧ A.card = c} 3 := by
  have h := ekr_isGreatest (n := 4) (k := 2) (by norm_num) (by norm_num)
  norm_num at h
  exact h

end ErdosKoRadoOQ02
