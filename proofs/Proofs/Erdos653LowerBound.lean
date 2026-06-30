/-
Erdős Problem #653 — Elementary Lower-Bound Construction (companion)

Source: https://erdosproblems.com/653

This companion to `Erdos653Problem.lean` supplies the *lower-bound* side that the
main file leaves unproven. The main file states `g(n) ≤ n` and the sharper
`g(n) ≤ n - 1` (theorem `g_le_n_sub_one`), but its only lower bound is the deep
literature axiom `csizmadia_bound` (`g(n) > 0.7n`). Even the trivial lower bound
`g(n) ≥ 1` is only asserted in a docstring, never proved.

This file provides:

* `collinearConfig n` — the explicit `n`-point configuration
  `(0,0), (1,0), …, (n-1,0)` on the x-axis, with `collinearConfig_card` proving
  it has exactly `n` distinct points. This is the reusable construction needed by
  *any* elementary lower bound on `g`.
* `gSet`, `gSet_bddAbove`, `g_eq_sSup` — the supremum set that defines `g`, shown
  bounded above, so `le_csSup` applies.
* `g_ge_one` — the file's first *proved* lower bound: `g(n) ≥ 1` for `n ≥ 1`.
  (Witnessed by any nonempty configuration; needs no distance values.)
* `euclidDist_collinearPoint` — the verified fact that the distance between two
  x-axis points is `|i - j|`. This seeds the deferred sharper bound
  `g(n) ≥ ⌈n/2⌉`, whose remaining combinatorial steps (the distinct distances
  from the i-th collinear point number `max(i, n-1-i)`, giving `⌈n/2⌉` distinct
  R-values overall) are certified numerically in
  `research/problems/erdos-653-oq-01/verify_g_structure.py`.

The open conjecture `g(n) ≥ (1 - o(1))n` is OUT OF SCOPE and untouched here.
-/

import Mathlib.Tactic
import Proofs.Erdos653Problem

namespace Erdos653

open Finset Real

/-- The `n` collinear points `(0,0), (1,0), …, (n-1,0)` on the x-axis. -/
noncomputable def collinearConfig (n : ℕ) : Finset (Fin 2 → ℝ) :=
  (Finset.range n).image (fun i : ℕ => ![(i : ℝ), 0])

/-- The collinear configuration has exactly `n` distinct points. -/
theorem collinearConfig_card (n : ℕ) : (collinearConfig n).card = n := by
  unfold collinearConfig
  rw [Finset.card_image_of_injOn]
  · exact Finset.card_range n
  · intro a _ b _ hab
    have h0 : (a : ℝ) = (b : ℝ) := by
      have := congrFun hab 0
      simpa using this
    exact_mod_cast h0

/-- For every `n` there exists an `n`-point configuration (the collinear one). -/
theorem collinearConfig_exists (n : ℕ) :
    ∃ S : Finset (Fin 2 → ℝ), S.card = n :=
  ⟨collinearConfig n, collinearConfig_card n⟩

/-- The set of attainable distinct-R-value counts for `n`-point configurations.
`g n` is by definition the supremum of this set. -/
def gSet (n : ℕ) : Set ℕ :=
  { k : ℕ | ∃ S : Finset (Fin 2 → ℝ), S.card = n ∧ numDistinctRValues S = k }

/-- Membership in `gSet` is exactly the existence of a witnessing configuration. -/
theorem mem_gSet {n k : ℕ} :
    k ∈ gSet n ↔
      ∃ S : Finset (Fin 2 → ℝ), S.card = n ∧ numDistinctRValues S = k :=
  Iff.rfl

/-- `g n` is the supremum of `gSet n` (unfolds the definition of `g`). -/
theorem g_eq_sSup (n : ℕ) : g n = sSup (gSet n) := rfl

/-- The attainable-count set is bounded above by `n`: a configuration with `n`
points has at most `n` distinct R-values (`card_image_le`). -/
theorem gSet_bddAbove (n : ℕ) : BddAbove (gSet n) := by
  refine ⟨n, ?_⟩
  intro k hk
  obtain ⟨S, hcard, rfl⟩ := mem_gSet.mp hk
  unfold numDistinctRValues rValueSet
  calc (S.image (distinctDistCount S)).card
      ≤ S.card := Finset.card_image_le
    _ = n := hcard

/-- Any nonempty configuration has at least one distinct R-value. -/
theorem numDistinctRValues_pos {S : Finset (Fin 2 → ℝ)} (hS : S.Nonempty) :
    0 < numDistinctRValues S := by
  unfold numDistinctRValues rValueSet
  exact (hS.image (distinctDistCount S)).card_pos

/-- **First proved lower bound:** `g(n) ≥ 1` for `n ≥ 1`.

The main file asserts this only in a docstring ("Trivial Lower Bound: g(n) ≥ 1");
here it is an actual theorem. Witnessed by `collinearConfig n`, which is nonempty
for `n ≥ 1` and therefore contributes at least one distinct R-value to `gSet n`. -/
theorem g_ge_one (n : ℕ) (hn : 1 ≤ n) : 1 ≤ g n := by
  rw [g_eq_sSup]
  have hne : (collinearConfig n).Nonempty := by
    rw [← Finset.card_pos, collinearConfig_card]; omega
  have hmem : numDistinctRValues (collinearConfig n) ∈ gSet n :=
    mem_gSet.mpr ⟨collinearConfig n, collinearConfig_card n, rfl⟩
  have hpos : 1 ≤ numDistinctRValues (collinearConfig n) := numDistinctRValues_pos hne
  calc 1 ≤ numDistinctRValues (collinearConfig n) := hpos
    _ ≤ sSup (gSet n) := le_csSup (gSet_bddAbove n) hmem

/-- **Distance seed for the `⌈n/2⌉` bound.** The Euclidean distance between two
x-axis points `(i,0)` and `(j,0)` is `|i - j|`. The distinct distances from the
`i`-th collinear point therefore number `max(i, n-1-i)`, and the distinct
R-values across the configuration number `⌈n/2⌉` (certified numerically; the
combinatorial Lean proof is the deferred next step). -/
theorem euclidDist_collinearPoint (i j : ℝ) :
    euclidDist ![i, 0] ![j, 0] = |i - j| := by
  unfold euclidDist
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show ((0 : ℝ) - 0) = 0 by ring, show (0 : ℝ) ^ 2 = 0 by ring, add_zero,
    Real.sqrt_sq_eq_abs]

/-! ## The sharp elementary lower bound `g(n) ≥ ⌈n/2⌉`

The remaining elementary lower bound. The collinear configuration achieves
`numDistinctRValues = ⌈n/2⌉ = (n+1)/2`, so `g(n) ≥ (n+1)/2`. The argument has three
layers: a pure-ℕ counting identity (`maxCount_image_card`), a pure-ℕ image
characterization of the per-point distance multiset (`absDiff_image_eq`), and a single
real-arithmetic bridge (`distinctDistCount_collinearConfig`) that ports the ℕ count to
the actual Euclidean distinct-distance count via `euclidDist_collinearPoint`. -/

/-- **ℕ counting core.** The per-point distinct-distance counts `{max(i, n-1-i) : i < n}`
take exactly `⌈n/2⌉ = (n+1)/2` distinct values: the image fills `Finset.Icc (n/2) (n-1)`. -/
theorem maxCount_image_card (n : ℕ) :
    ((Finset.range n).image (fun i => max i (n - 1 - i))).card = (n + 1) / 2 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have h : (Finset.range n).image (fun i => max i (n - 1 - i))
        = Finset.Icc (n / 2) (n - 1) := by
      ext m
      simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
      constructor
      · rintro ⟨i, hi, rfl⟩; omega
      · rintro ⟨h1, h2⟩; exact ⟨m, by omega, by omega⟩
    rw [h, Nat.card_Icc]; omega

/-- **ℕ image characterization.** The natural-number distances `|i - j| = max i j - min i j`
from index `i` to the other indices `j ∈ {0,…,n-1} \ {i}` fill exactly `[1, max(i, n-1-i)]`. -/
theorem absDiff_image_eq (n i : ℕ) (hi : i < n) :
    ((Finset.range n).erase i).image (fun j => max i j - min i j)
      = Finset.Icc 1 (max i (n - 1 - i)) := by
  ext m
  simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨j, ⟨hji, hjn⟩, rfl⟩; omega
  · rintro ⟨hm1, hm2⟩
    by_cases hmi : m ≤ i
    · exact ⟨i - m, ⟨by omega, by omega⟩, by omega⟩
    · exact ⟨i + m, ⟨by omega, by omega⟩, by omega⟩

/-- **L1 — the real-arithmetic bridge.** In the collinear configuration the `i`-th point
sees exactly `max(i, n-1-i)` distinct distances. The distances to the other points are the
reals `|i - j|`, `j ≠ i`, which are the casts of the naturals filling `[1, max(i, n-1-i)]`;
counting them reduces to `absDiff_image_eq` via the injectivity of `ℕ ↪ ℝ`. -/
theorem distinctDistCount_collinearConfig (n i : ℕ) (hi : i < n) :
    distinctDistCount (collinearConfig n) ![(i : ℝ), 0] = max i (n - 1 - i) := by
  -- The nat distance `max a b - min a b` casts to the real `|a - b|`.
  have hcast : ∀ a b : ℕ, (↑(max a b - min a b) : ℝ) = |(a : ℝ) - b| := by
    intro a b
    rcases le_total a b with h | h
    · have hr : (a : ℝ) ≤ b := by exact_mod_cast h
      rw [max_eq_right h, min_eq_left h, Nat.cast_sub h, abs_of_nonpos (by linarith)]; ring
    · have hr : (b : ℝ) ≤ a := by exact_mod_cast h
      rw [max_eq_left h, min_eq_right h, Nat.cast_sub h, abs_of_nonneg (by linarith)]
  -- The distance set is the cast image of the ℕ abs-difference set.
  have hset : distanceSet (collinearConfig n) ![(i : ℝ), 0]
      = (((Finset.range n).erase i).image (fun j => max i j - min i j)).image
          (fun k : ℕ => (k : ℝ)) := by
    ext d
    constructor
    · intro hd
      unfold distanceSet at hd
      rw [Finset.mem_image] at hd
      obtain ⟨p, hpf, hpd⟩ := hd
      rw [Finset.mem_filter] at hpf
      obtain ⟨hpmem, hpne⟩ := hpf
      unfold collinearConfig at hpmem
      rw [Finset.mem_image] at hpmem
      obtain ⟨j, hjr, hjp⟩ := hpmem
      rw [Finset.mem_range] at hjr
      subst hjp
      have hji : j ≠ i := by intro h; apply hpne; rw [h]
      rw [euclidDist_collinearPoint] at hpd
      rw [Finset.mem_image]
      refine ⟨max i j - min i j, ?_, ?_⟩
      · rw [Finset.mem_image]
        exact ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_range.mpr hjr⟩, rfl⟩
      · rw [hcast]; exact hpd
    · intro hd
      rw [Finset.mem_image] at hd
      obtain ⟨k, hk, hkd⟩ := hd
      rw [Finset.mem_image] at hk
      obtain ⟨j, hje, hjk⟩ := hk
      rw [Finset.mem_erase, Finset.mem_range] at hje
      obtain ⟨hji, hjn⟩ := hje
      unfold distanceSet
      rw [Finset.mem_image]
      refine ⟨![(j : ℝ), 0], ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · unfold collinearConfig
          rw [Finset.mem_image]
          exact ⟨j, Finset.mem_range.mpr hjn, rfl⟩
        · intro h
          have hh := congrFun h 0
          simp only [Matrix.cons_val_zero] at hh
          exact hji (by exact_mod_cast hh)
      · rw [euclidDist_collinearPoint, ← hcast i j, hjk]; exact hkd
  unfold distinctDistCount
  rw [hset, Finset.card_image_of_injective _ Nat.cast_injective, absDiff_image_eq n i hi,
    Nat.card_Icc]
  omega

/-- The collinear configuration realizes exactly `⌈n/2⌉ = (n+1)/2` distinct R-values. -/
theorem numDistinctRValues_collinearConfig (n : ℕ) :
    numDistinctRValues (collinearConfig n) = (n + 1) / 2 := by
  have hrv : rValueSet (collinearConfig n)
      = (Finset.range n).image (fun j => max j (n - 1 - j)) := by
    unfold rValueSet
    ext v
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      unfold collinearConfig at hp
      rw [Finset.mem_image] at hp
      obtain ⟨j, hjr, rfl⟩ := hp
      rw [Finset.mem_range] at hjr
      exact ⟨j, Finset.mem_range.mpr hjr,
        (distinctDistCount_collinearConfig n j hjr).symm⟩
    · rintro ⟨j, hjr, rfl⟩
      rw [Finset.mem_range] at hjr
      refine ⟨![(j : ℝ), 0], ?_, ?_⟩
      · unfold collinearConfig
        rw [Finset.mem_image]
        exact ⟨j, Finset.mem_range.mpr hjr, rfl⟩
      · exact distinctDistCount_collinearConfig n j hjr
  unfold numDistinctRValues
  rw [hrv]
  exact maxCount_image_card n

/-- **Sharp elementary lower bound:** `g(n) ≥ ⌈n/2⌉` (written `(n+1)/2` in ℕ).

Witnessed by `collinearConfig n`: the `n` equally-spaced collinear points
`(0,0),…,(n-1,0)`, whose `i`-th point sees `max(i, n-1-i)` distinct distances, so the
configuration attains `⌈n/2⌉` distinct R-values. This is the file's first lower bound
beyond the trivial `g(n) ≥ 1`; it is the elementary 1-dimensional optimum (no collinear
configuration beats `⌈n/2⌉`), strictly weaker than the deep literature `g(n) > 0.7n`
(`csizmadia_bound`), which requires genuinely 2-dimensional constructions. -/
theorem g_ge_half (n : ℕ) : (n + 1) / 2 ≤ g n := by
  rw [g_eq_sSup]
  exact le_csSup (gSet_bddAbove n)
    (mem_gSet.mpr ⟨collinearConfig n, collinearConfig_card n,
      numDistinctRValues_collinearConfig n⟩)

/-! ## Exact small values of `g`

The merged upper bounds (`g_le_n`, `g_le_n_sub_one`) and lower bounds (`g_ge_one`,
`g_ge_half`) coincide at the smallest arguments, pinning down the *exact* values of `g`
there. These are the first formalized exact values of `g`; each is a one-line `omega`
corollary (`omega` discharges the `Nat` subtraction `n-1` and the division `(n+1)/2`).
`g(4)` does NOT close this way — `g_le_n_sub_one` gives only `g 4 ≤ 3` while `g_ge_half`
gives only `g 4 ≥ 2` — so pinning `g(4) = 3` needs the certified construction. -/

/-- `g(0) = 0`: no points, no distinct distances. From `g_le_n 0` (`g 0 ≤ 0`). -/
theorem g_zero : g 0 = 0 := by
  have h := g_le_n 0
  omega

/-- `g(1) = 1`: from `g_le_n 1` (`g 1 ≤ 1`) and `g_ge_one 1` (`1 ≤ g 1`). -/
theorem g_one : g 1 = 1 := by
  have h₁ := g_le_n 1
  have h₂ := g_ge_one 1 (by norm_num)
  omega

/-- `g(2) = 1`: the first place the sharp ceiling `g(n) ≤ n-1` meets `g(n) ≥ 1`.
From `g_le_n_sub_one 2` (`g 2 ≤ 1`) and `g_ge_one 2` (`1 ≤ g 2`). -/
theorem g_two : g 2 = 1 := by
  have h₁ := g_le_n_sub_one 2 (by norm_num)
  have h₂ := g_ge_one 2 (by norm_num)
  omega

/-- `g(3) = 2`: the sharp ceiling `g(n) ≤ n-1` meets `g(n) ≥ ⌈n/2⌉`.
From `g_le_n_sub_one 3` (`g 3 ≤ 2`) and `g_ge_half 3` (`(3+1)/2 = 2 ≤ g 3`). -/
theorem g_three : g 3 = 2 := by
  have h₁ := g_le_n_sub_one 3 (by norm_num)
  have h₂ := g_ge_half 3
  omega

end Erdos653
