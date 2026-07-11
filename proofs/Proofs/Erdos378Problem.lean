/-
Erdős Problem #378: Density of Squarefree Binomial Coefficients

Source: https://erdosproblems.com/378
Status: SOLVED (Granville–Ramaré 1996, observed by Aggarwal–Cambie)

Statement:
Let r ≥ 0. Does the density of integers n for which C(n,k) is squarefree
for at least r values of 1 ≤ k < n exist? Is this density > 0?

Answer: YES to both questions.

Key Results:
1. Granville–Ramaré (1996) showed that, for each m, the density η_m of the set
   of n with C(n,k) squarefree for exactly 2m + 2 values of k exists.
2. The density in the original question is 1 − Σ_{0 ≤ m ≤ (r-1)/2} η_m.
3. This density is positive, since the excluded tail (in particular
   η_{(r-1)/2 + 1}) carries positive mass, so the partial sum is < 1.

What this file does:
- The two deep analytic inputs of Granville–Ramaré are isolated as explicit
  axioms (`granville_ramare_density_exists`, `complement_density`). These are the
  *only* assumptions; everything else is machine-checked.
- From those inputs the two questions are resolved with **no sorries**: existence
  of the density follows from a clean complementation argument
  (`natDensity_compl`), and positivity follows from the `d < 1` clause of the
  complement axiom.
- A genuinely verified structural result is added, independent of the axioms:
  `squarefreeCount_even_of_odd` — for odd n the count of squarefree binomials in
  row n is even. This is the elementary reason Granville–Ramaré only ever see
  *even* counts `2m + 2`: the involution k ↦ n − k pairs the interior indices up,
  and for odd n it has no fixed point.

References:
- Granville–Ramaré (1996): "Explicit bounds on exponential sums and the
  scarcity of squarefree binomial coefficients", Mathematika 43.
- Erdős–Graham: Original problem.
- Aggarwal–Cambie: Observed the connection to Granville–Ramaré.
-/

import Mathlib

open Nat Finset

namespace Erdos378

/-
## Part I: Squarefree binomial coefficients

We use Mathlib's `Squarefree`, which is decidable on `ℕ`, rather than a bespoke
definition. This connects the formalization to Mathlib's squarefree theory and
lets the concrete examples below be discharged by `decide`.
-/

/-- `C(n,k)` is squarefree. -/
def BinomialSquarefree (n k : ℕ) : Prop :=
  Squarefree (n.choose k)

/-- For a given `n`, the number of `k ∈ [1, n-1]` with `C(n,k)` squarefree. -/
def squarefreeCount (n : ℕ) : ℕ :=
  ((range n).filter (fun k => 1 ≤ k ∧ Squarefree (n.choose k))).card

/-- `n` has at least `r` values of `k` with `C(n,k)` squarefree. -/
def hasAtLeastSquarefree (n r : ℕ) : Prop :=
  squarefreeCount n ≥ r

/-
## Part II: Concrete examples (fully verified)
-/

/-- `C(2,1) = 2` is squarefree. -/
theorem binomialSquarefree_2_1 : BinomialSquarefree 2 1 := by
  unfold BinomialSquarefree
  rw [show Nat.choose 2 1 = 2 from rfl]
  exact Nat.prime_two.prime.squarefree

/-- `C(4,2) = 6 = 2·3` is squarefree. -/
theorem binomialSquarefree_4_2 : BinomialSquarefree 4 2 := by
  unfold BinomialSquarefree
  rw [show Nat.choose 4 2 = 2 * 3 from rfl, Nat.squarefree_mul_iff]
  exact ⟨by decide, Nat.prime_two.prime.squarefree,
    (by norm_num : Nat.Prime 3).prime.squarefree⟩

/-- `C(6,3) = 20 = 2²·5` is **not** squarefree. -/
theorem not_binomialSquarefree_6_3 : ¬ BinomialSquarefree 6 3 := by
  unfold BinomialSquarefree
  rw [show Nat.choose 6 3 = 20 from rfl]
  intro h
  -- `Squarefree 20` would force `2` (with `2*2 ∣ 20`) to be a unit.
  have hu : IsUnit (2 : ℕ) := h 2 (by norm_num)
  rw [Nat.isUnit_iff] at hu
  exact absurd hu (by norm_num)

/-
## Part III: Symmetry and the parity structure

`C(n,k) = C(n, n-k)`, so squarefreeness is symmetric under `k ↦ n − k`. This is
the elementary reason Granville–Ramaré only ever count *even* numbers `2m + 2` of
squarefree binomials in a row: the interior indices pair up under this involution,
and for odd `n` it is fixed-point free.
-/

/-- Squarefreeness of `C(n,k)` is symmetric under `k ↦ n − k`. -/
theorem binomialSquarefree_symm {n k : ℕ} (hk : k ≤ n) :
    BinomialSquarefree n k ↔ BinomialSquarefree n (n - k) := by
  unfold BinomialSquarefree
  rw [Nat.choose_symm hk]

/-- **Parity theorem.** For odd `n`, the number of squarefree interior binomials
in row `n` is even.

Proof: the involution `k ↦ n − k` preserves the squarefree-index predicate and
splits the counted set into the halves `2k < n` and `2k > n`, which it maps
bijectively onto each other. For odd `n` the case `2k = n` cannot occur, so the
two halves exhaust the set and have equal size; the total is therefore `2 ·`
(size of one half). -/
theorem squarefreeCount_even_of_odd {n : ℕ} (hn : Odd n) :
    Even (squarefreeCount n) := by
  classical
  obtain ⟨j, hj⟩ := hn
  set S : Finset ℕ := (range n).filter (fun k => 1 ≤ k ∧ Squarefree (n.choose k))
    with hS
  set A : Finset ℕ := S.filter (fun k => 2 * k < n) with hA
  set B : Finset ℕ := S.filter (fun k => ¬ 2 * k < n) with hB
  -- Membership in S.
  have memS : ∀ k, k ∈ S ↔ (k < n ∧ 1 ≤ k ∧ Squarefree (n.choose k)) := by
    intro k; simp only [hS, mem_filter, mem_range]; try tauto
  -- For k ∈ S we have k < n.
  have klt : ∀ k ∈ S, k < n := fun k hk => ((memS k).1 hk).1
  -- The map ι := (n - ·) preserves S, using symmetry of binomial squarefreeness.
  have mapsS : ∀ k ∈ S, (n - k) ∈ S := by
    intro k hk
    obtain ⟨hkn, hk1, hsq⟩ := (memS k).1 hk
    rw [memS]
    refine ⟨by omega, by omega, ?_⟩
    rw [Nat.choose_symm hkn.le]; exact hsq
  -- ι is an involution on S.
  have invol : ∀ k ∈ S, n - (n - k) = k := by
    intro k hk; have := klt k hk; omega
  -- Split S = A ⊔ B.
  have splitS : S.card = A.card + B.card := by
    rw [hA, hB]; exact (filter_card_add_filter_neg_card_eq_card _).symm
  -- ι maps A bijectively onto B.
  have cardAB : A.card = B.card := by
    refine card_nbij' (fun k => n - k) (fun k => n - k) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_coe, hA, hB, mem_filter] at hk ⊢
      obtain ⟨hkS, h2k⟩ := hk
      have := klt k hkS
      exact ⟨mapsS k hkS, by omega⟩
    · intro k hk
      simp only [Finset.mem_coe, hA, hB, mem_filter] at hk ⊢
      obtain ⟨hkS, h2k⟩ := hk
      have hkn := klt k hkS
      -- ¬ 2k < n means 2k ≥ n; oddness rules out 2k = n, so 2k > n.
      have h2kn : 2 * k > n := by
        rcases Nat.lt_or_ge (2 * k) n with h | h
        · exact absurd h h2k
        · rcases Nat.eq_or_lt_of_le h with he | hlt
          · omega    -- he : n = 2 * k contradicts hj : n = 2 * j + 1
          · exact hlt
      exact ⟨mapsS k hkS, by omega⟩
    · intro k hk
      simp only [Finset.mem_coe, hA, mem_filter] at hk
      exact invol k hk.1
    · intro k hk
      simp only [Finset.mem_coe, hB, mem_filter] at hk
      exact invol k hk.1
  -- Conclude: squarefreeCount n = 2 · A.card.
  have hsc : squarefreeCount n = S.card := by rw [hS]; rfl
  rw [hsc, splitS, cardAB]
  exact ⟨B.card, rfl⟩

/-- **Parity theorem, even rows.** For even `n ≥ 2`, the number of squarefree
interior binomials in row `n` is *odd* exactly when the central binomial
coefficient `C(n, n/2)` is squarefree.

This complements `squarefreeCount_even_of_odd` and completes the parity theory of
row counts: for odd `n` the count is always even (the involution `k ↦ n − k` is
fixed-point free), while for even `n` the involution has the single fixed point
`k = n/2`, so `squarefreeCount n = 2·|A| + |F|` where `|F| ∈ {0,1}` records
whether the central index is itself squarefree. Hence the count is odd iff
`C(n, n/2)` is squarefree. In particular an odd count forces `n` even — the
Granville–Ramaré count `2m + 2` is even, matching the odd-`n` theorem. -/
theorem squarefreeCount_odd_iff_central_squarefree {n : ℕ}
    (hn : Even n) (hn2 : 2 ≤ n) :
    Odd (squarefreeCount n) ↔ Squarefree (n.choose (n / 2)) := by
  classical
  obtain ⟨j, hj⟩ := hn
  set S : Finset ℕ := (range n).filter (fun k => 1 ≤ k ∧ Squarefree (n.choose k))
    with hS
  set A : Finset ℕ := S.filter (fun k => 2 * k < n) with hA
  set C : Finset ℕ := S.filter (fun k => n < 2 * k) with hC
  set F : Finset ℕ := S.filter (fun k => 2 * k = n) with hF
  have memS : ∀ k, k ∈ S ↔ (k < n ∧ 1 ≤ k ∧ Squarefree (n.choose k)) := by
    intro k; simp only [hS, mem_filter, mem_range]; try tauto
  have klt : ∀ k ∈ S, k < n := fun k hk => ((memS k).1 hk).1
  have mapsS : ∀ k ∈ S, (n - k) ∈ S := by
    intro k hk
    obtain ⟨hkn, hk1, hsq⟩ := (memS k).1 hk
    rw [memS]
    refine ⟨by omega, by omega, ?_⟩
    rw [Nat.choose_symm hkn.le]; exact hsq
  have invol : ∀ k ∈ S, n - (n - k) = k := by
    intro k hk; have := klt k hk; omega
  -- Split S on (2k < n): S = A ⊔ D.
  set D : Finset ℕ := S.filter (fun k => ¬ 2 * k < n) with hD
  have splitAD : S.card = A.card + D.card := by
    rw [hA, hD]; exact (filter_card_add_filter_neg_card_eq_card _).symm
  -- Within D (2k ≥ n), split on (n < 2k): the strict part is C, the equality part F.
  have hCeq : C = D.filter (fun k => n < 2 * k) := by
    ext k; simp only [hC, hD, mem_filter]
    constructor
    · rintro ⟨hkS, h2⟩; exact ⟨⟨hkS, by omega⟩, h2⟩
    · rintro ⟨⟨hkS, _⟩, h2⟩; exact ⟨hkS, h2⟩
  have hFeq : F = D.filter (fun k => ¬ n < 2 * k) := by
    ext k; simp only [hF, hD, mem_filter]
    constructor
    · rintro ⟨hkS, h2⟩; exact ⟨⟨hkS, by omega⟩, by omega⟩
    · rintro ⟨⟨hkS, hnlt⟩, h2⟩; exact ⟨hkS, by omega⟩
  have splitDCF : D.card = C.card + F.card := by
    rw [hCeq, hFeq]
    exact (filter_card_add_filter_neg_card_eq_card (fun k => n < 2 * k)).symm
  -- ι := (n - ·) maps A bijectively onto C.
  have cardAC : A.card = C.card := by
    refine card_nbij' (fun k => n - k) (fun k => n - k) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_coe, hA, hC, mem_filter] at hk ⊢
      obtain ⟨hkS, h2k⟩ := hk
      have hkn := klt k hkS
      exact ⟨mapsS k hkS, by omega⟩
    · intro k hk
      simp only [Finset.mem_coe, hC, hA, mem_filter] at hk ⊢
      obtain ⟨hkS, h2k⟩ := hk
      have hkn := klt k hkS
      exact ⟨mapsS k hkS, by omega⟩
    · intro k hk
      simp only [Finset.mem_coe, hA, mem_filter] at hk
      exact invol k hk.1
    · intro k hk
      simp only [Finset.mem_coe, hC, mem_filter] at hk
      exact invol k hk.1
  -- The fixed-point set F is the singleton {n/2} when squarefree, else empty.
  have eFc : F = S.filter (fun k => k = n / 2) := by
    ext k; simp only [hF, mem_filter]
    constructor
    · rintro ⟨hkS, h2⟩; exact ⟨hkS, by omega⟩
    · rintro ⟨hkS, h2⟩; exact ⟨hkS, by omega⟩
  have hFodd : Odd F.card ↔ (n / 2) ∈ S := by
    by_cases h : (n / 2) ∈ S
    · have hFs : F = {n / 2} := by rw [eFc, filter_eq', if_pos h]
      rw [hFs, Finset.card_singleton]; exact iff_of_true (by decide) h
    · have hFe : F = ∅ := by rw [eFc, filter_eq', if_neg h]
      rw [hFe, Finset.card_empty]; exact iff_of_false (by decide) h
  -- Assemble: squarefreeCount n = 2·|C| + |F|, so its parity is that of |F|.
  have key : squarefreeCount n = 2 * C.card + F.card := by
    have hsc : squarefreeCount n = S.card := by rw [hS]; rfl
    omega
  have hparity : Odd (2 * C.card + F.card) ↔ Odd F.card := by
    rw [Nat.odd_iff, Nat.odd_iff]; omega
  have hlt : n / 2 < n := by omega
  have hge : 1 ≤ n / 2 := by omega
  rw [key, hparity, hFodd, memS (n / 2)]
  tauto

/-- **Complete parity characterization of the row count.**  Unifying the odd-row
theorem (`squarefreeCount_even_of_odd`) and the even-row theorem
(`squarefreeCount_odd_iff_central_squarefree`), the number of squarefree interior
binomials in row `n` is *odd* precisely when `n` is even, at least `2`, and the central
binomial coefficient `C(n, n/2)` is squarefree:

    Odd (squarefreeCount n) ↔ Even n ∧ 2 ≤ n ∧ Squarefree (C(n, n/2)).

Every other row has an even count: odd rows (the `k ↦ n−k` involution is fixed-point
free) and the degenerate rows `n = 0, 1` (empty interior).  In particular an odd count
*forces* `n` even with a squarefree central coefficient — a single closed criterion for
the entire parity behaviour of the row-count sequence. -/
theorem odd_squarefreeCount_iff {n : ℕ} :
    Odd (squarefreeCount n) ↔ (Even n ∧ 2 ≤ n ∧ Squarefree (n.choose (n / 2))) := by
  rcases Nat.even_or_odd n with he | ho
  · -- even `n`: split on the degenerate `n = 0` versus the genuine `n ≥ 2` rows
    rcases lt_or_ge n 2 with hlt | hge
    · have hn0 : n = 0 := by have := Nat.even_iff.mp he; omega
      subst hn0
      have h0 : squarefreeCount 0 = 0 := by simp [squarefreeCount]
      rw [h0]
      exact ⟨fun h => absurd h (by decide), fun h => absurd h.2.1 (by decide)⟩
    · rw [squarefreeCount_odd_iff_central_squarefree he hge]
      exact ⟨fun h => ⟨he, hge, h⟩, fun h => h.2.2⟩
  · -- odd `n`: the count is even, and the right side fails because `n` is not even
    have heven : Even (squarefreeCount n) := squarefreeCount_even_of_odd ho
    exact ⟨fun h => absurd h (not_odd_iff_even.mpr heven),
           fun h => absurd h.1 (not_even_iff_odd.mpr ho)⟩

/-
## Part IV: Natural density
-/

/-- The natural density of `S ⊆ ℕ` is `d` if the counting ratios
`|S ∩ [0,N)| / N` converge to `d`. The count is the cardinality of `S ∩ [0,N)`
as a set (`Set.ncard`), which avoids any decidability assumption on `S`. -/
def NaturalDensity (S : Set ℕ) (d : ℝ) : Prop :=
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    |((S ∩ Set.Iio N).ncard : ℝ) / (N : ℝ) - d| < ε

/-- `S` has a natural density if the limit exists. -/
def HasDensity (S : Set ℕ) : Prop :=
  ∃ d : ℝ, NaturalDensity S d

/-- **Complementation.** If `S` has density `d`, then its complement has density
`1 − d`. Elementary: `S ∩ [0,N)` and `Sᶜ ∩ [0,N)` partition `[0,N)`, so their
cardinalities sum to `N`. -/
theorem natDensity_compl {S : Set ℕ} {d : ℝ} (h : NaturalDensity S d) :
    NaturalDensity Sᶜ (1 - d) := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := h ε hε
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hNpos : 0 < N :=
    lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) hN)
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
  -- `[0,N) = Iio N` is finite, and both pieces are finite.
  have hfinS : (S ∩ Set.Iio N).Finite := (Set.finite_Iio N).inter_of_right S
  have hfinC : (Sᶜ ∩ Set.Iio N).Finite := (Set.finite_Iio N).inter_of_right Sᶜ
  have hIio : (Set.Iio N).ncard = N := by
    rw [← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]
  -- The two pieces partition `Iio N`.
  have hdisj : Disjoint (S ∩ Set.Iio N) (Sᶜ ∩ Set.Iio N) :=
    (disjoint_compl_right).mono Set.inter_subset_left Set.inter_subset_left
  have hunion : (S ∩ Set.Iio N) ∪ (Sᶜ ∩ Set.Iio N) = Set.Iio N := by
    rw [← Set.union_inter_distrib_right, Set.union_compl_self, Set.univ_inter]
  have hpart : (S ∩ Set.Iio N).ncard + (Sᶜ ∩ Set.Iio N).ncard = N := by
    rw [← Set.ncard_union_eq hdisj hfinS hfinC, hunion, hIio]
  -- Real-arithmetic rearrangement.
  have hcard : ((Sᶜ ∩ Set.Iio N).ncard : ℝ)
      = (N : ℝ) - ((S ∩ Set.Iio N).ncard : ℝ) := by
    have hpartR : ((S ∩ Set.Iio N).ncard : ℝ) + ((Sᶜ ∩ Set.Iio N).ncard : ℝ)
        = (N : ℝ) := by exact_mod_cast hpart
    linarith
  rw [hcard]
  have hfield :
      ((N : ℝ) - ((S ∩ Set.Iio N).ncard : ℝ)) / (N : ℝ) - (1 - d)
        = -(((S ∩ Set.Iio N).ncard : ℝ) / (N : ℝ) - d) := by
    field_simp; ring
  rw [hfield, abs_neg]
  exact hN₀ N hN0

/-- **Uniqueness of the natural density.** A set has at most one natural density:
if `S` has density `d` and density `d'` then `d = d'`.

This is the well-definedness underlying the whole density framework — in particular it
justifies `eta m` (defined via `Classical.choose` of `granville_ramare_density_exists`)
being genuinely *the* density `η_m` of `exactlySquarefree m`, not merely *a* value the
counting ratios could approach. Elementary ε/2 argument: if `d ≠ d'`, take
`ε = |d − d'|/2 > 0`; past both thresholds the common counting ratio `x` at `N = max N₁ N₂`
satisfies `|x − d| < ε` and `|x − d'| < ε`, so by the triangle inequality
`|d − d'| ≤ |x − d| + |x − d'| < 2ε = |d − d'|`, a contradiction. Fully verified, uses none
of the Granville–Ramaré axioms. -/
theorem naturalDensity_unique {S : Set ℕ} {d d' : ℝ}
    (h : NaturalDensity S d) (h' : NaturalDensity S d') : d = d' := by
  by_contra hne
  have h0 : 0 < |d - d'| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨N₁, hN₁⟩ := h (|d - d'| / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := h' (|d - d'| / 2) (by linarith)
  have h1 := hN₁ (max N₁ N₂) (le_max_left _ _)
  have h2 := hN₂ (max N₁ N₂) (le_max_right _ _)
  -- `x` is the common counting ratio at `N = max N₁ N₂`.
  set x : ℝ := ((S ∩ Set.Iio (max N₁ N₂)).ncard : ℝ) / ((max N₁ N₂ : ℕ) : ℝ)
  have htri : |d - d'| ≤ |d - x| + |x - d'| := abs_sub_le d x d'
  rw [abs_sub_comm d x] at htri
  linarith [add_lt_add h1 h2, htri]

/-
## Part V: The Granville–Ramaré inputs (axioms)

These two statements are the deep analytic content of Granville–Ramaré (1996).
They are the only assumptions in this file; the theorems below are derived from
them by elementary, fully checked arguments.
-/

/-- The set of `n` with `C(n,k)` squarefree for exactly `2m + 2` values of `k`. -/
def exactlySquarefree (m : ℕ) : Set ℕ :=
  {n : ℕ | squarefreeCount n = 2 * m + 2}

/-- **Granville–Ramaré (1996), Input 1.** The density `η_m` of `exactlySquarefree m`
exists for every `m`. -/
axiom granville_ramare_density_exists :
    ∀ m : ℕ, HasDensity (exactlySquarefree m)

/-- `η_m`: the density of `exactlySquarefree m`. -/
noncomputable def eta (m : ℕ) : ℝ :=
  Classical.choose (granville_ramare_density_exists m)

/-- **Granville–Ramaré (1996), Input 2.** For each `r`, the set of `n` with
*fewer than* `r` squarefree interior binomials has a density
`d = Σ_{0 ≤ m ≤ (r-1)/2} η_m`, and this density is strictly less than `1` (the
excluded tail carries positive mass). The `d < 1` clause is exactly the
positivity content of the resolution. -/
axiom complement_density (r : ℕ) :
    ∃ d : ℝ, d = ∑ m ∈ range ((r - 1) / 2 + 1), eta m ∧
      NaturalDensity {n : ℕ | squarefreeCount n < r} d ∧ d < 1

/-
## Part VI: Resolution of Erdős Problem #378
-/

/-- The set of `n` with at least `r` squarefree interior binomials. -/
def atLeastSquarefree (r : ℕ) : Set ℕ :=
  {n : ℕ | hasAtLeastSquarefree n r}

/-- `atLeastSquarefree r` is the complement of `{n | squarefreeCount n < r}`. -/
theorem atLeastSquarefree_eq_compl (r : ℕ) :
    atLeastSquarefree r = {n : ℕ | squarefreeCount n < r}ᶜ := by
  ext n
  simp only [atLeastSquarefree, hasAtLeastSquarefree, Set.mem_setOf_eq,
    Set.mem_compl_iff, not_lt]

/-- **`hasAtLeastSquarefree` is antitone in the threshold `r`.**  If `n` has at least `r`
values of `k` with `C(n,k)` squarefree, then it has at least `r'` for every `r' ≤ r`: the
requirement only weakens as the threshold drops (`r' ≤ r ≤ squarefreeCount n`). -/
theorem hasAtLeastSquarefree_antitone {n r r' : ℕ} (hr : r' ≤ r)
    (h : hasAtLeastSquarefree n r) : hasAtLeastSquarefree n r' :=
  le_trans hr h

/-- **The `atLeastSquarefree r` sets form a decreasing filtration.**  A larger threshold `r`
carves out a smaller set: `atLeastSquarefree r ⊆ atLeastSquarefree r'` whenever `r' ≤ r`.  So
the Erdős #378 answer sets are nested `atLeastSquarefree 0 ⊇ atLeastSquarefree 1 ⊇ ⋯`, and the
positive-density statement `erdos_378_density_positive` at threshold `r` propagates down to every
smaller threshold `r' ≤ r`. -/
theorem atLeastSquarefree_antitone {r r' : ℕ} (hr : r' ≤ r) :
    atLeastSquarefree r ⊆ atLeastSquarefree r' :=
  fun _ hn => hasAtLeastSquarefree_antitone hr hn

/-- **Main Theorem, Part 1 — the density exists.**

The density of the integers `n` for which `C(n,k)` is squarefree for at least `r`
values of `k` exists. (No sorries: complementation of the Granville–Ramaré input.) -/
theorem erdos_378_density_exists (r : ℕ) :
    HasDensity (atLeastSquarefree r) := by
  obtain ⟨d, _, hd_density, _⟩ := complement_density r
  refine ⟨1 - d, ?_⟩
  rw [atLeastSquarefree_eq_compl]
  exact natDensity_compl hd_density

/-- **Main Theorem, Part 2 — the density is positive.**

The density of the integers `n` for which `C(n,k)` is squarefree for at least `r`
values of `k` is positive. (No sorries: it equals `1 − d` with `d < 1`.) -/
theorem erdos_378_density_positive (r : ℕ) :
    ∃ d : ℝ, d > 0 ∧ NaturalDensity (atLeastSquarefree r) d := by
  obtain ⟨d, _, hd_density, hd_lt⟩ := complement_density r
  refine ⟨1 - d, by linarith, ?_⟩
  rw [atLeastSquarefree_eq_compl]
  exact natDensity_compl hd_density

/-- **Erdős Problem #378 — full resolution.**

For every `r`, the set of `n` with at least `r` squarefree interior binomials has a
natural density, and that density is positive. -/
theorem erdos_378 :
    (∀ r : ℕ, HasDensity (atLeastSquarefree r)) ∧
    (∀ r : ℕ, ∃ d : ℝ, d > 0 ∧ NaturalDensity (atLeastSquarefree r) d) :=
  ⟨erdos_378_density_exists, erdos_378_density_positive⟩

/-- The answer, packaged: for any `r`, the set of `n` with at least `r` squarefree
binomials has a positive density (which in particular exists). -/
theorem erdos_378_answer (r : ℕ) :
    ∃ d : ℝ, d > 0 ∧ HasDensity (atLeastSquarefree r) ∧
      NaturalDensity (atLeastSquarefree r) d := by
  obtain ⟨d, hd_pos, hd_density⟩ := erdos_378_density_positive r
  exact ⟨d, hd_pos, ⟨d, hd_density⟩, hd_density⟩

/-
## Part VII: Elementary two-sided bounds on the natural density
-/

/-- **A natural density is nonnegative.**  The counting ratio
`|S ∩ [0,N)| / N` is a ratio of nonnegative reals, so its limit `d` cannot be
negative: were `d < 0`, taking `ε = −d > 0` past the convergence threshold would
force the (nonnegative) ratio strictly below `0`.  Elementary, uses no axioms. -/
theorem natDensity_nonneg {S : Set ℕ} {d : ℝ} (h : NaturalDensity S d) : 0 ≤ d := by
  by_contra hd
  push_neg at hd
  obtain ⟨N₀, hN₀⟩ := h (-d) (by linarith)
  set N := max N₀ 1 with hNdef
  have hb := hN₀ N (le_max_left _ _)
  have hratio : 0 ≤ ((S ∩ Set.Iio N).ncard : ℝ) / (N : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [abs_lt] at hb
  linarith [hb.2, hratio]

/-- **A natural density is at most one.**  Since `S ∩ [0,N) ⊆ [0,N)` has at most
`N` elements, the counting ratio is `≤ 1`, so its limit `d` cannot exceed `1`:
were `1 < d`, taking `ε = d − 1 > 0` past the threshold would force the ratio
strictly above `1`.  Elementary, uses no axioms. -/
theorem natDensity_le_one {S : Set ℕ} {d : ℝ} (h : NaturalDensity S d) : d ≤ 1 := by
  by_contra hd
  push_neg at hd
  obtain ⟨N₀, hN₀⟩ := h (d - 1) (by linarith)
  set N := max N₀ 1 with hNdef
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hb := hN₀ N (le_max_left _ _)
  have hcard : (S ∩ Set.Iio N).ncard ≤ N := by
    calc (S ∩ Set.Iio N).ncard
        ≤ (Set.Iio N).ncard :=
          Set.ncard_le_ncard Set.inter_subset_right (Set.finite_Iio N)
      _ = N := by rw [← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]
  have hle : ((S ∩ Set.Iio N).ncard : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcard
  have hratio : ((S ∩ Set.Iio N).ncard : ℝ) / (N : ℝ) ≤ 1 := (div_le_one hNR).mpr hle
  rw [abs_lt] at hb
  linarith [hb.1, hratio]

/-- **The Erdős #378 density lies in `(0, 1]`.**  Combining the positivity
`erdos_378_density_positive` with the universal upper bound `natDensity_le_one`:
for every threshold `r`, the density of the integers with at least `r` squarefree
interior binomials exists and lies strictly above `0` and at most `1` — the sharp
two-sided localisation of the answer to Erdős #378. -/
theorem erdos_378_density_mem_Ioc (r : ℕ) :
    ∃ d : ℝ, d ∈ Set.Ioc (0 : ℝ) 1 ∧ NaturalDensity (atLeastSquarefree r) d := by
  obtain ⟨d, hd_pos, hd_density⟩ := erdos_378_density_positive r
  exact ⟨d, ⟨hd_pos, natDensity_le_one hd_density⟩, hd_density⟩

/-
## Part VIII: The threshold-`0` boundary — density exactly `1`

The universal upper bound `natDensity_le_one` says every density is `≤ 1`. Here we
exhibit the extreme case where it is *attained*: at threshold `r = 0` the answer set
is all of `ℕ` (every `n` has at least `0` squarefree interior binomials), so its
density is exactly `1`. This pins the top endpoint of the interval
`erdos_378_density_mem_Ioc` and needs none of the Granville–Ramaré axioms.
-/

/-- **The full set `ℕ` has natural density `1`.**  For every `N ≥ 1` the counting
ratio is `|univ ∩ [0,N)| / N = N / N = 1`, so the limit is `1`.  Elementary, uses no
axioms. -/
theorem natDensity_univ : NaturalDensity Set.univ 1 := by
  intro ε hε
  refine ⟨1, fun N hN => ?_⟩
  have hNR : (N : ℝ) ≠ 0 := by
    have : 0 < N := hN
    exact_mod_cast this.ne'
  have hcard : (Set.univ ∩ Set.Iio N).ncard = N := by
    rw [Set.univ_inter, ← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]
  rw [hcard, div_self hNR, sub_self, abs_zero]
  exact hε

/-- **At threshold `0` the answer set is everything.**  `hasAtLeastSquarefree n 0`
holds for every `n` (the count is always `≥ 0`), so `atLeastSquarefree 0 = ℕ`. -/
theorem atLeastSquarefree_zero_eq_univ : atLeastSquarefree 0 = Set.univ := by
  ext n
  simp only [atLeastSquarefree, hasAtLeastSquarefree, Set.mem_setOf_eq, Set.mem_univ,
    iff_true]
  exact Nat.zero_le _

/-- **The Erdős #378 density at threshold `0` is exactly `1`.**  Since
`atLeastSquarefree 0 = ℕ`, the density equals that of the full set, namely `1` — the
maximal value permitted by `natDensity_le_one` and the top endpoint of the interval in
`erdos_378_density_mem_Ioc`.  So the universal upper bound `d ≤ 1` is sharp, attained
precisely at the (vacuous) threshold `r = 0`. -/
theorem erdos_378_density_zero : NaturalDensity (atLeastSquarefree 0) 1 := by
  rw [atLeastSquarefree_zero_eq_univ]
  exact natDensity_univ

/-
## Part IX: Monotonicity of natural density — the density is order-preserving

The framework already records the two extreme bounds `natDensity_nonneg` (density `≥ 0`)
and `natDensity_le_one` (density `≤ 1`). Both are instances of a single structural fact:
natural density is *monotone* under set inclusion. Below we prove that general law and
apply it to the decreasing filtration `atLeastSquarefree_antitone`, obtaining that the
Erdős #378 densities are **antitone in the threshold** — a larger demand `r` on the number
of squarefree interior binomials cannot increase the density of qualifying integers. All
axiom-free (independent of the Granville–Ramaré inputs).
-/

/-- **Natural density is monotone under inclusion.**  If `S ⊆ T` and both have natural
densities `d` and `d'`, then `d ≤ d'`.  For every `N` the counting cardinalities satisfy
`|S ∩ [0,N)| ≤ |T ∩ [0,N)|`, so the ratios are ordered; taking `N` past both convergence
thresholds forces the limits to be ordered too.  This subsumes both `natDensity_nonneg`
(the case `S = ∅`, `d = 0`) and `natDensity_le_one` (the case `T = univ`, `d' = 1`).
Elementary ε-argument, uses none of the axioms. -/
theorem natDensity_mono {S T : Set ℕ} {d d' : ℝ} (hst : S ⊆ T)
    (hS : NaturalDensity S d) (hT : NaturalDensity T d') : d ≤ d' := by
  by_contra hlt
  push_neg at hlt  -- `d' < d`
  set ε : ℝ := (d - d') / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  obtain ⟨N₁, hN₁⟩ := hS ε hε
  obtain ⟨N₂, hN₂⟩ := hT ε hε
  set N := max (max N₁ N₂) 1 with hNdef
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hb1 := hN₁ N (le_trans (le_max_left _ _) (le_max_left _ _))
  have hb2 := hN₂ N (le_trans (le_max_right _ _) (le_max_left _ _))
  -- counting-ratio monotonicity from the cardinality inclusion
  have hsub : (S ∩ Set.Iio N) ⊆ (T ∩ Set.Iio N) :=
    Set.inter_subset_inter_left _ hst
  have hfinT : (T ∩ Set.Iio N).Finite := (Set.finite_Iio N).inter_of_right T
  have hcardR : ((S ∩ Set.Iio N).ncard : ℝ) ≤ ((T ∩ Set.Iio N).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hsub hfinT
  have hratio : ((S ∩ Set.Iio N).ncard : ℝ) / (N : ℝ)
      ≤ ((T ∩ Set.Iio N).ncard : ℝ) / (N : ℝ) :=
    div_le_div_of_nonneg_right hcardR (le_of_lt hNR)
  rw [abs_lt] at hb1 hb2
  linarith [hb1.1, hb2.2, hratio]

/-- **The Erdős #378 densities are antitone in the threshold.**  For thresholds `r ≤ r'`,
if the answer sets at both thresholds have natural densities `d` and `d'`, then `d' ≤ d`:
raising the required number of squarefree interior binomials shrinks the qualifying set
(`atLeastSquarefree_antitone`), so by `natDensity_mono` its density cannot increase.  This
is the monotone structure of the density profile `r ↦ d(r)` descending from `d(0) = 1`
(`erdos_378_density_zero`).  Axiom-free (the densities are supplied as hypotheses, so the
Granville–Ramaré existence input is not invoked). -/
theorem erdos_378_density_antitone {r r' : ℕ} {d d' : ℝ} (hr : r ≤ r')
    (hd : NaturalDensity (atLeastSquarefree r) d)
    (hd' : NaturalDensity (atLeastSquarefree r') d') : d' ≤ d :=
  natDensity_mono (atLeastSquarefree_antitone hr) hd' hd

end Erdos378
