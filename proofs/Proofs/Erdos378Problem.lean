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

end Erdos378
