import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

/-
# Erdős Problem #428: Prime Offsets with Positive Density

Is there a set A ⊆ ℕ such that for infinitely many n, all of n - a are
prime for every a ∈ A with 0 < a < n, and
  liminf |A ∩ [1,x]| / π(x) > 0?

Erdős and Graham (1980) showed this holds with limsup replacing liminf,
assuming the prime k-tuple conjecture. The liminf version remains open.

The problem asks whether a set of "prime-generating offsets" can have
positive density relative to the prime counting function.

Reference: https://erdosproblems.com/428
-/

-- ## Prime Counting and Density

/-- The prime counting function π(n): number of primes ≤ n. -/
noncomputable def primeCounting (n : ℕ) : ℕ :=
  (Finset.filter Nat.Prime (Finset.range (n + 1))).card

/-- The density ratio |A ∩ [1,x]| / π(x) for a set A relative to primes. -/
noncomputable def primeDensityRatio (A : Set ℕ) (n : ℕ) : ℝ :=
  (A ∩ Set.Icc 1 n).ncard / (primeCounting n : ℝ)

-- ## Prime Offset Property

/-- For a given n, all offsets a ∈ A with 0 < a < n yield n - a prime. -/
def AllOffsetsPrime (A : Set ℕ) (n : ℕ) : Prop :=
  ∀ a ∈ A, 0 < a → a < n → (n - a).Prime

-- ## Main Conjecture

/-- Erdős Problem 428: Does there exist A ⊆ ℕ with positive prime density
    such that AllOffsetsPrime A n holds for infinitely many n? -/
def ErdosProblem428 : Prop :=
  ∃ A : Set ℕ,
    (∃ᶠ n in Filter.atTop, AllOffsetsPrime A n) ∧
    Filter.liminf (fun n => primeDensityRatio A n) Filter.atTop > 0

-- ## Limsup Variant

/-- The limsup variant: same but with limsup instead of liminf.
    This holds under the prime k-tuple conjecture (Erdős-Graham). -/
def ErdosProblem428Limsup : Prop :=
  ∃ A : Set ℕ,
    (∃ᶠ n in Filter.atTop, AllOffsetsPrime A n) ∧
    Filter.limsup (fun n => primeDensityRatio A n) Filter.atTop > 0

/-- The liminf version implies the limsup version.

    Proof: From liminf > 0, extract ε > 0 with eventually ε ≤ f.
    Show limsup ≥ ε via IsCoboundedUnder (f ≥ 0) + le_limsup_of_le.
    This avoids needing IsBoundedUnder (· ≤ ·) for liminf_le_limsup. -/
theorem liminf_implies_limsup :
    ErdosProblem428 → ErdosProblem428Limsup := by
  intro ⟨A, hfreq, hliminf⟩
  refine ⟨A, hfreq, ?_⟩
  set f := fun n => primeDensityRatio A n with hf_def
  -- f is bounded below by 0 (needed for eventually_lt_of_lt_liminf)
  have hbdd_below : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop f := by
    refine ⟨0, ?_⟩
    simp only [Filter.eventually_map]
    exact Filter.eventually_of_forall (fun n => primeDensityRatio_nonneg A n)
  -- IsCoboundedUnder: any eventual upper bound for f is ≥ 0 (since f ≥ 0)
  have hcobdd : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop f := by
    use 0
    intro a ha
    simp only [Filter.eventually_map] at ha
    obtain ⟨n, h1, h2⟩ := ((Filter.eventually_of_forall
      (fun n => primeDensityRatio_nonneg A n)).and ha).exists
    linarith
  -- Extract ε = liminf/2 > 0 with eventually ε ≤ f
  set ε := Filter.liminf f Filter.atTop / 2
  have hε_pos : 0 < ε := div_pos hliminf (by norm_num : (0:ℝ) < 2)
  have h_ev : ∀ᶠ n in Filter.atTop, ε ≤ f n :=
    (Filter.eventually_lt_of_lt_liminf (show ε < Filter.liminf f Filter.atTop by linarith)
      hbdd_below).mono (fun _ h => le_of_lt h)
  -- ε ≤ limsup via le_limsup_of_le (uses IsCoboundedUnder, not IsBoundedUnder)
  linarith [Filter.le_limsup_of_le hcobdd h_ev]

-- ## Prime k-Tuple Conjecture

/-- The prime k-tuple conjecture (Hardy-Littlewood): any admissible
    k-tuple pattern occurs infinitely often. -/
def PrimeKTupleConjecture : Prop :=
  ∀ H : Finset ℕ,
    (∀ p : ℕ, p.Prime → ∃ n : ℕ, ∀ h ∈ H, ¬(p ∣ (n + h))) →
    ∃ᶠ n in Filter.atTop, ∀ h ∈ H, (n + h).Prime

/-- Erdős-Graham: the k-tuple conjecture implies the limsup variant. -/
axiom erdos_graham_limsup :
    PrimeKTupleConjecture → ErdosProblem428Limsup

-- ## Basic Properties

/-- The prime counting function is positive for n ≥ 2. -/
theorem primeCounting_pos (n : ℕ) (hn : 2 ≤ n) :
    0 < primeCounting n := by
  unfold primeCounting
  apply Finset.card_pos.mpr
  exact ⟨2, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by decide⟩⟩

/-- Singleton sets always satisfy AllOffsetsPrime for appropriate n. -/
theorem singleton_offset (a : ℕ) (n : ℕ) (ha : 0 < a) (han : a < n)
    (hp : (n - a).Prime) :
    AllOffsetsPrime {a} n := by
  intro x hx hx0 hxn
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact hp

/-- The empty set trivially satisfies AllOffsetsPrime but has zero density. -/
theorem empty_trivial (n : ℕ) : AllOffsetsPrime ∅ n := by
  intro a ha
  exact absurd ha (Set.notMem_empty a)

/-- Subsets preserve the AllOffsetsPrime property. -/
theorem allOffsetsPrime_mono {A B : Set ℕ} {n : ℕ}
    (hAB : A ⊆ B) (hB : AllOffsetsPrime B n) :
    AllOffsetsPrime A n := by
  intro a ha h0 hn
  exact hB a (hAB ha) h0 hn

/-- The prime density ratio is nonneg. -/
theorem primeDensityRatio_nonneg (A : Set ℕ) (n : ℕ) :
    0 ≤ primeDensityRatio A n := by
  unfold primeDensityRatio
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

-- ## Finite Set Density Proof

/-- primeCounting is monotone: more primes counted up to larger n. -/
private lemma primeCounting_mono : Monotone primeCounting := by
  intro m n hmn
  unfold primeCounting
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact Finset.range_mono (by omega)

/-- Strictly more primes are counted up to a prime p than up to any smaller N. -/
private lemma primeCounting_lt_of_prime {N p : ℕ} (hp : p.Prime) (hpN : N < p) :
    primeCounting N < primeCounting p := by
  unfold primeCounting
  apply Finset.card_lt_card
  constructor
  · exact Finset.filter_subset_filter _ (Finset.range_mono (by omega))
  · intro h
    have hp_in : p ∈ Finset.filter Nat.Prime (Finset.range (p + 1)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩
    exact absurd (h hp_in) (by
      simp only [Finset.mem_filter, Finset.mem_range, not_and]
      intro h; omega)

/-- The prime counting function grows without bound (ℕ-valued). -/
private lemma primeCounting_tendsto_nat :
    Filter.Tendsto primeCounting Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_atTop_of_monotone primeCounting_mono
  intro M
  induction M with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ k ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (N + 1)
    have hNp : N < p := by omega
    have h_lt := primeCounting_lt_of_prime hp_prime hNp
    exact ⟨p, by omega⟩

/-- The real-valued prime counting function grows without bound. -/
private lemma primeCounting_real_tendsto :
    Filter.Tendsto (fun n => (primeCounting n : ℝ)) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  obtain ⟨N, hN⟩ := (Filter.tendsto_atTop_atTop.mp primeCounting_tendsto_nat) ⌈max b 0⌉₊
  exact ⟨N, fun n hn => le_trans (le_trans (le_max_left b 0) (Nat.le_ceil _))
    (by exact_mod_cast hN n hn)⟩

/-- Finite sets have zero liminf prime density.

Proof: For finite A with |A| = M, the intersection (A ∩ [1,n]) has at most M elements,
so primeDensityRatio A n ≤ M / π(n). Since π(n) → ∞ by the infinitude of primes,
this ratio is squeezed to 0. -/
theorem finite_set_zero_density (A : Set ℕ) (hA : A.Finite) :
    Filter.liminf (fun n => primeDensityRatio A n) Filter.atTop = 0 := by
  -- Step 1: Show the density ratio tends to 0
  suffices h_tendsto : Filter.Tendsto (fun n => primeDensityRatio A n) Filter.atTop (nhds 0) by
    exact h_tendsto.liminf_eq
  -- Step 2: Squeeze between 0 and A.ncard / π(n)
  apply squeeze_zero (primeDensityRatio_nonneg A)
  · -- Upper bound: primeDensityRatio A n ≤ A.ncard / π(n)
    intro n
    show (↑(A ∩ Set.Icc 1 n).ncard : ℝ) / ↑(primeCounting n) ≤ ↑A.ncard / ↑(primeCounting n)
    apply div_le_div_of_nonneg_right
    · exact_mod_cast Set.ncard_le_ncard Set.inter_subset_left hA
    · exact Nat.cast_nonneg _
  · -- A.ncard / π(n) → 0 since π(n) → ∞
    have h_inv : Filter.Tendsto (fun n => ((primeCounting n : ℝ))⁻¹)
        Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp primeCounting_real_tendsto
    have h_mul := tendsto_const_nhds (x := (A.ncard : ℝ)) |>.mul h_inv
    rwa [mul_zero] at h_mul

/-- Any solution to Problem 428 must use an infinite set. -/
theorem erdos428_requires_infinite :
    ErdosProblem428 → ∃ A : Set ℕ, A.Infinite ∧
      (∃ᶠ n in Filter.atTop, AllOffsetsPrime A n) ∧
      Filter.liminf (fun n => primeDensityRatio A n) Filter.atTop > 0 := by
  intro ⟨A, hfreq, hliminf⟩
  refine ⟨A, ?_, hfreq, hliminf⟩
  by_contra hfin
  push_neg at hfin
  have := finite_set_zero_density A hfin
  linarith
