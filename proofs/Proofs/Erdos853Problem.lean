import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-
# Erdos Problem #853: Smallest Missing Prime Gap

Let d_n = p_{n+1} - p_n be the n-th prime gap. Let r(x) be the smallest
even integer t such that d_n = t has no solution for p_n <= x.
Is it true that r(x) -> infinity? Or even r(x) / log x -> infinity?

## Key Results

- The even restriction is necessary since all prime gaps > 1 are even
- Maynard-Tao (2014): bounded gaps -- infinitely many d_n <= 246
- Zhang (2013): bounded gaps -- infinitely many d_n <= 70,000,000
- The question asks about the completeness of gap sizes up to x

## Formalization Approach

We use Mathlib-based definitions:
- `nthPrime n = Nat.nth Nat.Prime n` (0-indexed: p_0=2, p_1=3, p_2=5, ...)
- `primeGap n = nthPrime(n+1) - nthPrime(n)`

Key structural properties (gap evenness, positivity, monotonicity of nthPrime)
are proved from Mathlib. We formalize the r(x) function and state the open
conjectures.

## References

- Erdos [Er85c]
- OEIS A001223 (prime gaps), A390769
-/

open Nat Finset

-- ## Mathlib-Based Prime Infrastructure

/-- The n-th prime (0-indexed): p_0=2, p_1=3, p_2=5, ... -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The n-th prime gap: d_n = p_{n+1} - p_n. -/
noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

/-- The n-th prime is prime (from Mathlib). -/
lemma nthPrime_prime (n : ℕ) : Nat.Prime (nthPrime n) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n

/-- The prime sequence is strictly increasing (from Mathlib). -/
lemma nthPrime_strictMono : StrictMono nthPrime :=
  fun _ _ h => Nat.nth_strictMono Nat.infinite_setOf_prime h

/-- Prime gaps are positive. -/
theorem primeGap_pos (n : ℕ) : 0 < primeGap n := by
  unfold primeGap
  have : nthPrime n < nthPrime (n + 1) := nthPrime_strictMono (Nat.lt_succ_self n)
  omega

/-- p_0 = 2. -/
theorem nthPrime_zero : nthPrime 0 = 2 := by
  unfold nthPrime; exact Nat.nth_prime_zero_eq_two

/-- p_1 = 3. -/
theorem nthPrime_one : nthPrime 1 = 3 := by
  unfold nthPrime; exact Nat.nth_prime_one_eq_three

/-- d_0 = p_1 - p_0 = 3 - 2 = 1 (the only odd gap). -/
theorem primeGap_zero : primeGap 0 = 1 := by
  show nthPrime 1 - nthPrime 0 = 1
  rw [nthPrime_zero, nthPrime_one]

/-- All prime gaps for n >= 1 are even (both p_n, p_{n+1} are odd primes). -/
theorem primeGap_even (n : ℕ) (hn : n ≥ 1) : 2 ∣ primeGap n := by
  unfold primeGap nthPrime
  have hp_n : Nat.Prime (Nat.nth Nat.Prime n) :=
    Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n
  have hp_n1 : Nat.Prime (Nat.nth Nat.Prime (n + 1)) :=
    Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (n + 1)
  have hn_ge : Nat.nth Nat.Prime n ≥ 3 := by
    have h1 : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
    have hmono : Nat.nth Nat.Prime 1 ≤ Nat.nth Nat.Prime n :=
      (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone hn
    omega
  have h_lt : Nat.nth Nat.Prime n < Nat.nth Nat.Prime (n + 1) :=
    Nat.nth_strictMono Nat.infinite_setOf_prime (Nat.lt_succ_self n)
  have hodd_n : ¬ 2 ∣ Nat.nth Nat.Prime n := by
    intro h2
    have := hp_n.eq_one_or_self_of_dvd 2 h2
    rcases this with h | h <;> omega
  have hodd_n1 : ¬ 2 ∣ Nat.nth Nat.Prime (n + 1) := by
    intro h2
    have := hp_n1.eq_one_or_self_of_dvd 2 h2
    rcases this with h | h <;> omega
  have hmod_n : Nat.nth Nat.Prime n % 2 = 1 := by omega
  have hmod_n1 : Nat.nth Nat.Prime (n + 1) % 2 = 1 := by omega
  have hdiff : (Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n) % 2 = 0 := by omega
  exact Nat.dvd_of_mod_eq_zero hdiff

/-- Prime gaps for n >= 1 are at least 2. -/
theorem primeGap_ge_two (n : ℕ) (hn : n ≥ 1) : primeGap n ≥ 2 := by
  have heven := primeGap_even n hn
  have hpos := primeGap_pos n
  obtain ⟨k, hk⟩ := heven
  omega

/-- nthPrime is monotone (non-strict). -/
theorem nthPrime_mono : Monotone nthPrime :=
  nthPrime_strictMono.monotone

-- ## The Gap Set and r(x)

/-- The set of all prime gap values for primes p_n <= x (n >= 1, so gaps are even). -/
def gapSet (x : ℕ) : Set ℕ :=
  {t : ℕ | ∃ n : ℕ, n ≥ 1 ∧ nthPrime n ≤ x ∧ primeGap n = t}

/-- gapSet is monotone: if x <= y then gapSet(x) ⊆ gapSet(y). -/
theorem gapSet_mono {x y : ℕ} (hxy : x ≤ y) : gapSet x ⊆ gapSet y := by
  intro t ⟨n, hn1, hn2, hn3⟩
  exact ⟨n, hn1, le_trans hn2 hxy, hn3⟩

/-- Every element of gapSet(x) for n >= 1 is even. -/
theorem gapSet_even {t : ℕ} {x : ℕ} (ht : t ∈ gapSet x) : 2 ∣ t := by
  obtain ⟨n, hn1, _, hn3⟩ := ht
  rw [← hn3]
  exact primeGap_even n hn1

/-- Every element of gapSet(x) is positive. -/
theorem gapSet_pos {t : ℕ} {x : ℕ} (ht : t ∈ gapSet x) : t > 0 := by
  obtain ⟨n, _, _, hn3⟩ := ht
  rw [← hn3]
  exact primeGap_pos n

/-- Every element of gapSet(x) is at least 2. -/
theorem gapSet_ge_two {t : ℕ} {x : ℕ} (ht : t ∈ gapSet x) : t ≥ 2 := by
  obtain ⟨n, hn1, _, hn3⟩ := ht
  rw [← hn3]
  exact primeGap_ge_two n hn1

-- ## Defining r(x) via Nat.find

/-- nthPrime is bounded below by its index. -/
theorem nthPrime_ge (n : ℕ) : n ≤ nthPrime n := by
  induction n with
  | zero => simp [nthPrime_zero]
  | succ n ih =>
    have hlt : nthPrime n < nthPrime (n + 1) :=
      nthPrime_strictMono (Nat.lt_succ_self n)
    omega

/-- gapSet(x) is finite: the image of a bounded index set under primeGap. -/
theorem gapSet_finite (x : ℕ) : Set.Finite (gapSet x) := by
  apply Set.Finite.subset ((Set.finite_Iio (x + 1)).image primeGap)
  intro t ⟨n, _, hn2, hn3⟩
  exact ⟨n, Set.mem_Iio.mpr (Nat.lt_succ_of_le (le_trans (nthPrime_ge n) hn2)), hn3⟩

/-- There exists an even integer ≥ 2 not in gapSet(x). -/
theorem exists_even_not_in_gapSet (x : ℕ) (_hx : x ≥ 3) :
    ∃ t : ℕ, t ≥ 2 ∧ t % 2 = 0 ∧ t ∉ gapSet x := by
  by_contra h
  push_neg at h
  -- h says all even t ≥ 2 are in gapSet(x), but gapSet(x) is finite
  have h_range_inf : Set.Infinite (Set.range (fun k : ℕ => 2 * k + 2)) :=
    Set.infinite_range_of_injective (fun a b hab => by omega)
  have h_sub_gap : Set.range (fun k : ℕ => 2 * k + 2) ⊆ gapSet x := by
    rintro _ ⟨k, rfl⟩
    have h1 : 2 * k + 2 ≥ 2 := by omega
    have h2 : (2 * k + 2) % 2 = 0 := by
      rw [show 2 * k + 2 = 2 * (k + 1) from by ring]; exact Nat.mul_mod_right 2 _
    exact h _ h1 h2
  exact (h_range_inf.mono h_sub_gap) (gapSet_finite x)

noncomputable instance decidableMemGapSet (x t : ℕ) : Decidable (t ∈ gapSet x) :=
  Classical.dec _

/-- r(x): smallest even integer ≥ 2 not in gapSet(x).
    DEFINED via Nat.find (previously axiomatized). Returns 2 for x < 3. -/
noncomputable def r (x : ℕ) : ℕ :=
  if hx : x ≥ 3 then Nat.find (exists_even_not_in_gapSet x hx) else 2

private theorem r_unfold (x : ℕ) (hx : x ≥ 3) :
    r x = Nat.find (exists_even_not_in_gapSet x hx) := dif_pos hx

/-- r(x) is even and at least 2. PROVED from Nat.find_spec. -/
theorem r_even_pos (x : ℕ) (hx : x ≥ 3) : r x ≥ 2 ∧ r x % 2 = 0 := by
  rw [r_unfold x hx]
  have h := Nat.find_spec (exists_even_not_in_gapSet x hx)
  exact ⟨h.1, h.2.1⟩

/-- r(x) is not a gap for any prime p_n ≤ x. PROVED from Nat.find_spec. -/
theorem r_not_gap (x : ℕ) (hx : x ≥ 3) : r x ∉ gapSet x := by
  rw [r_unfold x hx]; exact (Nat.find_spec (exists_even_not_in_gapSet x hx)).2.2

/-- r(x) is minimal: every even t with 2 ≤ t < r(x) is in gapSet(x).
    PROVED from Nat.find_min. -/
theorem r_minimal (x : ℕ) (hx : x ≥ 3) :
    ∀ t : ℕ, 2 ≤ t → t < r x → t % 2 = 0 → t ∈ gapSet x := by
  intro t ht2 htlt hteven
  rw [r_unfold x hx] at htlt
  by_contra h
  exact Nat.find_min (exists_even_not_in_gapSet x hx) htlt ⟨ht2, hteven, h⟩

-- ## Proved Properties of r(x)

/-- r is weakly monotone increasing: as x grows, more gaps appear,
    so the smallest missing gap can only increase (or stay the same). -/
theorem r_monotone {x y : ℕ} (hxy : x ≤ y) (hx : x ≥ 3) (hy : y ≥ 3) :
    r x ≤ r y := by
  by_contra h
  push_neg at h
  have ⟨hry2, hry_even⟩ := r_even_pos y hy
  have h_in_gapx := r_minimal x hx (r y) hry2 h hry_even
  have h_in_gapy := gapSet_mono hxy h_in_gapx
  exact r_not_gap y hy h_in_gapy

/-- Bertrand's postulate implies prime gaps d_n < p_n for n ≥ 1.
    Key step: 2·p_n is even > 2 hence not prime, so p_{n+1} < 2·p_n. -/
theorem gap_lt_prime (k : ℕ) (hk : k ≥ 1) : primeGap k < nthPrime k := by
  unfold primeGap
  have hpk3 : nthPrime k ≥ 3 := by
    calc nthPrime k ≥ nthPrime 1 := nthPrime_mono hk
    _ = 3 := nthPrime_one
  -- Bertrand: ∃ prime q with nthPrime k < q ≤ 2 * nthPrime k
  obtain ⟨q, hq_prime, hq_gt, hq_le⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (nthPrime k) (by omega)
  -- nthPrime(k+1) ≤ q: q is prime and > nthPrime k, use Galois connection
  have h_count : k < Nat.count Nat.Prime q :=
    (Nat.lt_nth_iff_count_lt Nat.infinite_setOf_prime).mpr hq_gt
  have h_count_succ : Nat.count Nat.Prime (q + 1) = Nat.count Nat.Prime q + 1 := by
    rw [Nat.count_succ, if_pos hq_prime]
  have h_next : nthPrime (k + 1) < q + 1 :=
    (Nat.lt_nth_iff_count_lt Nat.infinite_setOf_prime).mp (by omega)
  -- 2 * nthPrime k is even > 2, hence not prime
  have h_not_prime : ¬ Nat.Prime (2 * nthPrime k) := by
    intro hp
    have := hp.eq_one_or_self_of_dvd 2 ⟨nthPrime k, rfl⟩
    rcases this with h | h <;> omega
  -- So q < 2 * nthPrime k (since q ≤ 2·p_k and q is prime but 2·p_k isn't)
  have hq_strict : q < 2 * nthPrime k := by
    rcases lt_or_eq_of_le hq_le with h | h
    · exact h
    · exact absurd (h ▸ hq_prime) h_not_prime
  omega

/-- All gaps in gapSet(x) are strictly less than x. -/
theorem gapSet_lt (t : ℕ) (x : ℕ) (ht : t ∈ gapSet x) : t < x := by
  obtain ⟨n, hn1, hn2, hn3⟩ := ht
  rw [← hn3]
  calc primeGap n < nthPrime n := gap_lt_prime n hn1
  _ ≤ x := hn2

/-- r(x) ≤ x for even x ≥ 4.
    x is even, ≥ 2, and x ∉ gapSet(x) (since all gaps < x). -/
theorem r_upper_bound_even (x : ℕ) (hx : x ≥ 4) (heven : x % 2 = 0) : r x ≤ x := by
  have hx3 : x ≥ 3 := by omega
  -- x is a candidate: even, ≥ 2, and not in gapSet(x)
  have hx_not_gap : x ∉ gapSet x := by
    intro hc; exact Nat.lt_irrefl x (gapSet_lt x x hc)
  -- r(x) is the minimal such candidate, so r(x) ≤ x
  by_contra h; push_neg at h
  have hr := r_even_pos x hx3
  exact hx_not_gap (r_minimal x hx3 x (by omega) h heven)

/-- r(x) ≤ x for x ≥ 4.
    Note: FALSE at x = 3 (r(3) = 4 since gapSet(3) = {2}).
    For even x: x ∉ gapSet(x) since gaps < x, so r ≤ x.
    For odd x: needs a counting argument (number of primes < number of even values). -/
theorem r_upper_bound (x : ℕ) (hx : x ≥ 4) : r x ≤ x := by
  sorry

-- ## Main Conjectures (OPEN)

/-- **Erdos Problem #853, Weak Form** (OPEN): r(x) -> infinity as x -> infinity.
    Every even gap size eventually appears among prime gaps.
    Equivalently: for every M, there exists X such that for all x >= X, r(x) >= M. -/
axiom erdos_853_weak :
  ∀ M : ℕ, ∃ X : ℕ, ∀ x : ℕ, x ≥ X → r x ≥ M

/-- **Erdos Problem #853, Strong Form** (OPEN): r(x) / log x -> infinity.
    The smallest missing gap grows faster than logarithmically. -/
axiom erdos_853_strong :
  ∀ C : ℝ, C > 0 → ∃ X : ℕ, ∀ x : ℕ, x ≥ X →
    (r x : ℝ) ≥ C * Real.log x

-- ## Consequences of the Weak Conjecture

/-- If erdos_853_weak holds, then for every even t >= 2, t eventually
    enters gapSet(x) for large enough x. -/
theorem weak_implies_all_even_gaps :
    (∀ M : ℕ, ∃ X : ℕ, ∀ x : ℕ, x ≥ X → r x ≥ M) →
    ∀ t : ℕ, t ≥ 2 → t % 2 = 0 →
      ∀ X : ℕ, ∃ x : ℕ, x ≥ X ∧ t ∈ gapSet x := by
  intro hweak t ht2 hteven X
  obtain ⟨X', hX'⟩ := hweak (t + 1)
  refine ⟨max X (max X' 3), le_max_left _ _, ?_⟩
  have hx_ge_X' : max X (max X' 3) ≥ X' := le_trans (le_max_left X' 3) (le_max_right X _)
  have hx_ge_3 : max X (max X' 3) ≥ 3 := le_trans (le_max_right X' 3) (le_max_right X _)
  have hrx : r (max X (max X' 3)) ≥ t + 1 := hX' _ hx_ge_X'
  exact r_minimal _ hx_ge_3 t ht2 (by omega) hteven

-- ## Related Results (Deep Number Theory)

/-- Maynard-Tao bounded gaps: infinitely many prime gaps <= 246. -/
axiom maynard_tao_bounded_gaps :
  ∃ t : ℕ, t ≤ 246 ∧ t % 2 = 0 ∧
    ∀ X : ℕ, ∃ n : ℕ, nthPrime n > X ∧ primeGap n = t

/-- Cramer's conjecture (OPEN): the largest prime gap below x is O((log x)^2).
    Combined with the weak conjecture, this would give r(x) <= O((log x)^2). -/
axiom cramer_conjecture_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ x : ℕ, x ≥ 2 →
    (r x : ℝ) ≤ C * (Real.log x) ^ 2

/-
## Summary

**Proved from Mathlib** (14 theorems):
- nthPrime_prime, nthPrime_strictMono, nthPrime_mono
- nthPrime_zero, nthPrime_one
- primeGap_pos, primeGap_zero, primeGap_even, primeGap_ge_two
- gapSet_mono, gapSet_even, gapSet_pos, gapSet_ge_two
- r_monotone (from axioms about r)
- weak_implies_all_even_gaps (consequence of weak conjecture)

**Axioms** (4 deep results):
- erdos_853_weak, erdos_853_strong: the OPEN conjectures
- maynard_tao_bounded_gaps: deep result (Maynard-Tao 2014)
- cramer_conjecture_bound: OPEN conjecture (Cramer)

**1 sorry** (r_upper_bound: correct for x ≥ 4, proof infrastructure built)

**New infrastructure**:
- gap_lt_prime: d_n < p_n for n ≥ 1 (from Bertrand's postulate)
- gapSet_lt: all gaps in gapSet(x) are < x

**Bugfix**: r_upper_bound was FALSE at x = 3 (r(3) = 4). Fixed hypothesis to x ≥ 4.
-/
