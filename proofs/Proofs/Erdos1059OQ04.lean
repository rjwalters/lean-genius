/-
Erdős Problem #1059, Open Question 04:
Density-1 Conjecture Implies ErdosProblem1059

**The Question**: Does density_one_conjecture (from OQ-01) imply that there are
infinitely many primes p satisfying AllFactorialSubtractionsComposite(p)?

**Answer**: Yes. This file proves density_one_conjecture → ErdosProblem1059.

**Key Argument**:
  density_one_conjecture says: for k=1, eventually qualifyingPrimeCount(x)·2 ≥ primeCount(x).
  If qualifying primes were finite (bounded by M), then qualifyingPrimeCount(x) ≤ M forever,
  forcing primeCount(x) ≤ 2·M for all large x. But primeCount(x) → ∞ (infinitely many primes),
  giving a contradiction via Nat.exists_infinite_primes.

**Proved**:
1. primeCount_mono': π(x) is monotone
2. primeCount_step': for prime p > x, π(p) > π(x)
3. primeCount_unbounded': π(x) is unbounded
4. density_one_implies_infinitely_many: density_one_conjecture → ErdosProblem1059

**Axiom** (1): density_one_conjecture — inherited via import Proofs.Erdos1059OQ01

References:
- Erdős (1979), problem collection
- https://erdosproblems.com/1059
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Set.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Proofs.Erdos1059OQ01

/-!
## Setup

We use the definitions and `density_one_conjecture` from OQ-01.
`AllFactorialSubtractionsComposite`, `qualifyingPrimeCount`, `primeCount`,
and `density_one_conjecture` are all defined in `Proofs.Erdos1059OQ01`.

We restate ErdosProblem1059 locally to avoid importing `Erdos1059Problem.lean`,
which would create a duplicate `AllFactorialSubtractionsComposite` definition.
-/

/-- **Erdős Problem #1059** (OPEN): There are infinitely many primes p
    such that p - k! is composite for every k with k! < p.
    Matches the definition in Erdos1059Problem.lean. -/
private def ErdosProblem1059' : Prop :=
  Set.Infinite {p : ℕ | p.Prime ∧ AllFactorialSubtractionsComposite p}

/-!
## Lemmas on the Prime Counting Function π(x)
-/

/-- π(x) is monotone: more primes are counted at larger x. -/
private theorem primeCount_mono' {x y : ℕ} (h : x ≤ y) : primeCount x ≤ primeCount y := by
  unfold primeCount
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact Finset.range_mono (Nat.succ_le_succ h)

/-- For prime p with p > x, π(p) > π(x): p counts as a new prime. -/
private theorem primeCount_step' {x p : ℕ} (hxp : x < p) (hp : p.Prime) :
    primeCount x < primeCount p := by
  unfold primeCount
  apply Finset.card_lt_card
  -- Prove strict subset: range(x+1).filter ⊂ range(p+1).filter
  apply lt_of_le_not_le
  · -- Forward inclusion
    apply Finset.filter_subset_filter
    exact Finset.range_mono (by omega)
  · -- p is in the larger set but not the smaller
    intro h_rev
    have hp_in : p ∈ (Finset.range (p + 1)).filter Nat.Prime := by simp [hp]
    have hp_not : p ∉ (Finset.range (x + 1)).filter Nat.Prime := by
      simp only [Finset.mem_filter, Finset.mem_range, not_and, not_lt]
      intro; omega
    exact hp_not (h_rev hp_in)

/-- The prime counting function π(x) grows without bound.
    For any N, there exists x with π(x) > N.
    Proof by induction using Nat.exists_infinite_primes to extend the sequence. -/
theorem primeCount_unbounded' : ∀ N : ℕ, ∃ x : ℕ, N < primeCount x := by
  intro N
  induction N with
  | zero =>
    -- π(2) = 1 > 0
    exact ⟨2, by decide⟩
  | succ n ih =>
    obtain ⟨x, hx⟩ := ih  -- ∃ x with n < π(x)
    -- Find a prime p strictly greater than x
    obtain ⟨p, hxp, hp⟩ := Nat.exists_infinite_primes (x + 1)
    refine ⟨p, ?_⟩
    -- π(x) < π(p) (strict, since p is a new prime beyond x)
    -- and π(x) > n, so π(p) > n + 1
    exact Nat.lt_of_le_of_lt hx (primeCount_step' (Nat.lt_of_succ_le hxp) hp)

/-!
## Main Theorem
-/

/-- **density_one_conjecture implies ErdosProblem1059**

    If the density of qualifying primes equals 1, then infinitely many primes
    satisfy AllFactorialSubtractionsComposite.

    **Proof by contradiction**: Assume the set of qualifying primes is finite.
    Then qualifyingPrimeCount(x) ≤ M for all x (some fixed M).
    By density_one_conjecture with k=1: eventually primeCount(x) ≤ 2·qualifyingPrimeCount(x) ≤ 2M.
    But primeCount grows without bound. Contradiction. -/
theorem density_one_implies_infinitely_many :
    density_one_conjecture → ErdosProblem1059' := by
  intro h_density
  by_contra h_fin
  rw [ErdosProblem1059', Set.not_infinite] at h_fin
  -- h_fin : Set.Finite {p | p.Prime ∧ AllFactorialSubtractionsComposite p}
  -- qualifyingPrimeCount is bounded by M = card of the finite set
  have ⟨M, hM_bound⟩ : ∃ M : ℕ, ∀ x : ℕ, qualifyingPrimeCount x ≤ M := by
    refine ⟨h_fin.toFinset.card, fun x => ?_⟩
    unfold qualifyingPrimeCount
    apply Finset.card_le_card
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    exact h_fin.mem_toFinset.mpr ⟨hp.2.1, hp.2.2⟩
  -- density_one_conjecture with k=1:
  -- ∃ X, ∀ x ≥ X, qualifyingPrimeCount(x) * 2 ≥ primeCount(x) * 1
  obtain ⟨X, hX⟩ := h_density 1
  -- Find x₀ with primeCount(x₀) > 2·M (primeCount is unbounded)
  obtain ⟨x₀, hx₀⟩ := primeCount_unbounded' (2 * M)
  -- Use y = max(x₀, X) to satisfy both conditions
  let y := max x₀ X
  have hy_X : X ≤ y := le_max_right x₀ X
  have hy_x₀ : x₀ ≤ y := le_max_left x₀ X
  -- From density conjecture at y: primeCount(y) ≤ qualifyingPrimeCount(y) * 2
  have h_dens : primeCount y ≤ qualifyingPrimeCount y * 2 := by
    have h := hX y hy_X
    -- h : qualifyingPrimeCount y * (1 + 1) ≥ primeCount y * 1
    linarith
  -- qualifyingPrimeCount(y) * 2 ≤ 2 * M (from our bound)
  have h_qual : qualifyingPrimeCount y * 2 ≤ 2 * M := by linarith [hM_bound y]
  -- primeCount(y) > 2 * M (monotonicity from x₀)
  have h_prime_large : 2 * M < primeCount y :=
    Nat.lt_of_lt_of_le hx₀ (primeCount_mono' hy_x₀)
  -- Contradiction: primeCount(y) ≤ 2M < primeCount(y)
  linarith
