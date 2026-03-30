/-
  Aristotle targets for Erdős Problem #454
  Routine supporting lemmas for automated proof search.
  See Erdos454Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture (limsup = ∞)
  - NOT deep analytic results (Pomerance 1979, PNT)
  - Known results provable from Mathlib (infimum bounds, limsup theory, basic arithmetic)
  - Clean theorem statements with no definition sorries
  - No axioms

  The main file formalizes: Is limsup_{n→∞} (f(n) - 2p_n) = ∞,
  where f(n) = min_{i<n} (p_{n+i} + p_{n-i})?
-/
import Mathlib

namespace Erdos454Aristotle

open Nat Filter

/- ## Definitions (mirrored from Erdos454Problem.lean) -/

/-- The k-th prime number (0-indexed: p_0 = 2, p_1 = 3, ...). -/
noncomputable def nthPrime (k : ℕ) : ℕ := k.nth Prime

/-- f(n) = min_{i<n} (p_{n+i} + p_{n-i}). -/
noncomputable def f (n : ℕ) : ℕ :=
  if n = 0 then 0
  else ⨅ i : Fin n, nthPrime (n + i) + nthPrime (n - i)

/-- Alternative definition using Finset.inf'. -/
noncomputable def f' (n : ℕ) : ℕ :=
  if n = 0 then 0
  else (Finset.range n).inf' (by simp) (fun i => nthPrime (n + i) + nthPrime (n - i))

/-- The deviation of f(n) from 2p_n. -/
noncomputable def deviation (n : ℕ) : ℤ :=
  (f n : ℤ) - 2 * (nthPrime n : ℤ)

/-- The deviation as an extended natural (for limsup). -/
noncomputable def deviationENat (n : ℕ) : ℕ∞ :=
  if (f n : ℤ) ≥ 2 * (nthPrime n : ℤ) then
    ((f n : ℤ) - 2 * (nthPrime n : ℤ)).toNat
  else 0

/-- The main conjecture: limsup = ∞. -/
def Erdos454Conjecture : Prop :=
  limsup deviationENat atTop = ⊤

/-- The negation: deviations are bounded. -/
def Erdos454Negation : Prop :=
  ∃ M : ℕ, limsup deviationENat atTop ≤ M

/- ## Routine Lemmas -/

-- nth prime basics
/-- The nth prime sequence is strictly increasing. -/
theorem nthPrime_strictMono : StrictMono nthPrime :=
  Nat.nth_prime_strictMono

/-- All nth primes are prime. -/
theorem nthPrime_prime (k : ℕ) : (nthPrime k).Prime :=
  Nat.prime_nth_prime k

-- f(n) bounds
/-- The i=0 term of the infimum equals 2*p_n. -/
theorem symmetric_sum_at_zero (n : ℕ) (hn : n > 0) :
    nthPrime (n + 0) + nthPrime (n - 0) = 2 * nthPrime n := by
  simp; ring

/-- f(n) ≤ 2p_n, since the infimum includes the i=0 term. -/
theorem f_le_twice_nthPrime (n : ℕ) (hn : n > 0) :
    f n ≤ 2 * nthPrime n := by
  simp only [f, if_neg (by omega : n ≠ 0)]
  refine (ciInf_le ⟨0, by rintro _ ⟨_, rfl⟩; exact Nat.zero_le _⟩ ⟨0, hn⟩).trans ?_
  simp [symmetric_sum_at_zero n hn]

/-- The two definitions of f are equivalent. -/
theorem f_eq_f' (n : ℕ) : f n = f' n := by
  sorry -- Needs equivalence between iInf over Fin n and Finset.inf' over range n

-- Conjecture / negation relationship
/-- The conjecture and its negation are complementary. -/
theorem conjecture_iff_not_negation :
    Erdos454Conjecture ↔ ¬Erdos454Negation := by
  simp only [Erdos454Conjecture, Erdos454Negation]
  constructor
  · intro heq ⟨M, hM⟩
    rw [heq] at hM
    exact absurd hM (not_le.mpr (WithTop.coe_lt_top M))
  · intro hne
    by_contra h
    apply hne
    have hne_top : limsup deviationENat atTop ≠ ⊤ := h
    exact ⟨(limsup deviationENat atTop).toNat,
      le_of_eq (ENat.coe_toNat hne_top).symm⟩

-- Limsup consequences (assuming Pomerance's result as hypothesis, not axiom)
/-- If limsup ≥ 2, then infinitely many n have deviationENat ≥ 2. -/
theorem infinitely_many_deviation_ge_2
    (h : 2 ≤ limsup deviationENat atTop) :
    {n : ℕ | deviationENat n ≥ 2}.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨N, hN⟩ := hfin.bddAbove
  have hev : ∀ᶠ n in atTop, deviationENat n ≤ 1 := by
    simp only [Filter.eventually_atTop]
    refine ⟨N + 1, fun n hn => ?_⟩
    by_contra h'
    push_neg at h'
    exact absurd (hN (Order.succ_le_of_lt h')) (by omega)
  exact absurd (h.trans (Filter.limsup_le_of_le ⟨⊥, fun _ _ => bot_le⟩ hev)) (by norm_num)

-- Prime gap existence (known result, not open)
/-- There exist arbitrarily large prime gaps: for any G,
    some consecutive prime gap is ≥ G. Proof: (G+1)!+2, ..., (G+1)!+(G+1)
    are all composite. -/
theorem large_prime_gaps_exist :
    ∀ G : ℕ, ∃ k, nthPrime (k + 1) - nthPrime k ≥ G := by
  sorry -- Needs factorial gap construction: (G+1)!+2,...,(G+1)!+(G+1) are all composite

-- Asymmetric behavior of primes around a central index
/-- For i > 0, primes at n+i exceed p_n and primes at n-i are below p_n. -/
theorem asymmetric_behavior (n i : ℕ) (hi : 0 < i) (hin : i < n) :
    nthPrime (n + i) > nthPrime n ∧ nthPrime (n - i) < nthPrime n := by
  constructor
  · exact nthPrime_strictMono (by omega)
  · exact nthPrime_strictMono (by omega)

end Erdos454Aristotle
