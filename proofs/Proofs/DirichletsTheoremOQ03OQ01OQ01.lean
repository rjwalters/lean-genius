/-
  Open Question (derived): The Linnik Constant is at Least 1 — the Lower Bound, Axiom-Free

  Parent (dirichlets-theorem-oq-03): the Linnik constant L is the infimum of exponents
  L > 0 for which the least prime p ≡ a (mod q) satisfies p(a,q) ≤ c·q^L. The parent file
  states `linnikConstant_pos : linnikConstant ≥ 1` but discharges it with `sorry`, noting
  it "requires p(1,q) ≥ q + 1". The sibling (oq-03-oq-01) built the abstract
  critical-exponent ray structure but left the actual `≥ 1` lower bound unproved.

  This file proves that lower bound, AXIOM-FREE and SORRY-FREE. The mathematics is
  elementary and splits into two independent halves:

    (A) An abstract growth statement: for any growth function `f` dominating an unbounded
        base `b ≥ 1` (i.e. `b i ≤ f i` for all `i`), every admissible exponent is `≥ 1`,
        hence the critical exponent `sInf (admissible f b) ≥ 1`. Intuition: an admissible
        `L` forces `b i ≤ c · b i ^ L`, i.e. `b i ^ (1 - L) ≤ c`; if `L < 1` the left side
        is unbounded in `b i`, a contradiction.

    (B) A number-theoretic domination: any prime `p ≡ 1 (mod q)` satisfies `q ≤ p`
        (elementary: `q ∣ p - 1` and `p ≥ 2`). So the least-prime-in-AP growth function
        dominates the base `q`, supplying the hypothesis of (A).

  Combined, for any selector `P` of primes `P q ≡ 1 (mod q)` (the existence of which is
  Dirichlet's theorem, axiomatized in the parent), the associated Linnik constant is `≥ 1`.
  Thus the parent's `sorry` is resolved: the `≥ 1` bound needs no deep analytic input — only
  that a prime `≡ 1 (mod q)` is at least `q`.

  Tags: number-theory, primes, arithmetic-progressions, linnik-constant, critical-exponent
-/

import Mathlib

open Real Set

namespace LinnikLowerBound

variable {I : Type*}

-- ============================================================================
-- § A. The abstract critical exponent and its lower bound
-- ============================================================================

/-- The set of admissible exponents for a growth function `f` over a base `b`:
    those `L > 0` for which `f i ≤ c · (b i) ^ L` holds uniformly in `i` for some `c > 0`.
    For Linnik's theorem, `f i` is the least prime `≡ a (mod q)` and `b i = q`. -/
def admissible (f b : I → ℝ) : Set ℝ :=
  { L | 0 < L ∧ ∃ c, 0 < c ∧ ∀ i, f i ≤ c * b i ^ L }

/-- The critical exponent: the infimum of admissible exponents. In the arithmetic-
    progression instance this is exactly the Linnik constant of the parent file. -/
noncomputable def criticalExponent (f b : I → ℝ) : ℝ := sInf (admissible f b)

/-- **Lower bound on every admissible exponent.** If the growth function `f` dominates an
    unbounded base `b ≥ 1`, then every admissible exponent is `≥ 1`.

    Proof: an admissible `L` gives `b i ≤ f i ≤ c · b i ^ L`, hence `b i ^ (1 - L) ≤ c`
    for every `i`. If `L < 1` then `1 - L > 0`, so picking `i` with `b i` exceeding the
    threshold `c ^ (1/(1-L))` makes `b i ^ (1 - L) > c` — a contradiction. -/
theorem admissible_ge_one {f b : I → ℝ}
    (hb : ∀ i, 1 ≤ b i) (hlower : ∀ i, b i ≤ f i)
    (hunb : ∀ M : ℝ, ∃ i, M < b i)
    {L : ℝ} (hL : L ∈ admissible f b) : 1 ≤ L := by
  obtain ⟨hLpos, c, hc, hbound⟩ := hL
  by_contra hlt
  push_neg at hlt                       -- hlt : L < 1
  have h1L : 0 < 1 - L := by linarith
  -- threshold whose `(1-L)`-th power is exactly `c`
  set t : ℝ := c ^ (1 / (1 - L)) with ht
  have htpos : 0 < t := Real.rpow_pos_of_pos hc _
  obtain ⟨i, hi⟩ := hunb (max t 1)
  have hbi1 : 1 ≤ b i := hb i
  have hbipos : 0 < b i := lt_of_lt_of_le one_pos hbi1
  have hti : t < b i := lt_of_le_of_lt (le_max_left t 1) hi
  -- the domination inequality
  have key : b i ≤ c * b i ^ L := le_trans (hlower i) (hbound i)
  have hbL : (0 : ℝ) < b i ^ L := Real.rpow_pos_of_pos hbipos L
  have e1 : b i ^ (1 - L) = b i / b i ^ L := by
    rw [Real.rpow_sub hbipos, Real.rpow_one]
  have step : b i ^ (1 - L) ≤ c := by
    rw [e1, div_le_iff₀ hbL]; exact key
  -- but the threshold identity contradicts it
  have htc : t ^ (1 - L) = c := by
    rw [ht, ← Real.rpow_mul hc.le, one_div_mul_cancel (ne_of_gt h1L), Real.rpow_one]
  have hmono : t ^ (1 - L) < b i ^ (1 - L) := Real.rpow_lt_rpow htpos.le hti h1L
  rw [htc] at hmono
  linarith

/-- **The critical exponent is at least 1** under the same hypotheses (plus nonemptiness of
    the admissible set, which in the Linnik setting is Linnik's existence theorem). -/
theorem criticalExponent_ge_one {f b : I → ℝ}
    (hb : ∀ i, 1 ≤ b i) (hlower : ∀ i, b i ≤ f i)
    (hunb : ∀ M : ℝ, ∃ i, M < b i)
    (hne : (admissible f b).Nonempty) :
    1 ≤ criticalExponent f b :=
  le_csInf hne (fun _ hL => admissible_ge_one hb hlower hunb hL)

-- ============================================================================
-- § B. The number-theoretic domination: a prime ≡ 1 (mod q) is ≥ q
-- ============================================================================

/-- **Any prime `p ≡ 1 (mod q)` satisfies `q ≤ p`.** Elementary: `q ∣ p - 1` and `p ≥ 2`,
    so `q ≤ p - 1 < p`. (No bound on `q` is needed; the case `q = 0` forces `p = 1`,
    excluded since `p` is prime, and the inequality holds vacuously as `0 ≤ p`.) -/
theorem prime_one_mod_ge {p q : ℕ} (hp : p.Prime) (h : p ≡ 1 [MOD q]) : q ≤ p := by
  have hp2 : 2 ≤ p := hp.two_le
  have hdvd : q ∣ p - 1 := (Nat.modEq_iff_dvd' (by omega)).mp h.symm
  have hle : q ≤ p - 1 := Nat.le_of_dvd (by omega) hdvd
  omega

-- ============================================================================
-- § C. Synthesis: the Linnik constant is ≥ 1
-- ============================================================================

/-- **The Linnik constant is `≥ 1`.**

    Let `P : ℕ → ℕ` be any selector of primes in the arithmetic progressions `≡ 1 (mod m)`
    for every modulus `m ≥ 1` (here `m = q + 1`); the existence of such primes is Dirichlet's
    theorem, axiomatized in the parent file. Then the growth function `q ↦ P (q+1)`
    dominates the base `q ↦ q + 1`, which is `≥ 1` and unbounded, so by `admissible_ge_one`
    its critical exponent — the Linnik constant — is at least `1`.

    This resolves the parent's `linnikConstant_pos` `sorry`: the lower bound `≥ 1` requires
    no analytic input, only `prime_one_mod_ge`. -/
theorem linnikConstant_ge_one
    (P : ℕ → ℕ) (hP : ∀ q, (P (q + 1)).Prime ∧ P (q + 1) ≡ 1 [MOD (q + 1)])
    (hne : (admissible (fun q => (P (q + 1) : ℝ)) (fun q => (q : ℝ) + 1)).Nonempty) :
    1 ≤ criticalExponent (fun q => (P (q + 1) : ℝ)) (fun q => (q : ℝ) + 1) := by
  refine criticalExponent_ge_one ?_ ?_ ?_ hne
  · intro q; have : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q; linarith
  · intro q
    obtain ⟨hpr, hmod⟩ := hP q
    have hnat : q + 1 ≤ P (q + 1) := prime_one_mod_ge hpr hmod
    have : ((q + 1 : ℕ) : ℝ) ≤ ((P (q + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at this ⊢; linarith
  · intro M
    obtain ⟨n, hn⟩ := exists_nat_gt M
    exact ⟨n, by linarith⟩

#check @admissible_ge_one
#check @criticalExponent_ge_one
#check @prime_one_mod_ge
#check @linnikConstant_ge_one

end LinnikLowerBound
