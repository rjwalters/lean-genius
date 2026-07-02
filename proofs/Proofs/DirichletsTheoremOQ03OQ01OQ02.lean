/-
  Open Question (derived): The Linnik Critical Exponent under Base Rescaling

  Parent chain:
  - dirichlets-theorem-oq-03      : the Linnik constant (best exponent in Linnik's theorem).
  - dirichlets-theorem-oq-03-oq-01: the Linnik constant as a *critical exponent* — the
    admissible-exponent set is an upward-closed ray, its infimum is the constant, and the
    constant is monotone under pointwise domination of the growth function.
  - dirichlets-theorem-oq-03-oq-01-oq-01: the lower bound (Linnik constant ≥ 1).

  This file adds the missing *reparametrization law*: how the critical exponent transforms
  when the BASE is rescaled by a power. If one measures the growth of `f` against `(b i)^k`
  instead of `b i` (for a fixed real exponent `k > 0`), then an exponent `L` is admissible
  for the rescaled base iff `k·L` is admissible for the original base — so the whole
  admissible ray is scaled by `1/k`, and the critical exponent scales exactly by `1/k`:

        criticalExponent f (fun i => (b i)^k) = criticalExponent f b / k.

  This is the precise sense in which the Linnik constant is a *dimensionless* critical
  exponent: it is defined relative to a choice of base scale, and changing that scale by a
  power `k` divides the constant by `k`. In particular measuring the least prime `p(a,q)`
  against `q²` rather than `q` halves the critical exponent.

  Everything is AXIOM-FREE and SORRY-FREE, stated for an abstract growth function
  `f : I → ℝ` over a nonnegative base `b : I → ℝ`. As in the sibling files, the deep input
  (Linnik's theorem: one admissible exponent exists) enters only as a nonemptiness
  hypothesis, never as an axiom.

  Tags: number-theory, primes, arithmetic-progressions, linnik-constant, critical-exponent,
        rescaling
-/

import Mathlib

open Real Set

namespace LinnikBaseRescaling

variable {I : Type*}

/-- The set of admissible exponents for a growth function `f` over a base `b`:
    those `L > 0` for which `f i ≤ c · (b i) ^ L` holds uniformly for some `c > 0`.
    (Same definition as the sibling entries; repeated here to keep the file self-contained.) -/
def admissible (f b : I → ℝ) : Set ℝ :=
  { L | 0 < L ∧ ∃ c, 0 < c ∧ ∀ i, f i ≤ c * b i ^ L }

/-- The admissible set is bounded below by `0`, so its infimum exists. -/
theorem admissible_bddBelow (f b : I → ℝ) : BddBelow (admissible f b) :=
  ⟨0, fun _ hL => le_of_lt hL.1⟩

/-- The critical exponent: the infimum of the admissible set. In the Linnik instance
    (`f = leastPrimeInAP`, `b = q`) this is the Linnik constant. -/
noncomputable def criticalExponent (f b : I → ℝ) : ℝ := sInf (admissible f b)

/-!
## The reparametrization bijection

The heart of the file: admissibility for the rescaled base `b^k` at exponent `L` is
*exactly* admissibility for `b` at exponent `k·L`, using `(b i ^ k) ^ L = b i ^ (k·L)`
(valid because `b i ≥ 0`) and `0 < L ↔ 0 < k·L` (valid because `k > 0`).
-/

/-- Reparametrization: `L` is admissible for the rescaled base `b^k` iff `k·L` is
    admissible for the original base `b`. -/
theorem mem_admissible_rpow_base_iff {f b : I → ℝ} {k : ℝ} (hk : 0 < k)
    (hb : ∀ i, 0 ≤ b i) (L : ℝ) :
    L ∈ admissible f (fun i => b i ^ k) ↔ k * L ∈ admissible f b := by
  constructor
  · rintro ⟨hLpos, c, hc, hbound⟩
    refine ⟨mul_pos hk hLpos, c, hc, fun i => ?_⟩
    have h := hbound i
    rwa [← Real.rpow_mul (hb i)] at h
  · rintro ⟨hkLpos, c, hc, hbound⟩
    have hLpos : 0 < L := by
      by_contra h
      push_neg at h
      exact absurd hkLpos (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hk.le h))
    refine ⟨hLpos, c, hc, fun i => ?_⟩
    have h := hbound i
    rwa [Real.rpow_mul (hb i)] at h

/-- Nonemptiness transfers along the reparametrization: the rescaled admissible set is
    nonempty iff the original one is. -/
theorem admissible_rpow_base_nonempty_iff {f b : I → ℝ} {k : ℝ} (hk : 0 < k)
    (hb : ∀ i, 0 ≤ b i) :
    (admissible f (fun i => b i ^ k)).Nonempty ↔ (admissible f b).Nonempty := by
  constructor
  · rintro ⟨L, hL⟩
    exact ⟨k * L, (mem_admissible_rpow_base_iff hk hb L).mp hL⟩
  · rintro ⟨M, hM⟩
    refine ⟨M / k, (mem_admissible_rpow_base_iff hk hb (M / k)).mpr ?_⟩
    rwa [mul_div_cancel₀ M (ne_of_gt hk)]

/-!
## The rescaling law for the critical exponent
-/

/-- **Base-rescaling law.** For a fixed real power `k > 0` and a nonnegative base `b`, the
    critical exponent for the rescaled base `b^k` is the original critical exponent divided
    by `k`:  `criticalExponent f (b^k) = criticalExponent f b / k`.  Measuring growth
    against a higher power of the base lowers the critical exponent proportionally. -/
theorem criticalExponent_rpow_base {f b : I → ℝ} {k : ℝ} (hk : 0 < k)
    (hb : ∀ i, 0 ≤ b i) (hne : (admissible f b).Nonempty) :
    criticalExponent f (fun i => b i ^ k) = criticalExponent f b / k := by
  have hne' : (admissible f (fun i => b i ^ k)).Nonempty :=
    (admissible_rpow_base_nonempty_iff hk hb).mpr hne
  apply le_antisymm
  · -- `crit A' ≤ crit A / k`: for every `M ∈ A`, `M/k ∈ A'`, so `crit A' ≤ M/k`.
    rw [le_div_iff₀ hk]
    apply le_csInf hne
    intro M hM
    have hMk : M / k ∈ admissible f (fun i => b i ^ k) := by
      apply (mem_admissible_rpow_base_iff hk hb (M / k)).mpr
      rwa [mul_div_cancel₀ M (ne_of_gt hk)]
    have hle : criticalExponent f (fun i => b i ^ k) ≤ M / k :=
      csInf_le (admissible_bddBelow _ _) hMk
    calc criticalExponent f (fun i => b i ^ k) * k
        ≤ (M / k) * k := mul_le_mul_of_nonneg_right hle hk.le
      _ = M := div_mul_cancel₀ M (ne_of_gt hk)
  · -- `crit A / k ≤ crit A'`: `crit A / k` is a lower bound for `A'`.
    apply le_csInf hne'
    intro L hL
    have hkL : k * L ∈ admissible f b := (mem_admissible_rpow_base_iff hk hb L).mp hL
    have hle : criticalExponent f b ≤ k * L :=
      csInf_le (admissible_bddBelow f b) hkL
    rw [div_le_iff₀ hk]
    linarith [mul_comm k L]

/-- Sanity check: rescaling by `k = 1` leaves the critical exponent unchanged
    (the rescaled base `b^1` and `b` define the same critical exponent). -/
theorem criticalExponent_rpow_base_one {f b : I → ℝ}
    (hb : ∀ i, 0 ≤ b i) (hne : (admissible f b).Nonempty) :
    criticalExponent f (fun i => b i ^ (1 : ℝ)) = criticalExponent f b := by
  rw [criticalExponent_rpow_base one_pos hb hne, div_one]

/-- Doubling the base scale halves the critical exponent: measuring against `q²` instead of
    `q` in the Linnik setting gives exactly half the constant. -/
theorem criticalExponent_rpow_base_two {f b : I → ℝ}
    (hb : ∀ i, 0 ≤ b i) (hne : (admissible f b).Nonempty) :
    criticalExponent f (fun i => b i ^ (2 : ℝ)) = criticalExponent f b / 2 :=
  criticalExponent_rpow_base (by norm_num) hb hne

/-- Monotone in the scale: a larger base power gives a smaller (or equal) critical exponent,
    for a nonnegative critical exponent. This packages the `1/k` dependence as an order
    statement. -/
theorem criticalExponent_rpow_base_antitone {f b : I → ℝ} {k₁ k₂ : ℝ}
    (hk₁ : 0 < k₁) (hk₁₂ : k₁ ≤ k₂) (hb : ∀ i, 0 ≤ b i)
    (hne : (admissible f b).Nonempty) (hcpos : 0 ≤ criticalExponent f b) :
    criticalExponent f (fun i => b i ^ k₂) ≤ criticalExponent f (fun i => b i ^ k₁) := by
  have hk₂ : 0 < k₂ := lt_of_lt_of_le hk₁ hk₁₂
  rw [criticalExponent_rpow_base hk₁ hb hne, criticalExponent_rpow_base hk₂ hb hne]
  apply div_le_div_of_nonneg_left hcpos hk₁ hk₁₂

/-!
## Linnik specialization

For the arithmetic-progression data (`f = p(·,·)`, `b = q`), the rescaling law says the
Linnik critical exponent measured against `q^k` is the ordinary Linnik constant divided by
`k`. The deep Linnik input is again only the nonemptiness hypothesis.
-/

/-- The Linnik constant measured against the rescaled base `q^k` equals the ordinary Linnik
    constant divided by `k`. -/
theorem linnikConstant_rpow_base (p : ℕ × ℕ → ℝ) {k : ℝ} (hk : 0 < k)
    (hne : (admissible p (fun i => (i.2 : ℝ))).Nonempty) :
    criticalExponent p (fun i => (i.2 : ℝ) ^ k)
      = criticalExponent p (fun i => (i.2 : ℝ)) / k :=
  criticalExponent_rpow_base hk (fun i => by positivity) hne

#check @mem_admissible_rpow_base_iff
#check @criticalExponent_rpow_base
#check @criticalExponent_rpow_base_two
#check @linnikConstant_rpow_base

end LinnikBaseRescaling
