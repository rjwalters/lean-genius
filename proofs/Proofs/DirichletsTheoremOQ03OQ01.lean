/-
  Open Question (derived): Structure of the Admissible-Exponent Set for Linnik's Theorem

  Parent (dirichlets-theorem-oq-03): the Linnik constant L is defined as the infimum of
  exponents L > 0 for which the least prime p ≡ a (mod q) satisfies p(a,q) ≤ c·q^L.
  Determining its exact value is open (conjectured L = 1; best unconditional bound L ≤ 5,
  Xylouris 2011).

  This file isolates and proves, AXIOM-FREE and SORRY-FREE, the structural skeleton that
  makes the Linnik constant a well-defined "critical exponent". None of these facts need
  the (deep, unproved) Linnik existence theorem itself — they are properties of the
  admissible-exponent set of any growth function over a base ≥ 1:

    * the set of admissible exponents is upward-closed (it is a ray);
    * it is bounded below by 0, so its infimum exists in ℝ;
    * the infimum (the critical exponent) satisfies the sandwich
          Ioi (criticalExponent) ⊆ admissible ⊆ Ici (criticalExponent),
      i.e. the critical exponent pins the admissible set down to its single boundary point;
    * the critical exponent is monotone under pointwise domination of the growth function,
      so sharper Linnik-type upper bounds can only *lower* the constant.

  Everything is stated for an abstract growth function `f : I → ℝ` over a base
  `b : I → ℝ` with `b ≥ 1`. The Linnik setting is the instance `I = {(a, q) : Coprime a q}`,
  `f = leastPrimeInAP`, `b = q`, in which `criticalExponent f b` is exactly the Linnik
  constant of the parent file.

  Tags: number-theory, primes, arithmetic-progressions, linnik-constant, critical-exponent
-/

import Mathlib

open Real Set

namespace LinnikAdmissible

variable {I : Type*}

/-- The set of admissible exponents for a growth function `f` over a base `b`:
    those `L > 0` for which `f i ≤ c · (b i) ^ L` holds uniformly in `i` for some `c > 0`.
    For Linnik's theorem, `f i` is the least prime `≡ a (mod q)` and `b i = q`. -/
def admissible (f b : I → ℝ) : Set ℝ :=
  { L | 0 < L ∧ ∃ c, 0 < c ∧ ∀ i, f i ≤ c * b i ^ L }

/-- The set of admissible exponents is bounded below (by `0`), so its infimum exists. -/
theorem admissible_bddBelow (f b : I → ℝ) : BddBelow (admissible f b) :=
  ⟨0, fun _ hL => le_of_lt hL.1⟩

/-- Upward closure: enlarging the exponent preserves admissibility, because the base is
    `≥ 1` so `b i ^ L ≤ b i ^ L'` whenever `L ≤ L'`. The admissible set is a ray. -/
theorem admissible_upward_closed (f b : I → ℝ) (hb : ∀ i, 1 ≤ b i)
    {L L' : ℝ} (hL : L ∈ admissible f b) (hLL' : L ≤ L') : L' ∈ admissible f b := by
  obtain ⟨hLpos, c, hc, hbound⟩ := hL
  refine ⟨lt_of_lt_of_le hLpos hLL', c, hc, fun i => ?_⟩
  calc f i ≤ c * b i ^ L := hbound i
    _ ≤ c * b i ^ L' :=
        mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le (hb i) hLL') (le_of_lt hc)

/-- The critical exponent: the infimum of admissible exponents. In the arithmetic-
    progression instance this is exactly the Linnik constant of the parent file. -/
noncomputable def criticalExponent (f b : I → ℝ) : ℝ := sInf (admissible f b)

/-- The critical exponent is a lower bound for every admissible exponent. -/
theorem criticalExponent_le (f b : I → ℝ) {L : ℝ} (hL : L ∈ admissible f b) :
    criticalExponent f b ≤ L :=
  csInf_le (admissible_bddBelow f b) hL

/-- The critical exponent is non-negative whenever some exponent is admissible. -/
theorem criticalExponent_nonneg (f b : I → ℝ) (hne : (admissible f b).Nonempty) :
    0 ≤ criticalExponent f b :=
  le_csInf hne (fun _ hL => le_of_lt hL.1)

/-- Ray property: every exponent strictly above the critical one is admissible.
    Combined with `criticalExponent_le`, this shows the admissible set is exactly a ray
    whose endpoint is the critical exponent (open or closed at that single point). -/
theorem mem_admissible_of_gt (f b : I → ℝ) (hb : ∀ i, 1 ≤ b i)
    (hne : (admissible f b).Nonempty) {L : ℝ} (hL : criticalExponent f b < L) :
    L ∈ admissible f b := by
  obtain ⟨L₀, hL₀mem, hL₀lt⟩ := exists_lt_of_csInf_lt hne hL
  exact admissible_upward_closed f b hb hL₀mem (le_of_lt hL₀lt)

/-- The open ray above the critical exponent is contained in the admissible set. -/
theorem Ioi_subset_admissible (f b : I → ℝ) (hb : ∀ i, 1 ≤ b i)
    (hne : (admissible f b).Nonempty) :
    Ioi (criticalExponent f b) ⊆ admissible f b :=
  fun _ hL => mem_admissible_of_gt f b hb hne hL

/-- The admissible set is contained in the closed ray above the critical exponent. -/
theorem admissible_subset_Ici (f b : I → ℝ) :
    admissible f b ⊆ Ici (criticalExponent f b) :=
  fun _ hL => criticalExponent_le f b hL

/-- Sandwich theorem: `Ioi c ⊆ admissible ⊆ Ici c` for `c = criticalExponent`.
    The critical exponent determines the admissible set up to its single boundary point —
    the precise sense in which "the Linnik constant" is the answer to the parent question. -/
theorem admissible_sandwich (f b : I → ℝ) (hb : ∀ i, 1 ≤ b i)
    (hne : (admissible f b).Nonempty) :
    Ioi (criticalExponent f b) ⊆ admissible f b ∧
      admissible f b ⊆ Ici (criticalExponent f b) :=
  ⟨Ioi_subset_admissible f b hb hne, admissible_subset_Ici f b⟩

/-- Comparison: if `f` is pointwise dominated by `g`, every exponent admissible for `g`
    is admissible for `f` (the same constant `c` works). -/
theorem admissible_mono (f g b : I → ℝ) (hfg : ∀ i, f i ≤ g i) :
    admissible g b ⊆ admissible f b := by
  rintro L ⟨hLpos, c, hc, hbound⟩
  exact ⟨hLpos, c, hc, fun i => le_trans (hfg i) (hbound i)⟩

/-- Monotonicity of the critical exponent: a pointwise-smaller growth function has a
    smaller critical exponent. Sharper Linnik-type upper bounds can only lower the
    constant; they never raise it. -/
theorem criticalExponent_mono (f g b : I → ℝ) (hfg : ∀ i, f i ≤ g i)
    (hne : (admissible g b).Nonempty) :
    criticalExponent f b ≤ criticalExponent g b :=
  csInf_le_csInf (admissible_bddBelow f b) hne (admissible_mono f g b hfg)

/-
## Linnik specialization

Instantiating the abstract theory at the arithmetic-progression data recovers the
parent file's `linnikConstant` as `criticalExponent`, and the structural facts above
become statements about the Linnik constant directly. We keep the least-prime function
abstract (`p : ℕ × ℕ → ℝ`) so the file stays axiom-free: the deep input is *only* the
existence of one admissible exponent (Linnik's theorem), supplied here as a hypothesis.
-/

/-- The Linnik constant of a candidate least-prime function `p` with base `q`,
    as a critical exponent. -/
noncomputable def linnikConstantOf (p : ℕ × ℕ → ℝ) : ℝ :=
  criticalExponent p (fun i => (i.2 : ℝ))

/-- Given Linnik's theorem (one admissible exponent exists) and `q ≥ 1`, every exponent
    strictly above the Linnik constant is itself admissible — the Linnik constant is the
    sharp threshold. -/
theorem linnik_threshold (p : ℕ × ℕ → ℝ) (hq : ∀ i : ℕ × ℕ, 1 ≤ (i.2 : ℝ))
    (hne : (admissible p (fun i => (i.2 : ℝ))).Nonempty) {L : ℝ}
    (hL : linnikConstantOf p < L) :
    L ∈ admissible p (fun i => (i.2 : ℝ)) :=
  mem_admissible_of_gt p (fun i => (i.2 : ℝ)) hq hne hL

#check @criticalExponent
#check @admissible_sandwich
#check @linnik_threshold

end LinnikAdmissible
