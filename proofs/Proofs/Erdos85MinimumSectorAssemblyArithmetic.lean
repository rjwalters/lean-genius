import Mathlib

/-!
# Abstract arithmetic for the minimum-sector assembly squeeze

The counting layer of the large-prime sector terminal reduces to pure
integer arithmetic: if the minimum-sector cross-pair identity

`Σ_{c ∈ s} [(d − L c)² − (d − L c) − (a·p − 3)] + T = |s|·(|s| − 1)·a·p`

holds with `T ≥ 0`, the leakage obeys `a·Σ L ≤ N − |s|·a`, the boundary
factorization `d² − d + 3 = N·p` holds, and the prime window gives
`d + 1 ≤ p`, then the presence of any non-minimum coefficient mass
(`|s|·a < N`) forces `|s| = 1` and `a = 1`.

The graph-facing capstone consumes this with `s` the set of minimum
components, `L` the per-component leakage toward larger components, and
`T` the (nonnegative) larger-vertex correction term, which vanishes under
the larger-target source-uniqueness lemma.
-/

namespace Erdos85

/-- **Minimum-sector assembly squeeze.**  The cross-pair identity plus the
leakage bound force a solitary minimum block: `|s| = 1` and `a = 1`. -/
theorem minimum_sector_assembly_squeeze
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (L : ι → ℤ) (T d p N a : ℤ)
    (hs : 1 ≤ (s.card : ℤ))
    (ha : 1 ≤ a) (hd : 4 ≤ d) (hp : d + 1 ≤ p)
    (hLnonneg : ∀ c ∈ s, 0 ≤ L c)
    (hboundary : d * d - d + 3 = N * p)
    (hidentity :
      (∑ c ∈ s, ((d - L c) * (d - L c) - (d - L c) - (a * p - 3))) + T =
        (s.card : ℤ) * ((s.card : ℤ) - 1) * (a * p))
    (hT : 0 ≤ T)
    (hleak : a * (∑ c ∈ s, L c) ≤ N - (s.card : ℤ) * a)
    (hstrict : (s.card : ℤ) * a < N) :
    (s.card : ℤ) = 1 ∧ a = 1 := by
  have hSLnonneg : 0 ≤ ∑ c ∈ s, L c := Finset.sum_nonneg hLnonneg
  have hquad : 0 ≤ ∑ c ∈ s, L c * L c :=
    Finset.sum_nonneg fun c _ => mul_self_nonneg (L c)
  have hconst : d * d - d - (a * p - 3) = (N - a) * p := by
    have h5 : d * d - d = N * p - 3 := by linarith
    rw [h5]
    ring
  -- Pointwise expansion of the cross-pair summand.
  have hexpand :
      (∑ c ∈ s, ((d - L c) * (d - L c) - (d - L c) - (a * p - 3))) =
        (s.card : ℤ) * ((N - a) * p) -
          (2 * d - 1) * (∑ c ∈ s, L c) + ∑ c ∈ s, L c * L c := by
    have hpt : ∀ c ∈ s,
        (d - L c) * (d - L c) - (d - L c) - (a * p - 3) =
          (N - a) * p - (2 * d - 1) * L c + L c * L c := by
      intro c _
      linear_combination hconst
    calc
      (∑ c ∈ s, ((d - L c) * (d - L c) - (d - L c) - (a * p - 3))) =
          ∑ c ∈ s,
            ((N - a) * p - (2 * d - 1) * L c + L c * L c) :=
        Finset.sum_congr rfl hpt
      _ = (∑ _c ∈ s, (N - a) * p) -
            (∑ c ∈ s, (2 * d - 1) * L c) + ∑ c ∈ s, L c * L c := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = (s.card : ℤ) * ((N - a) * p) -
            (2 * d - 1) * (∑ c ∈ s, L c) + ∑ c ∈ s, L c * L c := by
        rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  -- Assemble: `|s| * p * (N - |s| * a) ≤ (2d - 1) * Σ L`.
  have hmain :
      (s.card : ℤ) * p * (N - (s.card : ℤ) * a) ≤
        (2 * d - 1) * (∑ c ∈ s, L c) := by
    have h1 :
        (s.card : ℤ) * ((N - a) * p) -
            (2 * d - 1) * (∑ c ∈ s, L c) +
            (∑ c ∈ s, L c * L c) + T =
          (s.card : ℤ) * ((s.card : ℤ) - 1) * (a * p) := by
      rw [← hexpand]
      exact hidentity
    nlinarith [hquad, hT]
  -- Multiply through by `a` and use the leakage bound.
  have h2d : (0 : ℤ) < 2 * d - 1 := by linarith
  have hchain :
      a * ((s.card : ℤ) * p * (N - (s.card : ℤ) * a)) ≤
        (2 * d - 1) * (N - (s.card : ℤ) * a) := by
    have h4 :
        a * ((s.card : ℤ) * p * (N - (s.card : ℤ) * a)) ≤
          a * ((2 * d - 1) * (∑ c ∈ s, L c)) :=
      mul_le_mul_of_nonneg_left hmain (by linarith)
    have h3 :
        (2 * d - 1) * (a * (∑ c ∈ s, L c)) ≤
          (2 * d - 1) * (N - (s.card : ℤ) * a) :=
      mul_le_mul_of_nonneg_left hleak (by linarith)
    nlinarith [h4, h3]
  have hgap : 1 ≤ N - (s.card : ℤ) * a := by linarith
  -- Cancel the positive gap.
  have haup : a * (s.card : ℤ) * p ≤ 2 * d - 1 := by
    by_contra hcon
    push Not at hcon
    have h6 :
        (2 * d - 1) * (N - (s.card : ℤ) * a) + (N - (s.card : ℤ) * a) ≤
          a * (s.card : ℤ) * p * (N - (s.card : ℤ) * a) := by
      nlinarith [hgap, hcon]
    nlinarith [hchain, hgap, h6]
  -- The prime window forces `a * |s| ≤ 1`, hence both are one.
  have hau : a * (s.card : ℤ) ≤ 1 := by
    by_contra hcon
    push Not at hcon
    have hp0 : (0 : ℤ) < p := by linarith
    have h7 : (2 : ℤ) * p ≤ a * (s.card : ℤ) * p := by
      have h8 : (2 : ℤ) ≤ a * (s.card : ℤ) := by linarith
      exact mul_le_mul_of_nonneg_right h8 (le_of_lt hp0)
    linarith [haup, hp, h7]
  have hu1 : (s.card : ℤ) = 1 := by
    have h9 : (s.card : ℤ) ≤ a * (s.card : ℤ) :=
      le_mul_of_one_le_left (by linarith) ha
    omega
  have ha1 : a = 1 := by
    have h10 : a ≤ a * (s.card : ℤ) :=
      le_mul_of_one_le_right (by linarith) hs
    omega
  exact ⟨hu1, ha1⟩

end Erdos85
