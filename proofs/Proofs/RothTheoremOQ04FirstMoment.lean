/-
  Roth Theorem OQ-04: the L¹ first moment of the quadratic Gauss sum.

  The magnitude machinery of `RothTheorem` (`sqGaussSum_normSq_le_gcd`,
  `sqGaussSum_norm_le_sqrt_gcd`) controls the quadratic Gauss sum
  `G(r) = ∑_{n} ψ(r · n²)` *pointwise* by the arithmetic quantity
  `√(N · gcd(2r, N))`.  The Sárközy square-difference density bound, however,
  is driven not by the pointwise maximum but by the **average** size of `G`.
  The relevant averaged quantity is the first moment (the `L¹` norm)
  `∑_{r} ‖G(r)‖`.

  This file evaluates the natural upper bound for that first moment at **odd
  moduli** as an exact multiplicative divisor sum.  Two ingredients:

  * `sum_weight_gcd_eq_divisor_sum` — a self-contained arithmetic identity:
    for any weight `w`, `∑_{c<n} w(gcd(n,c)) = ∑_{d∣n} φ(n/d)·w(d)`.  Each
    divisor `d` is hit by exactly `φ(n/d)` residues `c` with `gcd(n,c)=d`
    (Mathlib's `Nat.totient_div_of_dvd`), so the gcd-weighted sum collapses to a
    sum over divisors.

  * `sum_norm_sqGaussSum_le_of_odd` — the capstone.  Summing the pointwise
    bound, factoring out `√N`, reindexing `r ↦ 2r` (a bijection of `ZMod N`
    since `2` is a unit at odd `N`) and transporting the residue sum to
    `range N`, gives

      `∑_{r} ‖G(r)‖ ≤ √N · ∑_{d ∣ N} φ(N/d) · √d`.

  The right-hand side is a concrete multiplicative arithmetic function of `N`,
  the first-moment companion of the pointwise `√(N·gcd)` and the second-moment
  (Plancherel) `∑_r ‖G(r)‖² = N · #{n² = m²}` bounds.  It is the exact input a
  quantitative Sárközy density estimate needs.

  All results are fully machine-checked, 0 sorries, no `native_decide`.
-/
import Mathlib
import Proofs.RothTheorem

open Finset

namespace Szemeredi.Roth

/-- **Weighted gcd–divisor identity.**  For `n > 0` and any real weight `w`, the
    sum of `w (gcd n c)` over the residues `c ∈ range n` regroups by the divisor
    `d = gcd n c`; each divisor `d ∣ n` is the gcd of exactly `φ(n/d)` residues
    (`Nat.totient_div_of_dvd`), so the whole sum collapses to
    `∑_{d ∣ n} φ(n/d) · w d`. -/
theorem sum_weight_gcd_eq_divisor_sum (n : ℕ) (hn : 0 < n) (w : ℕ → ℝ) :
    ∑ c ∈ range n, w (n.gcd c) = ∑ d ∈ n.divisors, ((n / d).totient : ℝ) * w d := by
  rw [← Finset.sum_fiberwise_of_maps_to
        (fun c (_ : c ∈ range n) => Nat.mem_divisors.2 ⟨Nat.gcd_dvd_left n c, hn.ne'⟩)
        (fun c => w (n.gcd c))]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hcongr : ∀ c ∈ {c ∈ range n | n.gcd c = d}, w (n.gcd c) = w d := by
    intro c hc; rw [(Finset.mem_filter.1 hc).2]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, ← Nat.totient_div_of_dvd hdvd,
    nsmul_eq_mul]

/-- **L¹ first moment of the quadratic Gauss sum at odd moduli.**  Summing the
    pointwise bound `‖G(r)‖ ≤ √(N · gcd(2r, N))` and collapsing the resulting
    gcd-weighted residue sum to a divisor sum gives the exact multiplicative
    ceiling

      `∑_{r} ‖G(r)‖ ≤ √N · ∑_{d ∣ N} φ(N/d) · √d`.

    Oddness enters only through the reindexing `r ↦ 2r`, a bijection of `ZMod N`
    (as `2` is a unit), which turns `∑_r √(gcd(2r, N))` into the divisor sum. -/
theorem sum_norm_sqGaussSum_le_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) :
    ∑ r : ZMod N, ‖sqGaussSum r‖
      ≤ Real.sqrt N * ∑ d ∈ N.divisors, ((N / d).totient : ℝ) * Real.sqrt d := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  -- Step 1: pointwise bound, then pull out the constant factor √N.
  have step1 : ∑ r : ZMod N, ‖sqGaussSum r‖
      ≤ Real.sqrt N * ∑ r : ZMod N, Real.sqrt (N.gcd (2 * r).val) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    have h := sqGaussSum_norm_le_sqrt_gcd r
    rw [Nat.gcd_comm (2 * r).val N, Real.sqrt_mul (by positivity : (0:ℝ) ≤ (N:ℝ))] at h
    exact h
  -- Step 2: reindex r ↦ 2r (a bijection of ZMod N, since 2 is a unit at odd N).
  have hcop : Nat.Coprime 2 N := Nat.coprime_two_left.mpr hodd
  have hunit : IsUnit (2 : ZMod N) := by
    have h := (ZMod.isUnit_iff_coprime 2 N).mpr hcop
    simpa using h
  have hbij : Function.Bijective (fun r : ZMod N => 2 * r) :=
    Finite.injective_iff_bijective.mp hunit.mul_right_injective
  have step2 : ∑ r : ZMod N, Real.sqrt (N.gcd (2 * r).val)
      = ∑ c : ZMod N, Real.sqrt (N.gcd c.val) :=
    Fintype.sum_bijective (fun r : ZMod N => 2 * r) hbij
      (fun r => Real.sqrt (N.gcd (2 * r).val)) (fun c => Real.sqrt (N.gcd c.val))
      (fun _ => rfl)
  -- Step 3: transport the residue sum to `range N`.
  have himg : Finset.image ZMod.val (univ : Finset (ZMod N)) = range N := by
    ext k
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨c, rfl⟩; exact ZMod.val_lt c
    · intro hk; exact ⟨(k : ZMod N), ZMod.val_natCast_of_lt hk⟩
  have step3 : ∑ c : ZMod N, Real.sqrt (N.gcd c.val) = ∑ k ∈ range N, Real.sqrt (N.gcd k) := by
    rw [← himg, Finset.sum_image ((ZMod.val_injective N).injOn)]
  -- Assemble.
  calc ∑ r : ZMod N, ‖sqGaussSum r‖
      ≤ Real.sqrt N * ∑ r : ZMod N, Real.sqrt (N.gcd (2 * r).val) := step1
    _ = Real.sqrt N * ∑ c : ZMod N, Real.sqrt (N.gcd c.val) := by rw [step2]
    _ = Real.sqrt N * ∑ k ∈ range N, Real.sqrt (N.gcd k) := by rw [step3]
    _ = Real.sqrt N * ∑ d ∈ N.divisors, ((N / d).totient : ℝ) * Real.sqrt d := by
          rw [sum_weight_gcd_eq_divisor_sum N hN (fun m : ℕ => Real.sqrt m)]

end Szemeredi.Roth
