/-
  Chebyshev Bounds OQ-04-OQ-01 — Weak Mertens estimate (floor-identity route)

  Companion to `ChebyshevBoundsOQ04OQ01.lean`. Self-contained: imports only
  Mathlib so it is portable to Aristotle `prove_file` (no `Proofs.*` imports).

  ## Goal

  Prove the *weak Mertens reciprocal bound*

      |M₁(N)| ≤ 1,   where  M₁(N) := Σ_{d=1}^{N} μ(d)/d.

  This is the tight form of the |Σ μ(d)/d| ≤ 1 + log N estimate needed for the
  Selberg symmetry step toward an elementary PNT. The route avoids
  summation-by-parts entirely (the classical Dirichlet hyperbola / floor route):

  - **Step 1 (floor identity).** Σ_{d=1}^{N} μ(d)·⌊N/d⌋ = 1 for N ≥ 1.
    Because ⌊N/d⌋ = #{m ∈ Icc 1 N : d ∣ m}, swap the order of the double sum
    over `d ∣ m` and collapse the inner sum via the Möbius indicator
    Σ_{d ∣ m} μ(d) = [m = 1].
  - **Step 2 (decompose the floor).** ⌊N/d⌋ = N/d − fract(N/d) over ℝ, hence
    N·M₁(N) = 1 + Σ_{d=1}^{N} μ(d)·fract(N/d).
  - **Step 3 (bound).** |fract| < 1 and the d = 1 term vanishes, so
    |N·M₁(N)| < N, giving |M₁(N)| ≤ 1 after dividing by N > 0.

  No axioms are introduced; the parent `chebyshevPsi_asymptotic` axiom remains
  the open target.
-/
import Mathlib

open Finset
open scoped BigOperators ArithmeticFunction

namespace ChebyshevBoundsOQ04OQ01

/-- The reciprocal Mertens partial sum `M₁(N) := Σ_{1 ≤ d ≤ N} μ(d)/d`, in ℝ. -/
noncomputable def mertensRecip (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)

/-- `M₁(0) = 0` since `Icc 1 0 = ∅`. -/
theorem mertensRecip_zero : mertensRecip 0 = 0 := by
  unfold mertensRecip
  rw [Finset.Icc_eq_empty_of_lt (by decide : (0 : ℕ) < 1)]
  simp

/-- The number of multiples of `d` in `Icc 1 N` equals `N / d` (nat division).
    `⌊N/d⌋ = #{m : 1 ≤ m ≤ N, d ∣ m}`.
    Mathlib hook: `Nat.Ioc_filter_dvd_card_eq_div N d : #{x ∈ Ioc 0 N | d ∣ x} = N / d`,
    combined with `Finset.Ioc 0 N = Finset.Icc 1 N` (for ℕ, since `Ioc 0 N` and
    `Icc 1 N` describe the same set `{1, …, N}`). -/
theorem card_multiples_Icc (N d : ℕ) :
    ((Finset.Icc 1 N).filter (fun m => d ∣ m)).card = N / d := by
  have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hIcc, Nat.Ioc_filter_dvd_card_eq_div]

/-- **Möbius indicator**: `Σ_{d ∣ m} μ(d) = [m = 1]` cast to ℤ.
    Mathlib hook: `(μ * ζ) m = ∑_{d ∣ m} μ d` via `ArithmeticFunction.coe_mul_zeta_apply`
    (or `coe_zeta_mul_apply`), and `μ * ζ = 1` via `ArithmeticFunction.moebius_mul_coe_zeta`;
    then `ArithmeticFunction.one_apply` gives `(1 : ArithmeticFunction ℤ) m = if m = 1 then 1 else 0`. -/
theorem sum_moebius_divisors (m : ℕ) (_hm : 1 ≤ m) :
    ∑ d ∈ m.divisors, ArithmeticFunction.moebius d = if m = 1 then 1 else 0 := by
  rw [← ArithmeticFunction.coe_mul_zeta_apply,
    ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]

/-- **Step 1 — floor identity**: `Σ_{d=1}^{N} μ(d)·⌊N/d⌋ = 1` for `N ≥ 1`.
    Proof: rewrite `N/d` as the count of multiples, swap the double sum over the
    `d ∣ m` relation, collapse the inner sum by the Möbius indicator. -/
theorem sum_moebius_mul_floor (N : ℕ) (hN : 1 ≤ N) :
    ∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℤ) * ((N / d : ℕ) : ℤ) = 1 := by
  -- Rewrite each term `μ(d)·⌊N/d⌋` as an inner sum over `k ∈ {1,…,N}` guarded by `d ∣ k`.
  have key : ∀ d : ℕ,
      (ArithmeticFunction.moebius d : ℤ) * ((N / d : ℕ) : ℤ)
        = ∑ k ∈ Finset.Icc 1 N, (if d ∣ k then ArithmeticFunction.moebius d else 0) := by
    intro d
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_eq_mul, card_multiples_Icc]
    ring
  calc
    ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℤ) * ((N / d : ℕ) : ℤ)
        = ∑ d ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
            (if d ∣ k then ArithmeticFunction.moebius d else 0) :=
          Finset.sum_congr rfl (fun d _ => key d)
    _ = ∑ k ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N,
            (if d ∣ k then ArithmeticFunction.moebius d else 0) := Finset.sum_comm
    _ = ∑ k ∈ Finset.Icc 1 N, ∑ d ∈ k.divisors, ArithmeticFunction.moebius d := by
          refine Finset.sum_congr rfl (fun k hk => ?_)
          simp only [Finset.mem_Icc] at hk
          rw [← Finset.sum_filter]
          congr 1
          ext d
          simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
          constructor
          · rintro ⟨⟨_, _⟩, hdvd⟩
            exact ⟨hdvd, by omega⟩
          · rintro ⟨hdvd, _⟩
            have hkpos : 0 < k := by omega
            have hd_le : d ≤ k := Nat.le_of_dvd hkpos hdvd
            have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hkpos
            exact ⟨⟨hd_pos, by omega⟩, hdvd⟩
    _ = ∑ k ∈ Finset.Icc 1 N, (if k = 1 then (1 : ℤ) else 0) := by
          refine Finset.sum_congr rfl (fun k hk => ?_)
          simp only [Finset.mem_Icc] at hk
          rw [sum_moebius_divisors k hk.1]
    _ = 1 := by
          simp [Finset.sum_ite_eq', Finset.mem_Icc, hN]

/-- **Step 2 — real form**: `N·M₁(N) = 1 + Σ_{d=1}^{N} μ(d)·fract(N/d)`.
    Obtained by writing `⌊N/d⌋ = N/d − fract(N/d)` over ℝ in Step 1. -/
theorem mul_mertensRecip_eq (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) * mertensRecip N
      = 1 + ∑ d ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius d : ℝ) * Int.fract ((N : ℝ) / (d : ℝ)) := by
  unfold mertensRecip
  rw [Finset.mul_sum]
  -- Per-term: `N · (μ d / d) = μ d · ⌊N/d⌋ + μ d · fract(N/d)`.
  have hsplit : ∀ d ∈ Finset.Icc 1 N,
      (N : ℝ) * ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ))
        = (ArithmeticFunction.moebius d : ℝ) * ((N / d : ℕ) : ℝ)
          + (ArithmeticFunction.moebius d : ℝ) * Int.fract ((N : ℝ) / (d : ℝ)) := by
    intro d _
    -- ⌊(N:ℝ)/(d:ℝ)⌋ as a real equals the nat floor `N / d`.
    have hfloorcast : (⌊(N : ℝ) / (d : ℝ)⌋ : ℝ) = ((N / d : ℕ) : ℝ) := by
      have hz : ⌊(N : ℝ) / (d : ℝ)⌋ = ((N / d : ℕ) : ℤ) := by
        rw [Int.floor_div_natCast, Int.floor_natCast, Int.natCast_div]
      rw [hz]; norm_cast
    -- fract(N/d) = N/d − ⌊N/d⌋.
    have hfract : Int.fract ((N : ℝ) / (d : ℝ))
        = (N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ) := by
      rw [← Int.self_sub_floor, hfloorcast]
    rw [hfract]; ring
  -- The integer floor identity, cast to ℝ.
  have hcast : (∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) * ((N / d : ℕ) : ℝ))
      = (((∑ d ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius d : ℤ) * ((N / d : ℕ) : ℤ)) : ℤ) : ℝ) := by
    rw [Int.cast_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [Int.cast_mul, Int.cast_natCast]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hcast,
    sum_moebius_mul_floor N hN, Int.cast_one]

/-- The fractional remainder sum is bounded by `N − 1`: the `d = 1` term
    vanishes (`fract` of an integer is `0`) and every other term has
    `|μ(d)·fract| ≤ 1`, with `N − 1` such terms.
    Mathlib hooks: `Int.fract_intCast` / `Int.fract_natCast` (the `d = 1` term:
    `fract (N/1) = fract N = 0`), `Int.fract_nonneg`, `Int.fract_lt_one`,
    `ArithmeticFunction.abs_moebius_le_one`, `Finset.abs_sum_le_sum_abs`. -/
theorem fract_sum_abs_le (N : ℕ) (hN : 1 ≤ N) :
    |∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) * Int.fract ((N : ℝ) / (d : ℝ))|
      ≤ (N : ℝ) - 1 := by
  set f : ℕ → ℝ :=
    fun d => (ArithmeticFunction.moebius d : ℝ) * Int.fract ((N : ℝ) / (d : ℝ)) with hf
  have h1mem : (1 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_refl 1, hN⟩
  -- The `d = 1` term vanishes: `fract (N / 1) = fract N = 0`.
  have hf1 : f 1 = 0 := by
    simp only [hf, Nat.cast_one, div_one, Int.fract_natCast, mul_zero]
  -- Drop the `d = 1` term from the sum.
  have hsum : ∑ d ∈ Finset.Icc 1 N, f d = ∑ d ∈ (Finset.Icc 1 N).erase 1, f d := by
    rw [← Finset.add_sum_erase _ f h1mem, hf1, zero_add]
  rw [hsum]
  calc |∑ d ∈ (Finset.Icc 1 N).erase 1, f d|
      ≤ ∑ d ∈ (Finset.Icc 1 N).erase 1, |f d| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ (Finset.Icc 1 N).erase 1, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d _
        have hμ : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
          have h := ArithmeticFunction.abs_moebius_le_one (n := d)
          calc |(ArithmeticFunction.moebius d : ℝ)|
              = ((|ArithmeticFunction.moebius d| : ℤ) : ℝ) := by rw [Int.cast_abs]
            _ ≤ ((1 : ℤ) : ℝ) := by exact_mod_cast h
            _ = 1 := by norm_num
        have hfr : |Int.fract ((N : ℝ) / (d : ℝ))| ≤ 1 := by
          rw [abs_of_nonneg (Int.fract_nonneg _)]
          exact le_of_lt (Int.fract_lt_one _)
        calc |f d|
            = |(ArithmeticFunction.moebius d : ℝ)| * |Int.fract ((N : ℝ) / (d : ℝ))| := by
              rw [hf]; exact abs_mul _ _
          _ ≤ 1 * 1 := mul_le_mul hμ hfr (abs_nonneg _) (by norm_num)
          _ = 1 := by norm_num
    _ = (((Finset.Icc 1 N).erase 1).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = (N : ℝ) - 1 := by
        rw [Finset.card_erase_of_mem h1mem, Nat.card_Icc]
        have hns : N + 1 - 1 - 1 = N - 1 := by omega
        rw [hns, Nat.cast_sub hN, Nat.cast_one]

/-- **Weak Mertens reciprocal bound**: `|M₁(N)| ≤ 1` for all `N`.
    For `N = 0` both sides are `0 ≤ 1`; for `N ≥ 1` combine Steps 2–3 and divide
    by `N > 0`. -/
theorem mertensRecip_abs_le_one (N : ℕ) : |mertensRecip N| ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; rw [mertensRecip_zero]; norm_num
  · have hN1 : 1 ≤ N := hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have heq := mul_mertensRecip_eq N hN1
    have hbound := fract_sum_abs_le N hN1
    -- `|N · M₁| = |1 + S| ≤ 1 + |S| ≤ 1 + (N − 1) = N`.
    have hkey : |(N : ℝ) * mertensRecip N| ≤ N := by
      rw [heq, abs_le]
      rw [abs_le] at hbound
      constructor <;> linarith [hbound.1, hbound.2]
    rw [abs_mul, abs_of_pos hNpos] at hkey
    nlinarith [hkey, hNpos, abs_nonneg (mertensRecip N)]

end ChebyshevBoundsOQ04OQ01
