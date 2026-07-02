/-
  Chebyshev–PNT Bridge OQ-04 — Mertens' first theorem via the von Mangoldt
  floor identity (Abel/Dirichlet hyperbola backbone)

  Self-contained: imports only Mathlib so it is portable to Aristotle
  `prove_file` (no `Proofs.*` imports).

  ## Target (open in this gallery)

  Mertens' theorems, derived from Chebyshev-type bounds:

    (M1)  Σ_{p ≤ x} (log p)/p = log x + O(1)
    (M2)  Σ_{p ≤ x} 1/p      = log log x + M + O(1/log x)   (M = Mertens constant)

  The classical route is: prove the **von Mangoldt average** Σ_{d ≤ x} Λ(d)/d =
  log x + O(1) (this file), strip the prime-power tail to get (M1), then feed
  (M1) into Abel partial summation to get (M2).

  ## What is proved here (verified, no axioms)

  The exact, elementary backbone of (M1) in its Λ-weighted form. With
  `S_log(N) := Σ_{n=1}^N log n` and `Λ`-sum `Σ_{d=1}^N Λ(d)/d`:

  - **Step A (floor identity).** `Σ_{d=1}^N Λ(d)·⌊N/d⌋ = Σ_{n=1}^N log n`.
    Proof: `log n = Σ_{d ∣ n} Λ(d)` (`vonMangoldt_sum`), swap the double sum over
    `d ∣ n`, and collapse the inner count via `⌊N/d⌋ = #{n ≤ N : d ∣ n}`. This is
    the same hyperbola/swap used in the companion Möbius file
    `ChebyshevBoundsOQ04OQ01Mertens.lean`, transported to `Λ`.
  - **Step B (floor decomposition).** `N · Σ_{d=1}^N Λ(d)/d = S_log(N) + E(N)`,
    where `E(N) := Σ_{d=1}^N Λ(d)·fract(N/d)` is the fractional remainder.
  - **Step C (remainder bound).** `0 ≤ E(N) ≤ ψ(N)`, where `ψ(N) := Σ_{d=1}^N Λ(d)`
    is the second Chebyshev function. (Uses `Λ ≥ 0` and `0 ≤ fract < 1`.)

  ## Conditional result

  Combining Steps A–C with the two genuine analytic inputs — Chebyshev's bound
  `ψ(N) = O(N)` and Stirling's estimate `S_log(N) = N log N − N + O(log N)` —
  gives the Λ-weighted first Mertens estimate

    `Σ_{d=1}^N Λ(d)/d = log N + O(1)`.

  The two inputs are packaged as the hypotheses of `MertensInputs`. They are
  genuine *assumptions* (Chebyshev's `ψ = O(N)` is the gallery's standing open
  axiom `chebyshevPsi_asymptotic`; Stirling's `O(log N)` form is real-analytic),
  so this entry is `axiomatized` with 2 structure-encoded assumptions.

  ## Prime-power strip (this session, verified, no new axioms)

  The Λ-sum is split exactly into the honest prime sum and a prime-power tail,
  `Σ_{d≤N} Λ(d)/d = Σ_{p≤N} (log p)/p + R(N)` (`lambdaRecip_prime_split`), where
  `R(N) := Σ_{d≤N, d not prime} Λ(d)/d ≥ 0` (`primePowerTail_nonneg`). Because the
  tail is nonnegative, the conditional Λ-weighted estimate transfers directly to
  the honest prime sum as an *upper* bound (`primeLogRecip_le`):

    `Σ_{p≤N} (log p)/p ≤ log N + (1 + c_S + c_ψ)`   (N ≥ 2).

  This is the upper half of Mertens' first theorem for the actual prime sum,
  proved from the same 2 inputs (no new assumptions). The matching lower bound
  needs a uniform tail bound `R(N) = Σ_{p^k≤N, k≥2} (log p)/p^k = O(1)`; that
  geometric-series step and the Abel-summation passage M1 → M2 remain open.
-/
import Mathlib

open Finset
open scoped BigOperators ArithmeticFunction

namespace ChebyshevPNTBridgeOQ04

/-- The number of multiples of `d` in `Icc 1 N` equals `N / d` (nat division):
    `⌊N/d⌋ = #{n : 1 ≤ n ≤ N, d ∣ n}`.
    Mathlib hook: `Nat.Ioc_filter_dvd_card_eq_div`, with `Icc 1 N = Ioc 0 N` over ℕ. -/
theorem card_multiples_Icc (N d : ℕ) :
    ((Finset.Icc 1 N).filter (fun m => d ∣ m)).card = N / d := by
  have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hIcc, Nat.Ioc_filter_dvd_card_eq_div]

/-- **Step A — floor identity**: `Σ_{d=1}^N Λ(d)·⌊N/d⌋ = Σ_{n=1}^N log n`.
    Rewrite each `Λ(d)·⌊N/d⌋` as an inner count over `n ∈ {1,…,N}` with `d ∣ n`,
    swap the double sum, then collapse via `Σ_{d ∣ n} Λ(d) = log n`. -/
theorem sum_vonMangoldt_mul_floor_eq_sum_log (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ)
      = ∑ n ∈ Finset.Icc 1 N, Real.log n := by
  -- Per-term: `Λ(d)·⌊N/d⌋ = Σ_{n ∈ {1,…,N}} [d ∣ n] · Λ(d)`.
  have key : ∀ d : ℕ,
      ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ)
        = ∑ n ∈ Finset.Icc 1 N,
            (if d ∣ n then ArithmeticFunction.vonMangoldt d else 0) := by
    intro d
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_eq_mul, card_multiples_Icc]
    ring
  calc
    ∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ)
        = ∑ d ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
            (if d ∣ n then ArithmeticFunction.vonMangoldt d else 0) :=
          Finset.sum_congr rfl (fun d _ => key d)
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N,
            (if d ∣ n then ArithmeticFunction.vonMangoldt d else 0) := Finset.sum_comm
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d := by
          refine Finset.sum_congr rfl (fun n hn => ?_)
          simp only [Finset.mem_Icc] at hn
          rw [← Finset.sum_filter]
          congr 1
          ext d
          simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
          constructor
          · rintro ⟨⟨_, _⟩, hdvd⟩
            exact ⟨hdvd, by omega⟩
          · rintro ⟨hdvd, _⟩
            have hnpos : 0 < n := by omega
            have hd_le : d ≤ n := Nat.le_of_dvd hnpos hdvd
            have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hnpos
            exact ⟨⟨hd_pos, by omega⟩, hdvd⟩
    _ = ∑ n ∈ Finset.Icc 1 N, Real.log n := by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          rw [ArithmeticFunction.vonMangoldt_sum]

/-- The Λ-weighted reciprocal partial sum `Σ_{1 ≤ d ≤ N} Λ(d)/d`. -/
noncomputable def lambdaRecip (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d / (d : ℝ)

/-- The fractional remainder `E(N) := Σ_{1 ≤ d ≤ N} Λ(d)·fract(N/d)`. -/
noncomputable def lambdaFractRemainder (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    ArithmeticFunction.vonMangoldt d * Int.fract ((N : ℝ) / (d : ℝ))

/-- The second Chebyshev function `ψ(N) := Σ_{1 ≤ d ≤ N} Λ(d)`. -/
noncomputable def chebyshevPsi (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d

/-- **Step B — floor decomposition**:
    `N · (Σ Λ(d)/d) = (Σ log n) + E(N)`, by writing `⌊N/d⌋ = N/d − fract(N/d)`
    inside Step A. -/
theorem mul_lambdaRecip_eq (N : ℕ) :
    (N : ℝ) * lambdaRecip N
      = (∑ n ∈ Finset.Icc 1 N, Real.log n) + lambdaFractRemainder N := by
  unfold lambdaRecip lambdaFractRemainder
  rw [Finset.mul_sum]
  -- Per-term split `N · (Λ d / d) = Λ d · ⌊N/d⌋ + Λ d · fract(N/d)`.
  have hsplit : ∀ d ∈ Finset.Icc 1 N,
      (N : ℝ) * (ArithmeticFunction.vonMangoldt d / (d : ℝ))
        = ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ)
          + ArithmeticFunction.vonMangoldt d * Int.fract ((N : ℝ) / (d : ℝ)) := by
    intro d _
    have hfloorcast : (⌊(N : ℝ) / (d : ℝ)⌋ : ℝ) = ((N / d : ℕ) : ℝ) := by
      have hz : ⌊(N : ℝ) / (d : ℝ)⌋ = ((N / d : ℕ) : ℤ) := by
        rw [Int.floor_div_natCast, Int.floor_natCast, Int.natCast_div]
      rw [hz]; norm_cast
    have hfract : Int.fract ((N : ℝ) / (d : ℝ))
        = (N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ) := by
      rw [← Int.self_sub_floor, hfloorcast]
    rw [hfract]; ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
    sum_vonMangoldt_mul_floor_eq_sum_log]

/-- **Step C — remainder bound**: `0 ≤ E(N) ≤ ψ(N)`.
    Each term satisfies `0 ≤ Λ(d)·fract(N/d) ≤ Λ(d)` since `Λ(d) ≥ 0` and
    `0 ≤ fract < 1`. -/
theorem lambdaFractRemainder_bounds (N : ℕ) :
    0 ≤ lambdaFractRemainder N ∧ lambdaFractRemainder N ≤ chebyshevPsi N := by
  unfold lambdaFractRemainder chebyshevPsi
  refine ⟨?_, ?_⟩
  · refine Finset.sum_nonneg (fun d _ => ?_)
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Int.fract_nonneg _)
  · refine Finset.sum_le_sum (fun d _ => ?_)
    exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
      (le_of_lt (Int.fract_lt_one _))

/-- The exact decomposition rearranged: for `N ≥ 1`,
    `Σ Λ(d)/d = (Σ log n)/N + E(N)/N`. -/
theorem lambdaRecip_eq (N : ℕ) (hN : 1 ≤ N) :
    lambdaRecip N
      = (∑ n ∈ Finset.Icc 1 N, Real.log n) / (N : ℝ)
        + lambdaFractRemainder N / (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have h := mul_lambdaRecip_eq N
  rw [div_add_div_same, eq_div_iff hN0]
  linear_combination h

/-- The two analytic inputs to Mertens' first theorem, packaged as hypotheses.

    Both are genuine assumptions (counted toward `axiomCount = 2`):

    * `chebyshev` — Chebyshev's bound `ψ(N) ≤ c_ψ · N` (the gallery's open
      `chebyshevPsi_asymptotic`, upper half).
    * `stirling`  — Stirling's estimate `|Σ_{n≤N} log n − (N log N − N)| ≤ c_S · log N`.

    The constants are assumed nonnegative (true for any genuine error bound). -/
structure MertensInputs where
  cChebyshev : ℝ
  cChebyshev_nonneg : 0 ≤ cChebyshev
  chebyshev : ∀ N : ℕ, chebyshevPsi N ≤ cChebyshev * (N : ℝ)
  cStirling : ℝ
  cStirling_nonneg : 0 ≤ cStirling
  stirling : ∀ N : ℕ, 2 ≤ N →
    |(∑ n ∈ Finset.Icc 1 N, Real.log n) - ((N : ℝ) * Real.log N - (N : ℝ))|
      ≤ cStirling * Real.log N

/-- **Mertens' first theorem, Λ-weighted form (conditional)**:
    `Σ_{d=1}^N Λ(d)/d = log N + O(1)`, with the explicit constant
    `C = 1 + c_S + c_ψ` from the two analytic inputs. -/
theorem lambdaRecip_sub_log_le (h : MertensInputs) :
    ∀ N : ℕ, 2 ≤ N →
      |lambdaRecip N - Real.log N| ≤ 1 + h.cStirling + h.cChebyshev := by
  intro N hN
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  -- Notation.
  set S : ℝ := ∑ n ∈ Finset.Icc 1 N, Real.log n with hS
  set E : ℝ := lambdaFractRemainder N with hE
  have hlogN_pos : 0 < Real.log N := by
    have : (1 : ℝ) < N := by exact_mod_cast hN
    exact Real.log_pos this
  -- log N ≤ N, hence (log N)/N ≤ 1.
  have hlogN_le : Real.log N ≤ (N : ℝ) := by
    have := Real.log_le_sub_one_of_pos hNpos
    linarith
  have hlogN_div_le : Real.log N / (N : ℝ) ≤ 1 := by
    rw [div_le_one hNpos]; exact hlogN_le
  -- Decompose: Σ Λ/d = S/N + E/N.
  have hdecomp := lambdaRecip_eq N hN1
  rw [← hS, ← hE] at hdecomp
  -- Stirling: S/N = log N − 1 + r/N with |r| ≤ c_S log N.
  have hst := h.stirling N hN
  rw [← hS] at hst
  -- Chebyshev: 0 ≤ E ≤ ψ(N) ≤ c_ψ N.
  have hEbounds := lambdaFractRemainder_bounds N
  rw [← hE] at hEbounds
  have hpsi := h.chebyshev N
  have hE_nonneg : 0 ≤ E := hEbounds.1
  have hE_le : E ≤ h.cChebyshev * (N : ℝ) := le_trans hEbounds.2 hpsi
  -- Bound |E/N| ≤ c_ψ.
  have hE_div_le : E / (N : ℝ) ≤ h.cChebyshev := by
    rw [div_le_iff₀ hNpos]; exact hE_le
  have hE_div_nonneg : 0 ≤ E / (N : ℝ) := div_nonneg hE_nonneg (le_of_lt hNpos)
  -- Bound |S/N − (log N − 1)| = |S − (N log N − N)|/N ≤ c_S log N / N ≤ c_S.
  have hSN : |S / (N : ℝ) - (Real.log N - 1)| ≤ h.cStirling := by
    have hrw : S / (N : ℝ) - (Real.log N - 1)
        = (S - ((N : ℝ) * Real.log N - (N : ℝ))) / (N : ℝ) := by
      field_simp; ring
    rw [hrw, abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos]
    calc |S - ((N : ℝ) * Real.log N - (N : ℝ))|
        ≤ h.cStirling * Real.log N := hst
      _ ≤ h.cStirling * (N : ℝ) :=
          mul_le_mul_of_nonneg_left hlogN_le h.cStirling_nonneg
  -- Assemble: Σ Λ/d − log N = (S/N − (log N − 1)) + E/N − 1.
  have hfinal : lambdaRecip N - Real.log N
      = (S / (N : ℝ) - (Real.log N - 1)) + E / (N : ℝ) - 1 := by
    rw [hdecomp]; ring
  rw [hfinal]
  -- |a + b − 1| ≤ |a| + |b| + 1 ≤ c_S + c_ψ + 1.
  have habs := abs_le.mp hSN
  rw [abs_le]
  constructor <;>
    linarith [habs.1, habs.2, hE_div_nonneg, hE_div_le,
      h.cChebyshev_nonneg, h.cStirling_nonneg]

/-!
## Prime-power strip (Step 2 toward M1 for the honest prime sum)

The Λ-weighted sum `Σ_{d≤N} Λ(d)/d` counts *all* prime powers. Mertens' first
theorem is a statement about the prime sum `Σ_{p≤N} (log p)/p`. We split the
Λ-sum exactly into its prime block and a prime-power tail, and use the tail's
nonnegativity to transfer the *upper* half of the conditional estimate directly
to the honest prime sum — with **no new assumptions** (still the 2 inputs of
`MertensInputs`). The lower half needs a uniform upper bound on the tail
`Σ_{p^k≤N, k≥2} (log p)/p^k = O(1)`, which remains the open analytic step.
-/

/-- The honest first-Mertens partial sum `Σ_{p ≤ N, p prime} (log p)/p`. -/
noncomputable def primeLogRecip (N : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 N).filter (fun d => Nat.Prime d), Real.log d / (d : ℝ)

/-- The prime-power tail `R(N) := Σ_{d ≤ N, d not prime} Λ(d)/d`.
    Its only nonzero terms are the higher prime powers `d = p^k` with `k ≥ 2`
    (where `Λ(d) = log p ≠ 0` but `d` is not prime). -/
noncomputable def primePowerTail (N : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 N).filter (fun d => ¬ Nat.Prime d),
    ArithmeticFunction.vonMangoldt d / (d : ℝ)

/-- **Exact prime/prime-power split** of the Λ-weighted sum:
    `Σ_{d≤N} Λ(d)/d = Σ_{p≤N} (log p)/p + R(N)`.
    On the prime block `Λ(p) = log p` (`vonMangoldt_apply_prime`); the rest is
    the tail `R(N)` by definition. -/
theorem lambdaRecip_prime_split (N : ℕ) :
    lambdaRecip N = primeLogRecip N + primePowerTail N := by
  unfold lambdaRecip primeLogRecip primePowerTail
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N)
        (fun d => Nat.Prime d)
        (fun d => ArithmeticFunction.vonMangoldt d / (d : ℝ))]
  congr 1
  refine Finset.sum_congr rfl (fun d hd => ?_)
  simp only [Finset.mem_filter] at hd
  rw [ArithmeticFunction.vonMangoldt_apply_prime hd.2]

/-- **Tail nonnegativity**: `0 ≤ R(N)`. Each term `Λ(d)/d ≥ 0`. -/
theorem primePowerTail_nonneg (N : ℕ) : 0 ≤ primePowerTail N := by
  unfold primePowerTail
  refine Finset.sum_nonneg (fun d _ => ?_)
  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)

/-- **Upper half of Mertens' first theorem for the honest prime sum**
    (conditional, no new assumptions):
    `Σ_{p ≤ N} (log p)/p ≤ log N + (1 + c_S + c_ψ)` for `N ≥ 2`.

    Since `primeLogRecip N = lambdaRecip N − R(N)` and `R(N) ≥ 0`, the prime sum
    is dominated by the Λ-sum, and the conditional Λ-weighted estimate
    `lambdaRecip N ≤ log N + (1+c_S+c_ψ)` transfers directly. The matching lower
    bound requires `R(N) = O(1)` (the prime-power tail bound), still open. -/
theorem primeLogRecip_le (h : MertensInputs) :
    ∀ N : ℕ, 2 ≤ N →
      primeLogRecip N ≤ Real.log N + (1 + h.cStirling + h.cChebyshev) := by
  intro N hN
  have hsplit := lambdaRecip_prime_split N
  have htail := primePowerTail_nonneg N
  have hM1 := lambdaRecip_sub_log_le h N hN
  have hupper := (abs_le.mp hM1).2
  linarith [hsplit, htail, hupper]

end ChebyshevPNTBridgeOQ04
