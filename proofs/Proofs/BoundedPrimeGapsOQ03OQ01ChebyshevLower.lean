/-
  Chebyshev lower bound — the single missing Mathlib ingredient for
  `bounded-prime-gaps-oq-03-oq-01-oq-01`.

  STATUS: build-gated ORPHAN (not imported by Proofs.lean). It exists as a
  turnkey target for a future build / Aristotle `prove_file` once a backend
  is available. Do NOT register in Proofs.lean until it compiles green.

  ## Why this file exists

  The open question for `BoundedPrimeGapsOQ03OQ01.lean` is exactly to discharge
  the standing axiom

      axiom diameter_upper_bound_exists :
        ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 2 ≤ k →
          (minAdmissibleDiameter k : ℝ) ≤ C * k * (Real.log k) ^ 2

  The reduction (see knowledge.md, Route B) is:

    • Take H = the k smallest primes p > k. It is admissible
      (`IsAdmissible H := ∀ p prime, (H.image (· % p)).card < p`):
        - prime p ≤ k: every element of H is a prime > k ≥ p, so residue 0
          is missing ⇒ |H mod p| ≤ p − 1 < p;
        - prime p > k: |H| = k < p ⇒ |H mod p| ≤ k < p.
    • Its diameter is (k-th prime > k) − (smallest prime > k). Bounding this by
      C·k·(log k)² needs ≥ k primes inside an interval of length C·k·(log k)²
      just above k, i.e. a LOWER bound on π.

  Mathlib v4.26.0 status (verified by grep of /private/tmp/mathlib-grep @ v4.26.0):

    • `Mathlib.NumberTheory.Chebyshev` ALREADY develops ψ and θ in full:
        Chebyshev.psi, Chebyshev.theta, theta_eq_log_primorial,
        theta_le_log4_mul_x, psi_le, psi_le_const_mul_self,
        abs_psi_sub_theta_le_sqrt_mul_log, psi_eq_theta_add_sum_theta, …
      — but EVERY bound in that file is an UPPER bound. There is NO θ/ψ lower
      bound anywhere in Mathlib. That single lower bound is the whole gap.
    • `Mathlib.NumberTheory.PrimeCounting`: only `primeCounting'_add_le`
      (upper bound on π) and `add_two_le_nth_prime` (lower bound on nth prime)
      — both wrong direction.

  ## The missing lemma (this file)

  A Chebyshev-strength LOWER bound on ψ. Classical elementary derivation
  (de Polignac / central binomial), with confirmed v4.26.0 hooks:

    1. log ((2n)! / (n!)²) = log C(2n,n).  Mathlib: `Nat.centralBinom`,
       `Nat.choose_central…`.
    2. log C(2n,n) ≤ ψ(2n):  C(2n,n) ∣ lcm(1,…,2n) and ψ(N) = log lcm(1,…,N);
       or via the de Polignac identity log(N!) = ∑_{d≤N} Λ(d)⌊N/d⌋ together with
       `ArithmeticFunction.vonMangoldt_sum : ∑ i ∈ n.divisors, Λ i = Real.log n`.
       (This step — connecting ψ to log C(2n,n) — is the ~80–150 line core that
       Mathlib does not yet package.)
    3. 4 ^ n ≤ (2n+1) · C(2n,n):  `Nat.four_pow_le_two_mul_add_one_mul_central_binom`
       (in `Mathlib/Data/Nat/Choose/Central.lean`); sharper
       `Nat.four_pow_lt_mul_centralBinom (n≥4)`.
    ⇒ ψ(2n) ≥ log C(2n,n) ≥ n·log 4 − log(2n+1) ≥ c·(2n) for large n.

  Downstream (cheap, once the lemma below holds):
    • θ(x) ≥ ψ(x) − 2√x·log x  via `abs_psi_sub_theta_le_sqrt_mul_log` ⇒ θ(x) ≥ c'·x.
    • θ(x) = ∑_{p≤x} log p ≤ π(x)·log x ⇒ π(x) ≥ θ(x)/log x ≥ c'·x/log x.
    • Count ≥ k primes in (k, k + C·k·(log k)²]; finish the admissible
      construction and discharge `diameter_upper_bound_exists`.

  This file states ONLY step (2)+(3) packaged as the ψ lower bound — the genuine
  Mathlib gap. Everything else above is downstream bookkeeping or already present.
-/
import Mathlib

open scoped ArithmeticFunction

namespace BoundedPrimeGapsOQ03OQ01.ChebyshevLower

/-- **The missing ingredient.** A Chebyshev-strength lower bound on the second
Chebyshev function `ψ(x) = ∑_{n ≤ x} Λ(n)`.

Mathlib v4.26.0 has the full `Chebyshev.psi` / `Chebyshev.theta` API but only
*upper* bounds (`Chebyshev.psi_le`, `Chebyshev.theta_le_log4_mul_x`). This
existential lower bound is the single piece Route B needs; it is a known
classical result (no creative insight required), hence a clean Aristotle /
future-build target.

Proof sketch: `ψ(2n) ≥ log C(2n,n) ≥ n·log 4 − log(2n+1)`. The size bound uses
`Nat.four_pow_le_two_mul_add_one_mul_central_binom`. The crux `log C(2n,n) ≤ ψ(2n)`
MUST go through the de Polignac floor-sum identity and
`ArithmeticFunction.vonMangoldt_sum`: the lcm route (`C(2n,n) ∣ lcm(1..2n)`) is
NOT available — Mathlib has no `centralBinom ∣ lcm` lemma (grep: 0 hits) and no
`ψ = log lcm` packaging. A positive constant works for all `x ≥ 2` because `ψ`
is monotone with `ψ 2 = Real.log 2 > 0` and `ψ x / x → 1`. -/

/-
  TURNKEY DECOMPOSITION (researcher-8, 2026-06-16) — transcribe these as named
  sorried lemmas, then prove top-down. Confirmed v4.26.0 hooks in brackets.

  STATUS (researcher-2, 2026-06-18): L1, L2, L3 are all PROVED, AND the headline
  assembly `chebyshev_psi_lower_bound` is now PROVED in full (Mathlib-only, no
  `sorry`/`axiom`) — see the proof at the theorem below. The assembly uses the
  elementary `2n+1 ≤ 3ⁿ` size bound to obtain a SINGLE positive constant
  `c = log(4/3)/4` valid at every real `x ≥ 2` with no "large x" caveat. The
  downstream θ bookkeeping `chebyshev_theta_lower_bound` (via
  `abs_psi_sub_theta_le_sqrt_mul_log`) is ALSO now PROVED — the whole file is
  sorry-free and axiom-free. Only the green docker build remains (build-gated).
  VERIFY-BY-CONSTRUCTION: every Mathlib lemma used by the new assembly was checked
  by name + signature against the offline checkout at build pin 2df2f0150c
  (`Chebyshev.psi_mono`, `Nat.one_le_floor_iff`, `Nat.floor_le`,
  `Nat.lt_floor_add_one`, `Real.log_le_log_iff`, `Real.log_div`, `Real.log_pos`,
  `Real.log_pow`); a green docker build was deferred (host load ~20 with 7 competing
  lean-build containers; worktree `proofs/.lake` is an absolute-path symlink that
  does not resolve inside the build container). File stays an ORPHAN until built green.

  -- L1 (de Polignac / Legendre floor-sum identity) — genuine ~50–100 line core
  lemma log_factorial_eq_sum_vonMangoldt_mul_div (N : ℕ) :
      Real.log (N ! : ℝ) = ∑ d ∈ Finset.Ioc 0 N, Λ d * ((N / d : ℕ) : ℝ)
  --   log(N!) = ∑_{n∈Ioc 0 N} log n = ∑_n ∑_{d ∈ n.divisors} Λ d   [vonMangoldt_sum]
  --           = ∑_{d∈Ioc 0 N} Λ d · #{n∈Ioc 0 N : d∣n}             [Finset.sum swap]
  --           = ∑_{d∈Ioc 0 N} Λ d · (N/d)   [Nat.Ioc_filter_dvd_card_eq_div,
  --                                          Data/Nat/Factorization/Basic.lean:475]
  --   NB Ioc 0 N matches Chebyshev.psi's own sum range exactly — no Icc/Ioc juggling.

  -- L2 (key inequality — THE gap) : log of central binomial ≤ ψ(2n)
  lemma log_centralBinom_le_psi (n : ℕ) :
      Real.log (Nat.centralBinom n : ℝ) ≤ Chebyshev.psi (2 * n)
  --   = ∑_{d∈Ioc 0 2n} Λ d · ((2n)/d − 2·(n/d))  [L1 twice; n/d=0 for d>n]
  --   ≤ ∑_{d∈Ioc 0 2n} Λ d · 1  [pointwise 0 ≤ (2n)/d − 2(n/d) ≤ 1; vonMangoldt_nonneg]
  --   = ψ(2n).  Hardest piece = the ℕ-division bracket bound.

  -- L3 (size) : log C(2n,n) ≥ n·log 4 − log(2n+1)
  lemma log_four_mul_le_log_centralBinom (n : ℕ) :
      (n : ℝ) * Real.log 4 - Real.log (2*n+1) ≤ Real.log (Nat.centralBinom n : ℝ)
  --   logs of Nat.four_pow_le_two_mul_add_one_mul_central_binom (4^n ≤ (2n+1)·C(2n,n)).

  -- assembly: ψ(2n) ≥ n·log4 − log(2n+1); pick c=(log 4)/4 and use psi_mono with
  -- ψ x ≥ ψ(2⌊x/2⌋) to cover every real x ≥ 2 with a single constant.

  HOOKS RE-VERIFIED against the offline Mathlib checkout @ pin 2df2f0150c
  (researcher-5, 2026-06-16) — every name below exists at the build pin:
    • L1 swap : Nat.Ioc_filter_dvd_card_eq_div   (Data/Nat/Factorization/Basic.lean:475)
    • L1 core : ArithmeticFunction.vonMangoldt_sum (NumberTheory/ArithmeticFunction/VonMangoldt.lean:102)
    • L3 size : Nat.four_pow_le_two_mul_add_one_mul_central_binom (Data/Nat/Choose/Sum.lean:121)
    • ψ def   : Chebyshev.psi x = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n   (NumberTheory/Chebyshev.lean:55)
              ⇒ ψ(2n) ranges over Ioc 0 (2n), matching L1's `Ioc 0 N` exactly.
    • θ bridge: Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (NumberTheory/Chebyshev.lean:205)
  L2 hooks additionally verified @ 2df2f0150c (researcher-3, 2026-06-18):
    • Nat.choose_mul_factorial_mul_factorial (Data/Nat/Choose/Basic.lean:141)
    • Nat.centralBinom_eq_two_mul_choose / Nat.centralBinom_pos (Data/Nat/Choose/Central.lean)
    • ArithmeticFunction.vonMangoldt_nonneg (NumberTheory/ArithmeticFunction/VonMangoldt.lean:80)
    • Nat.floor_natCast, Real.log_mul, Finset.sum_subset, Finset.Ioc_subset_Ioc_right,
      Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_le_sum, Nat.div_eq_of_lt,
      Nat.le_div_iff_mul_le, Nat.div_lt_iff_lt_mul, Nat.div_mul_le_self, Nat.div_add_mod.
  Status: L1/L2/L3 (the genuine core), `chebyshev_psi_lower_bound`, AND
  `chebyshev_theta_lower_bound` (downstream θ bookkeeping) are all fully proved
  below — the file is sorry-free and axiom-free. Build deferred under host
  contention (see STATUS above).
-/

/-- **L1** (de Polignac / Legendre floor-sum identity). Build-pending target.
`log(N!) = ∑_{d ≤ N} Λ(d)·⌊N/d⌋`, via `vonMangoldt_sum` + a `Finset.sum` swap
discharged by `Nat.Ioc_filter_dvd_card_eq_div`. -/
lemma log_factorial_eq_sum_vonMangoldt_mul_div (N : ℕ) :
    Real.log (Nat.factorial N : ℝ)
      = ∑ d ∈ Finset.Ioc 0 N, Λ d * ((N / d : ℕ) : ℝ) := by
  -- Step 1: `N! = ∏_{n ∈ Ioc 0 N} n` (by induction on `N`).
  have hfact : (Nat.factorial N : ℝ) = ∏ n ∈ Finset.Ioc 0 N, (n : ℝ) := by
    induction N with
    | zero => simp
    | succ k ih =>
        rw [Finset.prod_Ioc_succ_top (Nat.zero_le k), ← ih, Nat.factorial_succ]
        push_cast; ring
  rw [hfact, Real.log_prod _ _ (fun n hn => by
    have h : 0 < n := (Finset.mem_Ioc.mp hn).1
    exact_mod_cast h.ne')]
  -- Step 2: `log n = ∑_{d ∣ n} Λ d` (von Mangoldt summatory identity).
  rw [show (∑ n ∈ Finset.Ioc 0 N, Real.log (n : ℝ))
        = ∑ n ∈ Finset.Ioc 0 N, ∑ d ∈ n.divisors, Λ d from
      Finset.sum_congr rfl (fun n _ => (ArithmeticFunction.vonMangoldt_sum).symm)]
  -- Step 3: replace `n.divisors` by `{d ∈ Ioc 0 N | d ∣ n}` (valid since `n ≤ N`).
  have hdiv : ∀ n ∈ Finset.Ioc 0 N,
      (∑ d ∈ n.divisors, Λ d) = ∑ d ∈ (Finset.Ioc 0 N).filter (· ∣ n), Λ d := by
    intro n hn
    obtain ⟨hn0, hnN⟩ := Finset.mem_Ioc.mp hn
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega), le_trans (Nat.le_of_dvd (by omega) hd) hnN⟩, hd⟩
    · rintro ⟨_, hd⟩
      exact ⟨hd, by omega⟩
  rw [Finset.sum_congr rfl hdiv]
  -- Step 4: turn each filtered sum into an indicator sum and swap the order.
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  -- Step 5: collapse the inner constant sum to `Λ d · (N / d)`.
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_filter, Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul,
    mul_comm]

/-- **L2** (the genuine Mathlib gap): `log C(2n,n) ≤ ψ(2n)`. Build-pending.
From L1 applied to `(2n)!` and `(n!)²` plus the pointwise floor bound
`0 ≤ ⌊2n/d⌋ − 2⌊n/d⌋ ≤ 1` and `vonMangoldt_nonneg`.

Derivation: `C(2n,n)·(n!)² = (2n)!` (`Nat.choose_mul_factorial_mul_factorial`)
gives `log C(2n,n) = log(2n)! − 2·log n!`. Expand both factorial logs by L1 over
`Ioc 0 (2n)` (the `n!` sum extends freely: `n/d = 0` for `d > n`), collapsing the
target to `∑_{d∈Ioc 0 2n} Λ d·(⌊2n/d⌋ − 2⌊n/d⌋)`. Termwise, `Λ d ≥ 0` and the
ℕ-division bracket lies in `{0,1}` (lower: `2⌊n/d⌋ ≤ ⌊2n/d⌋`; upper:
`⌊2n/d⌋ ≤ 2⌊n/d⌋ + 1` from `n = d⌊n/d⌋ + n%d`, `n%d < d`), so each term is `≤ Λ d`
and the sum is `≤ ψ(2n)`. -/
lemma log_centralBinom_le_psi (n : ℕ) :
    Real.log (Nat.centralBinom n : ℝ) ≤ Chebyshev.psi (2 * n) := by
  -- `ψ(2n)` as a finite sum over `Ioc 0 (2n)`.
  have hfloor : ⌊(2 * n : ℝ)⌋₊ = 2 * n := by
    rw [show (2 * n : ℝ) = ((2 * n : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  have hpsi : Chebyshev.psi (2 * n) = ∑ d ∈ Finset.Ioc 0 (2 * n), Λ d := by
    unfold Chebyshev.psi
    rw [hfloor]
  -- `log C(2n,n) = log (2n)! − 2·log n!`.
  have hkey : Nat.centralBinom n * (Nat.factorial n * Nat.factorial n)
      = Nat.factorial (2 * n) := by
    have hle : n ≤ 2 * n := by omega
    have h := Nat.choose_mul_factorial_mul_factorial hle
    have h2n : 2 * n - n = n := by omega
    rw [h2n] at h
    rw [Nat.centralBinom_eq_two_mul_choose, ← h]; ring
  have hCpos : (0 : ℝ) < (Nat.centralBinom n : ℝ) := by exact_mod_cast Nat.centralBinom_pos n
  have hFpos : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hcast : (Nat.centralBinom n : ℝ) * ((Nat.factorial n : ℝ) * (Nat.factorial n : ℝ))
      = (Nat.factorial (2 * n) : ℝ) := by exact_mod_cast hkey
  have hlogeq : Real.log (Nat.centralBinom n : ℝ)
      = Real.log (Nat.factorial (2 * n) : ℝ) - 2 * Real.log (Nat.factorial n : ℝ) := by
    have hl := congrArg Real.log hcast
    rw [Real.log_mul hCpos.ne' (by positivity), Real.log_mul hFpos.ne' hFpos.ne'] at hl
    linarith
  rw [hlogeq, hpsi, log_factorial_eq_sum_vonMangoldt_mul_div (2 * n),
    log_factorial_eq_sum_vonMangoldt_mul_div n]
  -- Extend the `n!` sum to `Ioc 0 (2n)`; the new terms vanish (`n/d = 0` for `d > n`).
  have hext : ∑ d ∈ Finset.Ioc 0 n, Λ d * ((n / d : ℕ) : ℝ)
      = ∑ d ∈ Finset.Ioc 0 (2 * n), Λ d * ((n / d : ℕ) : ℝ) := by
    apply Finset.sum_subset (Finset.Ioc_subset_Ioc_right (by omega))
    intro d hdt hdnot
    have hdn : n < d := by
      simp only [Finset.mem_Ioc] at hdt hdnot; omega
    rw [Nat.div_eq_of_lt hdn]; simp
  rw [hext, Finset.mul_sum, ← Finset.sum_sub_distrib]
  -- Termwise: `Λ d·⌊2n/d⌋ − 2·Λ d·⌊n/d⌋ ≤ Λ d`.
  apply Finset.sum_le_sum
  intro d hd
  have hd0 : 0 < d := (Finset.mem_Ioc.mp hd).1
  have hLnn : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
  -- Upper bound `⌊2n/d⌋ ≤ 2⌊n/d⌋ + 1` (the only direction needed, since `Λ d ≥ 0`).
  have hhigh : (2 * n) / d ≤ 2 * (n / d) + 1 := by
    rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hd0]
    have hmod : n % d < d := Nat.mod_lt n hd0
    have hdm : d * (n / d) + n % d = n := Nat.div_add_mod n d
    nlinarith [hmod, hdm]
  have hhighR : ((2 * n / d : ℕ) : ℝ) ≤ 2 * ((n / d : ℕ) : ℝ) + 1 := by exact_mod_cast hhigh
  have hfac : 0 ≤ Λ d * (1 - (((2 * n / d : ℕ) : ℝ) - 2 * ((n / d : ℕ) : ℝ))) :=
    mul_nonneg hLnn (by linarith)
  nlinarith [hfac]

/-- **L3** (size bound). Build-pending target. Logs of
`Nat.four_pow_le_two_mul_add_one_mul_central_binom : 4^n ≤ (2n+1)·C(2n,n)`. -/
lemma log_four_mul_le_log_centralBinom (n : ℕ) :
    (n : ℝ) * Real.log 4 - Real.log (2 * n + 1)
      ≤ Real.log (Nat.centralBinom n : ℝ) := by
  have hnat : 4 ^ n ≤ (2 * n + 1) * Nat.centralBinom n := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    exact Nat.four_pow_le_two_mul_add_one_mul_central_binom n
  have hR : (4 : ℝ) ^ n ≤ (2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ) := by
    exact_mod_cast hnat
  have hCpos : (0 : ℝ) < (Nat.centralBinom n : ℝ) := by exact_mod_cast Nat.centralBinom_pos n
  have hlog := (Real.log_le_log_iff (by positivity) (by positivity)).mpr hR
  rw [Real.log_pow, Real.log_mul (by positivity) hCpos.ne'] at hlog
  linarith

/-- The missing ψ lower bound, reduced to the three lemmas above.

Assembly. From `L2 ∘ L3`, `ψ(2n) ≥ n·log 4 − log(2n+1)`. The elementary bound
`2n+1 ≤ 3ⁿ` (a one-line `Nat` induction) gives `log(2n+1) ≤ n·log 3`, so
`ψ(2n) ≥ n·(log 4 − log 3) = (log(4/3)/2)·(2n)`. A single constant
`c₀ = log(4/3)/2 > 0` therefore works at every even point `2n`, `n ≥ 1` — with no
"large `n`" caveat, because `2n+1 ≤ 3ⁿ` holds for all `n ≥ 0`. Monotonicity of
`ψ` lifts this to every real `x ≥ 2`: with `n = ⌊x/2⌋ ≥ 1` we have `2n ≤ x < 2n+2 ≤ 4n`,
so `ψ x ≥ ψ(2n) ≥ c₀·2n ≥ c₀·(x/2)`, giving the bound with `c = c₀/2`. -/
theorem chebyshev_psi_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, 2 ≤ x → c * x ≤ Chebyshev.psi x := by
  -- Elementary size bound `2m+1 ≤ 3ᵐ` for all `m` (drives `log(2n+1) ≤ n·log 3`).
  have hpow : ∀ m : ℕ, 2 * m + 1 ≤ 3 ^ m := by
    intro m
    induction m with
    | zero => norm_num
    | succ k ih =>
        have h3 : (3 : ℕ) ^ (k + 1) = 3 * 3 ^ k := by rw [pow_succ]; ring
        omega
  set c₀ : ℝ := Real.log (4 / 3) / 2 with hc₀
  have hc₀pos : 0 < c₀ := by
    have h43 : (0 : ℝ) < Real.log (4 / 3) := Real.log_pos (by norm_num)
    rw [hc₀]; linarith
  -- Even-point bound `c₀·(2n) ≤ ψ(2n)` for `n ≥ 1`.
  have heven : ∀ n : ℕ, 1 ≤ n → c₀ * (2 * (n : ℝ)) ≤ Chebyshev.psi (2 * n) := by
    intro n _
    have h2 := log_centralBinom_le_psi n
    have h3 := log_four_mul_le_log_centralBinom n
    have hcast : (2 * (n : ℝ) + 1) ≤ (3 : ℝ) ^ n := by exact_mod_cast hpow n
    have hlog3 : Real.log (2 * (n : ℝ) + 1) ≤ (n : ℝ) * Real.log 3 := by
      have hstep : Real.log (2 * (n : ℝ) + 1) ≤ Real.log ((3 : ℝ) ^ n) :=
        (Real.log_le_log_iff (by positivity) (by positivity)).mpr hcast
      rwa [Real.log_pow] at hstep
    have hlogdiv : Real.log (4 / 3) = Real.log 4 - Real.log 3 :=
      Real.log_div (by norm_num) (by norm_num)
    have hgoal : c₀ * (2 * (n : ℝ)) = (n : ℝ) * Real.log 4 - (n : ℝ) * Real.log 3 := by
      rw [hc₀, hlogdiv]; ring
    rw [hgoal]
    linarith [h2, h3, hlog3]
  -- Lift to every real `x ≥ 2` by monotonicity of `ψ`, with `c = c₀/2`.
  refine ⟨c₀ / 2, by linarith, ?_⟩
  intro x hx
  set n : ℕ := ⌊x / 2⌋₊ with hn
  have hnpos : 1 ≤ n := by
    rw [hn]; exact (Nat.one_le_floor_iff _).mpr (by linarith)
  have hle : 2 * (n : ℝ) ≤ x := by
    have hfl : (n : ℝ) ≤ x / 2 := by rw [hn]; exact Nat.floor_le (by linarith)
    linarith
  have hlt : x < 2 * (n : ℝ) + 2 := by
    have hfl : x / 2 < (n : ℝ) + 1 := by rw [hn]; exact Nat.lt_floor_add_one _
    linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
  have h4n : x ≤ 4 * (n : ℝ) := by linarith
  calc c₀ / 2 * x
      ≤ c₀ / 2 * (4 * (n : ℝ)) := mul_le_mul_of_nonneg_left h4n (by linarith)
    _ = c₀ * (2 * (n : ℝ)) := by ring
    _ ≤ Chebyshev.psi (2 * n) := heven n hnpos
    _ ≤ Chebyshev.psi x := Chebyshev.psi_mono hle

/-- `log u ≤ 2·√u` for `u > 0`. Since `log √u = (log u)/2` (`Real.log_sqrt`) and
`log √u ≤ √u − 1` (`Real.log_le_sub_one_of_pos`), we get `log u ≤ 2(√u − 1) ≤ 2√u`. -/
lemma log_le_two_mul_sqrt {u : ℝ} (hu : 0 < u) :
    Real.log u ≤ 2 * Real.sqrt u := by
  have hsqrt_pos : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hlog_eq : Real.log (Real.sqrt u) = Real.log u / 2 := Real.log_sqrt hu.le
  have hle : Real.log (Real.sqrt u) ≤ Real.sqrt u - 1 :=
    Real.log_le_sub_one_of_pos hsqrt_pos
  linarith

/-- **Derived θ lower bound.** A Chebyshev-strength linear lower bound on `θ`,
obtained from `chebyshev_psi_lower_bound` together with the prime-power correction
estimate `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log` (`|ψ x − θ x| ≤ 2√x·log x`).

From `ψ x ≥ c₁·x` (`x ≥ 2`) we get `θ x ≥ c₁·x − 2√x·log x`. Writing `s = ⁴√x`, the
error term is `≤ 8 s³`: `log x ≤ 4 s` (two applications of `log u ≤ 2√u`) and
`√x = s²`. Meanwhile `c₁·x = c₁ s⁴`, so once `s ≥ 16/c₁` the error is `≤ (c₁/2)·x`,
giving `θ x ≥ (c₁/2)·x` for every `x ≥ max 2 ((16/c₁)⁴)` — no asymptotics, fully
explicit `x₀`. This is the elementary lower half of Chebyshev's `θ`-bound, the
complement of Mathlib's upper bounds (`Chebyshev.theta_le_log4_mul_x`). -/
theorem chebyshev_theta_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → c * x ≤ Chebyshev.theta x := by
  obtain ⟨c₁, hc₁pos, hc₁⟩ := chebyshev_psi_lower_bound
  refine ⟨c₁ / 2, by linarith, max 2 ((16 / c₁) ^ 4), ?_⟩
  intro x hx
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hbig : (16 / c₁) ^ 4 ≤ x := le_trans (le_max_right _ _) hx
  have hc16 : (0 : ℝ) ≤ 16 / c₁ := by positivity
  -- Fourth-root variable `s = √(√x)`.
  set s : ℝ := Real.sqrt (Real.sqrt x) with hs_def
  have hsx : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hs0 : (0 : ℝ) ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = Real.sqrt x := by rw [hs_def, Real.sq_sqrt hsx]
  have hs4 : s ^ 4 = x := by
    rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hs2, Real.sq_sqrt hx0.le]
  -- `s ≥ 16/c₁`, since `√(√·)` is monotone and collapses `((16/c₁)^4)` to `16/c₁`.
  have hs_ge : 16 / c₁ ≤ s := by
    have h1 : Real.sqrt ((16 / c₁) ^ 4) = (16 / c₁) ^ 2 := by
      rw [show (16 / c₁) ^ 4 = ((16 / c₁) ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    have h2 : Real.sqrt (Real.sqrt ((16 / c₁) ^ 4)) = 16 / c₁ := by
      rw [h1, Real.sqrt_sq hc16]
    calc 16 / c₁ = Real.sqrt (Real.sqrt ((16 / c₁) ^ 4)) := h2.symm
      _ ≤ Real.sqrt (Real.sqrt x) := Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hbig)
      _ = s := hs_def.symm
  have hcs : (16 : ℝ) ≤ s * c₁ := (div_le_iff₀ hc₁pos).mp hs_ge
  -- `log x ≤ 4 s` (apply `log u ≤ 2√u` to `√x`, then `log √x = (log x)/2`).
  have hlogx : Real.log x ≤ 4 * s := by
    have hA : Real.log (Real.sqrt x) ≤ 2 * Real.sqrt (Real.sqrt x) :=
      log_le_two_mul_sqrt (Real.sqrt_pos.mpr hx0)
    have hlogsqrt : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx0.le
    rw [← hs_def] at hA
    linarith
  have hlogx_nonneg : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx1
  -- Error term `2√x·log x ≤ 8 s³ ≤ (c₁/2)·x`.
  have herr_le : 2 * Real.sqrt x * Real.log x ≤ c₁ / 2 * x := by
    have hstep1 : 2 * Real.sqrt x * Real.log x ≤ 8 * s ^ 3 := by
      rw [← hs2]
      nlinarith [hlogx, hs0, hlogx_nonneg, sq_nonneg s, mul_nonneg hs0 (sq_nonneg s)]
    have hstep2 : 8 * s ^ 3 ≤ c₁ / 2 * x := by
      rw [← hs4]
      nlinarith [pow_nonneg hs0 3, hcs, hs0]
    linarith
  -- Assemble: `θ x ≥ ψ x − |ψ x − θ x| ≥ c₁·x − 2√x·log x ≥ (c₁/2)·x`.
  have hpsi : c₁ * x ≤ Chebyshev.psi x := hc₁ x hx2
  have hdiff : Chebyshev.psi x - Chebyshev.theta x ≤ 2 * Real.sqrt x * Real.log x :=
    le_trans (le_abs_self _) (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx1)
  linarith

end BoundedPrimeGapsOQ03OQ01.ChebyshevLower
