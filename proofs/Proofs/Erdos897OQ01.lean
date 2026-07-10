/-
  Erdős Problem #897 — OQ-01 (Part I): Non-Vacuity, Selectivity, and a
  Strongly-Additive Reduction

  Companion to `Erdos897Problem.lean`. Part I of Erdős #897 asks: if `f` is
  additive with `limsup_{p,k} f(p^k)/log(p^k) = ∞`, must
  `limsup_n (f(n+1)-f(n))/log n = ∞`?  The forward implication is OPEN and is
  **not** asserted here. This file supplies the verified surrounding theory that
  any analysis of Part I needs:

  (1) **Non-vacuity.** The hypothesis `UnboundedOnPrimePowers` is satisfiable:
      `logSqWeight n = ∑_{p ∣ n} (log p)²` is additive — in fact strongly
      additive — and grows faster than `log` on prime powers. So Part I is not
      vacuously true.
  (2) **Selectivity.** The parent file's flagship additive functions `log` and
      `ω` both FAIL the hypothesis (`log` sits exactly at the boundary,
      `ω` is bounded on prime powers). The hypothesis therefore isolates functions
      growing strictly faster than `log` on prime powers.
  (3) The hypothesis forces plain unboundedness of `f` on prime powers, and is a
      **positive cone**: closed under positive scaling (`unboundedOnPrimePowers_smul`)
      and under adding a function nonnegative on prime powers
      (`unboundedOnPrimePowers_add_nonneg`).
  (4) **Strongly-additive reduction.** For strongly additive `f` the hypothesis
      collapses to `f(p)/log p` unbounded over primes — the counterpart of the
      parent file's completely-additive reduction. The cancellation differs: the
      value is constant in `k`, so the binding case is `k = 1`, and the `M < 0`
      branch is handled by invoking the hypothesis at `0`.
  (5) **Lattice structure.** The hypothesis cuts the pointwise order into a
      sup-closed **filter** (the "large" functions, closed under `max` with
      anything — `unboundedOnPrimePowers_max_left`) and a complementary sup-closed
      **ideal** (the `O(log)`-on-prime-powers functions, closed under `max` of two
      — `not_unboundedOnPrimePowers_max`).

  Verified, 0 axioms, 0 sorries, no `native_decide`.
-/

import Proofs.Erdos897Problem

namespace Erdos897

open Finset

/-
## (1) Non-vacuity: an explicit witness satisfying the hypothesis

`logSqWeight n = ∑_{p ∈ primeFactors n} (log p)²`. On a prime power `p^k` (k ≥ 1)
its value is `(log p)²`, independent of `k`, while `log(p^k) = k·log p`. Choosing a
large prime makes `(log p)² / log(p^k) = log p / k` as large as we like at `k = 1`,
so the function is unbounded on prime powers relative to `log`.
-/

/-- The additive weight `logSqWeight n = ∑_{p ∣ n} (log p)²`, our witness that the
Erdős #897 hypothesis `UnboundedOnPrimePowers` is non-vacuous. -/
noncomputable def logSqWeight (n : ℕ) : ℝ :=
  ∑ p ∈ n.primeFactors, (Real.log p) ^ 2

/-- On a prime power the sum collapses to the single prime: `logSqWeight p = (log p)²`. -/
theorem logSqWeight_prime {p : ℕ} (hp : p.Prime) :
    logSqWeight p = (Real.log p) ^ 2 := by
  simp only [logSqWeight, hp.primeFactors, Finset.sum_singleton]

/-- `logSqWeight` is additive: prime supports of coprime numbers are disjoint, so the
defining sum splits over a coprime product. -/
theorem logSqWeight_additive : IsAdditive logSqWeight := by
  intro a b ha hb hab
  simp only [logSqWeight]
  rw [Nat.primeFactors_mul ha.ne' hb.ne',
      Finset.sum_union hab.disjoint_primeFactors]

/-- `logSqWeight` is in fact **strongly additive**: `logSqWeight (p^k) = logSqWeight p`
for every prime `p` and `k ≥ 1`, since `(p^k).primeFactors = p.primeFactors`. -/
theorem logSqWeight_stronglyAdditive : IsStronglyAdditive logSqWeight := by
  refine ⟨logSqWeight_additive, ?_⟩
  intro p k hp hk
  simp only [logSqWeight]
  rw [Nat.primeFactors_pow p (by omega : k ≠ 0)]

/-- `logSqWeight` satisfies the Erdős #897 hypothesis: it is unbounded on prime powers
relative to `log`. At `k = 1` we have `logSqWeight p = (log p)²` versus `log p`, and a
sufficiently large prime makes `(log p)² > M·log p` for any target `M`. -/
theorem logSqWeight_unboundedOnPrimePowers : UnboundedOnPrimePowers logSqWeight := by
  intro M
  -- Pick a prime `p` with `log p > M` by going past `exp M`.
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (⌈Real.exp M⌉₊ + 1)
  refine ⟨p, 1, hp, le_refl 1, ?_⟩
  have hlogpos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlogM : M < Real.log p := by
    have hexp_lt : Real.exp M < (p : ℝ) := by
      have hceil : Real.exp M ≤ (⌈Real.exp M⌉₊ : ℝ) := Nat.le_ceil _
      have hNp : ((⌈Real.exp M⌉₊ + 1 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpN
      push_cast at hNp
      linarith
    have := Real.log_lt_log (Real.exp_pos M) hexp_lt
    rwa [Real.log_exp] at this
  simp only [pow_one]
  rw [logSqWeight_prime hp]
  -- goal: `(log p)² > M * log p`; both factors of `(log p)(log p - M)` are positive.
  nlinarith [mul_pos hlogpos (sub_pos.mpr hlogM)]

/-- **Non-vacuity (headline).** There exists an additive function satisfying the
Erdős #897 hypothesis, so Part I is not vacuously true. Witness: `logSqWeight`. -/
theorem exists_additive_unboundedOnPrimePowers :
    ∃ f : ℕ → ℝ, IsAdditive f ∧ UnboundedOnPrimePowers f :=
  ⟨logSqWeight, logSqWeight_additive, logSqWeight_unboundedOnPrimePowers⟩

/-
## (2) Selectivity: the classical examples fail the hypothesis

`log` sits exactly at the boundary (`log(p^k)/log(p^k) = 1`) and `ω` is bounded on
prime powers (`ω(p^k) = 1`). Neither is unbounded relative to `log`, so the
hypothesis genuinely restricts to functions growing *strictly* faster than `log`.
-/

/-- **Selectivity for `log`.** The logarithm does not satisfy the hypothesis:
`logN(p^k) = log(p^k)` exactly, so it never exceeds `1 · log(p^k)`. -/
theorem not_unboundedOnPrimePowers_logN : ¬ UnboundedOnPrimePowers logN := by
  intro h
  obtain ⟨p, k, _hp, _hk, hlt⟩ := h 1
  simp only [logN, one_mul, Nat.cast_pow] at hlt
  exact lt_irrefl _ hlt

/-- **Selectivity for `ω`.** The distinct-prime-factor count is bounded (`ω(p^k) = 1`)
on prime powers, so it cannot outgrow `log`: with `M = 2/log 2` the required
inequality `ω(p^k) > M·log(p^k)` would force `1 > 2`. -/
theorem not_unboundedOnPrimePowers_omega : ¬ UnboundedOnPrimePowers omega := by
  intro h
  obtain ⟨p, k, hp, hk, hlt⟩ := h (2 / Real.log 2)
  have homega : omega (p ^ k) = 1 := by
    simp only [omega]
    rw [Nat.primeFactors_pow p (by omega : k ≠ 0), hp.primeFactors, Finset.card_singleton]
    norm_num
  rw [homega] at hlt
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpk2 : (2 : ℝ) ≤ (p : ℝ) ^ k := by
    have hle : 2 ≤ p ^ k := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    calc (2 : ℝ) ≤ ((p ^ k : ℕ) : ℝ) := by exact_mod_cast hle
      _ = (p : ℝ) ^ k := by push_cast; ring
  have hloglb : Real.log 2 ≤ Real.log ((p : ℝ) ^ k) := Real.log_le_log (by norm_num) hpk2
  have hcnn : (0 : ℝ) ≤ 2 / Real.log 2 := by positivity
  have hmul : (2 / Real.log 2) * Real.log 2 ≤ (2 / Real.log 2) * Real.log ((p : ℝ) ^ k) :=
    mul_le_mul_of_nonneg_left hloglb hcnn
  have hval : (2 / Real.log 2) * Real.log 2 = 2 := by field_simp
  linarith

/-
## (3) The hypothesis forces plain unboundedness on prime powers
-/

/-- If `f` is unbounded on prime powers relative to `log`, then `f` is plainly
unbounded on prime powers: for every `B` some `f(p^k)` exceeds `B`. The uniform
lower bound `log(p^k) ≥ log 2 > 0` lets us dial the multiplier against `B`. -/
theorem unboundedOnPrimePowers_unbounded {f : ℕ → ℝ}
    (hf : UnboundedOnPrimePowers f) :
    ∀ B : ℝ, ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ f (p ^ k) > B := by
  intro B
  set M := (|B| + 1) / Real.log 2 with hMdef
  obtain ⟨p, k, hp, hk, hpk⟩ := hf M
  refine ⟨p, k, hp, hk, ?_⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hMnn : 0 ≤ M := by rw [hMdef]; positivity
  have hpk2 : (2 : ℝ) ≤ (p : ℝ) ^ k := by
    have hle : 2 ≤ p ^ k := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    calc (2 : ℝ) ≤ ((p ^ k : ℕ) : ℝ) := by exact_mod_cast hle
      _ = (p : ℝ) ^ k := by push_cast; ring
  have hloglb : Real.log 2 ≤ Real.log ((p : ℝ) ^ k) := Real.log_le_log (by norm_num) hpk2
  have hchain : M * Real.log 2 ≤ M * Real.log ((p : ℝ) ^ k) :=
    mul_le_mul_of_nonneg_left hloglb hMnn
  have hval : M * Real.log 2 = |B| + 1 := by rw [hMdef]; field_simp
  have hBlt : B < |B| + 1 := by nlinarith [abs_nonneg B, le_abs_self B]
  calc B < |B| + 1 := hBlt
    _ = M * Real.log 2 := hval.symm
    _ ≤ M * Real.log ((p : ℝ) ^ k) := hchain
    _ < f (p ^ k) := hpk

/-
## Closure properties of the hypothesis class

`UnboundedOnPrimePowers` is a *positive cone*: it is preserved by scaling with a
positive constant and by adding any function that is nonnegative on prime powers.
Together these say the hypothesis is robust — e.g. the witnesses `logSqWeight` and
`bigOmega` can be positively combined and still satisfy it — and let one normalize
a witness (`c = 1`) without loss of generality.
-/

/-- **Closure under positive scaling.** If `f` is unbounded on prime powers relative
to `log`, so is `c • f` for any `c > 0`: apply the hypothesis at the shifted
multiplier `M / c` and scale the resulting strict inequality by `c`. -/
theorem unboundedOnPrimePowers_smul {f : ℕ → ℝ} (hf : UnboundedOnPrimePowers f)
    {c : ℝ} (hc : 0 < c) : UnboundedOnPrimePowers (fun n => c * f n) := by
  intro M
  obtain ⟨p, k, hp, hk, hgt⟩ := hf (M / c)
  refine ⟨p, k, hp, hk, ?_⟩
  show c * f (p ^ k) > M * Real.log (p ^ k)
  have hstep : c * ((M / c) * Real.log (p ^ k)) < c * f (p ^ k) :=
    mul_lt_mul_of_pos_left hgt hc
  have heq : c * ((M / c) * Real.log (p ^ k)) = M * Real.log (p ^ k) := by
    have hc0 : c ≠ 0 := ne_of_gt hc
    field_simp
  rwa [heq] at hstep

/-- **Closure under adding a function nonnegative on prime powers.** If `f` is
unbounded on prime powers and `g` is `≥ 0` at every prime power, then `f + g` is
still unbounded on prime powers: the witness `(p, k)` for `f` works for `f + g`
because `g (p ^ k) ≥ 0` only helps the strict inequality.  (Taking `g = bigOmega`
or `g = logSqWeight`, both nonnegative, keeps any witness in the class.) -/
theorem unboundedOnPrimePowers_add_nonneg {f g : ℕ → ℝ}
    (hf : UnboundedOnPrimePowers f)
    (hg : ∀ p k : ℕ, p.Prime → 1 ≤ k → 0 ≤ g (p ^ k)) :
    UnboundedOnPrimePowers (fun n => f n + g n) := by
  intro M
  obtain ⟨p, k, hp, hk, hgt⟩ := hf M
  refine ⟨p, k, hp, hk, ?_⟩
  show f (p ^ k) + g (p ^ k) > M * Real.log (p ^ k)
  have hgnn := hg p k hp hk
  linarith

/-
## (4) A strongly-additive reduction

For strongly additive `f`, `f(p^k) = f(p)` is constant in `k`, so the prime-power
hypothesis reduces to a statement about primes alone — the strongly-additive
counterpart of `completelyAdditive_unboundedOnPrimePowers_iff`.
-/

/-- **Reduction theorem (strongly additive).** For strongly additive `f`, the Erdős
#897 hypothesis is equivalent to `f(p)/log p` being unbounded over the primes.

Forward: since `f(p^k) = f(p)` the multiplier `k` appears only through
`log(p^k) = k·log p`; for `M ≥ 0` we drop the extra factor `k ≥ 1` (both `M` and
`log p` are nonnegative), and for `M < 0` we instead invoke the hypothesis at `0`
(then `f(p) > 0 ≥ M·log p`). Reverse: take `k = 1`. -/
theorem stronglyAdditive_unboundedOnPrimePowers_iff {f : ℕ → ℝ}
    (hf : IsStronglyAdditive f) :
    UnboundedOnPrimePowers f ↔
      ∀ M : ℝ, ∃ p : ℕ, p.Prime ∧ f p > M * Real.log p := by
  constructor
  · intro h M
    by_cases hM : 0 ≤ M
    · obtain ⟨p, k, hp, hk, hpk⟩ := h M
      refine ⟨p, hp, ?_⟩
      have hfp : f (p ^ k) = f p := hf.2 p k hp hk
      have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      rw [hfp, Real.log_pow] at hpk
      -- hpk : f p > M * (↑k * log p); drop the factor k ≥ 1.
      have hdrop : M * Real.log p ≤ M * ((k : ℝ) * Real.log p) := by
        nlinarith [mul_nonneg (mul_nonneg hM (by linarith : (0 : ℝ) ≤ (k : ℝ) - 1)) hlogp]
      linarith
    · push_neg at hM
      obtain ⟨p, k, hp, hk, hpk⟩ := h 0
      refine ⟨p, hp, ?_⟩
      have hfp : f (p ^ k) = f p := hf.2 p k hp hk
      rw [hfp, zero_mul] at hpk
      have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
      have hnp : M * Real.log p ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hM.le hlogp.le
      linarith
  · intro h M
    obtain ⟨p, hp, hpp⟩ := h M
    refine ⟨p, 1, hp, le_refl 1, ?_⟩
    have hfp : f (p ^ 1) = f p := hf.2 p 1 hp (le_refl 1)
    rw [hfp, pow_one]
    exact hpp

/-
## (5) The converse of (3) fails: `Ω` separates "plainly unbounded" from the hypothesis

Theorem (3) shows the Erdős #897 hypothesis forces plain unboundedness on prime powers.
The converse is **false**, and `Ω` (`bigOmega`) is the witness. `Ω` is completely
additive with `Ω(p^k) = k`, so `Ω(2^k) = k → ∞` — it is plainly unbounded on prime
powers. Yet it FAILS the normalized hypothesis: `Ω(p) = 1` for every prime while
`log p ≥ log 2`, so via the completely-additive reduction the hypothesis would demand
`1 > M·log p` at every `M`, which fails already at `M = 1/log 2`. Hence "unbounded on
prime powers" is strictly weaker than the #897 hypothesis "unbounded relative to `log`".
-/

/-- `Ω(p) = 1` for a prime `p`: its factor list with multiplicity is `[p]`. -/
theorem bigOmega_prime {p : ℕ} (hp : p.Prime) : bigOmega p = 1 := by
  simp [bigOmega, Nat.primeFactorsList_prime hp]

/-- **Selectivity for `Ω`.** The total-prime-factor count fails the hypothesis. Via the
completely-additive reduction it would require some prime with `Ω(p) = 1 > M·log p` for
every `M`; at `M = 1/log 2` this forces `log p < log 2`, impossible for a prime `p ≥ 2`. -/
theorem not_unboundedOnPrimePowers_bigOmega : ¬ UnboundedOnPrimePowers bigOmega := by
  rw [completelyAdditive_unboundedOnPrimePowers_iff bigOmega bigOmega_completelyAdditive]
  push_neg
  refine ⟨1 / Real.log 2, ?_⟩
  intro p hp
  rw [bigOmega_prime hp]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogp : Real.log 2 ≤ Real.log p :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
  have hnn : (0 : ℝ) ≤ 1 / Real.log 2 := by positivity
  have hmul : (1 / Real.log 2) * Real.log 2 ≤ (1 / Real.log 2) * Real.log p :=
    mul_le_mul_of_nonneg_left hlogp hnn
  have hinv : (1 / Real.log 2) * Real.log 2 = 1 := by field_simp
  linarith

/-- `Ω` is nonetheless **plainly** unbounded on prime powers: `Ω(2^k) = k` exceeds any
bound. Sharp complement to `not_unboundedOnPrimePowers_bigOmega`. -/
theorem bigOmega_unbounded_on_primePowers :
    ∀ B : ℝ, ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ bigOmega (p ^ k) > B := by
  intro B
  refine ⟨2, ⌈B⌉₊ + 1, Nat.prime_two, by omega, ?_⟩
  have hval : bigOmega (2 ^ (⌈B⌉₊ + 1)) = ((⌈B⌉₊ + 1 : ℕ) : ℝ) := by
    rw [bigOmega_completelyAdditive.2 2 (⌈B⌉₊ + 1) Nat.prime_two, bigOmega_prime Nat.prime_two]
    ring
  rw [hval]
  have hceil : B ≤ (⌈B⌉₊ : ℝ) := Nat.le_ceil B
  push_cast
  linarith

/-- **The converse of (3) is false (headline).** There is an additive function that is
plainly unbounded on prime powers yet fails the Erdős #897 hypothesis, so the two
notions of unboundedness are genuinely distinct. Witness: `Ω = bigOmega`. -/
theorem unbounded_not_implies_unboundedOnPrimePowers :
    ∃ f : ℕ → ℝ, IsAdditive f ∧
      (∀ B : ℝ, ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ f (p ^ k) > B) ∧
      ¬ UnboundedOnPrimePowers f :=
  ⟨bigOmega, bigOmega_completelyAdditive.1, bigOmega_unbounded_on_primePowers,
    not_unboundedOnPrimePowers_bigOmega⟩

/-
## (6) The master domination lemma and a cone of witnesses

`UnboundedOnPrimePowers` is a *largeness* condition, hence upward closed: if `f`
satisfies it and `g` dominates `f` on prime powers (`g(p^k) ≥ f(p^k)`), then `g`
satisfies it too — the same witnesses `(p,k)` work verbatim, since the comparison
value `M·log(p^k)` does not depend on the function. This single lemma is the
common source of the various closure properties of the class (positive scaling,
adding a prime-power-nonnegative function); it also turns the single witness
`logSqWeight` of (1) into an entire *cone* of witnesses: any `g ≥ logSqWeight` on
prime powers is a satisfier.
-/

/-- **Domination lemma.** If `f` is unbounded on prime powers relative to `log` and
`g(p^k) ≥ f(p^k)` for every prime power, then `g` is unbounded on prime powers too.
The comparison value `M·log(p^k)` is independent of the function, so the same
witness `(p,k)` transfers. -/
theorem unboundedOnPrimePowers_of_ge {f g : ℕ → ℝ}
    (hf : UnboundedOnPrimePowers f)
    (hdom : ∀ p k : ℕ, p.Prime → 1 ≤ k → f (p ^ k) ≤ g (p ^ k)) :
    UnboundedOnPrimePowers g := by
  intro M
  obtain ⟨p, k, hp, hk, hpk⟩ := hf M
  exact ⟨p, k, hp, hk, lt_of_lt_of_le hpk (hdom p k hp hk)⟩

/-- **A cone of witnesses.** Any function dominating `logSqWeight` on prime powers
satisfies the Erdős #897 hypothesis. So non-vacuity (1) is not an isolated accident:
the hypothesis holds for a whole family of functions, not just `logSqWeight`. -/
theorem unboundedOnPrimePowers_of_ge_logSqWeight {g : ℕ → ℝ}
    (hg : ∀ p k : ℕ, p.Prime → 1 ≤ k → logSqWeight (p ^ k) ≤ g (p ^ k)) :
    UnboundedOnPrimePowers g :=
  unboundedOnPrimePowers_of_ge logSqWeight_unboundedOnPrimePowers hg

/-
## (7) Structural properties of the witness `logSqWeight`

Beyond additivity and unboundedness, `logSqWeight` is a *prime-support functional*: a
sum of nonnegative terms indexed by the prime divisors of `n`. That shape alone forces
four structural facts — nonnegativity, determination by the prime support, monotonicity
under divisibility, and an exact zero-set `{0, 1}` — which together explain why it is the
natural *minimal* witness: every larger prime-support functional dominates it, feeding the
cone of (6).
-/

/-- `logSqWeight` is nonnegative — it is a sum of squares. -/
theorem logSqWeight_nonneg (n : ℕ) : 0 ≤ logSqWeight n :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- **Prime-support determination.** `logSqWeight` depends only on the *set* of prime
divisors: numbers with equal prime support have equal weight.  This is the structural
root of strong additivity (`logSqWeight (p^k) = logSqWeight p`, since `p^k` and `p`
share the prime support `{p}`). -/
theorem logSqWeight_eq_of_primeFactors_eq {m n : ℕ}
    (h : m.primeFactors = n.primeFactors) : logSqWeight m = logSqWeight n := by
  simp only [logSqWeight, h]

/-- **Monotonicity under divisibility.** If `m ∣ n` (with `n ≠ 0`) then
`logSqWeight m ≤ logSqWeight n`: passing to a multiple only enlarges the prime support,
and every term `(log p)²` is nonnegative. -/
theorem logSqWeight_mono_of_dvd {m n : ℕ} (hn : n ≠ 0) (hmn : m ∣ n) :
    logSqWeight m ≤ logSqWeight n :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (Nat.primeFactors_mono hmn hn) (fun _ _ _ => sq_nonneg _)

/-- **Exact zero-set.** `logSqWeight n = 0` iff `n` has no prime divisors, i.e. `n ∈ {0, 1}`.
Every prime `p` contributes a strictly positive `(log p)²`, so any `n ≥ 2` has positive
weight.  Combined with monotonicity this pins `logSqWeight` to the boundary of the positive
cone: it is zero exactly on the units and grows off them. -/
theorem logSqWeight_eq_zero_iff (n : ℕ) : logSqWeight n = 0 ↔ n = 0 ∨ n = 1 := by
  rw [← Nat.primeFactors_eq_empty]
  constructor
  · intro h
    by_contra hne
    obtain ⟨p, hp⟩ := Finset.nonempty_of_ne_empty hne
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hlogpos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hpp.one_lt)
    have hterm : 0 < (Real.log p) ^ 2 := pow_pos hlogpos 2
    have hz : (Real.log p) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => sq_nonneg _)).mp h p hp
    exact absurd hz (ne_of_gt hterm)
  · intro h
    simp only [logSqWeight, h, Finset.sum_empty]

/-
## (8) The dual boundary: anti-domination and the `O(log)` selectivity criterion

Section (6)'s domination lemma (`unboundedOnPrimePowers_of_ge`) expresses that the
hypothesis is a *largeness* condition — upward closed under domination on prime powers.
The dual completes the picture from below: largeness fails downward.  If `f` is
dominated on prime powers by a function that FAILS the hypothesis, then `f` fails too.
The concrete boundary is `O(log)`: any `f` with `f(p^k) ≤ C·log(p^k)` on prime powers
fails, for *every* constant `C`.  This single criterion subsumes the two ad-hoc
selectivity results of (2): `logN` (`not_unboundedOnPrimePowers_logN`, the case `C = 1`,
equality) and `ω` (`not_unboundedOnPrimePowers_omega`, the case `C = 1/log 2`, since
`ω(p^k) = 1 ≤ (1/log 2)·log(p^k)` because `log(p^k) ≥ log 2`).
-/

/-- **Anti-domination lemma (dual of `unboundedOnPrimePowers_of_ge`).**  If `g` fails the
Erdős #897 hypothesis and `f(p^k) ≤ g(p^k)` on every prime power, then `f` fails it too.
This is the exact contrapositive of the domination lemma: largeness transfers *upward*
under domination, so failure of largeness transfers *downward*.  Together the two lemmas
say the hypothesis class is an up-set in the prime-power domination order. -/
theorem not_unboundedOnPrimePowers_of_le {f g : ℕ → ℝ}
    (hg : ¬ UnboundedOnPrimePowers g)
    (hdom : ∀ p k : ℕ, p.Prime → 1 ≤ k → f (p ^ k) ≤ g (p ^ k)) :
    ¬ UnboundedOnPrimePowers f :=
  fun hf => hg (unboundedOnPrimePowers_of_ge hf hdom)

/-- **The `O(log)` selectivity criterion.**  If `f(p^k) ≤ C·log(p^k)` on every prime power
(for a fixed constant `C`), then `f` fails the Erdős #897 hypothesis.  Proof: evaluating
the hypothesis at the multiplier `M = C` would produce a prime power with
`f(p^k) > C·log(p^k)`, directly contradicting the bound.  This pins down the exact
boundary of the hypothesis — growth strictly faster than every constant multiple of `log`
on prime powers — and subsumes the selectivity of both `logN` (`C = 1`) and `ω`
(`C = 1/log 2`). -/
theorem not_unboundedOnPrimePowers_of_le_const_mul_log {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ p k : ℕ, p.Prime → 1 ≤ k → f (p ^ k) ≤ C * Real.log (p ^ k)) :
    ¬ UnboundedOnPrimePowers f := by
  intro h
  obtain ⟨p, k, hp, hk, hgt⟩ := h C
  exact absurd hgt (not_lt.mpr (hf p k hp hk))

/-
## (9) Sup-closure: the order structure is a lattice filter / ideal

Sections (6) and (8) established that the hypothesis class is an *up-set* in the
prime-power domination order (upward closed under `unboundedOnPrimePowers_of_ge`,
downward failure under `not_unboundedOnPrimePowers_of_le`).  This section completes
that picture with the **join** (pointwise `max`), turning the qualitative "up-set"
statement into the sharp lattice fact:

* the hypothesis functions are closed under `max` with an *arbitrary* function
  (`unboundedOnPrimePowers_max_left`) — they form a sup-closed **filter**;
* the *failing* functions are closed under `max` of two of them
  (`not_unboundedOnPrimePowers_max`) — they form a sup-closed **ideal**.

The second is not a mere domination corollary: it needs the two `O(log)` constants
to be merged into their maximum, using `log (p^k) ≥ 0`.  Together they say the
Erdős #897 hypothesis cuts the pointwise order into a filter of "large" functions
and a complementary ideal of "small" (`O(log)` on prime powers) ones, both stable
under joins.
-/

/-- **Sup-closure of the hypothesis (filter side).**  If `f` is unbounded on prime
powers relative to `log`, then so is its pointwise maximum with *any* function `g`:
`max (f n) (g n) ≥ f n` on every prime power, so the same witnesses transfer via the
domination lemma.  The hypothesis class is therefore closed under `max`. -/
theorem unboundedOnPrimePowers_max_left {f g : ℕ → ℝ}
    (hf : UnboundedOnPrimePowers f) :
    UnboundedOnPrimePowers (fun n => max (f n) (g n)) :=
  unboundedOnPrimePowers_of_ge hf (fun _ _ _ _ => le_max_left _ _)

/-- **Sup-closure of the hypothesis (symmetric form).**  Likewise `max` with a
function on the left. -/
theorem unboundedOnPrimePowers_max_right {f g : ℕ → ℝ}
    (hg : UnboundedOnPrimePowers g) :
    UnboundedOnPrimePowers (fun n => max (f n) (g n)) :=
  unboundedOnPrimePowers_of_ge hg (fun _ _ _ _ => le_max_right _ _)

/-- **Sup-closure of the failing class (ideal side).**  If both `f` and `g` FAIL the
Erdős #897 hypothesis — i.e. each is `O(log)` on prime powers, say `f ≤ Mf·log` and
`g ≤ Mg·log` — then their pointwise maximum also fails: `max (f, g) ≤ max(Mf,Mg)·log`
on every prime power (using `log(p^k) ≥ 0`), so the `O(log)` criterion of (8) applies.
Thus the small functions form a sup-closed ideal, dual to the filter above. -/
theorem not_unboundedOnPrimePowers_max {f g : ℕ → ℝ}
    (hf : ¬ UnboundedOnPrimePowers f) (hg : ¬ UnboundedOnPrimePowers g) :
    ¬ UnboundedOnPrimePowers (fun n => max (f n) (g n)) := by
  unfold UnboundedOnPrimePowers at hf hg
  push_neg at hf hg
  obtain ⟨Mf, hMf⟩ := hf
  obtain ⟨Mg, hMg⟩ := hg
  refine not_unboundedOnPrimePowers_of_le_const_mul_log
    (C := max Mf Mg) (fun p k hp hk => ?_)
  have hlog : 0 ≤ Real.log ((p : ℝ) ^ k) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_pow k p hp.pos)
  exact max_le
    (le_trans (hMf p k hp hk) (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog))
    (le_trans (hMg p k hp hk) (mul_le_mul_of_nonneg_right (le_max_right _ _) hlog))

/-
## (10) The boundedness selectivity criterion

Section (8)'s `O(log)` criterion `not_unboundedOnPrimePowers_of_le_const_mul_log`
subsumes the ad-hoc selectivity of `logN` and `ω` by comparing against `C·log`.
Its sharpest *constant* specialization deserves its own name: a function that is
merely **bounded above** on prime powers (`f(p^k) ≤ C` for a fixed `C`, no `log`
factor at all) fails the Erdős #897 hypothesis outright.  This is the qualitative
statement "bounded on prime powers ⟹ not unbounded relative to `log`", and it
covers *every* bounded arithmetic function in one stroke — in particular `ω`
(`ω(p^k) = 1`), and more generally any additive `f` taking finitely many values on
prime powers.
-/

/-- **Boundedness selectivity criterion.**  If an arithmetic function is bounded
above by a constant on prime powers — `f(p^k) ≤ C` for a fixed `C` and every prime
power — then it fails the Erdős #897 hypothesis.  The constant bound is dominated by
`(max C 0 / log 2)·log(p^k)`, because `log(p^k) ≥ log 2 > 0` on every prime power,
so the `O(log)` criterion of section (8) applies with `C' = max(C,0)/log 2`.  This
generalizes the `ω` selectivity of section (2) (`ω(p^k) = 1 ≤ C = 1`) to *any*
prime-power-bounded function, with no additivity or arithmetic structure required. -/
theorem not_unboundedOnPrimePowers_of_bounded {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ p k : ℕ, p.Prime → 1 ≤ k → f (p ^ k) ≤ C) :
    ¬ UnboundedOnPrimePowers f := by
  refine not_unboundedOnPrimePowers_of_le_const_mul_log
    (C := max C 0 / Real.log 2) (fun p k hp hk => ?_)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hmaxnn : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  have hloglow : Real.log 2 ≤ Real.log (p ^ k) := by
    apply Real.log_le_log
    · norm_num
    · have h : (2 : ℕ) ≤ p ^ k := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
      exact_mod_cast h
  have hmid : C ≤ (max C 0 / Real.log 2) * Real.log (p ^ k) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    have h1 : C * Real.log 2 ≤ max C 0 * Real.log 2 :=
      mul_le_mul_of_nonneg_right (le_max_left C 0) hlog2.le
    have h2 : max C 0 * Real.log 2 ≤ max C 0 * Real.log (p ^ k) :=
      mul_le_mul_of_nonneg_left hloglow hmaxnn
    linarith
  exact le_trans (hf p k hp hk) hmid

end Erdos897
