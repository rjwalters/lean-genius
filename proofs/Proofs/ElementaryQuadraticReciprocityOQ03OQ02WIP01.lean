import Proofs.ElementaryQuadraticReciprocityOQ03OQ02
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic

/-
# The Kronecker Symbol as a Periodic Character (completion of ...OQ03OQ02)

*Open question* (`elementary-quadratic-reciprocity-oq-03-oq-02-wip-01`): the parent
file `ElementaryQuadraticReciprocityOQ03OQ02` builds the Kronecker symbol `(a/n)`,
proves it is completely multiplicative in both arguments, and (Section 5) motivates
it as *"the associated primitive Dirichlet character"* of a fundamental discriminant.
The defining property of a Dirichlet character mod `n` — periodicity of the symbol
in its numerator, `(a/n)` depending only on `a mod n` — is asserted in the prose but
never formalized.  Likewise, for the `(·/2)` character `kronecker2` the parent proves
only *single-step* periodicity `kronecker2_periodic` (`(a+8/2) = (a/2)`), leaving the
full period statement `(a+8k/2) = (a/2)` and the residue-only dependence implicit.

This file closes those gaps, all derived from the parent's public API with no new
axioms (`propext`, `Classical.choice`, `Quot.sound` only):

## Numerator side — the Dirichlet-character property of `(·/n)`

* `kronecker_congr_left`      — for odd positive `n`, `a ≡ b (mod n) ⟹ (a/n) = (b/n)`.
                                The symbol is a function of the residue class `a mod n`.
* `kronecker_add_mul_left`    — `(a + n·k / n) = (a/n)` for every `k`: full periodicity
                                of the numerator with period `n`.
* `kronecker_periodic_left`   — the `k = 1` shift `(a + n / n) = (a/n)`, the textbook
                                statement that `(·/n)` is a character modulo `n`.

## `(·/2)` side — full periodicity of `kronecker2`

* `kronecker2_congr`          — `a ≡ b (mod 8) ⟹ kronecker2 a = kronecker2 b`.
* `kronecker2_add_mul_eight`  — `kronecker2 (a + 8·k) = kronecker2 a` (full period 8,
                                generalizing the parent's single-step `kronecker2_periodic`).

Together with the parent's `kronecker2_mul` / `kronecker2_neg` these complete the
identification of `(·/2)` and `(·/n)` (odd `n`) as genuine periodic characters — the
structural input the Gauss-sum route to generalized quadratic reciprocity rests on.

## Anti-periodicity and the orthogonality relations of `χ₈ = (·/2)`

* `kronecker2_add_four`         — `(a+4/2) = −(a/2)`: a half-period shift *flips the sign*,
                                  the sharp form of "period `8` does not descend to `4`".
* `kronecker2_sum_shifted_period` — `∑_{a=0}^{7} (c+a/2) = 0` for every `c`: the mean of
                                  `χ₈` over *any* full period vanishes (generalizes the
                                  parent-window `kronecker2_sum_period`, `c = 0`).
* `kronecker2_sq_sum_period`    — `∑_{a=0}^{7} (a/2)² = φ(8) = 4`: the self-orthogonality /
                                  `L²`-norm normalizing the Gauss sum `|τ(χ₈)|² = 8`.

## The complete autocorrelation spectrum of `χ₈ = (·/2)` (Section F)

* `kronecker2_mul_shift_odd`     — `(a/2)·(a+t/2) = 0` for every odd `t`: the parity
                                   obstruction, pointwise, on every `a`.
* `kronecker2_autocorr_odd`       — `C(t) = ∑_a (a/2)(a+t/2) = 0` for odd `t` (and its
                                   translation-invariant `_shifted` form).
* `kronecker2_autocorr_two`       — `C(2) = 0`, the one non-trivial (non-termwise) off-peak.
* `kronecker2_autocorr_spectrum`  — the full comb `C = (4,0,0,0,−4,0,0,0)`: `C(0)=4`,
                                   `C(1)=C(2)=C(3)=0`, `C(4)=−4`, completing the length-`8`
                                   autocorrelation whose DFT is the power spectrum `|τ(χ₈)|²=8`.

## The Gauss sum of `χ₈` — explicit value and sign (Section G)

* `zeta8` / `zeta8_eq_exp`        — the canonical primitive 8th root of unity
                                    `ζ₈ = (1+i)/√2 = e^{2πi/8}`, with `ζ₈² = i`, `ζ₈⁴ = −1`,
                                    `ζ₈⁸ = 1` and exact order `8` (`zeta8_orderOf`).
* `gaussSumChi8_eq`               — **the Gauss sum evaluated**: `τ(χ₈) = ∑_{a=0}^{7} χ₈(a)ζ₈^a
                                    = 2√2`, a *positive real* number.
* `gaussSumChi8_eq_sqrt_conductor` — the sign of the Gauss sum (Gauss 1805, instance `D = 8`):
                                    `τ(χ₈) = +√8`, the positive square root of the conductor.
* `gaussSumChi8_sq`               — `τ(χ₈)² = 8 = χ₈(−1)·8`: the squared Gauss sum equals the
                                    conductor, the identity that powers the Gauss-sum proof of
                                    (generalized) quadratic reciprocity for the even character `χ₈`.
* `gaussSumChi8_twisted`          — multiplicative covariance `∑_a χ₈(a)ζ₈^{ca} = χ₈(c)·τ(χ₈)`
                                    for every unit `c ∈ {1,3,5,7}` mod `8` — the twisted Gauss
                                    sums, the engine of the reciprocity argument.

## The Gauss-sum proof of the second supplementary law (Section H)

* `gaussSumK2`                    — the Gauss sum `τ_R(ζ) = ∑_{a=0}^{7} χ₈(a) ζ^a` over an
                                    *arbitrary* commutative ring `R`, specializing to
                                    `gaussSumChi8` at `R = ℂ`, `ζ = ζ₈` (`gaussSumK2_complex`).
* `gaussSumK2_sq`                 — **`τ² = 8` generically**: for any `ζ` with `ζ⁴ = −1`, in any
                                    commutative ring — the conductor identity freed from `ℂ`.
* `gaussSumK2_pow_char`           — **Frobenius covariance** `τ^p = χ₈(p)·τ` in odd prime
                                    characteristic `p`: the freshman's dream turns the `p`-th
                                    power into the twist `a ↦ pa`, evaluated by the mod-8 fold.
* `eight_pow_eq_kronecker2`       — cancelling `τ ≠ 0` from the two evaluations of `τ^p`:
                                    `8^{(p−1)/2} = χ₈(p)` in any such field.
* `exists_pow_four_eq_neg_one`    — `GF(p²)` contains an eighth root of unity (`ζ⁴ = −1`),
                                    since its cyclic unit group has order `p² − 1 ≡ 0 (mod 8)`.
* `legendreSym_two_eq_kronecker2` — **the second supplementary law `(2/p) = (p/2)`, proved by
                                    the Gauss-sum argument end to end**: Euler's criterion in
                                    `ℤ/p` descends `8^{(p−1)/2} = χ₈(p)` along `ℤ/p ↪ GF(p²)`
                                    to `(2/p) = χ₈(p) = kronecker2 p`.  Unlike the parent's
                                    `kronecker_two_odd` (imported from Mathlib's
                                    `jacobiSym.at_two`), no reciprocity-adjacent Mathlib result
                                    is consumed: the chain's first self-contained proof of one
                                    of the reciprocity laws it formalizes.

All results are fully machine-checked (0 axioms, 0 sorries).

Reference: Kronecker (1885); Hardy–Wright ch. 6; parent `ElementaryQuadraticReciprocityOQ03OQ02`.
-/

namespace KroneckerSymbol

open Int

-- ============================================================
-- Section A: The Dirichlet-character property of `(·/n)` (numerator side)
-- ============================================================

/-- **The Kronecker symbol depends only on the residue class of its numerator.**
    For odd positive `n`, if `a ≡ b (mod n)` then `(a/n) = (b/n)`.  On odd positive
    moduli the parent's `kronecker_eq_jacobi` identifies `(·/n)` with the Jacobi
    symbol, and `jacobiSym.mod_left'` supplies exactly this residue-invariance.  This
    is the defining periodicity of the Dirichlet character `(·/n)` promised (but not
    proved) in the parent's Section 5. -/
theorem kronecker_congr_left {a b : ℤ} {n : ℕ} (hn : 0 < n) (hodd : n % 2 = 1)
    (h : a % (n : ℤ) = b % (n : ℤ)) :
    kronecker a n = kronecker b n := by
  rw [kronecker_eq_jacobi a n hn hodd, kronecker_eq_jacobi b n hn hodd]
  exact jacobiSym.mod_left' h

/-- **Full numerator periodicity with period `n`.**  For odd positive `n` and every
    integer shift `k`, `(a + n·k / n) = (a/n)`: adding any multiple of the modulus to
    the numerator leaves the symbol unchanged.  Immediate from `kronecker_congr_left`
    since `(a + n·k) % n = a % n`. -/
theorem kronecker_add_mul_left (a k : ℤ) {n : ℕ} (hn : 0 < n) (hodd : n % 2 = 1) :
    kronecker (a + n * k) n = kronecker a n :=
  kronecker_congr_left hn hodd (by rw [Int.add_mul_emod_self_left])

/-- **`(·/n)` is a character modulo `n`: the unit shift.**  The `k = 1` case of
    `kronecker_add_mul_left`, `(a + n / n) = (a/n)` — the textbook statement that the
    Kronecker symbol at a fixed odd positive modulus `n` is periodic with period `n`. -/
theorem kronecker_periodic_left (a : ℤ) {n : ℕ} (hn : 0 < n) (hodd : n % 2 = 1) :
    kronecker (a + n) n = kronecker a n := by
  simpa using kronecker_add_mul_left a 1 hn hodd

-- ============================================================
-- Section B: Full periodicity of the `(·/2)` character `kronecker2`
-- ============================================================

/-- `kronecker2 x` depends only on `x % 8` (re-derived locally as a helper). -/
private theorem kronecker2_mod_eight (x : ℤ) : kronecker2 x = kronecker2 (x % 8) := by
  unfold kronecker2
  rw [Int.emod_emod_of_dvd x (by norm_num : (2 : ℤ) ∣ 8),
    Int.emod_emod_of_dvd x (by norm_num : (8 : ℤ) ∣ 8)]

/-- **`kronecker2` depends only on the residue mod `8`.**  If `a ≡ b (mod 8)` then
    `kronecker2 a = kronecker2 b`: the `(·/2)` symbol is a function of the residue
    class mod `8`.  This is the congruence-invariance underlying the parent's
    single-step `kronecker2_periodic`. -/
theorem kronecker2_congr {a b : ℤ} (h : a % 8 = b % 8) :
    kronecker2 a = kronecker2 b := by
  rw [kronecker2_mod_eight a, kronecker2_mod_eight b, h]

/-- **Full period `8` for `kronecker2`.**  `kronecker2 (a + 8·k) = kronecker2 a` for
    every integer `k`, generalizing the parent's single-step `kronecker2_periodic`
    (`k = 1`).  Since `kronecker2` depends only on `a % 8` (`kronecker2_congr`) and
    `(a + 8·k) % 8 = a % 8`, adding any multiple of `8` fixes the value — the exact
    period-8 statement identifying `(·/2)` as a Dirichlet character mod `8`. -/
theorem kronecker2_add_mul_eight (a k : ℤ) :
    kronecker2 (a + 8 * k) = kronecker2 a :=
  kronecker2_congr (by rw [Int.add_mul_emod_self_left])

-- ============================================================
-- Section C: `8` is the *minimal* period — `(·/2)` is primitive (conductor `8`)
-- ============================================================

/-- **`kronecker2` is not `4`-periodic.**  `kronecker2 (a + 4) = kronecker2 a` fails —
    witnessed at `a = 1`, where `kronecker2 5 = −1 ≠ 1 = kronecker2 1`
    (`kronecker2_five`, `kronecker2_one`).  So the period-`8` character `(·/2)` does not
    descend to a character mod `4`. -/
theorem kronecker2_not_period_four : ¬ ∀ a : ℤ, kronecker2 (a + 4) = kronecker2 a := by
  intro h
  have h1 := h 1
  rw [show (1 : ℤ) + 4 = 5 by norm_num, kronecker2_five, kronecker2_one] at h1
  norm_num at h1

/-- **`kronecker2` is not `2`-periodic.**  `kronecker2 (a + 2) = kronecker2 a` fails at
    `a = 1`: `kronecker2 3 = −1 ≠ 1 = kronecker2 1` (`kronecker2_three`,
    `kronecker2_one`).  A fortiori `(·/2)` is not `1`-periodic either. -/
theorem kronecker2_not_period_two : ¬ ∀ a : ℤ, kronecker2 (a + 2) = kronecker2 a := by
  intro h
  have h1 := h 1
  rw [show (1 : ℤ) + 2 = 3 by norm_num, kronecker2_three, kronecker2_one] at h1
  norm_num at h1

/-- **`8` is the exact conductor of `(·/2)`: primitivity.**  The `(·/2)` character
    `kronecker2` is periodic with period `8` (`kronecker2_add_mul_eight`) but with no
    proper divisor of `8` as a period — neither `4` (`kronecker2_not_period_four`) nor `2`
    (`kronecker2_not_period_two`).  Hence `8` is its *minimal* period: `χ₈ = (·/2)` is a
    **primitive** Dirichlet character mod `8`, not induced from a character of any smaller
    modulus.  This upgrades the period-`8` statement to the sharp conductor, the input the
    Gauss-sum route needs (only primitive characters have nonvanishing Gauss sums). -/
theorem kronecker2_conductor_eight :
    (∀ a k : ℤ, kronecker2 (a + 8 * k) = kronecker2 a) ∧
      (¬ ∀ a : ℤ, kronecker2 (a + 4) = kronecker2 a) ∧
      (¬ ∀ a : ℤ, kronecker2 (a + 2) = kronecker2 a) :=
  ⟨kronecker2_add_mul_eight, kronecker2_not_period_four, kronecker2_not_period_two⟩

-- ============================================================
-- Section D: The residue-level character table of `(·/2)`
-- ============================================================

/-- **`(·/2)` vanishes exactly on the even residues.**  `kronecker2 a = 0 ↔ a` even.
    Squaring `(·/2)` collapses its two unit classes onto the principal character mod `2`
    (`kronecker2_sq`: `(a/2)² = 0` on evens, `1` on odds), and over `ℤ` a value squares to
    `0` iff it is `0` (`mul_self_eq_zero`).  This pins the *support* of the character. -/
theorem kronecker2_eq_zero_iff (a : ℤ) : kronecker2 a = 0 ↔ a % 2 = 0 := by
  rw [← mul_self_eq_zero, kronecker2_sq]
  split_ifs with h <;> simp [h]

/-- **`(·/2)` is a unit exactly on the odd residues.**  `kronecker2 a ≠ 0 ↔ a` odd — the
    complement of `kronecker2_eq_zero_iff`, stating that `(·/2)` takes an invertible value
    `±1` precisely on the units mod `2`. -/
theorem kronecker2_ne_zero_iff (a : ℤ) : kronecker2 a ≠ 0 ↔ a % 2 = 1 := by
  rw [ne_eq, kronecker2_eq_zero_iff]; omega

/-- **`(·/2)` takes the value `+1` exactly on the residues `1, 7 (mod 8)`.**  The upper
    unit class of the primitive character `χ₈ = (·/2)`.  Direct from the definition: the
    `a % 8 = -1` disjunct is vacuous since `Int.emod` by `8` lands in `[0, 8)`, so the
    positive branch fires precisely on `a % 8 ∈ {1, 7}`. -/
theorem kronecker2_eq_one_iff (a : ℤ) : kronecker2 a = 1 ↔ a % 8 = 1 ∨ a % 8 = 7 := by
  unfold kronecker2
  split_ifs with h1 h2
  · exact ⟨fun h => by norm_num at h, fun h => by omega⟩
  · exact ⟨fun _ => by omega, fun _ => rfl⟩
  · exact ⟨fun h => by norm_num at h, fun h => by omega⟩

/-- **`(·/2)` takes the value `−1` exactly on the residues `3, 5 (mod 8)`.**  The lower
    unit class of `χ₈ = (·/2)`.  Together with `kronecker2_eq_one_iff` and
    `kronecker2_eq_zero_iff` this is the complete residue-level character table of the
    `(·/2)` symbol: `0` on evens, `+1` on `{1,7}`, `−1` on `{3,5}` mod `8`. -/
theorem kronecker2_eq_neg_one_iff (a : ℤ) : kronecker2 a = -1 ↔ a % 8 = 3 ∨ a % 8 = 5 := by
  unfold kronecker2
  split_ifs with h1 h2
  · exact ⟨fun h => by norm_num at h, fun h => by omega⟩
  · exact ⟨fun h => by norm_num at h, fun h => by omega⟩
  · exact ⟨fun _ => by omega, fun _ => rfl⟩

-- Section D: Boundedness and orthogonality of the character χ₈ = (·/2)

/-- **`(·/2)` is bounded by `1` in absolute value.**  Since `kronecker2` takes values in
    `{−1, 0, 1}` (`kronecker2_values`), `|kronecker2 a| ≤ 1` for every `a`.  The pointwise
    bound a character sum consumes term-by-term — the elementary input to the Gauss-sum /
    Pólya–Vinogradov estimates of the generalized-reciprocity route. -/
theorem kronecker2_abs_le_one (a : ℤ) : |kronecker2 a| ≤ 1 := by
  rcases kronecker2_values a with h | h | h <;> rw [h] <;> decide

/-- **Orthogonality: `χ₈ = (·/2)` sums to zero over a full period.**

        ∑_{a = 0}^{7} kronecker2 a = 0.

    The defining property of a *non-principal* Dirichlet character — its sum over any full
    period vanishes.  Concretely the residue table (`0` on evens, `+1` on `{1,7}`, `−1` on
    `{3,5}` mod `8`) gives `0 + 1 + 0 − 1 + 0 − 1 + 0 + 1 = 0`.  This is the orthogonality
    relation that opens the Gauss-sum evaluation (Target 2): the mean of `χ₈` is `0`, so the
    Gauss sum `∑ χ₈(a) ζ^a` has no constant-mode contribution. -/
theorem kronecker2_sum_period :
    (∑ a ∈ Finset.range 8, kronecker2 (a : ℤ)) = 0 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one]
  decide

-- ============================================================
-- Section E: Anti-periodicity, translation-invariant orthogonality, and the
--            self-orthogonality (L²) normalization of χ₈ = (·/2)
-- ============================================================

/-- **`χ₈` is anti-periodic with anti-period `4`: `(a+4/2) = −(a/2)`.**  Shifting the
    numerator by `4` negates the Kronecker symbol at `2`, for *every* integer `a` (on the
    even residues both sides are `0`).  Concretely `1↦5, 3↦7, 5↦1, 7↦3` swaps the two unit
    classes `{1,7}` (value `+1`) and `{3,5}` (value `−1`) mod `8`.  This anti-periodicity is
    the structural reason the period `8` does **not** descend to `4` — it upgrades
    `kronecker2_not_period_four` from "`4` is not a period" to the exact statement that a
    half-period shift *flips the sign*, the hallmark of a primitive character of conductor
    `8`.  Proved by reducing both sides to the residue mod `8` (`kronecker2_mod_eight`) and
    checking the eight classes. -/
theorem kronecker2_add_four (a : ℤ) : kronecker2 (a + 4) = - kronecker2 a := by
  have key : kronecker2 (a + 4) = kronecker2 (a % 8 + 4) := by
    rw [kronecker2_mod_eight (a + 4), kronecker2_mod_eight (a % 8 + 4)]
    congr 1
    omega
  rw [key, kronecker2_mod_eight a]
  have hr : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨
      a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by omega
  rcases hr with h | h | h | h | h | h | h | h <;> rw [h] <;> decide

/-- **Translation-invariant orthogonality: `χ₈` sums to zero over *any* full period.**

        ∀ c, ∑_{a = 0}^{7} kronecker2 (c + a) = 0.

    The parent's `kronecker2_sum_period` proves this only for the window `[0, 8)`; this is
    the full non-principal-character statement that the mean over *every* length-`8` window
    vanishes (the `c = 0` case recovers `kronecker2_sum_period`).  Clean proof from the
    anti-periodicity `kronecker2_add_four`: the second half of the window cancels the first,
    `kronecker2 (c+a+4) = −kronecker2 (c+a)`, so the eight terms pair off to `0`.  This is
    the translation invariance of the character mean that the Gauss-sum evaluation uses when
    it re-centers the sum `∑ χ₈(a) ζ^a` at an arbitrary residue. -/
theorem kronecker2_sum_shifted_period (c : ℤ) :
    (∑ a ∈ Finset.range 8, kronecker2 (c + a)) = 0 := by
  have h1 : kronecker2 (c + 5) = - kronecker2 (c + 1) := by
    have h := kronecker2_add_four (c + 1)
    rwa [show (c + 1 + 4 : ℤ) = c + 5 by ring] at h
  have h2 : kronecker2 (c + 6) = - kronecker2 (c + 2) := by
    have h := kronecker2_add_four (c + 2)
    rwa [show (c + 2 + 4 : ℤ) = c + 6 by ring] at h
  have h3 : kronecker2 (c + 7) = - kronecker2 (c + 3) := by
    have h := kronecker2_add_four (c + 3)
    rwa [show (c + 3 + 4 : ℤ) = c + 7 by ring] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one, add_zero, zero_add]
  linarith [kronecker2_add_four c, h1, h2, h3]

/-- **Self-orthogonality: the `L²`-norm of `χ₈` over a period is `φ(8) = 4`.**

        ∑_{a = 0}^{7} (kronecker2 a)² = 4.

    Since `χ₈` takes the value `±1` on the four units mod `8` (`{1,3,5,7}`) and `0` on the
    four evens, its second moment counts the units: `⟨χ₈, χ₈⟩ = 4`.  This is the diagonal
    orthogonality relation complementing the mean-zero `kronecker2_sum_period`; together they
    are the `⟨χ_i, χ_j⟩ = φ(8)·δ_{ij}` normalization that fixes the modulus of the Gauss sum
    (`|τ(χ₈)|² = 8`) in the Gauss-sum route to generalized reciprocity. -/
theorem kronecker2_sq_sum_period :
    (∑ a ∈ Finset.range 8, kronecker2 (a : ℤ) * kronecker2 (a : ℤ)) = 4 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one]
  decide

/-- **Translation-invariant `L²`-norm: `∑_{a=0}^{7} (c+a/2)² = 4` for every `c`.**

        ∀ c, ∑_{a = 0}^{7} kronecker2 (c + a) * kronecker2 (c + a) = 4.

    The parent's `kronecker2_sq_sum_period` proves the second moment over the base window
    `[0, 8)`; this is the full self-orthogonality statement — the `L²`-norm of `χ₈` over
    *every* length-`8` window is `φ(8) = 4` (the `c = 0` case recovers the parent lemma).
    It is the diagonal counterpart of the mean-zero `kronecker2_sum_shifted_period`: any
    `8` consecutive integers contain exactly four units mod `2`, each contributing
    `(±1)² = 1` (`kronecker2_sq`), the four evens contributing `0`.  Together they give the
    translation-invariant orthogonality `⟨χ₈(c+·), χ₈(c+·)⟩ = φ(8)` that fixes the modulus
    of the Gauss sum `|τ(χ₈)|² = 8` independently of where the period window is centred. -/
theorem kronecker2_sq_sum_shifted_period (c : ℤ) :
    (∑ a ∈ Finset.range 8, kronecker2 (c + a) * kronecker2 (c + a)) = 4 := by
  simp only [kronecker2_sq, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, add_zero, zero_add]
  split_ifs <;> omega

/-- **Anti-period autocorrelation: `∑_{a=0}^{7} (a/2)·(a+4/2) = −4`.**

        ∑_{a = 0}^{7} kronecker2 a * kronecker2 (a + 4) = -4.

    The shift-`4` autocorrelation of `χ₈` is `−4`, the exact negative of the diagonal
    self-orthogonality `kronecker2_sq_sum_period` (shift `0`, value `+4`).  Immediate from
    the anti-periodicity `kronecker2_add_four` (`(a+4/2) = −(a/2)`): every term becomes
    `(a/2)·(−(a/2)) = −(a/2)²`.  Together `C(0) = 4` and `C(4) = −4` pin down the two
    non-zero values of the length-`8` autocorrelation `C(t) = ∑_a χ₈(a) χ₈(a+t)` of the
    conductor-`8` character — the correlation data underlying `|τ(χ₈)|² = 8`. -/
theorem kronecker2_autocorr_four :
    (∑ a ∈ Finset.range 8, kronecker2 (a : ℤ) * kronecker2 ((a : ℤ) + 4)) = -4 := by
  have h : ∀ a ∈ Finset.range 8,
      kronecker2 (a : ℤ) * kronecker2 ((a : ℤ) + 4)
        = (-1) * (kronecker2 (a : ℤ) * kronecker2 (a : ℤ)) := by
    intro a _
    rw [kronecker2_add_four]; ring
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, kronecker2_sq_sum_period]
  norm_num

/-- **Translation-invariant anti-period autocorrelation: `∑_{a=0}^{7} (c+a/2)·(c+a+4/2) = −4`.**

        ∀ c, ∑_{a = 0}^{7} kronecker2 (c + a) * kronecker2 (c + a + 4) = -4.

    The shift-`4` autocorrelation of `χ₈` is `−4` over *every* period window, not just
    `[0, 8)` (`c = 0` recovers `kronecker2_autocorr_four`).  Same one-line mechanism —
    anti-periodicity `kronecker2_add_four` turns each term into `−(c+a/2)²` — now reduced
    against the translation-invariant `L²`-norm `kronecker2_sq_sum_shifted_period`.  This is
    the off-diagonal, re-centring-invariant orthogonality the Gauss-sum evaluation uses when
    it shifts the correlation window to an arbitrary residue. -/
theorem kronecker2_autocorr_four_shifted (c : ℤ) :
    (∑ a ∈ Finset.range 8, kronecker2 (c + a) * kronecker2 (c + a + 4)) = -4 := by
  have h : ∀ a ∈ Finset.range 8,
      kronecker2 (c + a) * kronecker2 (c + a + 4)
        = (-1) * (kronecker2 (c + a) * kronecker2 (c + a)) := by
    intro a _
    rw [kronecker2_add_four]; ring
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, kronecker2_sq_sum_shifted_period]
  norm_num

-- ============================================================
-- Section F: The complete autocorrelation spectrum of χ₈ = (·/2)
--            — the off-peak values C(1) = C(2) = C(3) = 0
-- ============================================================

/-- **Odd-shift pointwise vanishing: `(a/2)·(a+t/2) = 0` for every odd `t`.**  If `t` is
    odd then exactly one of `a`, `a + t` is even, and `χ₈` vanishes on the even residues
    (`kronecker2_eq_zero_iff`); so the product is `0` for *every* `a`, term by term.  This
    is the parity obstruction behind all the odd-shift autocorrelations of the conductor-`8`
    character: a character supported on the odd residues can never correlate with an
    odd translate of itself. -/
theorem kronecker2_mul_shift_odd (a : ℤ) {t : ℤ} (ht : Odd t) :
    kronecker2 a * kronecker2 (a + t) = 0 := by
  rcases Int.even_or_odd a with ha | ha
  · rw [(kronecker2_eq_zero_iff a).2 (Int.even_iff.mp ha), zero_mul]
  · have hz : (a + t) % 2 = 0 := by
      obtain ⟨j, hj⟩ := ha; obtain ⟨k, hk⟩ := ht; omega
    rw [(kronecker2_eq_zero_iff (a + t)).2 hz, mul_zero]

/-- **Odd-shift autocorrelation vanishes: `C(t) = 0` for every odd `t`.**

        ∀ odd t, ∑_{a = 0}^{7} kronecker2 a * kronecker2 (a + t) = 0.

    Immediate from the pointwise `kronecker2_mul_shift_odd`: every summand is already `0`,
    so no cancellation is even needed.  Instantiating `t = 1, 3` (and `t = 5, 7` by the
    evenness `C(t) = C(8−t)` implicit in period `8`) gives the four odd off-peak values of
    the length-`8` autocorrelation `C(t) = ∑_a χ₈(a) χ₈(a+t)`. -/
theorem kronecker2_autocorr_odd {t : ℤ} (ht : Odd t) :
    (∑ a ∈ Finset.range 8, kronecker2 (a : ℤ) * kronecker2 ((a : ℤ) + t)) = 0 :=
  Finset.sum_eq_zero fun a _ => kronecker2_mul_shift_odd (a : ℤ) ht

/-- **Translation-invariant odd-shift autocorrelation: `C(t) = 0` over any window.**

        ∀ c, ∀ odd t, ∑_{a = 0}^{7} kronecker2 (c + a) * kronecker2 (c + a + t) = 0.

    The odd-shift autocorrelation vanishes over *every* length-`8` window, not just `[0, 8)`
    (`c = 0` recovers `kronecker2_autocorr_odd`).  Still termwise from
    `kronecker2_mul_shift_odd` — the parity obstruction is translation invariant, since
    `c + a` and `c + a + t` have opposite parity whenever `t` is odd. -/
theorem kronecker2_autocorr_odd_shifted {t : ℤ} (ht : Odd t) (c : ℤ) :
    (∑ a ∈ Finset.range 8, kronecker2 (c + a) * kronecker2 (c + a + t)) = 0 :=
  Finset.sum_eq_zero fun a _ => kronecker2_mul_shift_odd (c + a) ht

/-- **Shift-`2` autocorrelation vanishes: `C(2) = 0`.**

        ∑_{a = 0}^{7} kronecker2 a * kronecker2 (a + 2) = 0.

    The one non-trivial off-peak value.  Unlike the odd shifts this is *not* termwise `0`
    (both `a` and `a + 2` can be odd); it vanishes by exact cancellation of the residue
    table: `χ₈(1)χ₈(3) + χ₈(3)χ₈(5) + χ₈(5)χ₈(7) + χ₈(7)χ₈(9) = (−1)+(1)+(−1)+(1) = 0`.
    Together with `kronecker2_autocorr_odd` this leaves `C(0) = 4` and `C(4) = −4` as the
    *only* non-zero autocorrelations of `χ₈`. -/
theorem kronecker2_autocorr_two :
    (∑ a ∈ Finset.range 8, kronecker2 (a : ℤ) * kronecker2 ((a : ℤ) + 2)) = 0 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one]
  decide

/-- **The complete autocorrelation spectrum of `χ₈ = (·/2)`.**

        C(t) := ∑_{a = 0}^{7} kronecker2 a · kronecker2 (a + t)
        C(0) = 4,  C(1) = 0,  C(2) = 0,  C(3) = 0,  C(4) = −4.

    Assembles the full length-`8` autocorrelation function of the conductor-`8` character
    from the pieces: the diagonal peak `C(0) = φ(8) = 4` (`kronecker2_sq_sum_period`), the
    odd off-peaks `C(1) = C(3) = 0` (`kronecker2_autocorr_odd`), the even off-peak
    `C(2) = 0` (`kronecker2_autocorr_two`), and the anti-diagonal peak `C(4) = −4`
    (`kronecker2_autocorr_four`).  By the real-character symmetry `C(t) = C(8 − t)` the
    remaining shifts are determined (`C(5) = C(3) = 0`, `C(6) = C(2) = 0`, `C(7) = C(1) = 0`),
    so the autocorrelation is the sparse comb `(4, 0, 0, 0, −4, 0, 0, 0)` — two equal-and-
    opposite spikes a half-period apart.  This is the correlation datum whose discrete
    Fourier transform is the power spectrum `|τ(χ₈)|² = 8` in the Gauss-sum route to
    generalized quadratic reciprocity. -/
theorem kronecker2_autocorr_spectrum :
    (∑ a ∈ Finset.range 8, kronecker2 (a : ℤ) * kronecker2 ((a : ℤ) + 0)) = 4 ∧
      (∑ a ∈ Finset.range 8, kronecker2 (a : ℤ) * kronecker2 ((a : ℤ) + 1)) = 0 ∧
      (∑ a ∈ Finset.range 8, kronecker2 (a : ℤ) * kronecker2 ((a : ℤ) + 2)) = 0 ∧
      (∑ a ∈ Finset.range 8, kronecker2 (a : ℤ) * kronecker2 ((a : ℤ) + 3)) = 0 ∧
      (∑ a ∈ Finset.range 8, kronecker2 (a : ℤ) * kronecker2 ((a : ℤ) + 4)) = -4 :=
  ⟨by simpa using kronecker2_sq_sum_period,
    kronecker2_autocorr_odd (Int.odd_iff.mpr (by decide)),
    kronecker2_autocorr_two,
    kronecker2_autocorr_odd (Int.odd_iff.mpr (by decide)),
    kronecker2_autocorr_four⟩

-- ============================================================
-- Section G: The Gauss sum τ(χ₈) — explicit value and sign
-- ============================================================

/-- The canonical primitive eighth root of unity `ζ₈ = (1 + i)/√2`.  This is the
    algebraic normal form of `e^{2πi/8}` (`zeta8_eq_exp` below); working with the
    closed form keeps every Gauss-sum computation inside field arithmetic over
    `ℚ(i, √2)` rather than transcendental-function manipulation. -/
noncomputable def zeta8 : ℂ := (1 + Complex.I) / (Real.sqrt 2 : ℂ)

/-- `(√2)² = 2` inside `ℂ` — the single algebraic relation through which every
    occurrence of `√2` is eliminated in the Gauss-sum computations below. -/
theorem sqrt_two_sq_complex : ((Real.sqrt 2 : ℂ)) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- `√2 ≠ 0` in `ℂ`, so division by `√2` in `zeta8` is honest field division. -/
theorem sqrt_two_ne_zero_complex : ((Real.sqrt 2 : ℂ)) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))

/-- `ζ₈² = i`: squaring the canonical eighth root of unity gives the canonical
    fourth root of unity.  With `(√2)² = 2` this is pure ring algebra:
    `((1+i)/√2)² = (1 + 2i + i²)/2 = i`. -/
theorem zeta8_sq : zeta8 ^ 2 = Complex.I := by
  unfold zeta8
  rw [div_pow, sqrt_two_sq_complex]
  linear_combination Complex.I_sq / 2

/-- `ζ₈⁴ = −1`: the fourth power lands on the primitive square root of unity —
    `ζ₈` is a square root of `i`, hence a fourth root of `−1`. -/
theorem zeta8_pow_four : zeta8 ^ 4 = -1 := by
  have h : zeta8 ^ 4 = (zeta8 ^ 2) ^ 2 := by ring
  rw [h, zeta8_sq, Complex.I_sq]

/-- `ζ₈⁸ = 1`: `ζ₈` is an eighth root of unity. -/
theorem zeta8_pow_eight : zeta8 ^ 8 = 1 := by
  have h : zeta8 ^ 8 = (zeta8 ^ 4) ^ 2 := by ring
  rw [h, zeta8_pow_four]
  norm_num

/-- **`ζ₈` is a *primitive* eighth root of unity**: its multiplicative order is
    exactly `8`.  Since `ζ₈⁸ = 1` the order divides `8 = 2³`; since `ζ₈⁴ = −1 ≠ 1`
    it does not divide `4 = 2²`, which forces order `2³` exactly
    (`orderOf_eq_prime_pow` with `p = 2`, `n = 2`). -/
theorem zeta8_orderOf : orderOf zeta8 = 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_eq_prime_pow (x := zeta8) (p := 2) (n := 2)
    (by rw [show (2:ℕ) ^ 2 = 4 from rfl, zeta8_pow_four]; norm_num)
    (by rw [show (2:ℕ) ^ (2 + 1) = 8 from rfl, zeta8_pow_eight])
  simpa using h

/-- **`ζ₈ = e^{2πi/8}`**: the closed form `(1+i)/√2` is exactly the canonical
    exponential eighth root of unity.  Unfolds `e^{iπ/4} = cos(π/4) + i·sin(π/4)`
    (Euler) and evaluates both trigonometric values to `√2/2`. -/
theorem zeta8_eq_exp : zeta8 = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 8) := by
  have harg : (2 * (Real.pi : ℂ) * Complex.I / 8) = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  unfold zeta8
  rw [div_eq_iff sqrt_two_ne_zero_complex]
  push_cast
  linear_combination (-(1 + Complex.I) / 2) * sqrt_two_sq_complex

/-- Powers of `ζ₈` reduce modulo `8` — the computational form of `ζ₈⁸ = 1`,
    used to fold the exponents `ca` of the twisted Gauss sums back into `[0, 8)`. -/
theorem zeta8_pow_mod (n : ℕ) : zeta8 ^ n = zeta8 ^ (n % 8) := by
  conv_lhs => rw [← Nat.div_add_mod n 8]
  rw [pow_add, pow_mul, zeta8_pow_eight, one_pow, one_mul]

/-- **The Gauss sum of `χ₈ = (·/2)`**: `τ(χ₈) = ∑_{a=0}^{7} χ₈(a) ζ₈^a`, the
    character sum against the canonical additive character of `ℤ/8ℤ`.  The
    orthogonality data of Sections E–F pins its modulus (`|τ|² = 8`); the theorems
    below compute the sum itself, sign included. -/
noncomputable def gaussSumChi8 : ℂ :=
  ∑ a ∈ Finset.range 8, (kronecker2 (a : ℤ) : ℂ) * zeta8 ^ a

/-- **The Gauss sum evaluated: `τ(χ₈) = 2√2`.**  Only the odd residues
    contribute, giving `τ = ζ₈ − ζ₈³ − ζ₈⁵ + ζ₈⁷ = 2ζ₈(1 − i) = 2√2` — a
    *positive real* number.  This single identity subsumes the modulus computation
    `|τ(χ₈)|² = 8` of the autocorrelation spectrum *and* determines the sign,
    which no amount of `|τ|` bookkeeping can see. -/
theorem gaussSumChi8_eq : gaussSumChi8 = 2 * (Real.sqrt 2 : ℂ) := by
  have h3 : zeta8 ^ 3 = zeta8 * Complex.I := by
    have h : zeta8 ^ 3 = zeta8 * zeta8 ^ 2 := by ring
    rw [h, zeta8_sq]
  have h5 : zeta8 ^ 5 = -zeta8 := by
    have h : zeta8 ^ 5 = zeta8 * zeta8 ^ 4 := by ring
    rw [h, zeta8_pow_four]
    ring
  have h7 : zeta8 ^ 7 = -(zeta8 * Complex.I) := by
    have h : zeta8 ^ 7 = zeta8 ^ 3 * zeta8 ^ 4 := by ring
    rw [h, h3, zeta8_pow_four]
    ring
  have key : zeta8 * (1 - Complex.I) = (Real.sqrt 2 : ℂ) := by
    unfold zeta8
    rw [div_mul_eq_mul_div, div_eq_iff sqrt_two_ne_zero_complex]
    linear_combination (-1 : ℂ) * sqrt_two_sq_complex - Complex.I_sq
  unfold gaussSumChi8
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat]
  rw [show kronecker2 0 = 0 from by decide, show kronecker2 1 = 1 from by decide,
    show kronecker2 2 = 0 from by decide, show kronecker2 3 = -1 from by decide,
    show kronecker2 4 = 0 from by decide, show kronecker2 5 = -1 from by decide,
    show kronecker2 6 = 0 from by decide, show kronecker2 7 = 1 from by decide,
    h3, h5, h7]
  push_cast
  linear_combination 2 * key

/-- **`τ(χ₈)² = 8`: the squared Gauss sum is the conductor.**  This is the
    `D = 8` instance of the fundamental identity `τ(χ_D)² = χ_D(−1)·D` for real
    primitive characters — since `χ₈(−1) = 1` (`kronecker2` is even), the square
    is `+8`.  It is exactly this identity that transports quadratic reciprocity
    through the Gauss-sum argument. -/
theorem gaussSumChi8_sq : gaussSumChi8 ^ 2 = 8 := by
  rw [gaussSumChi8_eq]
  linear_combination 4 * sqrt_two_sq_complex

/-- `τ(χ₈)² = χ₈(−1)·8`, the even-character form of the conductor identity,
    with the character value `χ₈(−1) = (−1/2) = 1` appearing explicitly. -/
theorem gaussSumChi8_sq_eq_chi_neg_one_mul_conductor :
    gaussSumChi8 ^ 2 = (kronecker2 (-1) : ℂ) * 8 := by
  rw [show kronecker2 (-1) = 1 from by decide, gaussSumChi8_sq]
  norm_num

/-- `√8 = 2√2` — the conductor's square root in lowest surd form. -/
theorem sqrt_eight_eq_two_mul_sqrt_two : Real.sqrt 8 = 2 * Real.sqrt 2 := by
  rw [show (8:ℝ) = 4 * 2 by norm_num, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4) 2,
    show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]

/-- **The sign of the Gauss sum (Gauss 1805, instance `D = 8`)**:
    `τ(χ₈) = +√8`, the *positive* square root of the conductor.  Determining this
    sign for general `D` was famously hard — Gauss conjectured it in 1801 and
    needed four more years for a proof.  For the even real primitive character of
    conductor `8` the present file settles it by direct evaluation. -/
theorem gaussSumChi8_eq_sqrt_conductor : gaussSumChi8 = (Real.sqrt 8 : ℂ) := by
  rw [gaussSumChi8_eq, sqrt_eight_eq_two_mul_sqrt_two]
  push_cast
  ring

/-- Twisted Gauss sum at `c = 3`: `∑_a χ₈(a) ζ₈^{3a} = χ₈(3)·τ(χ₈)`.
    Folding the exponents `3a mod 8` permutes the odd residues `{1,3,5,7}` and the
    permutation sign realized on the character values is exactly `χ₈(3) = −1`. -/
theorem gaussSumChi8_twisted_three :
    (∑ a ∈ Finset.range 8, (kronecker2 (a : ℤ) : ℂ) * zeta8 ^ (3 * a)) =
      (kronecker2 3 : ℂ) * gaussSumChi8 := by
  unfold gaussSumChi8
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, Nat.reduceMul]
  rw [show kronecker2 0 = 0 from by decide, show kronecker2 1 = 1 from by decide,
    show kronecker2 2 = 0 from by decide, show kronecker2 3 = -1 from by decide,
    show kronecker2 4 = 0 from by decide, show kronecker2 5 = -1 from by decide,
    show kronecker2 6 = 0 from by decide, show kronecker2 7 = 1 from by decide]
  rw [show zeta8 ^ (9:ℕ) = zeta8 ^ (1:ℕ) from by rw [zeta8_pow_mod],
    show zeta8 ^ (15:ℕ) = zeta8 ^ (7:ℕ) from by rw [zeta8_pow_mod],
    show zeta8 ^ (21:ℕ) = zeta8 ^ (5:ℕ) from by rw [zeta8_pow_mod]]
  push_cast
  ring

/-- Twisted Gauss sum at `c = 5`: `∑_a χ₈(a) ζ₈^{5a} = χ₈(5)·τ(χ₈)`. -/
theorem gaussSumChi8_twisted_five :
    (∑ a ∈ Finset.range 8, (kronecker2 (a : ℤ) : ℂ) * zeta8 ^ (5 * a)) =
      (kronecker2 5 : ℂ) * gaussSumChi8 := by
  unfold gaussSumChi8
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, Nat.reduceMul]
  rw [show kronecker2 0 = 0 from by decide, show kronecker2 1 = 1 from by decide,
    show kronecker2 2 = 0 from by decide, show kronecker2 3 = -1 from by decide,
    show kronecker2 4 = 0 from by decide, show kronecker2 5 = -1 from by decide,
    show kronecker2 6 = 0 from by decide, show kronecker2 7 = 1 from by decide]
  rw [show zeta8 ^ (15:ℕ) = zeta8 ^ (7:ℕ) from by rw [zeta8_pow_mod],
    show zeta8 ^ (25:ℕ) = zeta8 ^ (1:ℕ) from by rw [zeta8_pow_mod],
    show zeta8 ^ (35:ℕ) = zeta8 ^ (3:ℕ) from by rw [zeta8_pow_mod]]
  push_cast
  ring

/-- Twisted Gauss sum at `c = 7`: `∑_a χ₈(a) ζ₈^{7a} = χ₈(7)·τ(χ₈)`. -/
theorem gaussSumChi8_twisted_seven :
    (∑ a ∈ Finset.range 8, (kronecker2 (a : ℤ) : ℂ) * zeta8 ^ (7 * a)) =
      (kronecker2 7 : ℂ) * gaussSumChi8 := by
  unfold gaussSumChi8
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, Nat.reduceMul]
  rw [show kronecker2 0 = 0 from by decide, show kronecker2 1 = 1 from by decide,
    show kronecker2 2 = 0 from by decide, show kronecker2 3 = -1 from by decide,
    show kronecker2 4 = 0 from by decide, show kronecker2 5 = -1 from by decide,
    show kronecker2 6 = 0 from by decide, show kronecker2 7 = 1 from by decide]
  rw [show zeta8 ^ (21:ℕ) = zeta8 ^ (5:ℕ) from by rw [zeta8_pow_mod],
    show zeta8 ^ (35:ℕ) = zeta8 ^ (3:ℕ) from by rw [zeta8_pow_mod],
    show zeta8 ^ (49:ℕ) = zeta8 ^ (1:ℕ) from by rw [zeta8_pow_mod]]
  push_cast
  ring

/-- **Multiplicative covariance of the Gauss sum — the reciprocity engine.**
    For every unit `c` of `ℤ/8ℤ`, twisting the additive character by `c` scales
    the Gauss sum by the character value:

        ∑_{a=0}^{7} χ₈(a) ζ₈^{ca} = χ₈(c) · τ(χ₈).

    This covariance (substitute `a ↦ c⁻¹a` and use complete multiplicativity of
    `χ₈`) is the identity through which the Gauss sum transports quadratic
    reciprocity; here it is verified exhaustively over the unit group
    `(ℤ/8ℤ)ˣ = {1, 3, 5, 7}`. -/
theorem gaussSumChi8_twisted (c : ℕ) (hc : c = 1 ∨ c = 3 ∨ c = 5 ∨ c = 7) :
    (∑ a ∈ Finset.range 8, (kronecker2 (a : ℤ) : ℂ) * zeta8 ^ (c * a)) =
      (kronecker2 (c : ℤ) : ℂ) * gaussSumChi8 := by
  rcases hc with rfl | rfl | rfl | rfl
  · unfold gaussSumChi8
    simp only [one_mul, Nat.cast_one]
    rw [show kronecker2 1 = 1 from by decide]
    push_cast
    ring
  · exact gaussSumChi8_twisted_three
  · exact gaussSumChi8_twisted_five
  · exact gaussSumChi8_twisted_seven

-- ============================================================
-- Section H: The ring-generic Gauss sum and the Gauss-sum proof
--            of the second supplementary law
-- ============================================================

/-- **The Gauss sum of `χ₈` over an arbitrary commutative ring.**  For a
    commutative ring `R` and an element `ζ : R`, the character sum
    `τ_R(ζ) = ∑_{a=0}^{7} χ₈(a) ζ^a` with `χ₈ = (·/2) = kronecker2`.  At
    `R = ℂ`, `ζ = ζ₈` this is Section G's `gaussSumChi8` (`gaussSumK2_complex`);
    at `R = GF(p²)` with `ζ` an eighth root of unity it becomes the engine of
    the Gauss-sum proof of the second supplementary law
    (`legendreSym_two_eq_kronecker2` below). -/
def gaussSumK2 (R : Type*) [CommRing R] (ζ : R) : R :=
  ∑ a ∈ Finset.range 8, (kronecker2 (a : ℤ) : R) * ζ ^ a

/-- Over `ℂ` with `ζ = ζ₈`, the ring-generic Gauss sum is Section G's Gauss sum:
    `τ_ℂ(ζ₈) = τ(χ₈)`. -/
theorem gaussSumK2_complex : gaussSumK2 ℂ zeta8 = gaussSumChi8 := rfl

/-- An element with `ζ⁴ = −1` is an eighth root of unity: `ζ⁸ = (ζ⁴)² = 1`. -/
theorem pow_eight_of_pow_four_eq_neg_one {R : Type*} [CommRing R] {ζ : R}
    (hζ : ζ ^ 4 = -1) : ζ ^ 8 = 1 := by
  have h : ζ ^ 8 = (ζ ^ 4) ^ 2 := by ring
  rw [h, hζ]
  ring

/-- Exponent folding: powers of an eighth root of unity reduce modulo `8` — the
    ring-generic form of `zeta8_pow_mod`. -/
theorem pow_mod_eight_of_pow_four_eq_neg_one {R : Type*} [CommRing R] {ζ : R}
    (hζ : ζ ^ 4 = -1) (n : ℕ) : ζ ^ n = ζ ^ (n % 8) := by
  conv_lhs => rw [← Nat.div_add_mod n 8]
  rw [pow_add, pow_mul, pow_eight_of_pow_four_eq_neg_one hζ, one_pow, one_mul]

/-- **Closed form of the generic Gauss sum.**  If `ζ⁴ = −1`, only the four odd
    residues contribute and the sum collapses to
    `τ = ζ − ζ³ − ζ⁵ + ζ⁷ = 2(ζ − ζ³)` — the ring-generic analogue of the
    computation inside `gaussSumChi8_eq`. -/
theorem gaussSumK2_eq {R : Type*} [CommRing R] {ζ : R} (hζ : ζ ^ 4 = -1) :
    gaussSumK2 R ζ = 2 * (ζ - ζ ^ 3) := by
  unfold gaussSumK2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat]
  rw [show kronecker2 0 = 0 from by decide, show kronecker2 1 = 1 from by decide,
    show kronecker2 2 = 0 from by decide, show kronecker2 3 = -1 from by decide,
    show kronecker2 4 = 0 from by decide, show kronecker2 5 = -1 from by decide,
    show kronecker2 6 = 0 from by decide, show kronecker2 7 = 1 from by decide]
  push_cast
  linear_combination (ζ ^ 3 - ζ) * hζ

/-- **`τ² = 8` in every commutative ring.**  For `ζ⁴ = −1`,
    `τ² = 4(ζ² − 2ζ⁴ + ζ⁶) = 4(ζ² + 2 − ζ²) = 8`: the squared Gauss sum equals
    the conductor *generically*, lifting `gaussSumChi8_sq` (the case `R = ℂ`)
    to the finite-characteristic setting where the reciprocity argument runs. -/
theorem gaussSumK2_sq {R : Type*} [CommRing R] {ζ : R} (hζ : ζ ^ 4 = -1) :
    gaussSumK2 R ζ ^ 2 = 8 := by
  rw [gaussSumK2_eq hζ]
  linear_combination (4 * ζ ^ 2 - 8) * hζ

/-- **Frobenius covariance of the Gauss sum: `τ^p = χ₈(p)·τ`.**  In a
    commutative ring of odd prime characteristic `p` containing an eighth root
    of unity, the freshman's dream `(x − y)^p = x^p − y^p` turns the `p`-th
    power of `τ = 2(ζ − ζ³)` into the twist `a ↦ pa` of the additive character,
    and folding exponents mod `8` evaluates the twist to the character value —
    the finite-characteristic incarnation of Section G's twisted Gauss sums
    `gaussSumChi8_twisted`. -/
theorem gaussSumK2_pow_char {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime]
    [CharP R p] (hp : p % 2 = 1) {ζ : R} (hζ : ζ ^ 4 = -1) :
    gaussSumK2 R ζ ^ p = (kronecker2 (p : ℤ) : R) * gaussSumK2 R ζ := by
  have h2 : (2 : R) ^ p = 2 := by
    rw [show (2 : R) = 1 + 1 from by norm_num, add_pow_char, one_pow]
  have hfrob : gaussSumK2 R ζ ^ p = 2 * (ζ ^ (p % 8) - ζ ^ (3 * p % 8)) := by
    rw [gaussSumK2_eq hζ, mul_pow, h2, sub_pow_char, ← pow_mul,
      ← pow_mod_eight_of_pow_four_eq_neg_one hζ p,
      ← pow_mod_eight_of_pow_four_eq_neg_one hζ (3 * p)]
  have hcongr : kronecker2 (p : ℤ) = kronecker2 ((p % 8 : ℕ) : ℤ) :=
    kronecker2_congr (by omega)
  have hmod : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
  rw [hfrob, hcongr, gaussSumK2_eq hζ]
  rcases hmod with h | h | h | h
  · rw [h, show 3 * p % 8 = 3 from by omega,
      show kronecker2 ((1 : ℕ) : ℤ) = 1 from by decide]
    push_cast
    ring
  · rw [h, show 3 * p % 8 = 1 from by omega,
      show kronecker2 ((3 : ℕ) : ℤ) = -1 from by decide]
    push_cast
    ring
  · rw [h, show 3 * p % 8 = 7 from by omega,
      show kronecker2 ((5 : ℕ) : ℤ) = -1 from by decide]
    push_cast
    linear_combination (2 * ζ - 2 * ζ ^ 3) * hζ
  · rw [h, show 3 * p % 8 = 5 from by omega,
      show kronecker2 ((7 : ℕ) : ℤ) = 1 from by decide]
    push_cast
    linear_combination (2 * ζ ^ 3 - 2 * ζ) * hζ

/-- **`8^{(p−1)/2} = χ₈(p)` in any field of odd prime characteristic containing
    an eighth root of unity** — the heart of the Gauss-sum argument.  The two
    evaluations of `τ^p` — the odd-power split `τ^p = τ·(τ²)^{(p−1)/2} =
    τ·8^{(p−1)/2}` (`gaussSumK2_sq`) and the Frobenius covariance
    `τ^p = χ₈(p)·τ` (`gaussSumK2_pow_char`) — agree, and `τ ≠ 0`
    (since `τ² = 8 ≠ 0` when `p ≠ 2`) cancels to give the Euler-criterion
    value of the conductor `8`. -/
theorem eight_pow_eq_kronecker2 {F : Type*} [Field F] (p : ℕ) [Fact p.Prime]
    [CharP F p] (hp : p % 2 = 1) {ζ : F} (hζ : ζ ^ 4 = -1) :
    (8 : F) ^ ((p - 1) / 2) = (kronecker2 (p : ℤ) : F) := by
  have hτsq : gaussSumK2 F ζ ^ 2 = 8 := gaussSumK2_sq hζ
  have hτne : gaussSumK2 F ζ ≠ 0 := by
    intro h0
    have h8 : ((8 : ℕ) : F) = 0 := by
      push_cast
      rw [← hτsq, h0]
      ring
    have hdvd : p ∣ 8 := (CharP.cast_eq_zero_iff F p 8).mp h8
    have hdvd2 : p ∣ 2 :=
      (Fact.out : p.Prime).dvd_of_dvd_pow (show p ∣ 2 ^ 3 by simpa using hdvd)
    have hp2 : p = 2 :=
      (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hdvd2
    omega
  have hodd : p = 2 * ((p - 1) / 2) + 1 := by
    have := (Fact.out : p.Prime).two_le
    omega
  have hpow : gaussSumK2 F ζ ^ p = gaussSumK2 F ζ * (8 : F) ^ ((p - 1) / 2) := by
    conv_lhs => rw [hodd]
    rw [pow_add, pow_mul, hτsq, pow_one, mul_comm]
  have hfrob := gaussSumK2_pow_char p hp hζ
  have key : gaussSumK2 F ζ * ((8 : F) ^ ((p - 1) / 2)) =
      gaussSumK2 F ζ * (kronecker2 (p : ℤ) : F) := by
    rw [← hpow, hfrob, mul_comm]
  exact mul_left_cancel₀ hτne key

/-- **A finite field whose order is `1 mod 8` contains an eighth root of unity**,
    delivered as `ζ⁴ = −1`: the unit group is cyclic of order `Nat.card F − 1`
    divisible by `8`, so it has an element `ζ` of exact order `8`; then
    `(ζ⁴)² = 1` with `ζ⁴ ≠ 1`, and in a field the only square root of `1`
    besides `1` is `−1`. -/
theorem exists_pow_four_eq_neg_one {F : Type*} [Field F] [Finite F]
    (h8 : 8 ∣ Nat.card F - 1) : ∃ ζ : F, ζ ^ 4 = -1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = Nat.card Fˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have hcardu : Nat.card Fˣ = Nat.card F - 1 := Nat.card_units F
  obtain ⟨k, hk⟩ : 8 ∣ Nat.card Fˣ := by rw [hcardu]; exact h8
  have hk0 : 0 < k := by
    have hpos : 0 < Nat.card Fˣ := Nat.card_pos
    omega
  have hord8 : orderOf (g ^ k) = 8 := by
    rw [orderOf_pow, hord, hk, Nat.gcd_eq_right ⟨8, by ring⟩,
      Nat.mul_div_cancel _ hk0]
  refine ⟨((g ^ k : Fˣ) : F), ?_⟩
  have hu8 : (g ^ k) ^ 8 = 1 := by rw [← hord8]; exact pow_orderOf_eq_one _
  have hu4 : (g ^ k) ^ 4 ≠ 1 := by
    intro h
    have hdvd := orderOf_dvd_of_pow_eq_one h
    rw [hord8] at hdvd
    norm_num at hdvd
  have hf8 : ((g ^ k : Fˣ) : F) ^ 8 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hu8, Units.val_one]
  have hf4ne : ((g ^ k : Fˣ) : F) ^ 4 ≠ 1 := by
    intro h
    exact hu4 (Units.ext (by push_cast; exact h))
  have hsq : (((g ^ k : Fˣ) : F) ^ 4) * (((g ^ k : Fˣ) : F) ^ 4) = 1 := by
    rw [← pow_add]
    exact hf8
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · exact absurd h hf4ne
  · exact h

/-- The order of a finite field of odd characteristic `p` and degree `2` is
    `1 mod 8`: every odd square is `1 mod 8`. -/
theorem eight_dvd_sq_sub_one {p : ℕ} (hp : p % 2 = 1) : 8 ∣ p ^ 2 - 1 := by
  have h : p ^ 2 % 8 = 1 := by
    rw [Nat.pow_mod]
    have h8 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
    rcases h8 with h | h | h | h <;> rw [h]
  obtain ⟨m, hm⟩ : ∃ m, p ^ 2 = m := ⟨p ^ 2, rfl⟩
  rw [hm] at h ⊢
  omega

/-- **The second supplementary law, by the Gauss-sum argument.**  For every odd
    prime `p`, `(2/p) = (p/2)`: the Legendre symbol of `2` equals the Kronecker
    character `χ₈ = (·/2)` at `p`.  Unlike the parent's `kronecker_two_odd`
    (imported from Mathlib's `jacobiSym.at_two`), this proof runs the classical
    Gauss-sum argument end to end inside the chain: in `F = GF(p²)` pick `ζ`
    with `ζ⁴ = −1` (`exists_pow_four_eq_neg_one`, since `8 ∣ p² − 1`); then
    `τ = ∑ χ₈(a)ζ^a` satisfies `τ² = 8` and `τ^p = χ₈(p)·τ`, so
    `8^{(p−1)/2} = χ₈(p)` in `F` (`eight_pow_eq_kronecker2`); the identity
    descends along the injection `ℤ/p ↪ GF(p²)`, where Euler's criterion reads
    the left side as `(8/p) = (2/p)³ = (2/p)`.  Both symbols are `±1`, and
    `1 ≠ −1 (mod p)` for odd `p` upgrades the mod-`p` identity to `ℤ`. -/
theorem legendreSym_two_eq_kronecker2 (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p 2 = kronecker2 (p : ℤ) := by
  have hpodd : p % 2 = 1 := by
    rcases Nat.even_or_odd p with he | ho
    · exact absurd (((Fact.out : p.Prime).even_iff).mp he) hp
    · exact Nat.odd_iff.mp ho
  obtain ⟨ζ, hζ⟩ : ∃ ζ : GaloisField p 2, ζ ^ 4 = -1 := by
    apply exists_pow_four_eq_neg_one
    rw [GaloisField.card p 2 (by norm_num)]
    exact eight_dvd_sq_sub_one hpodd
  have key : (8 : GaloisField p 2) ^ ((p - 1) / 2) =
      (kronecker2 (p : ℤ) : GaloisField p 2) :=
    eight_pow_eq_kronecker2 p hpodd hζ
  have hdesc : (8 : ZMod p) ^ ((p - 1) / 2) = ((kronecker2 (p : ℤ) : ZMod p)) := by
    apply (algebraMap (ZMod p) (GaloisField p 2)).injective
    rw [map_pow, map_ofNat, map_intCast]
    exact key
  have heuler : (legendreSym p 8 : ZMod p) = (8 : ZMod p) ^ ((p - 1) / 2) := by
    have hdiv : p / 2 = (p - 1) / 2 := by omega
    rw [legendreSym.eq_pow, hdiv]
    norm_num
  have hcast : (legendreSym p 8 : ZMod p) = ((kronecker2 (p : ℤ) : ZMod p)) := by
    rw [heuler, hdesc]
  have hpndvd2 : ¬ p ∣ 2 := by
    intro hdvd
    exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hdvd)
  have h2ne : ((2 : ℤ) : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact fun h => hpndvd2 (by exact_mod_cast h)
  have h8ne : ((8 : ℤ) : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro h
    have h8 : p ∣ 8 := by exact_mod_cast h
    exact hpndvd2 ((Fact.out : p.Prime).dvd_of_dvd_pow (show p ∣ 2 ^ 3 by simpa using h8))
  have h8val := legendreSym.eq_one_or_neg_one (p := p) (a := 8) h8ne
  have h2val := legendreSym.eq_one_or_neg_one (p := p) (a := 2) h2ne
  have hkval : kronecker2 (p : ℤ) = 1 ∨ kronecker2 (p : ℤ) = -1 := by
    have hne := (kronecker2_ne_zero_iff (p : ℤ)).mpr (by omega)
    rcases kronecker2_values (p : ℤ) with h | h | h
    · exact Or.inr h
    · exact absurd h hne
    · exact Or.inl h
  have h8eq2 : legendreSym p 8 = legendreSym p 2 := by
    have h842 : (8 : ℤ) = 2 * (2 * 2) := by norm_num
    rw [h842, legendreSym.mul, legendreSym.mul]
    rcases h2val with h | h <;> rw [h] <;> norm_num
  have hcontra : ((1 : ℤ) : ZMod p) ≠ ((-1 : ℤ) : ZMod p) := by
    intro h
    apply h2ne
    push_cast at h ⊢
    linear_combination h
  rw [← h8eq2]
  rcases h8val with h1 | h1 <;> rcases hkval with h2 | h2
  · rw [h1, h2]
  · rw [h1, h2] at hcast
    exact absurd hcast hcontra
  · rw [h1, h2] at hcast
    exact absurd hcast.symm hcontra
  · rw [h1, h2]

/- ### Section I: the odd-prime quadratic Gauss sum — `g_q² = χ_q(−1)·q`

Sections G–H settled the conductor-8 character `χ₈ = (·/2)`: the concrete Gauss
sum `τ(χ₈) = √8` over `ℂ`, and the ring-generic `τ_R` whose Frobenius
covariance proved the second supplementary law `(2/p) = (p/2)`.  This section
begins the promised odd-prime generalization (the file's remaining open
question): for an odd prime `q`, the quadratic Gauss sum attached to the
Legendre character `χ_q = quadraticChar (ZMod q)` and any nontrivial `q`-th
root of unity `ζ` in any field `F`,

    `g_q(ζ) = ∑_{a ∈ ZMod q} χ_q(a) · ζ^a`,

satisfies the fundamental orthogonality identity `g_q(ζ)² = χ_q(−1) · q`.
Unlike the conductor-8 case this cannot be settled by finite case-checking
(`q` is arbitrary); the proof is the classical two-variable substitution
`b = a·c`, which needs exactly two orthogonality inputs:

* `∑_c χ_q(c) = 0` — the Legendre character is balanced
  (`quadraticChar_sum_zero`), and
* `∑_a ζ^{ak} = 0` for `k ≠ 0` — nontrivial root-of-unity modes vanish,
  proved here by the shift trick `ζ·S = S` (no `geom_sum` needed).

Combined with Frobenius covariance `g^p = χ_q(p)·g` in `GaloisField p k` (the
odd-`q` analogue of `gaussSumK2_pow_char`) this identity yields full quadratic
reciprocity with no appeal to `jacobiSym.quadratic_reciprocity`; that assembly
is the remaining step of the programme. -/

section GaussSumOddPrime

variable {q : ℕ} [Fact q.Prime] {F : Type*} [Field F]

omit [Fact q.Prime] in
/-- Exponent folding: a `q`-th root of unity only sees exponents mod `q`. -/
theorem pow_mod_of_pow_eq_one {ζ : F} (hζ : ζ ^ q = 1) (m : ℕ) :
    ζ ^ m = ζ ^ (m % q) := by
  conv_lhs => rw [← Nat.div_add_mod m q]
  rw [pow_add, pow_mul, hζ, one_pow, one_mul]

/-- Additivity of the exponential through `ZMod q`:
`ζ^{(a+b).val} = ζ^{a.val} · ζ^{b.val}` whenever `ζ^q = 1`. -/
theorem pow_val_add {ζ : F} (hζ : ζ ^ q = 1) (a b : ZMod q) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [ZMod.val_add, ← pow_mod_of_pow_eq_one hζ, pow_add]

/-- **Root-of-unity orthogonality, constant mode:** a nontrivial `q`-th root of
unity sums to zero over `ZMod q`.  Shift trick: multiplying the sum by `ζ`
permutes its terms (`a ↦ a + 1`), so `(ζ − 1)·S = 0`, and `ζ ≠ 1` forces
`S = 0`. -/
theorem sum_pow_val_eq_zero {ζ : F} (hζ : ζ ^ q = 1) (hζ1 : ζ ≠ 1) :
    ∑ a : ZMod q, ζ ^ a.val = 0 := by
  have hshift : ζ * ∑ a : ZMod q, ζ ^ a.val = ∑ a : ZMod q, ζ ^ a.val := by
    rw [Finset.mul_sum]
    calc ∑ a : ZMod q, ζ * ζ ^ a.val
        = ∑ a : ZMod q, ζ ^ (a + 1).val := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [pow_val_add hζ a 1, ZMod.val_one, pow_one, mul_comm]
      _ = ∑ a : ZMod q, ζ ^ a.val :=
          Fintype.sum_equiv (Equiv.addRight (1 : ZMod q)) _ _ fun a => rfl
  have h0 : (ζ - 1) * ∑ a : ZMod q, ζ ^ a.val = 0 := by
    rw [sub_mul, one_mul, hshift, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd (sub_eq_zero.mp h) hζ1
  · exact h

/-- **Root-of-unity orthogonality, all nonzero modes:** for `k ≠ 0` in `ZMod q`
the twisted sum `∑_a ζ^{(a·k).val}` vanishes — the substitution `a ↦ a·k`
permutes `ZMod q`. -/
theorem sum_pow_val_mul_eq_zero {ζ : F} (hζ : ζ ^ q = 1) (hζ1 : ζ ≠ 1)
    {k : ZMod q} (hk : k ≠ 0) :
    ∑ a : ZMod q, ζ ^ (a * k).val = 0 := by
  calc ∑ a : ZMod q, ζ ^ (a * k).val
      = ∑ a : ZMod q, ζ ^ a.val :=
        Fintype.sum_equiv (Equiv.mulRight₀ k hk) _ _ fun a => rfl
    _ = 0 := sum_pow_val_eq_zero hζ hζ1

/-- The odd-prime quadratic Gauss sum: `g_q(ζ) = ∑_{a ∈ ZMod q} χ_q(a)·ζ^a`
with `χ_q = quadraticChar (ZMod q)` the Legendre character, over an arbitrary
field `F` with a chosen `q`-th root of unity `ζ`.  The odd-prime analogue of
`gaussSumK2`. -/
def gaussSumLegendre (q : ℕ) [Fact q.Prime] (F : Type*) [Field F] (ζ : F) : F :=
  ∑ a : ZMod q, ((quadraticChar (ZMod q) a : ℤ) : F) * ζ ^ a.val

/-- **The fundamental Gauss-sum identity `g_q² = χ_q(−1)·q`** for an odd prime
`q`, over any field `F` and any nontrivial `q`-th root of unity `ζ`.

Proof (classical substitution): expand
`g² = ∑_a ∑_b χ(a)χ(b) ζ^{a+b}`; the `a = 0` slice dies (`χ(0) = 0`); for
`a ≠ 0` substitute `b = a·c`, so `χ(a)χ(ac) = χ(a)²χ(c) = χ(c)` and the sum
becomes `∑_c χ(c) ∑_{a≠0} ζ^{a(1+c)}`.  The inner sum is `q − 1` at `c = −1`
and `−1` otherwise (root-of-unity orthogonality), so the total is
`χ(−1)(q−1) − ∑_{c≠−1} χ(c) = χ(−1)·q` by the balanced-character relation. -/
theorem gaussSumLegendre_sq (hq2 : q ≠ 2) {ζ : F} (hζ : ζ ^ q = 1) (hζ1 : ζ ≠ 1) :
    gaussSumLegendre q F ζ ^ 2 = ((quadraticChar (ZMod q) (-1) : ℤ) : F) * (q : F) := by
  have hchar : ringChar (ZMod q) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; exact hq2
  -- the character with values in `F`, and its three working properties
  have hχ_zero : ((quadraticChar (ZMod q) (0 : ZMod q) : ℤ) : F) = 0 := by
    rw [quadraticChar_zero, Int.cast_zero]
  have hχ_sq : ∀ a : ZMod q, a ≠ 0 →
      ((quadraticChar (ZMod q) a : ℤ) : F) * ((quadraticChar (ZMod q) a : ℤ) : F) = 1 := by
    intro a ha
    have h : (quadraticChar (ZMod q) a) ^ 2 = 1 := quadraticChar_sq_one ha
    calc ((quadraticChar (ZMod q) a : ℤ) : F) * ((quadraticChar (ZMod q) a : ℤ) : F)
        = (((quadraticChar (ZMod q) a) ^ 2 : ℤ) : F) := by push_cast; ring
      _ = ((1 : ℤ) : F) := by rw [h]
      _ = 1 := Int.cast_one
  have hχ_sum : ∑ c : ZMod q, ((quadraticChar (ZMod q) c : ℤ) : F) = 0 := by
    rw [← Int.cast_sum, quadraticChar_sum_zero hchar, Int.cast_zero]
  -- Step 1: expand the square and merge the exponentials.
  have hsq : gaussSumLegendre q F ζ ^ 2
      = ∑ a : ZMod q, ∑ b : ZMod q,
          ((quadraticChar (ZMod q) a : ℤ) : F) * ((quadraticChar (ZMod q) b : ℤ) : F)
            * ζ ^ (a + b).val := by
    rw [sq, gaussSumLegendre, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [pow_val_add hζ a b]
    ring
  -- Step 2: kill the `a = 0` slice, and substitute `b = a·c` on each `a ≠ 0` slice.
  have hslice : ∀ a : ZMod q, a ≠ 0 →
      ∑ b : ZMod q,
          ((quadraticChar (ZMod q) a : ℤ) : F) * ((quadraticChar (ZMod q) b : ℤ) : F)
            * ζ ^ (a + b).val
        = ∑ c : ZMod q, ((quadraticChar (ZMod q) c : ℤ) : F) * ζ ^ (a * (1 + c)).val := by
    intro a ha
    calc ∑ b : ZMod q,
            ((quadraticChar (ZMod q) a : ℤ) : F) * ((quadraticChar (ZMod q) b : ℤ) : F)
              * ζ ^ (a + b).val
        = ∑ c : ZMod q,
            ((quadraticChar (ZMod q) a : ℤ) : F) * ((quadraticChar (ZMod q) (a * c) : ℤ) : F)
              * ζ ^ (a + a * c).val :=
          (Fintype.sum_equiv (Equiv.mulLeft₀ a ha) _ _ fun c => rfl).symm
      _ = ∑ c : ZMod q, ((quadraticChar (ZMod q) c : ℤ) : F) * ζ ^ (a * (1 + c)).val := by
          refine Finset.sum_congr rfl fun c _ => ?_
          have hmul : ((quadraticChar (ZMod q) (a * c) : ℤ) : F)
              = ((quadraticChar (ZMod q) a : ℤ) : F) * ((quadraticChar (ZMod q) c : ℤ) : F) := by
            rw [map_mul]; push_cast; ring
          have harg : a + a * c = a * (1 + c) := by ring
          rw [hmul, harg, ← mul_assoc, hχ_sq a ha, one_mul]
  -- Step 3: the inner `a`-sum over `univ.erase 0`, for each fixed `c`.
  have hinner : ∀ c : ZMod q,
      ∑ a ∈ Finset.univ.erase (0 : ZMod q), ζ ^ (a * (1 + c)).val
        = (∑ a : ZMod q, ζ ^ (a * (1 + c)).val) - 1 := by
    intro c
    have h := Finset.sum_erase_add Finset.univ (fun a : ZMod q => ζ ^ (a * (1 + c)).val)
      (Finset.mem_univ (0 : ZMod q))
    simp only [zero_mul, ZMod.val_zero, pow_zero] at h
    exact eq_sub_of_add_eq h
  -- Step 4: the full twisted sums — `0` off the peak, `q` at the peak `c = −1`.
  have hT_ne : ∀ c : ZMod q, c ≠ -1 → ∑ a : ZMod q, ζ ^ (a * (1 + c)).val = 0 := by
    intro c hc
    refine sum_pow_val_mul_eq_zero hζ hζ1 ?_
    intro h0
    exact hc (by linear_combination h0)
  have hT_neg_one : ∑ a : ZMod q, ζ ^ (a * (1 + (-1 : ZMod q))).val = (q : F) := by
    have hzero : (1 : ZMod q) + (-1) = 0 := by ring
    calc ∑ a : ZMod q, ζ ^ (a * (1 + (-1 : ZMod q))).val
        = ∑ _a : ZMod q, (1 : F) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [hzero, mul_zero, ZMod.val_zero, pow_zero]
      _ = (Fintype.card (ZMod q) : F) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      _ = (q : F) := by rw [ZMod.card]
  -- Step 5: assemble.
  calc gaussSumLegendre q F ζ ^ 2
      = ∑ a : ZMod q, ∑ b : ZMod q,
          ((quadraticChar (ZMod q) a : ℤ) : F) * ((quadraticChar (ZMod q) b : ℤ) : F)
            * ζ ^ (a + b).val := hsq
    _ = ∑ a ∈ Finset.univ.erase (0 : ZMod q), (∑ b : ZMod q,
          ((quadraticChar (ZMod q) a : ℤ) : F) * ((quadraticChar (ZMod q) b : ℤ) : F)
            * ζ ^ (a + b).val)
        + ∑ b : ZMod q,
            ((quadraticChar (ZMod q) (0 : ZMod q) : ℤ) : F)
              * ((quadraticChar (ZMod q) b : ℤ) : F) * ζ ^ ((0 : ZMod q) + b).val :=
        (Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (0 : ZMod q))).symm
    _ = ∑ a ∈ Finset.univ.erase (0 : ZMod q), (∑ c : ZMod q,
          ((quadraticChar (ZMod q) c : ℤ) : F) * ζ ^ (a * (1 + c)).val) + 0 := by
        congr 1
        · exact Finset.sum_congr rfl fun a ha => hslice a (Finset.ne_of_mem_erase ha)
        · exact Finset.sum_eq_zero fun b _ => by rw [hχ_zero, zero_mul, zero_mul]
    _ = ∑ c : ZMod q, ∑ a ∈ Finset.univ.erase (0 : ZMod q),
          ((quadraticChar (ZMod q) c : ℤ) : F) * ζ ^ (a * (1 + c)).val := by
        rw [add_zero, Finset.sum_comm]
    _ = ∑ c : ZMod q, ((quadraticChar (ZMod q) c : ℤ) : F)
          * ((∑ a : ZMod q, ζ ^ (a * (1 + c)).val) - 1) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [← Finset.mul_sum, hinner c]
    _ = ∑ c : ZMod q, (((quadraticChar (ZMod q) c : ℤ) : F)
          * (∑ a : ZMod q, ζ ^ (a * (1 + c)).val))
        - ∑ c : ZMod q, ((quadraticChar (ZMod q) c : ℤ) : F) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        ring
    _ = ∑ c : ZMod q, (((quadraticChar (ZMod q) c : ℤ) : F)
          * (∑ a : ZMod q, ζ ^ (a * (1 + c)).val)) := by
        rw [hχ_sum, sub_zero]
    _ = ((quadraticChar (ZMod q) (-1) : ℤ) : F) * (q : F) := by
        rw [Finset.sum_eq_single (-1 : ZMod q)
          (fun c _ hc => by rw [hT_ne c hc, mul_zero])
          (fun habs => absurd (Finset.mem_univ _) habs)]
        rw [hT_neg_one]

/-- The Gauss-sum identity in Legendre-symbol form:
`g_q² = (−1 / q)·q` (`legendreSym q (−1)` is the first-supplement value). -/
theorem gaussSumLegendre_sq_legendreSym (hq2 : q ≠ 2) {ζ : F} (hζ : ζ ^ q = 1)
    (hζ1 : ζ ≠ 1) :
    gaussSumLegendre q F ζ ^ 2 = ((legendreSym q (-1) : ℤ) : F) * (q : F) := by
  have h : legendreSym q (-1) = quadraticChar (ZMod q) (-1 : ZMod q) := by
    simp [legendreSym]
  rw [gaussSumLegendre_sq hq2 hζ hζ1, h]

/-- **Nonvanishing of the Gauss sum** whenever `q ≠ 0` in `F` (e.g. in
characteristic `p ≠ q` — the situation of the Frobenius-descent argument):
from `g² = χ(−1)·q` and `χ(−1)² = 1`, `g = 0` would force `q = 0` in `F`. -/
theorem gaussSumLegendre_ne_zero (hq2 : q ≠ 2) {ζ : F} (hζ : ζ ^ q = 1)
    (hζ1 : ζ ≠ 1) (hqF : (q : F) ≠ 0) :
    gaussSumLegendre q F ζ ≠ 0 := by
  intro h
  have hsq := gaussSumLegendre_sq hq2 hζ hζ1
  rw [h, zero_pow (two_ne_zero)] at hsq
  have hneg : (-1 : ZMod q) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have h1 : (quadraticChar (ZMod q) (-1 : ZMod q)) ^ 2 = 1 := quadraticChar_sq_one hneg
  have hF1 : ((quadraticChar (ZMod q) (-1 : ZMod q) : ℤ) : F) ^ 2 = 1 := by
    rw [← Int.cast_pow, h1, Int.cast_one]
  apply hqF
  calc (q : F) = 1 * (q : F) := (one_mul _).symm
    _ = ((quadraticChar (ZMod q) (-1 : ZMod q) : ℤ) : F) ^ 2 * (q : F) := by rw [hF1]
    _ = ((quadraticChar (ZMod q) (-1 : ZMod q) : ℤ) : F)
          * (((quadraticChar (ZMod q) (-1 : ZMod q) : ℤ) : F) * (q : F)) := by ring
    _ = ((quadraticChar (ZMod q) (-1 : ZMod q) : ℤ) : F) * 0 := by rw [← hsq]
    _ = 0 := mul_zero _

end GaussSumOddPrime

end KroneckerSymbol
