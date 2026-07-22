import Proofs.ElementaryQuadraticReciprocityOQ03OQ02
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

end KroneckerSymbol
