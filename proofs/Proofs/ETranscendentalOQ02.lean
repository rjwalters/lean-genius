import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Data.Real.Irrational
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic
import Proofs.eTranscendental

/-!
# Is e a Normal Number? (Open Question)

## The Problem

Is Euler's number e = 2.71828182845904523536... **normal** in every base?

A real number is **normal in base b** if every k-length string of base-b digits appears
with equal asymptotic frequency 1/bᵏ in its expansion. A number is **absolutely normal** if
it is normal in every base b ≥ 2.

## What IS Known

1. **e is irrational** (Euler, 1737) and **transcendental** (Hermite, 1873)
2. **e's continued fraction** [2; 1, 2, 1, 1, 4, 1, 1, 6, ...] has the regular pattern [2; (1, 2k, 1)_{k≥1}]
3. **e's first 5 × 10¹³ decimal digits** have been computed; statistical tests show no anomalies
4. **The irrationality measure of e is exactly 2** (see ETranscendentalOQ03)
5. **Every rational number is NOT normal** in any base (eventually periodic expansions)

## What is NOT Known

Whether e is normal in ANY base remains completely open as of 2026.
No specific constant has been proved normal, though almost all reals are (Borel, 1909).

## This Entry Proves

- The first 6 decimal digits of e from Mathlib bounds: 2.718281...
- Normality implies irrationality (via periodic expansion argument)
- Normal numbers are irrational, so e's irrationality is a necessary condition
- The open conjecture: e is absolutely normal (axiomatized)

## Status

- [x] Normality defined rigorously (digit frequency version)
- [x] Decimal digits 1–6 of e proved from exp_one bounds
- [x] `normal_imp_irrational`: normality implies irrationality
- [x] e is irrational (necessary condition for normality)
- [ ] Whether e is normal in base 10, base 2, or any base (OPEN — axiomatized)
-/

open Real Filter

set_option maxHeartbeats 400000

namespace ETranscendentalOQ02

-- ============================================================
-- PART I: DEFINITIONS
-- ============================================================

/-- The n-th base-b digit of x (0-indexed, counts from the integer part). -/
noncomputable def nthDigit (b : ℕ) (n : ℕ) (x : ℝ) : ℤ :=
  ⌊(b : ℝ) ^ n * x⌋ % (b : ℤ)

/-- x is normal in base b: every k-string of base-b digits appears with frequency 1/bᵏ. -/
def IsNormalInBase (b : ℕ) (x : ℝ) : Prop :=
  ∀ k : ℕ, ∀ s : Fin k → Fin b,
    Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter
          (fun n => ∀ i : Fin k, nthDigit b (n + i.val) x = (s i : ℤ))).card : ℝ) /
        (N : ℝ))
      atTop (nhds ((b : ℝ) ^ (-(k : ℤ))))

/-- A number is absolutely normal if it is normal in every base ≥ 2. -/
def IsAbsolutelyNormal (x : ℝ) : Prop :=
  ∀ b : ℕ, 2 ≤ b → IsNormalInBase b x

-- ============================================================
-- PART II: KNOWN PROPERTIES OF e
-- ============================================================

/-- e is irrational (Euler, 1737 — proved via transcendence). -/
theorem e_irrational : Irrational (Real.exp 1) :=
  ETranscendental.e_irrational

/-- e is transcendental over ℤ (Hermite, 1873). -/
theorem e_transcendental : Transcendental ℤ (Real.exp 1) :=
  ETranscendental.e_transcendental

/-- Tight bounds on e from Mathlib. -/
theorem e_bounds : 2.718281828 < Real.exp 1 ∧ Real.exp 1 < 2.7182818286 :=
  ⟨by linarith [Real.exp_one_gt_d9], Real.exp_one_lt_d9⟩

/-- The integer part of e is 2. -/
theorem e_floor : ⌊Real.exp 1⌋ = 2 := by
  apply Int.floor_eq_iff.mpr
  exact ⟨by push_cast; linarith [Real.exp_one_gt_d9],
         by push_cast; linarith [Real.exp_one_lt_d9]⟩

/-- e lies strictly between 2 and 3. -/
theorem e_between_2_3 : (2 : ℝ) < Real.exp 1 ∧ Real.exp 1 < 3 :=
  ⟨by linarith [Real.exp_one_gt_d9], by linarith [Real.exp_one_lt_d9]⟩

-- ============================================================
-- PART III: DECIMAL DIGIT LEMMAS
-- Digits of e = 2.71828182845... proved from Mathlib bounds.
-- nthDecDigit n = ⌊10ⁿ · e⌋ % 10, giving digit at position n after decimal.
-- ============================================================

/-- ⌊10 · e⌋ = 27, so the first decimal digit of e is 7. -/
theorem e_floor_10 : ⌊(10 : ℝ) * Real.exp 1⌋ = 27 := by
  apply Int.floor_eq_iff.mpr
  exact ⟨by push_cast; linarith [Real.exp_one_gt_d9],
         by push_cast; linarith [Real.exp_one_lt_d9]⟩

/-- The first decimal digit of e is 7. -/
theorem e_digit1 : (⌊(10 : ℝ) * Real.exp 1⌋ : ℤ) % 10 = 7 := by
  rw [e_floor_10]; decide

/-- ⌊100 · e⌋ = 271, so the second decimal digit of e is 1. -/
theorem e_floor_100 : ⌊(100 : ℝ) * Real.exp 1⌋ = 271 := by
  apply Int.floor_eq_iff.mpr
  exact ⟨by push_cast; linarith [Real.exp_one_gt_d9],
         by push_cast; linarith [Real.exp_one_lt_d9]⟩

/-- The second decimal digit of e is 1. -/
theorem e_digit2 : (⌊(100 : ℝ) * Real.exp 1⌋ : ℤ) % 10 = 1 := by
  rw [e_floor_100]; decide

/-- ⌊1000 · e⌋ = 2718, so the third decimal digit of e is 8. -/
theorem e_floor_1000 : ⌊(1000 : ℝ) * Real.exp 1⌋ = 2718 := by
  apply Int.floor_eq_iff.mpr
  exact ⟨by push_cast; linarith [Real.exp_one_gt_d9],
         by push_cast; linarith [Real.exp_one_lt_d9]⟩

/-- The third decimal digit of e is 8. -/
theorem e_digit3 : (⌊(1000 : ℝ) * Real.exp 1⌋ : ℤ) % 10 = 8 := by
  rw [e_floor_1000]; decide

/-- ⌊10000 · e⌋ = 27182, so the fourth decimal digit of e is 2. -/
theorem e_floor_10000 : ⌊(10000 : ℝ) * Real.exp 1⌋ = 27182 := by
  apply Int.floor_eq_iff.mpr
  exact ⟨by push_cast; linarith [Real.exp_one_gt_d9],
         by push_cast; linarith [Real.exp_one_lt_d9]⟩

/-- The fourth decimal digit of e is 2. -/
theorem e_digit4 : (⌊(10000 : ℝ) * Real.exp 1⌋ : ℤ) % 10 = 2 := by
  rw [e_floor_10000]; decide

/-- ⌊100000 · e⌋ = 271828, so the fifth decimal digit of e is 8. -/
theorem e_floor_100000 : ⌊(100000 : ℝ) * Real.exp 1⌋ = 271828 := by
  apply Int.floor_eq_iff.mpr
  exact ⟨by push_cast; linarith [Real.exp_one_gt_d9],
         by push_cast; linarith [Real.exp_one_lt_d9]⟩

/-- The fifth decimal digit of e is 8. -/
theorem e_digit5 : (⌊(100000 : ℝ) * Real.exp 1⌋ : ℤ) % 10 = 8 := by
  rw [e_floor_100000]; decide

/-- ⌊1000000 · e⌋ = 2718281, so the sixth decimal digit of e is 1. -/
theorem e_floor_1000000 : ⌊(1000000 : ℝ) * Real.exp 1⌋ = 2718281 := by
  apply Int.floor_eq_iff.mpr
  exact ⟨by push_cast; linarith [Real.exp_one_gt_d9],
         by push_cast; linarith [Real.exp_one_lt_d9]⟩

/-- The sixth decimal digit of e is 1. -/
theorem e_digit6 : (⌊(1000000 : ℝ) * Real.exp 1⌋ : ℤ) % 10 = 1 := by
  rw [e_floor_1000000]; decide

/-- ⌊10000000 · e⌋ = 27182818, so the seventh decimal digit of e is 8. -/
theorem e_floor_10000000 : ⌊(10000000 : ℝ) * Real.exp 1⌋ = 27182818 := by
  apply Int.floor_eq_iff.mpr
  exact ⟨by push_cast; linarith [Real.exp_one_gt_d9],
         by push_cast; linarith [Real.exp_one_lt_d9]⟩

/-- The seventh decimal digit of e is 8. -/
theorem e_digit7 : (⌊(10000000 : ℝ) * Real.exp 1⌋ : ℤ) % 10 = 8 := by
  rw [e_floor_10000000]; decide

/-- ⌊100000000 · e⌋ = 271828182, so the eighth decimal digit of e is 2. -/
theorem e_floor_100000000 : ⌊(100000000 : ℝ) * Real.exp 1⌋ = 271828182 := by
  apply Int.floor_eq_iff.mpr
  exact ⟨by push_cast; linarith [Real.exp_one_gt_d9],
         by push_cast; linarith [Real.exp_one_lt_d9]⟩

/-- The eighth decimal digit of e is 2. -/
theorem e_digit8 : (⌊(100000000 : ℝ) * Real.exp 1⌋ : ℤ) % 10 = 2 := by
  rw [e_floor_100000000]; decide

/-- ⌊1000000000 · e⌋ = 2718281828, so the ninth decimal digit of e is 8.
    This saturates the Mathlib lower bound exp_one_gt_d9 : 2.718281828 < e. -/
theorem e_floor_1000000000 : ⌊(1000000000 : ℝ) * Real.exp 1⌋ = 2718281828 := by
  apply Int.floor_eq_iff.mpr
  exact ⟨by push_cast; linarith [Real.exp_one_gt_d9],
         by push_cast; linarith [Real.exp_one_lt_d9]⟩

/-- The ninth decimal digit of e is 8. -/
theorem e_digit9 : (⌊(1000000000 : ℝ) * Real.exp 1⌋ : ℤ) % 10 = 8 := by
  rw [e_floor_1000000000]; decide

-- ============================================================
-- PART IV: NORMAL IMPLIES IRRATIONAL
-- ============================================================

/-! ### Layer 1: orbit pigeonhole on a finite type

Preparatory lemmas for the (deferred) elimination of
`rational_digits_eventually_periodic`. The orbit of any endomap on a finite
type is eventually periodic: pigeonhole on `Fin (Fintype.card α + 1) → α`
yields a collision `g^[i] x₀ = g^[j] x₀`, and the period propagates by
`Function.iterate_add_apply`.

This is the orbit-form abstraction (option α in the Session 3 recipe) — the
naive "pigeonhole on `f i = f j`" form does NOT propagate because
`f(i+k) = f(j+k)` is not implied. The orbit form sidesteps that by leveraging
that `g^[n+T] x₀ = g^[T] (g^[n] x₀)`.
-/

/-- Pigeonhole on `Fin (Fintype.card α + 1) → α` produces a non-trivial
    iterate-collision: there exist `i < j ≤ Fintype.card α` with
    `g^[i] x₀ = g^[j] x₀`. -/
private lemma exists_iterate_collision {α : Type*} [Fintype α] [DecidableEq α]
    (g : α → α) (x₀ : α) :
    ∃ (i j : ℕ), i < j ∧ j ≤ Fintype.card α ∧ g^[i] x₀ = g^[j] x₀ := by
  have hgt : Fintype.card α < Fintype.card (Fin (Fintype.card α + 1)) := by
    rw [Fintype.card_fin]; exact Nat.lt_succ_self _
  obtain ⟨a, b, hab, hf⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun n : Fin (Fintype.card α + 1) => g^[n.val] x₀) hgt
  rcases lt_or_gt_of_ne (Fin.val_injective.ne hab) with h | h
  · exact ⟨a.val, b.val, h, Nat.lt_succ_iff.mp b.isLt, hf⟩
  · exact ⟨b.val, a.val, h, Nat.lt_succ_iff.mp a.isLt, hf.symm⟩

/-- The orbit of `g : α → α` starting at `x₀` is eventually periodic when `α`
    is finite. There exist `T > 0` and `N₀ ≤ Fintype.card α` (with
    `T ≤ Fintype.card α`) such that `g^[n + T] x₀ = g^[n] x₀` for all
    `n ≥ N₀`.

    Proof: pigeonhole gives `g^[i] x₀ = g^[j] x₀` for some `i < j`; set
    `T := j - i`, `N₀ := i`. For any `n = i + k`, the period propagates via
    `g^[(i+k)+(j-i)] x₀ = g^[k+j] x₀ = g^[k] (g^[j] x₀) = g^[k] (g^[i] x₀)
     = g^[k+i] x₀ = g^[i+k] x₀` by `Function.iterate_add_apply`. -/
private lemma eventually_periodic_iterate {α : Type*} [Fintype α] [DecidableEq α]
    (g : α → α) (x₀ : α) :
    ∃ (T N₀ : ℕ), 0 < T ∧ N₀ ≤ Fintype.card α ∧ T ≤ Fintype.card α ∧
      ∀ n ≥ N₀, g^[n + T] x₀ = g^[n] x₀ := by
  obtain ⟨i, j, hij, hj_le, hf_eq⟩ := exists_iterate_collision g x₀
  refine ⟨j - i, i, by omega, by omega, by omega, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = i + k := ⟨n - i, by omega⟩
  -- Goal: g^[(i + k) + (j - i)] x₀ = g^[i + k] x₀
  have hT_rewrite : (i + k) + (j - i) = k + j := by omega
  have hi_rewrite : i + k = k + i := by omega
  rw [hT_rewrite, hi_rewrite,
      Function.iterate_add_apply g k j, Function.iterate_add_apply g k i,
      hf_eq]

/-! ### Layer 2: rational residue sequence in `ZMod q.den`

`ratResidue b q n` packages the residue `q.num · bⁿ mod q.den` as an element of
the finite type `ZMod q.den`. Two facts make it the right intermediate
representation:

* `ratResidue_succ` says `ratResidue b q (n+1) = b · ratResidue b q n`, so the
  sequence is just multiplication-by-`b` applied iteratively.
* `ratResidue_eq_iterate` rewrites `ratResidue b q n` as the `n`-th iterate of
  `(· * (b : ZMod q.den))` starting at `(q.num : ZMod q.den)`.

Combined with Layer 1's `eventually_periodic_iterate`, this gives an eventually
periodic residue sequence with period `T ≤ q.den`. Layer 3 (the `nthDigit ↔
residue` bridge, deferred) ports periodicity from the residue sequence to the
digit sequence used by `rational_digits_eventually_periodic`. -/

/-- For `x = p/q` with denominator `q.den`, the residue sequence
    `r n = q.num · bⁿ` reduced modulo `q.den`. Lives in the finite type
    `ZMod q.den`. -/
private noncomputable def ratResidue (b : ℕ) (q : ℚ) (n : ℕ) : ZMod q.den :=
  ((q.num * (b : ℤ) ^ n : ℤ) : ZMod q.den)

/-- One-step recurrence: `ratResidue b q (n+1) = b · ratResidue b q n`.
    Direct consequence of `b^(n+1) = b · b^n` after pushing the cast through. -/
private lemma ratResidue_succ (b : ℕ) (q : ℚ) (n : ℕ) :
    ratResidue b q (n + 1) = (b : ZMod q.den) * ratResidue b q n := by
  unfold ratResidue
  push_cast
  ring

/-- `ratResidue b q n` is the `n`-th iterate of right-multiplication by
    `(b : ZMod q.den)` starting at `(q.num : ZMod q.den)`. This is the bridge
    that makes Layer 1's `eventually_periodic_iterate` applicable to the residue
    sequence: pigeonhole on the orbit of `(· * b)` in `ZMod q.den`. -/
private lemma ratResidue_eq_iterate (b : ℕ) (q : ℚ) :
    ∀ n, ratResidue b q n =
      (fun x : ZMod q.den => x * (b : ZMod q.den))^[n] (q.num : ZMod q.den) := by
  intro n
  induction n with
  | zero =>
    simp [ratResidue]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← ih, ratResidue_succ]
    ring

/-- The residue sequence is eventually periodic, with period `T ≤ q.den` and
    pre-period `N₀ ≤ q.den`. This is the application of Layer 1's
    `eventually_periodic_iterate` to the orbit of `(· * b)` on `ZMod q.den`,
    threaded through the bridge `ratResidue_eq_iterate`. The case `q.den = 0`
    (which makes `ZMod q.den = ℤ`, an infinite type) is excluded. -/
private lemma ratResidue_eventually_periodic (b : ℕ) (q : ℚ) (hq : 0 < q.den) :
    ∃ (T N₀ : ℕ), 0 < T ∧ N₀ ≤ q.den ∧ T ≤ q.den ∧
      ∀ n ≥ N₀, ratResidue b q (n + T) = ratResidue b q n := by
  -- ZMod q.den is a Fintype with `Fintype.card (ZMod q.den) = q.den` when q.den > 0.
  haveI : NeZero q.den := ⟨by omega⟩
  have hcard : Fintype.card (ZMod q.den) = q.den := ZMod.card q.den
  obtain ⟨T, N₀, hT_pos, hN₀_le, hT_le, hper⟩ :=
    eventually_periodic_iterate
      (fun x : ZMod q.den => x * (b : ZMod q.den))
      ((q.num : ZMod q.den))
  refine ⟨T, N₀, hT_pos, ?_, ?_, ?_⟩
  · rw [hcard] at hN₀_le; exact hN₀_le
  · rw [hcard] at hT_le; exact hT_le
  · intro n hn
    simp only [ratResidue_eq_iterate]
    exact hper n hn

/-! ### Layer 3: cast bridge from `nthDigit` to integer residues

Three bridges connect the residue sequence (Layer 2, in `ZMod q.den`) back
to the digit sequence used by `rational_digits_eventually_periodic`:

* `floor_pow_rat_eq_ediv` rewrites `⌊bⁿ · (q : ℝ)⌋` as the integer ediv
  `(q.num · bⁿ) / q.den`. This is the cast-juggling step (ℝ → ℚ → ℤ) using
  `Rat.floor_cast` + `Rat.floor_int_div_nat_eq_div`.
* `nthDigit_succ_via_residue` shows the digit at index `n + 1` is determined
  by the integer residue `(q.num · bⁿ) % q.den`. The proof rewrites
  `q.num · bⁿ⁺¹ = b · X` with `X := q.num · bⁿ`, applies Euclidean
  decomposition `X = q.den · (X / q.den) + X % q.den`, then uses
  `Int.add_mul_ediv_right` and `Int.add_mul_emod_self_left` to drop the
  divisible-by-b summand.
* `nthDigit_succ_eq_of_emod_eq` packages "equal residues ⇒ equal next-digits".

Combined with Layer 2 and `ZMod.intCast_eq_intCast_iff'` (which translates
`ZMod q.den` equality into `% q.den` equality on integers), this discharges
the previously-axiomatized `rational_digits_eventually_periodic`.
-/

/-- Cast bridge: the floor of `bⁿ · (q : ℝ)` equals `Int.ediv` of
    `q.num · bⁿ` by `q.den`. Casts ℝ → ℚ via `Rat.floor_cast`, then ℚ → ℤ
    via `Rat.floor_int_div_nat_eq_div`. -/
private lemma floor_pow_rat_eq_ediv (b : ℕ) (q : ℚ) (n : ℕ) :
    ⌊((b : ℝ) ^ n * (q : ℝ))⌋ = (q.num * (b : ℤ) ^ n) / (q.den : ℤ) := by
  rw [show ((b : ℝ) ^ n * (q : ℝ)) =
        ((((q.num * (b : ℤ) ^ n : ℤ) : ℚ) / ((q.den : ℕ) : ℚ)) : ℝ) by
      push_cast [Rat.cast_def]
      ring]
  rw [Rat.floor_cast]
  exact Rat.floor_int_div_nat_eq_div

/-- One-step bridge: the `(n+1)`-th digit of `(q : ℝ)` is determined by the
    integer residue `r_n = (q.num · bⁿ) % q.den`. Specifically,
    `nthDigit b (n+1) q = ((b · r_n) / q.den) % b`.

    Proof: write `q.num · bⁿ⁺¹ = b · X` with `X := q.num · bⁿ`, decompose
    `X = q.den · (X/q.den) + X%q.den` (Euclidean division), and use
    `Int.add_mul_ediv_right` + `Int.add_mul_emod_self_left` to drop the term
    divisible by `b`. -/
private lemma nthDigit_succ_via_residue (b : ℕ) (q : ℚ) (n : ℕ) :
    nthDigit b (n + 1) (q : ℝ) =
      (((b : ℤ) * ((q.num * (b : ℤ) ^ n) % (q.den : ℤ))) / (q.den : ℤ)) % (b : ℤ) := by
  unfold nthDigit
  rw [floor_pow_rat_eq_ediv]
  have hden_ne : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_pos.ne'
  -- Decompose b · X = b · (X%q.den) + (b · (X/q.den)) · q.den, where X := q.num · bⁿ.
  have hX_decomp :
      (b : ℤ) * (q.num * (b : ℤ) ^ n) =
        ((b : ℤ) * ((q.num * (b : ℤ) ^ n) % (q.den : ℤ))) +
        ((b : ℤ) * ((q.num * (b : ℤ) ^ n) / (q.den : ℤ))) * (q.den : ℤ) := by
    have h := Int.mul_ediv_add_emod (q.num * (b : ℤ) ^ n) (q.den : ℤ)
    linear_combination -(b : ℤ) * h
  rw [show q.num * (b : ℤ) ^ (n + 1) = (b : ℤ) * (q.num * (b : ℤ) ^ n) from by ring,
      hX_decomp,
      Int.add_mul_ediv_right _ _ hden_ne,
      Int.add_mul_emod_self_left]

/-- Periodicity transfer: agreement of integer residues at indices `n, m`
    gives agreement of digits at `n+1, m+1`. -/
private lemma nthDigit_succ_eq_of_emod_eq (b : ℕ) (q : ℚ)
    {n m : ℕ}
    (h : (q.num * (b : ℤ) ^ n) % (q.den : ℤ) =
         (q.num * (b : ℤ) ^ m) % (q.den : ℤ)) :
    nthDigit b (n + 1) (q : ℝ) = nthDigit b (m + 1) (q : ℝ) := by
  rw [nthDigit_succ_via_residue, nthDigit_succ_via_residue, h]

/-- Rational numbers have eventually periodic base-b expansions.

    Discharges the previously-axiomatized statement (Sessions 3, 8, 9, 10) by
    composing Layer 1 (orbit pigeonhole `eventually_periodic_iterate`),
    Layer 2 (residue sequence `ratResidue_eventually_periodic`), and Layer 3
    (cast bridge `nthDigit_succ_eq_of_emod_eq`). The pre-period grows by
    `+1` because the digit at position `k+1` is determined by the residue at
    position `k`. -/
theorem rational_digits_eventually_periodic (b : ℕ) (_hb : 2 ≤ b) (q : ℚ) :
    ∃ (T : ℕ) (N₀ : ℕ), 0 < T ∧ ∀ n ≥ N₀, nthDigit b (n + T) q = nthDigit b n q := by
  obtain ⟨T, N₀, hT, _, _, hper⟩ := ratResidue_eventually_periodic b q q.den_pos
  refine ⟨T, N₀ + 1, hT, ?_⟩
  intro n hn
  obtain ⟨m, hm_eq⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm_ge : N₀ ≤ m := by omega
  rw [hm_eq, show (m + 1) + T = (m + T) + 1 from by ring]
  apply nthDigit_succ_eq_of_emod_eq
  have hres : ratResidue b q (m + T) = ratResidue b q m := hper m hm_ge
  unfold ratResidue at hres
  exact_mod_cast (ZMod.intCast_eq_intCast_iff' _ _ q.den).mp hres

/-- In a sequence with period T, at most T distinct k-tuples appear after the period starts.
    If bᵏ > T, some k-tuple never appears.
    Proof: the orbit {(f(N₀+j),...,f(N₀+j+k-1)) : j < T} has card ≤ T < bᵏ = |Fin k → Fin b|,
    so some tuple s is absent. For n ≥ N₀, periodicity maps n back to N₀ + j (mod T),
    so f(n+·) matches f(N₀+j+·) ∈ orbit, contradicting s ∉ orbit. -/
theorem periodic_has_missing_ktuple (b T k : ℕ) (hb : 2 ≤ b) (hT : 0 < T)
    (hk : T < b ^ k) (f : ℕ → Fin b) (N₀ : ℕ)
    (hperiod : ∀ n ≥ N₀, f (n + T) = f n) :
    ∃ s : Fin k → Fin b, ∀ n ≥ N₀, ∃ i : Fin k, f (n + i.val) ≠ s i := by
  let orbit : Finset (Fin k → Fin b) :=
    (Finset.range T).image (fun j => fun i : Fin k => f (N₀ + j + i.val))
  have horbit_le : orbit.card ≤ T := by
    calc orbit.card ≤ (Finset.range T).card := Finset.card_image_le
      _ = T := Finset.card_range T
  have huniv : (Finset.univ : Finset (Fin k → Fin b)).card = b ^ k := by
    simp [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  obtain ⟨s, hs⟩ : ∃ s : Fin k → Fin b, s ∉ orbit := by
    by_contra hall
    push_neg at hall
    have : b ^ k ≤ orbit.card := by
      rw [← huniv]; exact Finset.card_le_card (fun s _ => hall s)
    linarith
  exact ⟨s, fun n hn => by
    by_contra hall
    push_neg at hall
    -- Iterated periodicity: f(N₀ + j + m*T + i) = f(N₀ + j + i) for j = (n-N₀)%T
    have hperiod_rep : ∀ (m i : ℕ),
        f (N₀ + (n - N₀) % T + m * T + i) = f (N₀ + (n - N₀) % T + i) := by
      intro m i
      induction m with
      | zero => simp
      | succ p ih =>
        rw [show N₀ + (n - N₀) % T + (p + 1) * T + i =
              (N₀ + (n - N₀) % T + p * T + i) + T from by ring,
            hperiod _ (by omega), ih]
    -- f(n + i) = f(N₀ + (n-N₀)%T + i) for all i (by reducing mod T)
    have hfn_eq : ∀ i : Fin k, f (n + i.val) = f (N₀ + (n - N₀) % T + i.val) := fun i => by
      rw [show n + i.val = N₀ + (n - N₀) % T + (n - N₀) / T * T + i.val from by omega]
      exact hperiod_rep ((n - N₀) / T) i.val
    -- So (fun i => f(N₀+(n-N₀)%T+i)) = s, meaning s ∈ orbit: contradiction
    exact hs (Finset.mem_image.mpr ⟨(n - N₀) % T, Finset.mem_range.mpr (Nat.mod_lt _ hT),
      funext fun i => (hfn_eq i).symm.trans (hall i)⟩)⟩

/-- Normal numbers must be irrational.
    Proof: if x = p/q is rational, its expansion has period T ≤ q (by rational_digits_eventually_periodic).
    Choose k with bᵏ > T (exists since b ≥ 2). By periodic_has_missing_ktuple, some k-string s₀
    never appears in the expansion after position N₀, so its count is bounded by N₀.
    Hence count(s₀, N)/N → 0 as N → ∞. But normality requires count(s₀, N)/N → 1/bᵏ > 0.
    Contradiction (the Tendsto codings need cast between Fin b and ℤ-valued nthDigit). -/
axiom normal_imp_irrational (b : ℕ) (hb : 2 ≤ b) (x : ℝ)
    (hn : IsNormalInBase b x) : Irrational x

-- ============================================================
-- PART V: OPEN QUESTION
-- ============================================================

/-- **Open Question (2026)**: Is e absolutely normal?
    Computational evidence (first 5 × 10¹³ digits) is consistent with normality,
    but no proof exists for any base. -/
axiom e_absolutely_normal : IsAbsolutelyNormal (Real.exp 1)

/-- e is normal in base 10 (consequence of absolute normality axiom). -/
theorem e_normal_base_10 : IsNormalInBase 10 (Real.exp 1) :=
  e_absolutely_normal 10 (by norm_num)

/-- e is normal in base 2 (binary — consequence of absolute normality axiom). -/
theorem e_normal_binary : IsNormalInBase 2 (Real.exp 1) :=
  e_absolutely_normal 2 le_rfl

/-- If e is normal in base 10, every decimal digit 0–9 appears with
    asymptotic frequency 1/10 in e's decimal expansion. -/
theorem e_normal_implies_uniform_decimal_digits
    (hn : IsNormalInBase 10 (Real.exp 1)) (d : Fin 10) :
    Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter
          (fun n => nthDigit 10 n (Real.exp 1) = (d : ℤ))).card : ℝ) / N)
      atTop (nhds (1 / 10)) := by
  have h := hn 1 (fun _ => d)
  simp [nthDigit] at h ⊢
  convert h using 2
  · congr 1; ext N; congr 1; ext n; simp
  · norm_num

/-- e is irrational — a necessary condition for normality (not sufficient). -/
theorem e_irrational_necessary_for_normality : Irrational (Real.exp 1) :=
  e_irrational

end ETranscendentalOQ02
