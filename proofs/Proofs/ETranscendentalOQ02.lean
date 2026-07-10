import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Data.Real.Irrational
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Order.Filter.Basic
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
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
- [x] `normal_ktuple_infinitely_often` / `normal_imp_disjunctive`: normal ⇒ every
      finite digit-string occurs (infinitely often)
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
  _root_.e_irrational

/-- e is transcendental over ℤ (Hermite, 1873). -/
theorem e_transcendental : Transcendental ℤ (Real.exp 1) :=
  _root_.e_transcendental

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

/-! ### Layer 3a: floor of `b^n · (p/q)` reduces to integer division

Layer 3 — the residue-bridge for `nthDigit b n (p/q)` — factors into two
parts. Part (a), implemented here, discharges the `ℝ → ℤ` cast burden:
for `p : ℤ` and `q : ℕ`, the floor of `b^n · (p/q)` taken in `ℝ` is just
the integer Euclidean quotient `(b^n · p) / q`. Part (b), deferred,
relates this quotient to the residue `(b^n · p) mod q` in the `% b` form
needed by `nthDigit`. Splitting (a) out of (b) keeps the residue algebra
a pure-integer-arithmetic exercise, free of `Real`-side floor lemmas.
-/

/-- Floor of `b^n · (p / q)` (real-valued division) equals `(b^n · p) / q`
    (integer Euclidean division). For `q = 0` both sides reduce to 0 by
    Lean's division convention (`x / 0 = 0`). The proof reduces to
    `Int.floor_div_natCast` after rewriting the real expression as a
    single `ℤ`-cast over a `ℕ`-divisor. -/
private lemma floor_pow_mul_div (b : ℕ) (p : ℤ) (q : ℕ) (n : ℕ) :
    ⌊(b : ℝ) ^ n * ((p : ℝ) / (q : ℝ))⌋ = ((b : ℤ) ^ n * p) / q := by
  have hcast : (b : ℝ) ^ n * ((p : ℝ) / (q : ℝ)) =
      (((b : ℤ) ^ n * p : ℤ) : ℝ) / (q : ℝ) := by
    push_cast
    ring
  rw [hcast, Int.floor_div_natCast, Int.floor_intCast]

/-! ### Layer 3b: residue-bridge for `nthDigit`

Layer 3b is the integer-arithmetic step that connects `nthDigit` to the
ZMod-residue sequence. Given Layer 3a's `floor_pow_mul_div`, the digit at
position `n+1` is determined by `(q.num · b^n) mod q.den` — the integer-valued
form of `ratResidue`. Combined with Layer 2's
`ratResidue_eventually_periodic`, this discharges the previous
`rational_digits_eventually_periodic` axiom (Session 11).
-/

/-- Floor of `(b : ℝ)^n · (q : ℝ)` for `q : ℚ` reduces to integer Euclidean
    division `(q.num · b^n) / q.den`. Combines Layer 3a's `floor_pow_mul_div`
    with `Rat.cast_def` to lift from `(p : ℤ, q : ℕ)` to `q : ℚ`. -/
private lemma floor_pow_rat_eq_ediv (b : ℕ) (q : ℚ) (n : ℕ) :
    ⌊((b : ℝ) ^ n * (q : ℝ))⌋ = (q.num * (b : ℤ) ^ n) / (q.den : ℤ) := by
  have hcast : (b : ℝ) ^ n * (q : ℝ) =
      (b : ℝ) ^ n * ((q.num : ℝ) / (q.den : ℝ)) := by
    push_cast [Rat.cast_def]
    ring
  rw [hcast, floor_pow_mul_div]
  congr 1
  ring

/-- Integer-arithmetic identity used in Layer 3b: for `m ≠ 0` and integers `a, b`,
    `(b · a) / m = b · (a / m) + (b · (a % m)) / m`. Decomposes
    `a = m·(a/m) + (a%m)` and uses `Int.add_mul_ediv_left` to extract the
    multiple-of-m term cleanly. -/
private lemma int_mul_ediv_eq (b a m : ℤ) (hm : m ≠ 0) :
    b * a / m = b * (a / m) + (b * (a % m)) / m := by
  conv_lhs => rw [← Int.ediv_add_emod a m]
  rw [show b * (m * (a / m) + a % m) = b * (a % m) + m * (b * (a / m)) from by ring,
      Int.add_mul_ediv_left _ _ hm,
      add_comm]

/-- **Layer 3b**: the `(n+1)`-th base-b digit of `(q : ℝ)` is determined by the integer
    residue `(q.num · b^n) mod q.den`. Specifically:
    `nthDigit b (n+1) q = (b · ((q.num · b^n) mod q.den) / q.den) mod b`.
    The outer `mod b` is in fact a no-op (since the inner quotient lies in `[0, b)`),
    but we keep it for syntactic uniformity with `nthDigit`. -/
private lemma nthDigit_succ_via_residue (b : ℕ) (q : ℚ) (n : ℕ) :
    nthDigit b (n + 1) (q : ℝ) =
      (((b : ℤ) * ((q.num * (b : ℤ) ^ n) % (q.den : ℤ))) / (q.den : ℤ)) % (b : ℤ) := by
  unfold nthDigit
  rw [floor_pow_rat_eq_ediv]
  set m : ℤ := (q.den : ℤ) with hm_def
  have hm_ne : m ≠ 0 := by
    rw [hm_def]; exact_mod_cast q.den_pos.ne'
  set a : ℤ := q.num * (b : ℤ) ^ n with ha_def
  -- Goal: q.num * b^(n+1) / m % b = (b * (a % m)) / m % b
  have h_pow : q.num * (b : ℤ) ^ (n + 1) = (b : ℤ) * a := by
    rw [ha_def, pow_succ]; ring
  rw [h_pow, int_mul_ediv_eq (b : ℤ) a m hm_ne]
  -- Goal: (b * (a / m) + (b * (a % m)) / m) % b = (b * (a % m)) / m % b
  rw [add_comm, Int.add_mul_emod_self_left]

/-- If integer residues match at positions `n` and `m`, the corresponding digits
    (at positions `n+1` and `m+1`) match. -/
private lemma nthDigit_succ_eq_of_emod_eq (b : ℕ) (q : ℚ) {n m : ℕ}
    (h : (q.num * (b : ℤ) ^ n) % (q.den : ℤ) =
         (q.num * (b : ℤ) ^ m) % (q.den : ℤ)) :
    nthDigit b (n + 1) (q : ℝ) = nthDigit b (m + 1) (q : ℝ) := by
  rw [nthDigit_succ_via_residue, nthDigit_succ_via_residue, h]

/-- **Theorem replacing the previous axiom (Session 11)**: rational numbers have
    eventually periodic base-b expansions. Combines:
    - **Layer 1** (`eventually_periodic_iterate`, S8): orbits in finite types are eventually periodic.
    - **Layer 2** (`ratResidue_eventually_periodic`, S9): the residue sequence
      `(q.num · b^n) mod q.den` is eventually periodic with period `T ≤ q.den` and
      pre-period `N₀ ≤ q.den`.
    - **Layer 3a** (`floor_pow_mul_div`, S10): the `ℝ → ℤ` cast bridge.
    - **Layer 3b** (`nthDigit_succ_via_residue`, this session): the digit at position
      `n+1` is determined solely by the integer residue at position `n`.

    The digit pre-period is `N₀ + 1` (one more than the residue pre-period, since the
    digit at position `n+1` corresponds to the residue at position `n`). -/
theorem rational_digits_eventually_periodic (b : ℕ) (_hb : 2 ≤ b) (q : ℚ) :
    ∃ (T : ℕ) (N₀ : ℕ), 0 < T ∧
      ∀ n ≥ N₀, nthDigit b (n + T) (q : ℝ) = nthDigit b n (q : ℝ) := by
  haveI : NeZero q.den := ⟨q.den_pos.ne'⟩
  obtain ⟨T, N₀, hT_pos, _, _, hper⟩ := ratResidue_eventually_periodic b q q.den_pos
  refine ⟨T, N₀ + 1, hT_pos, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = N₀ + 1 + k := ⟨n - (N₀ + 1), by omega⟩
  have heq1 : N₀ + 1 + k + T = (N₀ + k + T) + 1 := by omega
  have heq2 : N₀ + 1 + k = (N₀ + k) + 1 := by omega
  rw [heq1, heq2]
  apply nthDigit_succ_eq_of_emod_eq
  have h_zmod : ratResidue b q (N₀ + k + T) = ratResidue b q (N₀ + k) :=
    hper (N₀ + k) (Nat.le_add_right _ _)
  unfold ratResidue at h_zmod
  exact (ZMod.intCast_eq_intCast_iff' _ _ _).mp h_zmod

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
      have key : N₀ + (n - N₀) % T + (n - N₀) / T * T = n := by
        rw [Nat.add_assoc, Nat.mod_add_div', Nat.add_sub_cancel' hn]
      rw [show n + i.val = N₀ + (n - N₀) % T + (n - N₀) / T * T + i.val from by rw [key]]
      exact hperiod_rep ((n - N₀) / T) i.val
    -- So (fun i => f(N₀+(n-N₀)%T+i)) = s, meaning s ∈ orbit: contradiction
    exact hs (Finset.mem_image.mpr ⟨(n - N₀) % T, Finset.mem_range.mpr (Nat.mod_lt _ hT),
      funext fun i => (hfn_eq i).symm.trans (hall i)⟩)⟩

-- ============================================================
-- PART IV.5: LAYER 4a — Fin b cast bridge (Session 12)
-- ============================================================

/-!
## Layer 4a: bridging `nthDigit` (ℤ-valued) to `Fin b`

The previous `periodic_has_missing_ktuple` works with `f : ℕ → Fin b`, but
`nthDigit` returns `ℤ` (always in `[0, b)` when `b ≥ 1`). Layer 4a builds
the cast bridge: `nthDigitFin b n x : Fin b` together with the lemma
`nthDigitFin_intCast` showing `((nthDigitFin b n x : ℕ) : ℤ) = nthDigit b n x`.

The headline lemma `rational_has_missing_ktuple` then composes Layers 1–3
(via `rational_digits_eventually_periodic`) with `periodic_has_missing_ktuple`
to assert that for any rational `q`, some `k`-tuple never appears in `(q : ℝ)`'s
base-b expansion past a finite cutoff. This is the structural input for the
full count/Tendsto contradiction argument that closes `normal_imp_irrational`
(slated for Session 13).
-/

/-- The n-th base-b digit is non-negative (it is a `% b` of an integer). -/
private lemma nthDigit_nonneg (b : ℕ) (hb : 0 < b) (n : ℕ) (x : ℝ) :
    0 ≤ nthDigit b n x := by
  unfold nthDigit
  exact Int.emod_nonneg _ (by exact_mod_cast hb.ne')

/-- The n-th base-b digit is strictly less than `b`. -/
private lemma nthDigit_lt_base (b : ℕ) (hb : 0 < b) (n : ℕ) (x : ℝ) :
    nthDigit b n x < (b : ℤ) := by
  unfold nthDigit
  exact Int.emod_lt_of_pos _ (by exact_mod_cast hb)

/-- The `Fin b` form of `nthDigit`: extract the integer-valued digit and pack
    it with its `[0, b)` bound into `Fin b`. -/
private noncomputable def nthDigitFin (b : ℕ) (hb : 0 < b) (n : ℕ) (x : ℝ) : Fin b :=
  ⟨(nthDigit b n x).toNat, by
    have hge : 0 ≤ nthDigit b n x := nthDigit_nonneg b hb n x
    have hlt : nthDigit b n x < (b : ℤ) := nthDigit_lt_base b hb n x
    have : ((nthDigit b n x).toNat : ℤ) = nthDigit b n x := Int.toNat_of_nonneg hge
    omega⟩

/-- The `Fin b` digit casts back to the original ℤ-valued `nthDigit`. -/
private lemma nthDigitFin_intCast (b : ℕ) (hb : 0 < b) (n : ℕ) (x : ℝ) :
    ((nthDigitFin b hb n x : ℕ) : ℤ) = nthDigit b n x := by
  unfold nthDigitFin
  simp only [Fin.val_mk]
  exact Int.toNat_of_nonneg (nthDigit_nonneg b hb n x)

/-- Equality of `Fin b` digits is equivalent to equality of the underlying ℤ digits. -/
private lemma nthDigitFin_eq_iff (b : ℕ) (hb : 0 < b) (n m : ℕ) (x y : ℝ) :
    nthDigitFin b hb n x = nthDigitFin b hb m y ↔
      nthDigit b n x = nthDigit b m y := by
  constructor
  · intro h
    have h1 := nthDigitFin_intCast b hb n x
    have h2 := nthDigitFin_intCast b hb m y
    have hval : (nthDigitFin b hb n x).val = (nthDigitFin b hb m y).val :=
      congrArg Fin.val h
    have hint : ((nthDigitFin b hb n x : ℕ) : ℤ) = ((nthDigitFin b hb m y : ℕ) : ℤ) := by
      exact_mod_cast hval
    linarith [h1, h2, hint]
  · intro h
    apply Fin.ext
    have h1 := nthDigitFin_intCast b hb n x
    have h2 := nthDigitFin_intCast b hb m y
    exact_mod_cast h1.trans (h.trans h2.symm)

/-- **Layer 4a (Session 12)**: For any rational `q : ℚ` and base `b ≥ 2`, the
    base-b expansion of `(q : ℝ)` has a missing `k`-tuple after position `N₀`,
    where `k` and `N₀` are explicit (k = T, N₀ = pre-period from Layer 3).

    Combines:
    - Layer 3 (`rational_digits_eventually_periodic`, S11): periodicity of digits
      with period `T` and pre-period `N₀`.
    - `periodic_has_missing_ktuple` (S11): `T < bᵏ` ⇒ some k-tuple never appears.
    - Layer 4a (this session): cast bridge `nthDigit ↔ nthDigitFin`.

    Choosing `k := T` makes `T < bᵏ` follow from `T < 2^T ≤ b^T` (`Nat.lt_two_pow_self`
    plus `Nat.pow_le_pow_left`).

    This is the structural input for `normal_imp_irrational`: given a missing
    tuple `s`, the count of starting positions in `[0, N)` where the digit
    sequence at offsets `0, …, k-1` matches `s` is bounded by `N₀`, so the
    frequency `→ 0`, contradicting normality which forces frequency `→ b^(-k) > 0`. -/
private theorem rational_has_missing_ktuple (b : ℕ) (hb : 2 ≤ b) (q : ℚ) :
    ∃ (k N₀ : ℕ) (s : Fin k → Fin b),
      0 < k ∧
      ∀ n ≥ N₀, ∃ i : Fin k,
        nthDigitFin b (by omega) (n + i.val) (q : ℝ) ≠ s i := by
  have hbpos : 0 < b := by omega
  -- Step 1: Get period T and pre-period N₀ from Layer 3.
  obtain ⟨T, N₀, hT_pos, hper⟩ := rational_digits_eventually_periodic b hb q
  -- Step 2: Bridge to a `Fin b`-valued sequence.
  let f : ℕ → Fin b := fun n => nthDigitFin b hbpos n (q : ℝ)
  have hper_fin : ∀ n ≥ N₀, f (n + T) = f n := by
    intro n hn
    show nthDigitFin b hbpos (n + T) (q : ℝ) = nthDigitFin b hbpos n (q : ℝ)
    exact (nthDigitFin_eq_iff b hbpos _ _ _ _).mpr (hper n hn)
  -- Step 3: Choose k = T; the bound `T < bᵏ` follows from `T < 2^T ≤ b^T`.
  have hT_lt : T < b ^ T := by
    calc T < 2 ^ T := Nat.lt_two_pow_self
      _ ≤ b ^ T := Nat.pow_le_pow_left (by omega) T
  -- Step 4: Apply `periodic_has_missing_ktuple`.
  obtain ⟨s, hs⟩ := periodic_has_missing_ktuple b T T hb hT_pos hT_lt f N₀ hper_fin
  exact ⟨T, N₀, s, hT_pos, hs⟩

/-- **Layer 4b bridge (Session 13)**: rational missing-tuple lifted to the
    ℤ-valued `nthDigit` form that appears literally inside `IsNormalInBase`. -/
private theorem rational_has_missing_ktuple_intCast (b : ℕ) (hb : 2 ≤ b) (q : ℚ) :
    ∃ (k N₀ : ℕ) (s : Fin k → Fin b),
      0 < k ∧
      ∀ n ≥ N₀, ∃ i : Fin k,
        nthDigit b (n + i.val) (q : ℝ) ≠ (s i : ℤ) := by
  obtain ⟨k, N₀, s, hk_pos, hs⟩ := rational_has_missing_ktuple b hb q
  refine ⟨k, N₀, s, hk_pos, ?_⟩
  intro n hn
  obtain ⟨i, hi⟩ := hs n hn
  refine ⟨i, ?_⟩
  intro hcontra
  apply hi
  apply Fin.ext
  have hbpos : 0 < b := by omega
  have hcast := nthDigitFin_intCast b hbpos (n + i.val) (q : ℝ)
  have : ((nthDigitFin b hbpos (n + i.val) (q : ℝ) : ℕ) : ℤ) = (s i : ℤ) := by
    rw [hcast]; exact hcontra
  exact_mod_cast this

/-- **Count bound (Session 13)**: positions where the digit-tuple matches `s`
    all lie below `N₀`, so the count over any `Finset.range N` is at most `N₀`. -/
private lemma rational_match_count_le (b : ℕ) (q : ℚ) (k N₀ : ℕ) (s : Fin k → Fin b)
    (h : ∀ n ≥ N₀, ∃ i : Fin k,
        nthDigit b (n + i.val) (q : ℝ) ≠ (s i : ℤ))
    (N : ℕ) :
    ((Finset.range N).filter
      (fun n => ∀ i : Fin k, nthDigit b (n + i.val) (q : ℝ) = (s i : ℤ))).card
      ≤ N₀ := by
  refine (Finset.card_le_card (s := _) (t := Finset.range N₀) ?_).trans
    (Finset.card_range N₀).le
  intro n hn
  rw [Finset.mem_filter, Finset.mem_range] at hn
  obtain ⟨_, hmatch⟩ := hn
  rw [Finset.mem_range]
  by_contra hN
  push_neg at hN
  obtain ⟨i, hi⟩ := h n hN
  exact hi (hmatch i)

/-- **Tendsto squeeze (Session 13)**: a sequence bounded above by `N₀` (in `ℕ`)
    has frequency `count_N / N → 0` as `N → ∞`. -/
private lemma tendsto_bounded_count_div_atTop_zero (N₀ : ℕ) (c : ℕ → ℕ)
    (hc : ∀ N, c N ≤ N₀) :
    Tendsto (fun N : ℕ => (c N : ℝ) / (N : ℝ)) atTop (nhds 0) := by
  have h_inv : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h_const_div : Tendsto (fun N : ℕ => (N₀ : ℝ) / (N : ℝ)) atTop (nhds 0) := by
    have : Tendsto (fun N : ℕ => (N₀ : ℝ) * (N : ℝ)⁻¹) atTop (nhds ((N₀ : ℝ) * 0)) :=
      h_inv.const_mul _
    simpa [div_eq_mul_inv] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_const_div
    (Filter.Eventually.of_forall fun N => ?_)
    (Filter.Eventually.of_forall fun N => ?_)
  · positivity
  · rcases Nat.eq_zero_or_pos N with hN | hN
    · simp [hN]
    · have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have h_le : (c N : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hc N
      gcongr

/-- **Normal numbers are irrational (Session 13).**
    Proof: if `x = q : ℚ` is rational, the base-`b` expansion has a missing
    `k`-tuple `s` after some `N₀` (`rational_has_missing_ktuple_intCast`). The
    matching-position count is then bounded by `N₀`, so its frequency tends to
    `0`. Normality forces the same frequency to tend to `b^(-k) > 0`, and the
    uniqueness of limits derives `b^(-k) = 0`, the desired contradiction. -/
theorem normal_imp_irrational (b : ℕ) (hb : 2 ≤ b) (x : ℝ)
    (hn : IsNormalInBase b x) : Irrational x := by
  rintro ⟨q, hq⟩
  subst hq
  obtain ⟨k, N₀, s, hk_pos, hmiss⟩ := rational_has_missing_ktuple_intCast b hb q
  have h_normal := hn k s
  have h_count_le := rational_match_count_le b q k N₀ s hmiss
  have h_zero :
      Tendsto
        (fun N : ℕ =>
          (((Finset.range N).filter
            (fun n => ∀ i : Fin k, nthDigit b (n + i.val) (q : ℝ) = (s i : ℤ))).card : ℝ)
            / (N : ℝ))
        atTop (nhds 0) :=
    tendsto_bounded_count_div_atTop_zero N₀ _ h_count_le
  have heq : (0 : ℝ) = (b : ℝ) ^ (-(k : ℤ)) :=
    tendsto_nhds_unique h_zero h_normal
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hpos : (0 : ℝ) < (b : ℝ) ^ (-(k : ℤ)) := zpow_pos hbR _
  linarith

/-- **Normal numbers are disjunctive (this session).**
    In a number normal in base `b`, every `k`-tuple of digits `s` occurs at
    *infinitely many* starting positions. Proof (the positive companion to
    `normal_imp_irrational`, which instead exhibits a *missing* tuple): if only
    finitely many positions matched `s`, the matching count would be bounded, so
    `tendsto_bounded_count_div_atTop_zero` would force its frequency to tend to
    `0`; but normality forces that same frequency to tend to `b^(-k) > 0`, and
    the uniqueness of limits yields the contradiction `b^(-k) = 0`. -/
theorem normal_ktuple_infinitely_often (b k : ℕ) (hb : 2 ≤ b) (x : ℝ)
    (hn : IsNormalInBase b x) (s : Fin k → Fin b) :
    {n : ℕ | ∀ i : Fin k, nthDigit b (n + i.val) x = (s i : ℤ)}.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  have h_count_le : ∀ N,
      ((Finset.range N).filter
        (fun n => ∀ i : Fin k, nthDigit b (n + i.val) x = (s i : ℤ))).card
        ≤ hfin.toFinset.card := by
    intro N
    refine Finset.card_le_card ?_
    intro n hnmem
    rw [Finset.mem_filter] at hnmem
    exact hfin.mem_toFinset.mpr hnmem.2
  have h_zero :
      Tendsto
        (fun N : ℕ =>
          (((Finset.range N).filter
            (fun n => ∀ i : Fin k, nthDigit b (n + i.val) x = (s i : ℤ))).card : ℝ)
            / (N : ℝ))
        atTop (nhds 0) :=
    tendsto_bounded_count_div_atTop_zero hfin.toFinset.card _ h_count_le
  have h_normal := hn k s
  have heq : (0 : ℝ) = (b : ℝ) ^ (-(k : ℤ)) :=
    tendsto_nhds_unique h_zero h_normal
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hpos : (0 : ℝ) < (b : ℝ) ^ (-(k : ℤ)) := zpow_pos hbR _
  linarith

/-- **Every finite string appears (disjunctivity corollary).**
    A number normal in base `b` contains every `k`-tuple of base-`b` digits at
    some starting position — immediate from the infinitude of matches. -/
theorem normal_imp_disjunctive (b k : ℕ) (hb : 2 ≤ b) (x : ℝ)
    (hn : IsNormalInBase b x) (s : Fin k → Fin b) :
    ∃ n : ℕ, ∀ i : Fin k, nthDigit b (n + i.val) x = (s i : ℤ) :=
  (normal_ktuple_infinitely_often b k hb x hn s).nonempty

-- ============================================================
-- PART IV.6: SHARP BOUNDARY — the converse obstruction to normality
-- ============================================================

/-!
## The non-normality criterion

`normal_imp_disjunctive` shows disjunctivity (every finite digit-string occurs)
is *necessary* for normality. The results below are its exact contrapositive:
if some tuple is *eventually absent*, the number cannot be normal. This is the
precise sharp boundary — normality is strictly stronger than both irrationality
and disjunctivity, and the frequency-`0` of a missing tuple is the obstruction.

The abstract count bound `match_count_le` is the `x`-general form of
`rational_match_count_le`; the final theorem `normal_imp_irrational_of_criterion`
re-derives "normal ⇒ irrational" from the criterion, showing it is non-vacuous
and subsumes the rational case.
-/

/-- **General count bound.** If the `k`-tuple `s` is eventually missing from `x`
    (never fully matched past position `N₀`), the matching starting positions in
    `Finset.range N` number at most `N₀`. The `x`-general core shared by
    `normal_imp_irrational` and the non-normality criterion. -/
private lemma match_count_le (b : ℕ) (x : ℝ) (k N₀ : ℕ) (s : Fin k → Fin b)
    (h : ∀ n ≥ N₀, ∃ i : Fin k, nthDigit b (n + i.val) x ≠ (s i : ℤ))
    (N : ℕ) :
    ((Finset.range N).filter
      (fun n => ∀ i : Fin k, nthDigit b (n + i.val) x = (s i : ℤ))).card
      ≤ N₀ := by
  refine (Finset.card_le_card (s := _) (t := Finset.range N₀) ?_).trans
    (Finset.card_range N₀).le
  intro n hn
  rw [Finset.mem_filter, Finset.mem_range] at hn
  obtain ⟨_, hmatch⟩ := hn
  rw [Finset.mem_range]
  by_contra hN
  push_neg at hN
  obtain ⟨i, hi⟩ := h n hN
  exact hi (hmatch i)

/-- **Sharp boundary: a missing tuple forbids normality.**
    If some `k`-tuple `s` of base-`b` digits is *eventually absent* from `x`
    (never fully matched past position `N₀`), then `x` is **not** normal in
    base `b`. This is the exact converse of `normal_imp_disjunctive`:
    disjunctivity is *necessary* for normality, so its failure rules normality
    out. Proof mirrors `normal_imp_irrational`: the matching-position count is
    bounded by `N₀`, so its frequency tends to `0`, while normality forces it to
    tend to `b^(-k) > 0`; uniqueness of limits yields `b^(-k) = 0`. -/
theorem not_normal_of_eventually_missing_ktuple (b : ℕ) (hb : 2 ≤ b) (x : ℝ)
    (k N₀ : ℕ) (s : Fin k → Fin b)
    (hmiss : ∀ n ≥ N₀, ∃ i : Fin k, nthDigit b (n + i.val) x ≠ (s i : ℤ)) :
    ¬ IsNormalInBase b x := by
  intro hn
  have h_count_le := match_count_le b x k N₀ s hmiss
  have h_zero :
      Tendsto
        (fun N : ℕ =>
          (((Finset.range N).filter
            (fun n => ∀ i : Fin k, nthDigit b (n + i.val) x = (s i : ℤ))).card : ℝ)
            / (N : ℝ))
        atTop (nhds 0) :=
    tendsto_bounded_count_div_atTop_zero N₀ _ h_count_le
  have h_normal := hn k s
  have heq : (0 : ℝ) = (b : ℝ) ^ (-(k : ℤ)) :=
    tendsto_nhds_unique h_zero h_normal
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hpos : (0 : ℝ) < (b : ℝ) ^ (-(k : ℤ)) := zpow_pos hbR _
  linarith

/-- **A single missing digit forbids normality.**
    If a digit `d` is eventually absent from the base-`b` expansion of `x`, then
    `x` is not normal in base `b`. The `k = 1` case of
    `not_normal_of_eventually_missing_ktuple` — the cleanest obstruction to
    normality (a frequency-`0` digit). -/
theorem not_normal_of_eventually_missing_digit (b : ℕ) (hb : 2 ≤ b) (x : ℝ)
    (d : Fin b) (N₀ : ℕ) (hmiss : ∀ n ≥ N₀, nthDigit b n x ≠ (d : ℤ)) :
    ¬ IsNormalInBase b x :=
  not_normal_of_eventually_missing_ktuple b hb x 1 N₀ (fun _ => d)
    (fun n hn => ⟨0, by simpa using hmiss n hn⟩)

/-- **The criterion subsumes `normal_imp_irrational`.**
    Every rational has an eventually-missing tuple
    (`rational_has_missing_ktuple_intCast`), so the non-normality criterion
    recovers "normal ⇒ irrational" as a special case — confirming the criterion
    is non-vacuous and strictly generalises the rational obstruction. -/
theorem normal_imp_irrational_of_criterion (b : ℕ) (hb : 2 ≤ b) (x : ℝ)
    (hn : IsNormalInBase b x) : Irrational x := by
  rintro ⟨q, hq⟩
  subst hq
  obtain ⟨k, N₀, s, _, hmiss⟩ := rational_has_missing_ktuple_intCast b hb q
  exact not_normal_of_eventually_missing_ktuple b hb (q : ℝ) k N₀ s hmiss hn

-- ============================================================
-- PART IV.7: FREQUENCY-MISMATCH CRITERION
-- ============================================================

/-!
## From absence to frequency anomaly

`not_normal_of_eventually_missing_ktuple` handles the extreme case of a tuple
whose matching frequency is `0`. The results below generalise it to *any*
frequency anomaly. If the matching frequency of a tuple `s` converges to a limit
`L ≠ b^{-k}`, or merely stays *eventually bounded away* from `b^{-k}` on one
side, then `x` cannot be normal in base `b`.

The `tendsto`-form (`not_normal_of_match_freq_tendsto_ne`) is the exact converse
of the definition, via uniqueness of limits. The one-sided `eventually` forms
(`_eventually_le` / `_eventually_ge`) are strictly stronger: they never assume
the frequency converges at all, only that it stays on the wrong side of a
threshold separated from `b^{-k}` — capturing *under-* and *over-representation*,
not just outright absence. The single-digit specialisation
`not_normal_of_digit_freq_tendsto_ne` records the familiar statement "a digit
occurring with density `≠ 1/b` forbids normality".
-/

/-- **Frequency-mismatch criterion (`k`-tuple form).** If the matching frequency
    of the tuple `s` converges to a limit `L ≠ b^{-k}`, then `x` is not normal in
    base `b`. Immediate from uniqueness of limits: normality forces the very same
    frequency to converge to `b^{-k}`. Generalises
    `not_normal_of_eventually_missing_ktuple`, which is the `L = 0` instance. -/
theorem not_normal_of_match_freq_tendsto_ne (b : ℕ) (hb : 2 ≤ b) (x : ℝ)
    (k : ℕ) (s : Fin k → Fin b) (L : ℝ)
    (hlim : Tendsto
        (fun N : ℕ =>
          (((Finset.range N).filter
            (fun n => ∀ i : Fin k, nthDigit b (n + i.val) x = (s i : ℤ))).card : ℝ)
            / (N : ℝ))
        atTop (nhds L))
    (hne : L ≠ (b : ℝ) ^ (-(k : ℤ))) :
    ¬ IsNormalInBase b x := by
  intro hn
  exact hne (tendsto_nhds_unique hlim (hn k s))

/-- **Under-representation forbids normality.** If the matching frequency of `s`
    is *eventually* at most some `c < b^{-k}`, then `x` is not normal — no
    convergence of the frequency itself is assumed. Choosing `c` strictly between
    `0` and `b^{-k}` recovers the eventually-missing obstruction. -/
theorem not_normal_of_match_freq_eventually_le (b : ℕ) (hb : 2 ≤ b) (x : ℝ)
    (k : ℕ) (s : Fin k → Fin b) (c : ℝ)
    (hc : c < (b : ℝ) ^ (-(k : ℤ)))
    (hbound : ∀ᶠ N in atTop,
        (((Finset.range N).filter
          (fun n => ∀ i : Fin k, nthDigit b (n + i.val) x = (s i : ℤ))).card : ℝ)
          / (N : ℝ) ≤ c) :
    ¬ IsNormalInBase b x := by
  intro hn
  have hle : (b : ℝ) ^ (-(k : ℤ)) ≤ c := le_of_tendsto (hn k s) hbound
  linarith

/-- **Over-representation forbids normality.** Dual of
    `not_normal_of_match_freq_eventually_le`: if the matching frequency of `s` is
    *eventually* at least some `c > b^{-k}`, then `x` is not normal. Again no
    convergence of the frequency is assumed. -/
theorem not_normal_of_match_freq_eventually_ge (b : ℕ) (hb : 2 ≤ b) (x : ℝ)
    (k : ℕ) (s : Fin k → Fin b) (c : ℝ)
    (hc : (b : ℝ) ^ (-(k : ℤ)) < c)
    (hbound : ∀ᶠ N in atTop,
        c ≤ (((Finset.range N).filter
          (fun n => ∀ i : Fin k, nthDigit b (n + i.val) x = (s i : ℤ))).card : ℝ)
          / (N : ℝ)) :
    ¬ IsNormalInBase b x := by
  intro hn
  have hge : c ≤ (b : ℝ) ^ (-(k : ℤ)) := ge_of_tendsto (hn k s) hbound
  linarith

/-- **Single-digit frequency-mismatch criterion.** If a digit `d` occurs in the
    base-`b` expansion of `x` with limiting frequency `L ≠ 1/b`, then `x` is not
    normal in base `b`. The `k = 1` case of `not_normal_of_match_freq_tendsto_ne`,
    recording the intuition that normality demands every digit at density `1/b`
    (`b^{-1} = b⁻¹`). Generalises `not_normal_of_eventually_missing_digit`, which
    is the `L = 0` instance. -/
theorem not_normal_of_digit_freq_tendsto_ne (b : ℕ) (hb : 2 ≤ b) (x : ℝ)
    (d : Fin b) (L : ℝ)
    (hlim : Tendsto
        (fun N : ℕ =>
          (((Finset.range N).filter (fun n => nthDigit b n x = (d : ℤ))).card : ℝ)
            / (N : ℝ))
        atTop (nhds L))
    (hne : L ≠ (b : ℝ)⁻¹) :
    ¬ IsNormalInBase b x := by
  refine not_normal_of_match_freq_tendsto_ne b hb x 1 (fun _ => d) L ?_ ?_
  · simp only [Fin.forall_fin_one, Fin.val_zero, add_zero]
    exact hlim
  · rwa [Nat.cast_one, zpow_neg_one]

/-- **Single-digit under-representation forbids normality.** If a digit `d` occurs
    with frequency *eventually* at most some `c < 1/b`, then `x` is not normal in
    base `b` — no convergence of the frequency is assumed. The `k = 1` case of
    `not_normal_of_match_freq_eventually_le`, and the one-sided eventual companion of
    `not_normal_of_digit_freq_tendsto_ne`. -/
theorem not_normal_of_digit_freq_eventually_le (b : ℕ) (hb : 2 ≤ b) (x : ℝ)
    (d : Fin b) (c : ℝ)
    (hc : c < (b : ℝ)⁻¹)
    (hbound : ∀ᶠ N in atTop,
        (((Finset.range N).filter (fun n => nthDigit b n x = (d : ℤ))).card : ℝ)
          / (N : ℝ) ≤ c) :
    ¬ IsNormalInBase b x := by
  refine not_normal_of_match_freq_eventually_le b hb x 1 (fun _ => d) c ?_ ?_
  · rwa [Nat.cast_one, zpow_neg_one]
  · simp only [Fin.forall_fin_one, Fin.val_zero, add_zero]
    exact hbound

/-- **Single-digit over-representation forbids normality.** Dual of
    `not_normal_of_digit_freq_eventually_le`: if a digit `d` occurs with frequency
    *eventually* at least some `c > 1/b`, then `x` is not normal in base `b`. The
    `k = 1` case of `not_normal_of_match_freq_eventually_ge`. -/
theorem not_normal_of_digit_freq_eventually_ge (b : ℕ) (hb : 2 ≤ b) (x : ℝ)
    (d : Fin b) (c : ℝ)
    (hc : (b : ℝ)⁻¹ < c)
    (hbound : ∀ᶠ N in atTop,
        c ≤ (((Finset.range N).filter (fun n => nthDigit b n x = (d : ℤ))).card : ℝ)
          / (N : ℝ)) :
    ¬ IsNormalInBase b x := by
  refine not_normal_of_match_freq_eventually_ge b hb x 1 (fun _ => d) c ?_ ?_
  · rwa [Nat.cast_one, zpow_neg_one]
  · simp only [Fin.forall_fin_one, Fin.val_zero, add_zero]
    exact hbound

-- ============================================================
-- PART IV.8: QUANTITATIVE DISJUNCTIVITY
-- ============================================================

/-!
## From "infinitely often" to a positive density

`normal_ktuple_infinitely_often` shows a normal number contains every tuple at
*infinitely many* positions, and `normal_imp_disjunctive` extracts a single
occurrence *somewhere*. Both are purely qualitative. The results below sharpen
them using the fact that normality pins the matching frequency to the strictly
positive value `b^{-k}`:

* `exists_match_lt_of_count_pos` is the pure-`Finset` bridge: a positive matching
  count over `range N` yields an explicit occurrence *below* `N`.
* `eventually_exists_match_lt_of_normal` upgrades disjunctivity to an
  effective-flavoured form — for a normal `x`, the tuple `s` occurs *before every
  sufficiently large window* `N`, not merely somewhere. (The bare definition of
  normality carries no convergence *rate*, so the position of the first
  occurrence cannot be bounded by an explicit function of `k`; but "occurs before
  every large `N`" is the strongest unconditional statement, and it pins the
  first occurrence below any effective threshold at which the count is known
  positive.)
* `match_count_ge_linear_of_normal` is the density statement: the number of
  occurrences of `s` below `N` is eventually at least `(b^{-k}/2)·N`, so the
  occurrence set has positive lower density (in fact density exactly `b^{-k}`).
  This strictly strengthens `normal_ktuple_infinitely_often`.
-/

/-- **Occurrence-extraction core.** If the count of tuple-`s` matches over
    `Finset.range N` is positive, an explicit matching position `< N` exists.
    The pure-`Finset` bridge underlying the quantitative statements below;
    carries no normality hypothesis. -/
theorem exists_match_lt_of_count_pos (b : ℕ) (x : ℝ) (k : ℕ) (s : Fin k → Fin b)
    (N : ℕ)
    (hpos : 0 < ((Finset.range N).filter
        (fun n => ∀ i : Fin k, nthDigit b (n + i.val) x = (s i : ℤ))).card) :
    ∃ n < N, ∀ i : Fin k, nthDigit b (n + i.val) x = (s i : ℤ) := by
  obtain ⟨n, hn⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter, Finset.mem_range] at hn
  exact ⟨n, hn.1, hn.2⟩

/-- **The matching count is eventually positive.** For a number normal in base
    `b`, the number of positions below `N` at which the tuple `s` matches is
    positive for all sufficiently large `N`. Proof: normality forces the
    frequency `count/N → b^{-k} > 0`, so eventually `count/N > 0`, whence
    (using `N ≥ 1`) `count > 0`. -/
theorem eventually_match_count_pos_of_normal (b : ℕ) (hb : 2 ≤ b) (x : ℝ)
    (hn : IsNormalInBase b x) (k : ℕ) (s : Fin k → Fin b) :
    ∀ᶠ N in atTop, 0 < ((Finset.range N).filter
        (fun n => ∀ i : Fin k, nthDigit b (n + i.val) x = (s i : ℤ))).card := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hposk : (0 : ℝ) < (b : ℝ) ^ (-(k : ℤ)) := zpow_pos hbR _
  have hev : ∀ᶠ N in atTop, (0 : ℝ) <
      (((Finset.range N).filter
        (fun n => ∀ i : Fin k, nthDigit b (n + i.val) x = (s i : ℤ))).card : ℝ)
        / (N : ℝ) :=
    (hn k s).eventually_const_lt hposk
  filter_upwards [hev, eventually_ge_atTop 1] with N hN _
  set c := ((Finset.range N).filter
      (fun n => ∀ i : Fin k, nthDigit b (n + i.val) x = (s i : ℤ))).card with hc
  rcases Nat.eq_zero_or_pos c with h0 | hpos
  · exfalso; rw [h0] at hN; simp at hN
  · exact hpos

/-- **Effective disjunctivity.** For a number normal in base `b`, the tuple `s`
    occurs at some position *below* `N` for every sufficiently large `N`. This
    strengthens `normal_imp_disjunctive` (one occurrence somewhere) to a bound
    relative to every large window. Immediate from
    `eventually_match_count_pos_of_normal` and the occurrence-extraction core. -/
theorem eventually_exists_match_lt_of_normal (b : ℕ) (hb : 2 ≤ b) (x : ℝ)
    (hn : IsNormalInBase b x) (k : ℕ) (s : Fin k → Fin b) :
    ∀ᶠ N in atTop,
      ∃ n < N, ∀ i : Fin k, nthDigit b (n + i.val) x = (s i : ℤ) := by
  filter_upwards [eventually_match_count_pos_of_normal b hb x hn k s] with N hN
  exact exists_match_lt_of_count_pos b x k s N hN

/-- **Positive lower density of occurrences.** For a number normal in base `b`,
    the number of positions below `N` at which the tuple `s` matches is eventually
    at least `(b^{-k}/2)·N`. Hence the occurrence set has positive lower density
    (in fact density exactly `b^{-k}`), strictly strengthening the qualitative
    `normal_ktuple_infinitely_often`. Proof: normality gives `count/N → b^{-k}`,
    so eventually `count/N > b^{-k}/2`; clearing the (positive) denominator yields
    the linear bound. -/
theorem match_count_ge_linear_of_normal (b : ℕ) (hb : 2 ≤ b) (x : ℝ)
    (hn : IsNormalInBase b x) (k : ℕ) (s : Fin k → Fin b) :
    ∀ᶠ N : ℕ in atTop,
      ((b : ℝ) ^ (-(k : ℤ)) / 2) * (N : ℝ) ≤
        (((Finset.range N).filter
          (fun n => ∀ i : Fin k, nthDigit b (n + i.val) x = (s i : ℤ))).card : ℝ) := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hposk : (0 : ℝ) < (b : ℝ) ^ (-(k : ℤ)) := zpow_pos hbR _
  have hhalf : (b : ℝ) ^ (-(k : ℤ)) / 2 < (b : ℝ) ^ (-(k : ℤ)) := by linarith
  have hev : ∀ᶠ N in atTop, (b : ℝ) ^ (-(k : ℤ)) / 2 <
      (((Finset.range N).filter
        (fun n => ∀ i : Fin k, nthDigit b (n + i.val) x = (s i : ℤ))).card : ℝ)
        / (N : ℝ) :=
    (hn k s).eventually_const_lt hhalf
  filter_upwards [hev, eventually_gt_atTop 0] with N hN hN0
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hmul := mul_lt_mul_of_pos_right hN hNR
  rw [div_mul_cancel₀ _ hNR.ne'] at hmul
  exact le_of_lt hmul

-- ============================================================
-- PART IV.9: EFFECTIVE NORMALITY WITH AN EXPLICIT MODULUS
-- ============================================================

/-!
## Effective first-occurrence bounds via a modulus of convergence

`IsNormalInBase` is a bare `Tendsto` statement: it carries no *rate* of
convergence, so — as flagged in `eventually_exists_match_lt_of_normal` — the
position of the first occurrence of a tuple cannot be bounded by an explicit
function of `k`. To obtain genuinely effective bounds one must *supply* a
modulus of convergence.

`EffectivelyNormalWithModulus b x M` asks for an explicit function
`M : ℕ → ℝ → ℕ` such that, for every tuple length `k`, every tuple `s`, and every
tolerance `ε > 0`, the matching frequency of `s` is within `ε` of `b^{-k}` for
all windows `N ≥ M k ε`. This is exactly the `ε`–`N` form of the `Tendsto` in
normality, so it *implies* `IsNormalInBase` (`isNormal_of_effectivelyNormal`);
but it additionally *exposes* the threshold, which upgrades every "eventually"
statement of PART IV.8 to an effective one:

* `first_occurrence_lt_of_modulus` — the tuple `s` occurs at an *explicit*
  position `< max (M k (b^{-k}/2)) 1`, a concrete function of the modulus and `k`.
  This is the effective form of the (non-constructive)
  `eventually_exists_match_lt_of_normal`.
* `match_count_ge_linear_of_modulus` — for every `N ≥ max (M k (b^{-k}/2)) 1` the
  occurrence count is at least `(b^{-k}/2)·N`, the effective (explicit-threshold)
  form of `match_count_ge_linear_of_normal`.
-/

/-- **Effective normality with an explicit modulus of convergence.** A witness
    that `x` is normal in base `b` *together with a rate*: for every tuple `s` of
    length `k` and every tolerance `ε > 0`, the matching frequency of `s` lies
    within `ε` of `b^{-k}` for all windows `N ≥ M k ε`. -/
def EffectivelyNormalWithModulus (b : ℕ) (x : ℝ) (M : ℕ → ℝ → ℕ) : Prop :=
  ∀ (k : ℕ) (s : Fin k → Fin b) (ε : ℝ), 0 < ε → ∀ N : ℕ, M k ε ≤ N →
    |(((Finset.range N).filter
        (fun n => ∀ i : Fin k, nthDigit b (n + i.val) x = (s i : ℤ))).card : ℝ)
        / (N : ℝ) - (b : ℝ) ^ (-(k : ℤ))| < ε

/-- **Effective normality implies normality.** The modulus form is precisely the
    `ε`–`N` (`Metric.tendsto_atTop`) characterisation of the `Tendsto` defining
    `IsNormalInBase`, so any number admitting a modulus of convergence is normal.
    Records that `EffectivelyNormalWithModulus` is a genuine strengthening, not a
    vacuous or incomparable notion. -/
theorem isNormal_of_effectivelyNormal (b : ℕ) (x : ℝ) (M : ℕ → ℝ → ℕ)
    (hM : EffectivelyNormalWithModulus b x M) : IsNormalInBase b x := by
  intro k s
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨M k ε, fun N hN => ?_⟩
  rw [Real.dist_eq]
  exact hM k s ε hε N hN

/-- **Effective first occurrence.** Given a modulus of normality, every tuple `s`
    of length `k` occurs at an *explicit* position below `max (M k (b^{-k}/2)) 1`
    — a concrete function of the modulus and `k`. This is the effective
    strengthening of `eventually_exists_match_lt_of_normal`, whose window bound
    was non-constructive (only "for all sufficiently large `N`"). Proof: at the
    tolerance `ε = b^{-k}/2` the frequency at `N₁ := max (M k ε) 1` is within `ε`
    of `b^{-k}`, hence `> b^{-k}/2 > 0`, so the matching count is positive and the
    occurrence-extraction core produces a witness `< N₁`. -/
theorem first_occurrence_lt_of_modulus (b : ℕ) (hb : 2 ≤ b) (x : ℝ)
    (M : ℕ → ℝ → ℕ) (hM : EffectivelyNormalWithModulus b x M)
    (k : ℕ) (s : Fin k → Fin b) :
    ∃ n < max (M k ((b : ℝ) ^ (-(k : ℤ)) / 2)) 1,
      ∀ i : Fin k, nthDigit b (n + i.val) x = (s i : ℤ) := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hposk : (0 : ℝ) < (b : ℝ) ^ (-(k : ℤ)) := zpow_pos hbR _
  set δ : ℝ := (b : ℝ) ^ (-(k : ℤ)) / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact div_pos hposk two_pos
  set N₁ := max (M k δ) 1 with hN1def
  have hN1pos : 0 < N₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hN1R : (0 : ℝ) < (N₁ : ℝ) := by exact_mod_cast hN1pos
  have hbound := hM k s δ hδpos N₁ (le_max_left _ _)
  set c := ((Finset.range N₁).filter
      (fun n => ∀ i : Fin k, nthDigit b (n + i.val) x = (s i : ℤ))).card with hc
  have habs := abs_lt.mp hbound
  have heq : (b : ℝ) ^ (-(k : ℤ)) - δ = δ := by rw [hδdef]; ring
  have hcpos_real : 0 < (c : ℝ) / (N₁ : ℝ) := by
    have hlow : (b : ℝ) ^ (-(k : ℤ)) - δ < (c : ℝ) / (N₁ : ℝ) := by linarith [habs.1]
    rw [heq] at hlow; linarith
  have hcR : (0 : ℝ) < (c : ℝ) := by
    have := mul_pos hcpos_real hN1R
    rwa [div_mul_cancel₀ _ hN1R.ne'] at this
  have hcpos : 0 < c := by exact_mod_cast hcR
  exact exists_match_lt_of_count_pos b x k s N₁ (hc ▸ hcpos)

/-- **Effective density lower bound.** Given a modulus of normality, for *every*
    window `N ≥ max (M k (b^{-k}/2)) 1` the occurrence count of the tuple `s` is
    at least `(b^{-k}/2)·N`. This is the effective (explicit-threshold) form of
    `match_count_ge_linear_of_normal`, which only held "eventually". -/
theorem match_count_ge_linear_of_modulus (b : ℕ) (hb : 2 ≤ b) (x : ℝ)
    (M : ℕ → ℝ → ℕ) (hM : EffectivelyNormalWithModulus b x M)
    (k : ℕ) (s : Fin k → Fin b) (N : ℕ)
    (hN : max (M k ((b : ℝ) ^ (-(k : ℤ)) / 2)) 1 ≤ N) :
    ((b : ℝ) ^ (-(k : ℤ)) / 2) * (N : ℝ) ≤
      (((Finset.range N).filter
        (fun n => ∀ i : Fin k, nthDigit b (n + i.val) x = (s i : ℤ))).card : ℝ) := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hposk : (0 : ℝ) < (b : ℝ) ^ (-(k : ℤ)) := zpow_pos hbR _
  set δ : ℝ := (b : ℝ) ^ (-(k : ℤ)) / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact div_pos hposk two_pos
  have hMN : M k δ ≤ N := le_trans (le_max_left _ _) hN
  have hN0 : 0 < N := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hN)
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hbound := hM k s δ hδpos N hMN
  set c := ((Finset.range N).filter
      (fun n => ∀ i : Fin k, nthDigit b (n + i.val) x = (s i : ℤ))).card with hc
  have habs := abs_lt.mp hbound
  have heq : (b : ℝ) ^ (-(k : ℤ)) - δ = δ := by rw [hδdef]; ring
  have hlow : δ < (c : ℝ) / (N : ℝ) := by
    have h : (b : ℝ) ^ (-(k : ℤ)) - δ < (c : ℝ) / (N : ℝ) := by linarith [habs.1]
    rwa [heq] at h
  have hmul := mul_lt_mul_of_pos_right hlow hNR
  rw [div_mul_cancel₀ _ hNR.ne'] at hmul
  exact le_of_lt hmul

-- ============================================================
-- PART IV.10: THE CONSERVATION LAW
-- ============================================================

/-!
## Digit-tuple frequencies form a probability distribution

Every base-`b` digit lies in `[0, b)` (`nthDigit_nonneg`, `nthDigit_lt_base`), so
each starting position `n` determines a *unique* `k`-tuple — the block of digits
at offsets `0, …, k-1`. Hence, over `Finset.range N`, the `bᵏ` tuple-match filters
(one per `s : Fin k → Fin b`) **partition** `range N`:

* `sum_match_count_eq` — the exact conservation law `∑ₛ count(s, N) = N`, proved by
  fibering `range N` over the digit-tuple map. No normality is assumed; it is a
  pure combinatorial identity of the digit expansion.
* `sum_matchFreq_eq_one` — dividing by `N` (`N ≥ 1`), the empirical frequencies
  `matchFreq b x k s N` sum to `1`: at every window the tuple frequencies are a
  genuine probability distribution on `Fin k → Fin b`.

The pay-off is **conservation-closure** of normality (`matchFreq_tendsto_of_others`,
`isNormalInBase_of_all_but_one`): because the frequencies sum to `1` and there are
exactly `bᵏ` tuples each demanded to converge to `b^{-k}` (whose total is `1`), the
equidistribution of any *one* tuple is forced by that of all the others. So to
certify normality one may omit an arbitrary block of each length — the conservation
law fills in the last frequency for free.
-/

/-- A `Fin b` digit equals a target `t` iff the underlying ℤ-valued `nthDigit`
    equals `(t : ℤ)`. The pointwise bridge between the `Fin b`-valued digit and
    the ℤ-valued form appearing in `IsNormalInBase`. -/
private lemma nthDigitFin_eq_s_iff (b : ℕ) (hb : 0 < b) (n : ℕ) (x : ℝ) (t : Fin b) :
    nthDigitFin b hb n x = t ↔ nthDigit b n x = (t : ℤ) := by
  have hcast := nthDigitFin_intCast b hb n x
  constructor
  · intro h
    rw [← hcast, h]
  · intro h
    apply Fin.ext
    have h2 : ((nthDigitFin b hb n x : ℕ) : ℤ) = ((t : ℕ) : ℤ) := by
      rw [hcast, h]
    exact_mod_cast h2

/-- The empirical frequency of the `k`-tuple `s` among the first `N` starting
    positions of the base-`b` expansion of `x`. This is exactly the quantity whose
    convergence to `b^{-k}` defines `IsNormalInBase`. -/
noncomputable def matchFreq (b : ℕ) (x : ℝ) (k : ℕ) (s : Fin k → Fin b) (N : ℕ) : ℝ :=
  (((Finset.range N).filter
      (fun n => ∀ i : Fin k, nthDigit b (n + i.val) x = (s i : ℤ))).card : ℝ) / (N : ℝ)

/-- **The conservation law.** Over the first `N` starting positions, the matching
    counts of the `bᵏ` tuples sum to exactly `N`: each position `n` belongs to the
    fiber of a *unique* tuple — the digit block it actually carries — so the
    tuple-match filters partition `Finset.range N`. A pure combinatorial identity
    of the digit expansion; no normality is assumed. -/
theorem sum_match_count_eq (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (k N : ℕ) :
    ∑ s : Fin k → Fin b,
      ((Finset.range N).filter
        (fun n => ∀ i : Fin k, nthDigit b (n + i.val) x = (s i : ℤ))).card = N := by
  classical
  have hbpos : 0 < b := by omega
  -- The fiber map: the digit block actually starting at `n`.
  set F : ℕ → (Fin k → Fin b) := fun n i => nthDigitFin b hbpos (n + i.val) x with hF
  -- A position matches `s` (in the ℤ form) iff its digit block *is* `s`.
  have key : ∀ (n : ℕ) (s : Fin k → Fin b),
      (F n = s) ↔ (∀ i : Fin k, nthDigit b (n + i.val) x = (s i : ℤ)) := by
    intro n s
    rw [funext_iff]
    refine forall_congr' (fun i => ?_)
    simp only [hF]
    exact nthDigitFin_eq_s_iff b hbpos (n + i.val) x (s i)
  -- Each match-filter equals the corresponding fiber.
  have hfilter : ∀ s : Fin k → Fin b,
      (Finset.range N).filter
          (fun n => ∀ i : Fin k, nthDigit b (n + i.val) x = (s i : ℤ))
        = (Finset.range N).filter (fun n => F n = s) := by
    intro s
    ext n
    simp only [Finset.mem_filter]
    exact and_congr_right (fun _ => (key n s).symm)
  -- Rewrite each match-filter to its fiber, then count fiberwise.
  have step1 :
      ∑ s : Fin k → Fin b,
          ((Finset.range N).filter
            (fun n => ∀ i : Fin k, nthDigit b (n + i.val) x = (s i : ℤ))).card
        = ∑ s : Fin k → Fin b,
            ((Finset.range N).filter (fun n => F n = s)).card :=
    Finset.sum_congr rfl (fun s _ => by rw [hfilter s])
  rw [step1]
  exact (Finset.card_eq_sum_card_fiberwise
      (s := Finset.range N) (t := Finset.univ)
      (f := F) (fun n _ => Finset.mem_univ (F n))).symm.trans (Finset.card_range N)

/-- **Frequencies form a probability distribution.** For `N ≥ 1` the empirical
    frequencies of the `bᵏ` tuples sum to `1` — the normalised form of the
    conservation law `sum_match_count_eq`. -/
theorem sum_matchFreq_eq_one (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (k N : ℕ) (hN : 0 < N) :
    ∑ s : Fin k → Fin b, matchFreq b x k s N = 1 := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [matchFreq]
  rw [← Finset.sum_div, ← Nat.cast_sum, sum_match_count_eq b hb x k N]
  exact div_self hNR

/-- **Conservation-closure of normality.** Fix a length `k` and a distinguished
    tuple `s₀`. If *every other* tuple `s ≠ s₀` has matching frequency converging
    to `b^{-k}`, then so does `s₀`. Proof: the frequencies sum to `1` at every
    window (`sum_matchFreq_eq_one`), so `matchFreq s₀ N = 1 - ∑_{s ≠ s₀} matchFreq s N`;
    the finite sum on the right converges to `(bᵏ - 1)·b^{-k} = 1 - b^{-k}`, hence
    the left side converges to `b^{-k}`. The equidistribution of one block is thus
    *forced* by that of all the others. -/
theorem matchFreq_tendsto_of_others (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (k : ℕ)
    (s₀ : Fin k → Fin b)
    (hothers : ∀ s : Fin k → Fin b, s ≠ s₀ →
      Tendsto (fun N => matchFreq b x k s N) atTop (nhds ((b : ℝ) ^ (-(k : ℤ))))) :
    Tendsto (fun N => matchFreq b x k s₀ N) atTop (nhds ((b : ℝ) ^ (-(k : ℤ)))) := by
  classical
  have hbpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hbk_pos : (0 : ℝ) < (b : ℝ) ^ k := pow_pos hbpos k
  have hbk_ne : (b : ℝ) ^ k ≠ 0 := ne_of_gt hbk_pos
  have hzpow : (b : ℝ) ^ (-(k : ℤ)) = ((b : ℝ) ^ k)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  -- The sum over the remaining tuples converges.
  have hsum_tendsto :
      Tendsto (fun N => ∑ s ∈ Finset.univ.erase s₀, matchFreq b x k s N) atTop
        (nhds (∑ _s ∈ Finset.univ.erase s₀, (b : ℝ) ^ (-(k : ℤ)))) :=
    tendsto_finset_sum (Finset.univ.erase s₀)
      (fun s hs => hothers s (Finset.ne_of_mem_erase hs))
  -- There are exactly bᵏ - 1 other tuples.
  have hcard : (Finset.univ.erase s₀ : Finset (Fin k → Fin b)).card = b ^ k - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    congr 1
    simp [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ]
  have hconst : (∑ _s ∈ Finset.univ.erase s₀, (b : ℝ) ^ (-(k : ℤ)))
      = ((b ^ k - 1 : ℕ) : ℝ) * (b : ℝ) ^ (-(k : ℤ)) := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
  -- Frequency of s₀ is 1 minus the rest, eventually.
  have heq : ∀ᶠ N in atTop, matchFreq b x k s₀ N
      = 1 - ∑ s ∈ Finset.univ.erase s₀, matchFreq b x k s N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hsum1 : ∑ s : Fin k → Fin b, matchFreq b x k s N = 1 :=
      sum_matchFreq_eq_one b hb x k N hN
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s₀)] at hsum1
    linarith [hsum1]
  -- Take the limit of `1 - (rest)`.
  have htarget :
      Tendsto (fun N => 1 - ∑ s ∈ Finset.univ.erase s₀, matchFreq b x k s N) atTop
        (nhds (1 - ((b ^ k - 1 : ℕ) : ℝ) * (b : ℝ) ^ (-(k : ℤ)))) := by
    have h := hsum_tendsto.const_sub (1 : ℝ)
    rwa [hconst] at h
  -- The forced limit value is exactly b^{-k}.
  have hval : (1 : ℝ) - ((b ^ k - 1 : ℕ) : ℝ) * (b : ℝ) ^ (-(k : ℤ))
      = (b : ℝ) ^ (-(k : ℤ)) := by
    rw [hzpow]
    have h1 : 1 ≤ b ^ k := Nat.one_le_pow _ _ (by omega)
    have hcast : ((b ^ k - 1 : ℕ) : ℝ) = (b : ℝ) ^ k - 1 := by
      rw [Nat.cast_sub h1]; push_cast; ring
    rw [hcast, sub_mul, mul_inv_cancel₀ hbk_ne]
    ring
  rw [← hval]
  exact Filter.Tendsto.congr' (heq.mono fun N h => h.symm) htarget

/-- **Normality needs only "all but one block per length".** If, for every tuple
    length `k`, all tuples except one distinguished `s₀ k` have matching frequency
    converging to `b^{-k}`, then `x` is normal in base `b` — the omitted block's
    frequency is supplied automatically by conservation
    (`matchFreq_tendsto_of_others`). A convenient reduction of the normality test. -/
theorem isNormalInBase_of_all_but_one (b : ℕ) (hb : 2 ≤ b) (x : ℝ)
    (s₀ : ∀ k, Fin k → Fin b)
    (h : ∀ k, ∀ s : Fin k → Fin b, s ≠ s₀ k →
        Tendsto (fun N => matchFreq b x k s N) atTop (nhds ((b : ℝ) ^ (-(k : ℤ))))) :
    IsNormalInBase b x := by
  intro k s
  by_cases hs : s = s₀ k
  · subst hs
    simpa only [matchFreq] using matchFreq_tendsto_of_others b hb x k (s₀ k) (h k)
  · simpa only [matchFreq] using h k s hs

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

/-- e is irrational — a necessary condition for normality (not sufficient). -/
theorem e_irrational_necessary_for_normality : Irrational (Real.exp 1) :=
  e_irrational

-- ============================================================
-- PART VI: SHARPNESS — AN EXPLICIT IRRATIONAL NON-NORMAL NUMBER
-- ============================================================

/-!
`normal_imp_irrational` shows normality ⇒ irrationality. Is the converse true?
No: irrationality is strictly weaker than normality. We exhibit a concrete
*verified* witness — the base-`b` Liouville constant
`liouvilleNumber b = ∑_{i≥0} b^(-i!)` (Mathlib) — which is irrational (indeed
transcendental) yet **not normal** in base `b` for every `b ≥ 3`: its base-`b`
digits are all `0` or `1` (from position `n ≥ 2` on), so the digit `2` is
eventually missing and the criterion `not_normal_of_eventually_missing_digit`
applies. This closes the sharp boundary of `normal_imp_irrational`.
-/

open scoped Nat in
/-- For every `n ≥ 1` there is a factorial "window" index `k` with
`k ! ≤ n < (k+1)!` (the position of `n` in the factorial number system). -/
theorem exists_factorial_window {n : ℕ} (hn : 1 ≤ n) :
    ∃ k, k ! ≤ n ∧ n < (k + 1)! := by
  have hex : ∃ m, n < (m + 1)! :=
    ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.self_le_factorial _)⟩
  classical
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  set k := Nat.find hex with hk
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [hk0]; simpa using hn
  · have hmin : ¬ n < (k - 1 + 1)! := Nat.find_min hex (Nat.sub_lt hkpos Nat.one_pos)
    rw [Nat.sub_add_cancel hkpos] at hmin
    exact Nat.not_lt.mp hmin

open scoped Nat in
/-- **Exact floor of `bⁿ · (base-b Liouville constant)`** (any base `b ≥ 2`).
For `k ! ≤ n < (k+1)!` the value `bⁿ · liouvilleNumber b` has integer part
`∑_{i=0}^{k} b^(n - i!)`: the partial sum contributes an integer (all exponents
`n - i!` are non-negative) and the remainder tail is `< 1`. Mathlib's *strict*
`remainder_lt'` gives `remainder < 2 / b^((k+1)!)`, and `2·bⁿ ≤ b^((k+1)!)`
(as `n + 1 ≤ (k+1)!`), so `bⁿ · remainder < 1` even in the tight base-`2` case
where `2·bⁿ = b^(n+1)` meets the bound with equality. -/
theorem liouvilleNumber_floor {b : ℕ} (hb : 2 ≤ b) {k n : ℕ}
    (hk_le : k ! ≤ n) (hk_lt : n < (k + 1)!) :
    ⌊(b : ℝ) ^ n * liouvilleNumber (b : ℝ)⌋
      = ∑ i ∈ Finset.range (k + 1), (b : ℤ) ^ (n - i !) := by
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 1 < b)
  have hb2R : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast (by omega : 2 ≤ b)
  have hbpos : (0 : ℝ) < (b : ℝ) := by linarith
  set P : ℤ := ∑ i ∈ Finset.range (k + 1), (b : ℤ) ^ (n - i !) with hP
  -- Claim 1: the partial sum scales to the integer P.
  have hbne : (b : ℝ) ≠ 0 := by positivity
  have hclaim1 : (b : ℝ) ^ n * LiouvilleNumber.partialSum (b : ℝ) k = (P : ℝ) := by
    rw [LiouvilleNumber.partialSum, Finset.mul_sum, hP, Int.cast_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i ! ≤ n :=
      le_trans (Nat.factorial_le (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) hk_le
    rw [Int.cast_pow, Int.cast_natCast, mul_one_div, div_eq_iff (pow_ne_zero _ hbne),
      ← pow_add, Nat.sub_add_cancel hik]
  -- The remainder tail is non-negative and < 1.
  have hrem_nonneg : 0 ≤ (b : ℝ) ^ n * LiouvilleNumber.remainder (b : ℝ) k :=
    mul_nonneg (by positivity) (le_of_lt (LiouvilleNumber.remainder_pos hb1 k))
  have hrem_lt : (b : ℝ) ^ n * LiouvilleNumber.remainder (b : ℝ) k < 1 := by
    have hR := LiouvilleNumber.remainder_lt' k hb1
    have hbn : (0 : ℝ) < (b : ℝ) ^ n := by positivity
    -- *Strict* tail bound: remainder < 2 / b^((k+1)!) (from the strict `remainder_lt'`).
    have hstep : LiouvilleNumber.remainder (b : ℝ) k < 2 / (b : ℝ) ^ (k + 1)! := by
      calc LiouvilleNumber.remainder (b : ℝ) k
          < (1 - 1 / (b : ℝ))⁻¹ * (1 / (b : ℝ) ^ (k + 1)!) := hR
        _ ≤ 2 * (1 / (b : ℝ) ^ (k + 1)!) := by
            gcongr; exact sub_one_div_inv_le_two hb2R
        _ = 2 / (b : ℝ) ^ (k + 1)! := by rw [mul_one_div]
    -- *Non-strict* polynomial gap: 2·bⁿ ≤ b^((k+1)!) since (k+1)! ≥ n+1 and b ≥ 2.
    -- (For b = 2 the first step is an equality — this is why the tail bound must
    -- carry the strictness instead.)
    have hexp : 2 * (b : ℝ) ^ n ≤ (b : ℝ) ^ (k + 1)! := by
      calc 2 * (b : ℝ) ^ n
          ≤ (b : ℝ) * (b : ℝ) ^ n := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast (by omega : (2 : ℕ) ≤ b)
        _ = (b : ℝ) ^ (n + 1) := by rw [pow_succ, mul_comm]
        _ ≤ (b : ℝ) ^ (k + 1)! := pow_le_pow_right₀ hb1.le (by omega)
    have key : (b : ℝ) ^ n * (2 / (b : ℝ) ^ (k + 1)!) ≤ 1 := by
      rw [← mul_div_assoc, div_le_one (by positivity)]
      linarith [hexp]
    exact lt_of_lt_of_le (mul_lt_mul_of_pos_left hstep hbn) key
  -- Assemble: bⁿ·x = P + (small tail), so the floor is P.
  have hsplit : (b : ℝ) ^ n * liouvilleNumber (b : ℝ)
      = (P : ℝ) + (b : ℝ) ^ n * LiouvilleNumber.remainder (b : ℝ) k := by
    rw [← LiouvilleNumber.partialSum_add_remainder hb1 k, mul_add, hclaim1]
  rw [Int.floor_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [hsplit]; exact le_add_of_nonneg_right hrem_nonneg
  · rw [hsplit]; push_cast; linarith [hrem_lt]

open scoped Nat in
/-- **Every base-b digit of the Liouville constant (from position 2 on) is 0 or 1.**
Consequently it is never equal to `2`. This is the digit obstruction that
forbids normality. -/
theorem liouvilleNumber_digit_le_one {b : ℕ} (hb : 2 ≤ b) {k n : ℕ}
    (hk_le : k ! ≤ n) (hk_lt : n < (k + 1)!) (hn : 2 ≤ n) :
    (⌊(b : ℝ) ^ n * liouvilleNumber (b : ℝ)⌋) % (b : ℤ) ≤ 1 := by
  rw [liouvilleNumber_floor hb hk_le hk_lt, Finset.sum_range_succ]
  -- Lower-index terms are all divisible by b (their exponents are ≥ 1).
  have hdvd : (b : ℤ) ∣ ∑ i ∈ Finset.range k, (b : ℤ) ^ (n - i !) := by
    apply Finset.dvd_sum
    intro i hi
    have hi_lt_k : i < k := Finset.mem_range.mp hi
    have hik : i ! < n := by
      rcases Nat.eq_zero_or_pos i with h0 | hp
      · rw [h0, Nat.factorial_zero]; omega
      · calc i ! < k ! := (Nat.factorial_lt hp).mpr hi_lt_k
          _ ≤ n := hk_le
    exact dvd_pow_self (b : ℤ) (by omega : n - i ! ≠ 0)
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, add_comm, Int.add_mul_emod_self_left]
  -- Remaining top term b^(n - k!) has residue 0 (if n > k!) or 1 (if n = k!).
  rcases eq_or_lt_of_le hk_le with heq | hlt
  · -- n = k! : b^0 = 1, and 1 % b = 1.
    have hz : n - k ! = 0 := by omega
    rw [hz, pow_zero]
    have h1 : (1 : ℤ) % (b : ℤ) = 1 :=
      Int.emod_eq_of_lt (by norm_num) (by exact_mod_cast (by omega : (1 : ℕ) < b))
    omega
  · -- k! < n : exponent ≥ 1, so b divides the term.
    obtain ⟨d, hd⟩ := dvd_pow_self (b : ℤ) (by omega : n - k ! ≠ 0)
    have h0 : (b : ℤ) ^ (n - k !) % (b : ℤ) = 0 := by rw [hd, Int.mul_emod_right]
    omega

open scoped Nat in
/-- The base-`b` Liouville constant is irrational (in fact transcendental). -/
theorem liouvilleNumber_irrational {b : ℕ} (hb : 2 ≤ b) :
    Irrational (liouvilleNumber (b : ℝ)) :=
  (liouville_liouvilleNumber hb).irrational

open scoped Nat in
/-- **The Liouville constant is not normal in base `b` (b ≥ 3).**
Its base-`b` digit `2` is absent from position `2` onwards, so
`not_normal_of_eventually_missing_digit` applies. -/
theorem liouvilleNumber_not_normal {b : ℕ} (hb : 3 ≤ b) :
    ¬ IsNormalInBase b (liouvilleNumber (b : ℝ)) := by
  have hb2 : 2 ≤ b := by omega
  have h2b : (2 : ℕ) < b := by omega
  refine not_normal_of_eventually_missing_digit b hb2 (liouvilleNumber (b : ℝ))
    (⟨2, h2b⟩ : Fin b) 2 ?_
  intro n hn
  obtain ⟨k, hk_le, hk_lt⟩ := exists_factorial_window (by omega : 1 ≤ n)
  have hdig := liouvilleNumber_digit_le_one hb2 hk_le hk_lt (by omega : 2 ≤ n)
  have hval : ((⟨2, h2b⟩ : Fin b) : ℤ) = 2 := by simp
  rw [hval]
  unfold nthDigit
  omega

open scoped Nat in
/-- **Sharpness of `normal_imp_irrational`: an explicit irrational non-normal number.**
For every base `b ≥ 3`, the Liouville constant is irrational yet not normal in
base `b`. -/
theorem exists_irrational_not_normal {b : ℕ} (hb : 3 ≤ b) :
    ∃ x : ℝ, Irrational x ∧ ¬ IsNormalInBase b x :=
  ⟨liouvilleNumber (b : ℝ), liouvilleNumber_irrational (by omega),
    liouvilleNumber_not_normal hb⟩

/-- **Irrationality does not imply normality.**
The converse of `normal_imp_irrational` fails: there is an irrational real that
is not normal in base `3`. Normality is therefore *strictly* stronger than
irrationality (together with disjunctivity). -/
theorem irrational_not_imp_normal :
    ¬ ∀ (b : ℕ), 2 ≤ b → ∀ x : ℝ, Irrational x → IsNormalInBase b x := by
  intro h
  obtain ⟨x, hx_irr, hx_not⟩ := exists_irrational_not_normal (b := 3) (by norm_num)
  exact hx_not (h 3 (by norm_num) x hx_irr)

-- ============================================================
-- PART VII: BASE-2 DIGIT STRUCTURE OF THE LIOUVILLE CONSTANT
-- ============================================================

/-!
The `b ≥ 3` witness above rules out normality via a *missing* digit (`2` never
occurs). That obstruction is unavailable in **base 2**: an irrational real must
use both digits `0` and `1` infinitely often, so no digit is eventually absent.
Base-2 non-normality is therefore genuinely a job for the *frequency* criterion
(`not_normal_of_digit_freq_tendsto_ne`), not the absence criterion — the digit
`1` occurs, but only with density `0`.

The results below pin down the exact base-`b` digit structure of the Liouville
constant (`liouvilleNumber_window_digit`) and specialise it to base `2`
(`liouvilleNumber_base_two_one_iff`): from position `2` on, the digit `1` occurs
**exactly at the factorial positions** `n = k !`, everything else being `0`.
This is the decisive structural input for base-`2` sharpness; what remains is the
purely analytic fact that the factorial positions have density `0`
(see the closing note).
-/

open scoped Nat in
/-- **Exact base-`b` digit of the Liouville constant at a window position**
    (any base `b ≥ 2`). If `k ! ≤ n < (k+1)!` and `n ≥ 2`, then the `n`-th
    base-`b` digit of `liouvilleNumber b` is `1` when `n = k !` and `0`
    otherwise. Strengthens `liouvilleNumber_digit_le_one` from the bound `≤ 1`
    to the exact value, and shows every digit of the Liouville constant is `0`
    or `1` in every base. -/
theorem liouvilleNumber_window_digit {b : ℕ} (hb : 2 ≤ b) {k n : ℕ}
    (hk_le : k ! ≤ n) (hk_lt : n < (k + 1)!) (hn : 2 ≤ n) :
    nthDigit b n (liouvilleNumber (b : ℝ)) = if n = k ! then 1 else 0 := by
  unfold nthDigit
  rw [liouvilleNumber_floor hb hk_le hk_lt, Finset.sum_range_succ]
  -- Lower-index terms are all divisible by `b` (their exponents are ≥ 1).
  have hdvd : (b : ℤ) ∣ ∑ i ∈ Finset.range k, (b : ℤ) ^ (n - i !) := by
    apply Finset.dvd_sum
    intro i hi
    have hi_lt_k : i < k := Finset.mem_range.mp hi
    have hik : i ! < n := by
      rcases Nat.eq_zero_or_pos i with h0 | hp
      · rw [h0, Nat.factorial_zero]; omega
      · calc i ! < k ! := (Nat.factorial_lt hp).mpr hi_lt_k
          _ ≤ n := hk_le
    exact dvd_pow_self (b : ℤ) (by omega : n - i ! ≠ 0)
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, add_comm, Int.add_mul_emod_self_left]
  -- Only the top term `b^(n - k!)` survives: residue `1` if `n = k!`, else `0`.
  rcases eq_or_lt_of_le hk_le with heq | hlt
  · -- n = k!
    have hz : n - k ! = 0 := by omega
    rw [hz, pow_zero, if_pos heq.symm]
    exact Int.emod_eq_of_lt (by norm_num) (by exact_mod_cast (by omega : (1 : ℕ) < b))
  · -- k! < n : the exponent is ≥ 1, so `b` divides the term.
    obtain ⟨d, hd⟩ := dvd_pow_self (b : ℤ) (by omega : n - k ! ≠ 0)
    rw [if_neg (by omega : n ≠ k !), hd, Int.mul_emod_right]

open scoped Nat in
/-- **Base-2 digit structure of the Liouville constant.** From position `2`
    onwards, the digit `1` of `liouvilleNumber 2` occurs exactly at the
    factorial positions: `nthDigit 2 n (liouvilleNumber 2) = 1 ↔ n = k !` for
    some `k`. Every other digit (from position `2` on) is `0`. -/
theorem liouvilleNumber_base_two_one_iff {n : ℕ} (hn : 2 ≤ n) :
    nthDigit 2 n (liouvilleNumber (2 : ℝ)) = 1 ↔ ∃ k, k ! = n := by
  obtain ⟨k, hk_le, hk_lt⟩ := exists_factorial_window (by omega : 1 ≤ n)
  have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  rw [← hcast, liouvilleNumber_window_digit (b := 2) (by norm_num) hk_le hk_lt hn]
  constructor
  · intro h
    split_ifs at h with he
    · exact ⟨k, he.symm⟩
    · exact absurd h (by norm_num)
  · rintro ⟨j, hj⟩
    -- The factorial window is unique: `n = j !` forces `k = j`, so `n = k !`.
    have hj2 : 2 ≤ j := by
      by_contra hlt
      push_neg at hlt
      interval_cases j
      · rw [Nat.factorial_zero] at hj; omega
      · rw [Nat.factorial_one] at hj; omega
    have hjpos : 0 < j := by omega
    have hkj : k = j := by
      rcases lt_trichotomy k j with h | h | h
      · -- k < j : (k+1)! ≤ j! = n < (k+1)!, contradiction
        have h1 : (k + 1)! ≤ j ! := Nat.factorial_le (by omega)
        rw [hj] at h1; omega
      · exact h
      · -- j < k : (j+1)! ≤ k! ≤ n = j! < (j+1)!, contradiction
        have h1 : (j + 1)! ≤ k ! := Nat.factorial_le (by omega)
        have h2 : j ! < (j + 1)! := (Nat.factorial_lt hjpos).mpr (Nat.lt_succ_self j)
        omega
    rw [if_pos (by rw [hkj, hj])]

-- ============================================================
-- PART VIII: BASE-2 SHARPNESS — THE LIOUVILLE CONSTANT IS NOT
--            NORMAL IN BASE 2 (FIRST GENUINE USE OF THE
--            FREQUENCY CRITERION)
-- ============================================================

/-!
The `b ≥ 3` witness (`liouvilleNumber_not_normal`) ruled out normality through a
*missing* digit. That obstruction is provably unavailable in base `2`: an
irrational base-`2` real omits no digit, so `not_normal_of_eventually_missing_*`
cannot apply. Base-`2` non-normality is therefore the **first genuine
application** of the frequency criterion `not_normal_of_digit_freq_tendsto_ne`:
the digit `1` of `liouvilleNumber 2` *does* occur, but with asymptotic density
`0`, not `1/2`.

The structural input is `liouvilleNumber_base_two_one_iff` (digit `1` sits
exactly at the factorial positions). The remaining content — carried out here —
is the analytic fact that the factorial positions have natural density `0`:

* `two_pow_le_factorial_succ` : `2 ^ m ≤ (m+1)!` (exponential growth of `!`).
* `liouvilleNumber_two_one_count_le` : the `1`-positions below `N` number at
  most `Nat.log 2 N + 4` (they inject into the factorials `k! < N`, of which
  there are `≤ Nat.log 2 N + O(1)` since `2^(k-1) ≤ k!`).
* `tendsto_natLog_two_div_atTop_zero` : `Nat.log 2 N / N → 0` (from
  `Real.log =o[atTop] id` transported through `Nat.pow_log_le_self`).
* `liouvilleNumber_two_one_density_zero` : the digit-`1` density is `0`.
* `liouvilleNumber_not_normal_base_two` : the payoff, `¬ IsNormalInBase 2 L`.
-/

open scoped Nat in
/-- Exponential lower bound for the factorial: `2 ^ m ≤ (m + 1)!`. Elementary
    induction: `(k+2)! = (k+2)·(k+1)! ≥ 2·2^k = 2^(k+1)`. -/
private lemma two_pow_le_factorial_succ (m : ℕ) : 2 ^ m ≤ (m + 1)! := by
  induction m with
  | zero => simp
  | succ k ih =>
    have hstep : 2 * 2 ^ k ≤ (k + 1 + 1) * (k + 1)! := Nat.mul_le_mul (by omega) ih
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≤ (k + 1 + 1) * (k + 1)! := hstep
      _ = (k + 1 + 1)! := (Nat.factorial_succ (k + 1)).symm

open scoped Nat in
/-- **Count bound for digit-`1` positions of `liouvilleNumber 2`.** The number of
    positions `n < N` at which the base-`2` digit is `1` is at most
    `Nat.log 2 N + 4`. Proof: every such `n` is either `0`, `1`, or (by
    `liouvilleNumber_base_two_one_iff`) a factorial `k! = n`; from
    `2^(k-1) ≤ k! = n < N` and `Nat.le_log_iff_pow_le` the index `k` is bounded
    by `Nat.log 2 N + 1`, so the `1`-positions inject into a set of size
    `≤ Nat.log 2 N + 4`. -/
private lemma liouvilleNumber_two_one_count_le (N : ℕ) :
    ((Finset.range N).filter
      (fun n => nthDigit 2 n (liouvilleNumber (2 : ℝ)) = 1)).card
      ≤ Nat.log 2 N + 4 := by
  classical
  have hsub : (Finset.range N).filter
      (fun n => nthDigit 2 n (liouvilleNumber (2 : ℝ)) = 1)
      ⊆ insert 0 (insert 1
        ((Finset.range (Nat.log 2 N + 2)).image Nat.factorial)) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnN, hdig⟩ := hn
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · interval_cases n
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · obtain ⟨k, hk⟩ := (liouvilleNumber_base_two_one_iff h2).mp hdig
      have hk_pos : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | hp
        · rw [h0, Nat.factorial_zero] at hk; omega
        · exact hp
      have hpow : 2 ^ (k - 1) ≤ n := by
        have h := two_pow_le_factorial_succ (k - 1)
        rw [Nat.sub_add_cancel hk_pos, hk] at h
        exact h
      have hn0 : n ≠ 0 := by omega
      have hklog : k - 1 ≤ Nat.log 2 n :=
        (Nat.le_log_iff_pow_le (by norm_num) hn0).mpr hpow
      have hk_lt : k < Nat.log 2 N + 2 := by
        have hmono : Nat.log 2 n ≤ Nat.log 2 N := Nat.log_mono_right hnN.le
        omega
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk_lt, hk⟩))
  have c1 : ((Finset.range (Nat.log 2 N + 2)).image Nat.factorial).card
      ≤ Nat.log 2 N + 2 :=
    Finset.card_image_le.trans (by rw [Finset.card_range])
  have c2 := Finset.card_insert_le 1
    ((Finset.range (Nat.log 2 N + 2)).image Nat.factorial)
  have c3 := Finset.card_insert_le 0
    (insert 1 ((Finset.range (Nat.log 2 N + 2)).image Nat.factorial))
  exact (Finset.card_le_card hsub).trans (by omega)

/-- **`Nat.log 2 N / N → 0`.** The base-`2` integer logarithm is `o(N)`. Proof:
    `Nat.pow_log_le_self` gives `2 ^ Nat.log 2 N ≤ N`, hence
    `Nat.log 2 N ≤ Real.log N / Real.log 2`; squeeze against
    `Real.log N / N → 0` (`Real.isLittleO_log_id_atTop`). -/
private lemma tendsto_natLog_two_div_atTop_zero :
    Tendsto (fun N : ℕ => (Nat.log 2 N : ℝ) / (N : ℝ)) atTop (nhds 0) := by
  have hlogid : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    have h := Real.isLittleO_log_id_atTop
    rw [Asymptotics.isLittleO_iff_tendsto
      (fun x hx => by simp only [id_eq] at hx; simp [hx])] at h
    simpa [id_eq] using h
  have hnat : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) atTop (nhds 0) := by
    simpa using hlogid.comp tendsto_natCast_atTop_atTop
  have hupper : Tendsto
      (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ) * (Real.log 2)⁻¹) atTop (nhds 0) := by
    simpa using hnat.mul_const (Real.log 2)⁻¹
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Filter.Eventually.of_forall fun N => by positivity) ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hkey : (Nat.log 2 N : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
    have hpow : (2 : ℕ) ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 hN.ne'
    have hpowR : (2 : ℝ) ^ Nat.log 2 N ≤ (N : ℝ) := by exact_mod_cast hpow
    have hlogle : Real.log ((2 : ℝ) ^ Nat.log 2 N) ≤ Real.log (N : ℝ) :=
      (Real.log_le_log_iff (by positivity) hNpos).mpr hpowR
    rw [Real.log_pow] at hlogle
    rw [le_div_iff₀ hlog2pos]
    exact hlogle
  calc (Nat.log 2 N : ℝ) / (N : ℝ)
      ≤ (Real.log (N : ℝ) / Real.log 2) / (N : ℝ) := by gcongr
    _ = Real.log (N : ℝ) / (N : ℝ) * (Real.log 2)⁻¹ := by ring

/-- **The digit `1` of `liouvilleNumber 2` has density `0`.** The matching
    frequency of digit `1` over `Finset.range N` tends to `0`, squeezed between
    `0` and `(Nat.log 2 N + 4)/N` via `liouvilleNumber_two_one_count_le`. This is
    the decisive frequency anomaly: normality would demand density `1/2`. -/
theorem liouvilleNumber_two_one_density_zero :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter
        (fun n => nthDigit 2 n (liouvilleNumber (2 : ℝ)) = 1)).card : ℝ) / (N : ℝ))
      atTop (nhds 0) := by
  have h4 : Tendsto (fun N : ℕ => (4 : ℝ) / (N : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hg : Tendsto
      (fun N : ℕ => (Nat.log 2 N : ℝ) / (N : ℝ) + (4 : ℝ) / (N : ℝ))
      atTop (nhds 0) := by
    simpa using tendsto_natLog_two_div_atTop_zero.add h4
  refine squeeze_zero (fun N => by positivity) (fun N => ?_) hg
  rcases Nat.eq_zero_or_pos N with hN | hN
  · simp [hN]
  · have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [← add_div]
    gcongr
    exact_mod_cast liouvilleNumber_two_one_count_le N

/-- **The Liouville constant is not normal in base `2`.** The digit `1` occurs
    with density `0 ≠ 1/2` (`liouvilleNumber_two_one_density_zero`), so the
    single-digit frequency criterion `not_normal_of_digit_freq_tendsto_ne`
    forbids normality. This is the first application of the frequency criterion
    to a number whose non-normality is *invisible* to the absence criterion (no
    digit is eventually missing in base `2`), completing
    `exists_irrational_not_normal` down to base `2`. -/
theorem liouvilleNumber_not_normal_base_two :
    ¬ IsNormalInBase 2 (liouvilleNumber (2 : ℝ)) := by
  have hval : ((1 : Fin 2) : ℤ) = 1 := by decide
  refine not_normal_of_digit_freq_tendsto_ne 2 (by norm_num)
    (liouvilleNumber (2 : ℝ)) (1 : Fin 2) 0 ?_ (by norm_num)
  simp only [hval]
  exact liouvilleNumber_two_one_density_zero

/-- **Sharpness of `normal_imp_irrational`, extended to base `2`.** For *every*
    base `b ≥ 2` there is an irrational real that is not normal in base `b`:
    the Liouville constant `liouvilleNumber b` (base `b ≥ 3`, via a missing
    digit) or `liouvilleNumber 2` (base `2`, via the digit-`1` density anomaly).
    Strengthens `exists_irrational_not_normal`, which required `b ≥ 3`. -/
theorem exists_irrational_not_normal_of_two_le {b : ℕ} (hb : 2 ≤ b) :
    ∃ x : ℝ, Irrational x ∧ ¬ IsNormalInBase b x := by
  rcases Nat.lt_or_ge b 3 with h3 | h3
  · have hb2 : b = 2 := by omega
    subst hb2
    exact ⟨liouvilleNumber (2 : ℝ), liouvilleNumber_irrational (by norm_num),
      liouvilleNumber_not_normal_base_two⟩
  · exact exists_irrational_not_normal h3

-- ============================================================
-- PART IX: BASE-2 BLOCK DISTRIBUTION — THE ALL-ZEROS k-TUPLE
--          HAS DENSITY 1 (FIRST k-BLOCK FREQUENCY COMPUTATION)
-- ============================================================

/-!
PART VIII computed a *single* digit frequency (`1` at density `0`). Here we
compute the frequency of an entire length-`k` block for the first time: the
all-zeros block `0…0` occupies density `1` in the base-`2` expansion of the
Liouville constant, for every `k`. Equivalently, the `1`-digits are so sparse
(only the factorial positions) that a random length-`k` window is all-zeros with
probability tending to `1`.

This is the *over-representation* counterpart to PART VIII's under-representation
(digit `1` at density `0`): normality would demand the all-zeros block at density
`2^{-k}`, but it actually occurs at density `1 > 2^{-k}`. It supplies the first
application of the general `k`-tuple criterion `not_normal_of_match_freq_tendsto_ne`
(all earlier applications were single-digit or the absence criterion), hence a
structurally different proof of base-`2` non-normality.

* `nthDigit_two_eq_zero_or_one` — every base-`2` digit is `0` or `1`.
* `liouvilleNumber_two_zeros_bad_count_le` — at most `k·(log₂(N+k)+4)` windows
  below `N` contain a `1` (cover each such window by the `1`-position inside it).
* `liouvilleNumber_two_all_zeros_density_one` — the all-zeros `k`-window density
  tends to `1`.
* `liouvilleNumber_all_zeros_not_normal_base_two` — base-`2` non-normality, via
  over-representation of the all-zeros block (`k ≥ 1`).
-/

/-- Every base-`2` digit is `0` or `1`: it is a residue modulo `2`. -/
private lemma nthDigit_two_eq_zero_or_one (n : ℕ) (x : ℝ) :
    nthDigit 2 n x = 0 ∨ nthDigit 2 n x = 1 := by
  unfold nthDigit
  simpa using Int.emod_two_eq_zero_or_one ⌊(2 : ℝ) ^ n * x⌋

/-- **Count bound for windows containing a `1`.** The number of positions `n < N`
    whose length-`k` window `[n, n+k)` contains a base-`2` digit `1` of the
    Liouville constant is at most `k · (log₂(N+k) + 4)`. Proof: cover the bad
    windows by the `1`-positions (`< N+k`), each of which lies in at most `k`
    windows; the `1`-positions number `≤ log₂(N+k) + 4` by
    `liouvilleNumber_two_one_count_le`. -/
private lemma liouvilleNumber_two_zeros_bad_count_le (k N : ℕ) :
    ((Finset.range N).filter
      (fun n => ¬ ∀ i : Fin k,
        nthDigit 2 (n + i.val) (liouvilleNumber (2 : ℝ)) = 0)).card
      ≤ k * (Nat.log 2 (N + k) + 4) := by
  classical
  -- Cover each bad window by the `1`-position it contains.
  have hsub : (Finset.range N).filter
      (fun n => ¬ ∀ i : Fin k,
        nthDigit 2 (n + i.val) (liouvilleNumber (2 : ℝ)) = 0)
      ⊆ ((Finset.range (N + k)).filter
          (fun j => nthDigit 2 j (liouvilleNumber (2 : ℝ)) = 1)).biUnion
        (fun j => (Finset.range N).filter (fun n => ∃ i : Fin k, n + i.val = j)) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnN, hbad⟩ := hn
    push_neg at hbad
    obtain ⟨i, hi⟩ := hbad
    have h1 : nthDigit 2 (n + i.val) (liouvilleNumber (2 : ℝ)) = 1 :=
      (nthDigit_two_eq_zero_or_one (n + i.val) _).resolve_left hi
    have hji : n + i.val < N + k := by have := i.isLt; omega
    refine Finset.mem_biUnion.mpr ⟨n + i.val, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hji, h1⟩
    · rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hnN, i, rfl⟩
  calc ((Finset.range N).filter
        (fun n => ¬ ∀ i : Fin k,
          nthDigit 2 (n + i.val) (liouvilleNumber (2 : ℝ)) = 0)).card
      ≤ (((Finset.range (N + k)).filter
            (fun j => nthDigit 2 j (liouvilleNumber (2 : ℝ)) = 1)).biUnion
          (fun j => (Finset.range N).filter
            (fun n => ∃ i : Fin k, n + i.val = j))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ _j ∈ (Finset.range (N + k)).filter
            (fun j => nthDigit 2 j (liouvilleNumber (2 : ℝ)) = 1),
          ((Finset.range N).filter (fun n => ∃ i : Fin k, n + i.val = _j)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ (Finset.range (N + k)).filter
            (fun j => nthDigit 2 j (liouvilleNumber (2 : ℝ)) = 1), k := by
        apply Finset.sum_le_sum
        intro j _
        have hsub2 : (Finset.range N).filter (fun n => ∃ i : Fin k, n + i.val = j)
            ⊆ (Finset.univ : Finset (Fin k)).image (fun i => j - i.val) := by
          intro n hn
          rw [Finset.mem_filter] at hn
          obtain ⟨i, hi⟩ := hn.2
          exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by omega⟩
        calc ((Finset.range N).filter (fun n => ∃ i : Fin k, n + i.val = j)).card
            ≤ ((Finset.univ : Finset (Fin k)).image (fun i => j - i.val)).card :=
              Finset.card_le_card hsub2
          _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
          _ = k := by rw [Finset.card_univ, Fintype.card_fin]
    _ = ((Finset.range (N + k)).filter
          (fun j => nthDigit 2 j (liouvilleNumber (2 : ℝ)) = 1)).card * k := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (Nat.log 2 (N + k) + 4) * k := by
        gcongr
        exact liouvilleNumber_two_one_count_le (N + k)
    _ = k * (Nat.log 2 (N + k) + 4) := Nat.mul_comm _ _

/-- **The all-zeros length-`k` block has density `1`** in the base-`2` expansion
    of the Liouville constant, for every `k`. The complementary "bad" windows
    (those containing a `1`) have density `0` by
    `liouvilleNumber_two_zeros_bad_count_le` squeezed against
    `k·(log₂(N+k)+4)/N → 0`; the all-zeros windows are their complement in
    `range N`, so their density tends to `1 - 0 = 1`. Normality would instead
    force density `2^{-k}`. -/
theorem liouvilleNumber_two_all_zeros_density_one (k : ℕ) :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter
        (fun n => ∀ i : Fin k,
          nthDigit 2 (n + i.val) (liouvilleNumber (2 : ℝ)) = 0)).card : ℝ)
        / (N : ℝ))
      atTop (nhds 1) := by
  classical
  -- The upper bound `k·(log₂(N+k)+4)/N` tends to `0`.
  have hUB : Tendsto (fun N : ℕ =>
      ((k * (Nat.log 2 (N + k) + 4) : ℕ) : ℝ) / (N : ℝ)) atTop (nhds 0) := by
    have hφ : Tendsto (fun N : ℕ => ((Nat.log 2 N : ℝ) + 5) / (N : ℝ))
        atTop (nhds 0) := by
      have h1 := tendsto_natLog_two_div_atTop_zero
      have h2 : Tendsto (fun N : ℕ => (5 : ℝ) / (N : ℝ)) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      simpa [add_div] using h1.add h2
    have hh : Tendsto (fun N : ℕ => (k : ℝ) * (((Nat.log 2 N : ℝ) + 5) / (N : ℝ)))
        atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (k : ℝ))).mul hφ
    refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ hh
    filter_upwards [eventually_ge_atTop (max 1 k)] with N hN
    have hN1 : 1 ≤ N := le_trans (le_max_left 1 k) hN
    have hNk : k ≤ N := le_trans (le_max_right 1 k) hN
    have hlog : Nat.log 2 (N + k) ≤ Nat.log 2 N + 1 :=
      calc Nat.log 2 (N + k) ≤ Nat.log 2 (N * 2) := Nat.log_mono_right (by omega)
        _ = Nat.log 2 N + 1 := Nat.log_mul_base (by norm_num) (by omega)
    have hbound : k * (Nat.log 2 (N + k) + 4) ≤ k * (Nat.log 2 N + 5) :=
      Nat.mul_le_mul le_rfl (by omega)
    calc ((k * (Nat.log 2 (N + k) + 4) : ℕ) : ℝ) / (N : ℝ)
        ≤ ((k * (Nat.log 2 N + 5) : ℕ) : ℝ) / (N : ℝ) := by
          have hbR : ((k * (Nat.log 2 (N + k) + 4) : ℕ) : ℝ)
              ≤ ((k * (Nat.log 2 N + 5) : ℕ) : ℝ) := by exact_mod_cast hbound
          gcongr
      _ = (k : ℝ) * (((Nat.log 2 N : ℝ) + 5) / (N : ℝ)) := by push_cast; ring
  -- Hence the bad-window density tends to `0`.
  have hbad0 : Tendsto (fun N : ℕ =>
      (((Finset.range N).filter
        (fun n => ¬ ∀ i : Fin k,
          nthDigit 2 (n + i.val) (liouvilleNumber (2 : ℝ)) = 0)).card : ℝ) / (N : ℝ))
      atTop (nhds 0) :=
    squeeze_zero (fun N => by positivity)
      (fun N => by
        gcongr
        exact_mod_cast liouvilleNumber_two_zeros_bad_count_le k N) hUB
  -- All-zeros windows are the complement, so their density is `1 - bad density`.
  have hcongr : (fun N : ℕ =>
      (((Finset.range N).filter
        (fun n => ∀ i : Fin k,
          nthDigit 2 (n + i.val) (liouvilleNumber (2 : ℝ)) = 0)).card : ℝ) / (N : ℝ))
      =ᶠ[atTop] (fun N : ℕ => 1 -
        (((Finset.range N).filter
          (fun n => ¬ ∀ i : Fin k,
            nthDigit 2 (n + i.val) (liouvilleNumber (2 : ℝ)) = 0)).card : ℝ) / (N : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hpart := Finset.filter_card_add_filter_neg_card_eq_card
      (s := Finset.range N)
      (p := fun n => ∀ i : Fin k,
        nthDigit 2 (n + i.val) (liouvilleNumber (2 : ℝ)) = 0)
    rw [Finset.card_range] at hpart
    have hBLE : ((Finset.range N).filter
        (fun n => ¬ ∀ i : Fin k,
          nthDigit 2 (n + i.val) (liouvilleNumber (2 : ℝ)) = 0)).card ≤ N := by omega
    have hA : ((Finset.range N).filter
        (fun n => ∀ i : Fin k,
          nthDigit 2 (n + i.val) (liouvilleNumber (2 : ℝ)) = 0)).card
        = N - ((Finset.range N).filter
          (fun n => ¬ ∀ i : Fin k,
            nthDigit 2 (n + i.val) (liouvilleNumber (2 : ℝ)) = 0)).card := by omega
    rw [hA, Nat.cast_sub hBLE, sub_div, div_self hNne]
  exact Tendsto.congr' hcongr.symm (by simpa using Tendsto.const_sub 1 hbad0)

/-- **The Liouville constant is not normal in base `2`, via the all-zeros block.**
    For any `k ≥ 1`, the all-zeros length-`k` block occurs with density
    `1 ≠ 2^{-k}` (`liouvilleNumber_two_all_zeros_density_one`), so the `k`-tuple
    frequency criterion `not_normal_of_match_freq_tendsto_ne` forbids normality.
    A structurally different proof from `liouvilleNumber_not_normal_base_two`
    (which used a single under-represented digit): here an entire *block* is
    over-represented, the first genuine `k`-block frequency computation in this
    development. -/
theorem liouvilleNumber_all_zeros_not_normal_base_two (k : ℕ) (hk : 1 ≤ k) :
    ¬ IsNormalInBase 2 (liouvilleNumber (2 : ℝ)) := by
  refine not_normal_of_match_freq_tendsto_ne 2 (by norm_num) (liouvilleNumber (2 : ℝ))
    k (fun _ => 0) 1 ?_ ?_
  · have h := liouvilleNumber_two_all_zeros_density_one k
    have h0 : ((0 : Fin 2) : ℤ) = 0 := by decide
    simpa only [h0] using h
  · have h2 : (2 : ℝ) ^ (-(k : ℤ)) < 1 :=
      zpow_lt_one_of_neg₀ (by norm_num) (by
        have : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
        omega)
    exact h2.ne'

-- ============================================================
-- PART VIII: ABSOLUTE-LEVEL COROLLARIES
-- ============================================================

/-!
## Consequences of absolute normality

`IsAbsolutelyNormal` (normal in *every* base `≥ 2`) is the notion the axiom
`e_absolutely_normal` asserts for `e`, but the file draws its consequences only
one base at a time. The two corollaries below package the base-uniform
consequences: an absolutely normal number is irrational, and is disjunctive in
every base. They follow from `normal_imp_irrational` / `normal_imp_disjunctive`
by instantiating the base.
-/

/-- **Absolutely normal numbers are irrational.**  The absolute-level form of
    `normal_imp_irrational`: an absolutely normal number is normal in *every* base,
    in particular base `2`, hence irrational. -/
theorem absolutely_normal_imp_irrational (x : ℝ) (h : IsAbsolutelyNormal x) :
    Irrational x :=
  normal_imp_irrational 2 (le_refl 2) x (h 2 (le_refl 2))

/-- **Absolutely normal numbers are disjunctive in every base.**  For each base
    `b ≥ 2` and every finite digit string `s`, the base-`b` expansion of an
    absolutely normal number contains `s` — by `normal_imp_disjunctive` applied to
    its normality in base `b`. -/
theorem absolutely_normal_imp_disjunctive (x : ℝ) (h : IsAbsolutelyNormal x)
    (b k : ℕ) (hb : 2 ≤ b) (s : Fin k → Fin b) :
    ∃ n : ℕ, ∀ i : Fin k, nthDigit b (n + i.val) x = (s i : ℤ) :=
  normal_imp_disjunctive b k hb x (h b hb) s

/-- **e is disjunctive in every base** (consequence of the absolute-normality axiom
    `e_absolutely_normal`).  For every base `b ≥ 2` and every finite digit string
    `s : Fin k → Fin b`, the base-`b` expansion of `e` contains `s` as a contiguous block:
    some window starting at position `n` matches `s` digit-for-digit.  This is the
    qualitative "every finite pattern eventually occurs in `e`" richness that absolute
    normality entails — the disjunctive companion of `e_normal_base_10` and
    `e_irrational_necessary_for_normality`.  Like every `e_normal_*` statement in this
    file it is conditional on the open axiom `e_absolutely_normal` (no base is proved
    normal for `e` unconditionally). -/
theorem e_disjunctive (b k : ℕ) (hb : 2 ≤ b) (s : Fin k → Fin b) :
    ∃ n : ℕ, ∀ i : Fin k, nthDigit b (n + i.val) (Real.exp 1) = (s i : ℤ) :=
  absolutely_normal_imp_disjunctive (Real.exp 1) e_absolutely_normal b k hb s

end ETranscendentalOQ02
