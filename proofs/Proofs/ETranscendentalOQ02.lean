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
      rw [show n + i.val = N₀ + (n - N₀) % T + (n - N₀) / T * T + i.val from by omega]
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
