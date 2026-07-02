/-
  Congruence lower bounds for the Waring number `G(k)`  (the "hard" Waring number)

  Parent gallery entry: `lagrange-four-squares-waring-g2`  (Waring's problem for
  squares, `g(2) = 4`).  Open question OQ-02 asks: **"What is `G(k)` for `k ≥ 3`?"**

  `G(k)` is the least `s` such that *every sufficiently large* natural number is a
  sum of `s` `k`-th powers.  Unlike the easier constant `g(k)` (all `n`, not just
  large ones), the exact value of `G(k)` is **open** for most `k`: only `G(2) = 4`
  (Lagrange) and `G(4) = 16` (Davenport 1939) are known, while e.g. `G(3)` is only
  pinned to `4 ≤ G(3) ≤ 7`.

  We cannot settle the open question.  What we *can* prove, completely and with no
  axioms, are the classical **elementary lower bounds** obtained from congruence
  obstructions:

  * `G(3) ≥ 4`  — cubes are `≡ 0, ±1 (mod 9)`, so a sum of three cubes is never
    `≡ 4 (mod 9)`; the residue class `4 (mod 9)` is infinite, hence no bound `s ≤ 3`
    can be universal for large `n`.  (This is the sharp lower half of the classical
    `4 ≤ G(3) ≤ 7`.)

  * `G(4) ≥ 15`  — fourth powers are `≡ 0, 1 (mod 16)`, so a sum of at most `14`
    fourth powers is never `≡ 15 (mod 16)`; the class `15 (mod 16)` is infinite,
    hence no bound `s ≤ 14` is universal.  (Davenport's `G(4) = 16` is the matching
    upper bound; the `≥ 15` obstruction is the clean elementary part.)

  Everything below is `0`-axiom.  The `decide` calls are ordinary kernel decisions
  over the finite rings `ZMod 9` / `ZMod 16`.
-/
import Mathlib

namespace WaringGgLowerBoundsOQ02

open scoped BigOperators

/-- `n` is a sum of `s` `k`-th powers of naturals:
    `n = f 0 ^ k + f 1 ^ k + ⋯ + f (s-1) ^ k` for some `f : Fin s → ℕ`. -/
def IsSumOfKthPowers (s k n : ℕ) : Prop := ∃ f : Fin s → ℕ, (∑ i, f i ^ k) = n

/-- A bound `s` is **universal for large `n`** (at exponent `k`) when every
    sufficiently large natural number is a sum of `s` `k`-th powers.  The Waring
    number `G(k)` is the least such `s`; the theorems below give lower bounds on it
    by showing small `s` are *not* universal. -/
def UniversalForLarge (s k : ℕ) : Prop := ∃ N, ∀ n, N ≤ n → IsSumOfKthPowers s k n

/-! ### Padding: more summands can only help -/

/-- Appending a zero summand: a sum of `s` `k`-th powers is also a sum of `s+1`
    of them (for `k ≠ 0`, so that `0 ^ k = 0`). -/
theorem isSumOfKthPowers_succ {s k n : ℕ} (hk : k ≠ 0)
    (h : IsSumOfKthPowers s k n) : IsSumOfKthPowers (s + 1) k n := by
  obtain ⟨f, hf⟩ := h
  refine ⟨Fin.cons 0 f, ?_⟩
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, zero_pow hk, zero_add]
  exact hf

/-- Monotonicity in the number of summands: if `s ≤ t` then any sum of `s`
    `k`-th powers is a sum of `t` `k`-th powers (`k ≠ 0`). -/
theorem isSumOfKthPowers_mono {s t k n : ℕ} (hk : k ≠ 0) (hst : s ≤ t)
    (h : IsSumOfKthPowers s k n) : IsSumOfKthPowers t k n := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hst
  induction d with
  | zero => simpa using h
  | succ d ih =>
      have hstep : IsSumOfKthPowers (s + d) k n := ih
      simpa [Nat.add_succ] using isSumOfKthPowers_succ hk hstep

/-- Congruence transport: `a ≡ b (mod n)` gives equal images in `ZMod n`. -/
theorem natCast_zmod_of_modEq {a b n : ℕ} (h : a ≡ b [MOD n]) :
    (a : ZMod n) = (b : ZMod n) :=
  (ZMod.natCast_eq_natCast_iff _ _ _).mpr h

/-! ### `G(3) ≥ 4` via cubes modulo `9` -/

/-- Every cube is `≡ 0, 1` or `8 (mod 9)` (i.e. `0` or `±1`). -/
theorem cube_zmod9 (x : ZMod 9) : x ^ 3 = 0 ∨ x ^ 3 = 1 ∨ x ^ 3 = 8 := by decide

/-- A sum of three cubes is never `≡ 4 (mod 9)`. -/
theorem three_cubes_ne_four (a b c : ZMod 9) : a ^ 3 + b ^ 3 + c ^ 3 ≠ 4 := by decide

/-- Bridge to `ℕ`: any `n ≡ 4 (mod 9)` is not a sum of three cubes. -/
theorem not_sum_three_cubes_of_mod9 {n : ℕ} (hn : (n : ZMod 9) = 4) :
    ¬ IsSumOfKthPowers 3 3 n := by
  rintro ⟨f, rfl⟩
  rw [Fin.sum_univ_three] at hn
  push_cast at hn
  exact three_cubes_ne_four _ _ _ hn

/-- The residue class `4 (mod 9)` is unbounded: for any `N` there is `n ≥ N` with
    `n ≡ 4 (mod 9)`, and such an `n` is not a sum of three cubes. -/
theorem infinitely_many_not_three_cubes (N : ℕ) :
    ∃ n, N ≤ n ∧ (n : ZMod 9) = 4 ∧ ¬ IsSumOfKthPowers 3 3 n := by
  have hmod : (9 * N + 4 : ℕ) ≡ 4 [MOD 9] := by
    unfold Nat.ModEq; omega
  have hcast : ((9 * N + 4 : ℕ) : ZMod 9) = 4 := by
    have := natCast_zmod_of_modEq hmod
    simpa using this
  exact ⟨9 * N + 4, by omega, hcast, not_sum_three_cubes_of_mod9 hcast⟩

/-- **`G(3) ≥ 4`.**  No bound `s ≤ 3` is universal for large `n`: any `s` that
    represents all sufficiently large numbers as sums of `s` cubes satisfies
    `4 ≤ s`.  Equivalently, the hard Waring number `G(3)` is at least `4`. -/
theorem waringG_three_ge_four {s : ℕ} (h : UniversalForLarge s 3) : 4 ≤ s := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨N, hN⟩ := h
  obtain ⟨n, hn_ge, hn_mod, _⟩ := infinitely_many_not_three_cubes N
  have hrep : IsSumOfKthPowers s 3 n := hN n hn_ge
  have h3 : IsSumOfKthPowers 3 3 n :=
    isSumOfKthPowers_mono (by norm_num) (by omega) hrep
  exact not_sum_three_cubes_of_mod9 hn_mod h3

/-! ### `G(4) ≥ 15` via fourth powers modulo `16`

Fourth powers take only the values `0` and `1` modulo `16`.  Hence a sum of at most
`14` fourth powers reduces modulo `16` to a sum of at most `14` values in `{0,1}`,
which never reaches `15`.  Since `15 (mod 16)` is an infinite residue class, no
bound `s ≤ 14` is universal, i.e. `G(4) ≥ 15`. -/

/-- Every fourth power is `≡ 0` or `1 (mod 16)`. -/
theorem fourth_pow_zmod16 (x : ZMod 16) : x ^ 4 = 0 ∨ x ^ 4 = 1 := by decide

/-- The fourth power of a natural number reduces mod `16` to its parity:
    `a ^ 4 % 16 = a % 2` (`0` for even `a`, `1` for odd `a`). -/
theorem fourth_pow_mod16 (a : ℕ) : a ^ 4 % 16 = a % 2 := by
  conv_lhs => rw [Nat.pow_mod]
  have hlt : a % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have h2 : a % 2 = (a % 16) % 2 := by omega
  rw [h2]
  interval_cases (a % 16) <;> rfl

/-- The mod-`16` reduction of a sum of `s ≤ 14` fourth powers equals the number of
    odd summands, `∑ i, f i % 2`, which is `≤ s` and hence never wraps past `16`. -/
theorem sum_fourth_pow_mod16 {s : ℕ} (hs : s ≤ 14) (f : Fin s → ℕ) :
    (∑ i, f i ^ 4) % 16 = ∑ i, (f i % 2) := by
  have hle : (∑ i, (f i % 2)) ≤ s := by
    have h1 : (∑ i, (f i % 2)) ≤ ∑ _i : Fin s, 1 := by
      apply Finset.sum_le_sum
      intro i _
      omega
    simpa using h1
  have hbound : (∑ i, (f i % 2)) < 16 := by omega
  have hmod : (∑ i, f i ^ 4) % 16 = (∑ i, (f i ^ 4 % 16)) % 16 :=
    Finset.sum_nat_mod _ _ _
  rw [hmod]
  simp only [fourth_pow_mod16]
  exact Nat.mod_eq_of_lt hbound

/-- Bridge to `ℕ`: any `n ≡ 15 (mod 16)` is not a sum of `s ≤ 14` fourth powers. -/
theorem not_sum_fourteen_fourth_powers_of_mod16 {s n : ℕ} (hs : s ≤ 14)
    (hn : n % 16 = 15) : ¬ IsSumOfKthPowers s 4 n := by
  rintro ⟨f, rfl⟩
  rw [sum_fourth_pow_mod16 hs f] at hn
  have hle : (∑ i, (f i % 2)) ≤ s := by
    have h1 : (∑ i, (f i % 2)) ≤ ∑ _i : Fin s, 1 := by
      apply Finset.sum_le_sum
      intro i _
      omega
    simpa using h1
  omega

/-- **`G(4) ≥ 15`.**  No bound `s ≤ 14` is universal for large `n`: any `s` that
    represents all sufficiently large numbers as sums of `s` fourth powers satisfies
    `15 ≤ s`.  (Davenport's `G(4) = 16` is the matching exact value.) -/
theorem waringG_four_ge_fifteen {s : ℕ} (h : UniversalForLarge s 4) : 15 ≤ s := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨N, hN⟩ := h
  have hn_ge : N ≤ 16 * N + 15 := by omega
  have hn_mod : (16 * N + 15) % 16 = 15 := by omega
  have hrep : IsSumOfKthPowers s 4 (16 * N + 15) := hN _ hn_ge
  exact not_sum_fourteen_fourth_powers_of_mod16 (by omega) hn_mod hrep

/-! ### Sanity anchors

The obstruction residues are genuinely reached (the classes are non-empty), so the
lower bounds are not vacuous. -/

example : ((4 : ℕ) : ZMod 9) = 4 := by decide
example : (15 : ℕ) % 16 = 15 := by rfl

end WaringGgLowerBoundsOQ02
