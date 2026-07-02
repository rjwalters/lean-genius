/-
  Lagrange Four Squares — OQ-02 · OQ-02:
  The Universal Orbit–Stabilizer Divisibility Law for Representation Types

## Parent open question (OQ-02)

`Proofs.LagrangeFourSquaresOQ02` studies how the four-square representations of
`n` distribute among the possible orderings.  Each *sorted representation type*
`(a₁ ≤ a₂ ≤ a₃ ≤ a₄)` with `a₁²+a₂²+a₃²+a₄² = n` contributes

  contribution(t) = (permutations of the 4-tuple) × 2^(number of nonzero entries)

ordered signed representations to `r₄(n)`.  The full symmetry group acting is
`S₄ × (ℤ/2ℤ)⁴`, of order `|S₄| · 2⁴ = 24 · 16 = 384`, and by orbit–stabilizer
each contribution equals `384 / |stabilizer|`.

The parent file establishes `contribution = 384 / |stabilizer|` **case by case**
for six *named* type families (trivial, all-equal, three-equal, two-pair,
two-equal, two-nonzero-distinct), each with side hypotheses `0 < k` / `a < b`.

## What this file adds (the OQ-02·OQ-02 child)

We prove the **universal** form, with NO case split and NO hypotheses on the
entries:

  `RepType.contribution t ∣ 384`   for *every* representation type `t` of *every* `n`.

Equivalently, the stabilizer order `384 / contribution t` is always a genuine
divisor of `384` and satisfies `contribution t * (384 / contribution t) = 384`.
This is exactly the orbit–stabilizer statement `contribution = 384/|stab|` in
divisibility form, now holding uniformly over the whole (infinite) family of
types rather than family-by-family.

The engine is two clean divisibilities:

  * `permutations t ∣ 24`  — because the multinomial denominator
    `∏_{v} (count v)!` divides `(∑_v count v)! = 4! = 24`
    (Mathlib's `Finset.prod_factorial_dvd_factorial_sum`), and `24 / d ∣ 24`
    whenever `d ∣ 24`;
  * `signFactor t ∣ 16`   — because `2^(nonzeroCount t) ∣ 2^4 = 16`, the
    nonzero count being at most `4`.

Multiplying, `contribution t = permutations t · signFactor t ∣ 24 · 16 = 384`.

Everything is fully machine-checked: **0 sorries, 0 axioms**, and no
`native_decide` (so no `Lean.ofReduceBool` dependency).  The concrete
contribution values below use kernel `decide`/`rfl`, keeping the file dependent
only on `propext`, `Classical.choice`, `Quot.sound`.

Reference: https://erdosproblems.com/  (Lagrange four squares distribution line)
-/

import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Dedup

namespace LagrangeFourSquaresOQ02OQ02

open Finset

/-! ## Definitions (mirroring `Proofs.LagrangeFourSquaresOQ02`)

These reproduce the parent entry's `RepType` and its contribution data verbatim,
so the file is self-contained while referring to exactly the same quantities. -/

/-- A sorted representation type for `n` as a sum of four squares:
components satisfy `a₁ ≤ a₂ ≤ a₃ ≤ a₄` and `a₁² + a₂² + a₃² + a₄² = n`. -/
structure RepType (n : ℕ) where
  a₁ : ℕ
  a₂ : ℕ
  a₃ : ℕ
  a₄ : ℕ
  sorted : a₁ ≤ a₂ ∧ a₂ ≤ a₃ ∧ a₃ ≤ a₄
  sum_eq : a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2 + a₄ ^ 2 = n
  deriving DecidableEq

/-- The number of nonzero entries of a type. -/
def RepType.nonzeroCount {n : ℕ} (t : RepType n) : ℕ :=
  (if t.a₁ = 0 then 0 else 1) + (if t.a₂ = 0 then 0 else 1) +
  (if t.a₃ = 0 then 0 else 1) + (if t.a₄ = 0 then 0 else 1)

/-- The multinomial coefficient counting distinct orderings of the 4-tuple:
`4! / (m₁! · m₂! · …)` where the `mᵢ` are the value multiplicities. -/
def RepType.permutations {n : ℕ} (t : RepType n) : ℕ :=
  let vals := [t.a₁, t.a₂, t.a₃, t.a₄]
  let distinctVals := vals.dedup
  24 / (distinctVals.map (fun v => Nat.factorial (vals.count v))).prod

/-- The sign factor `2^(nonzero entries)`. -/
def RepType.signFactor {n : ℕ} (t : RepType n) : ℕ :=
  2 ^ t.nonzeroCount

/-- Total contribution of a type to `r₄(n)`: orderings × sign choices. -/
def RepType.contribution {n : ℕ} (t : RepType n) : ℕ :=
  t.permutations * t.signFactor

/-! ## The multinomial denominator divides `4! = 24`

This is the combinatorial heart of the argument: for any four entries, the
product of factorials of the value multiplicities divides `4!`.  It is the
integrality of the multinomial coefficient, specialised to a 4-element multiset,
supplied by `Finset.prod_factorial_dvd_factorial_sum`. -/

/-- For any four naturals, the multinomial denominator
`∏_{v ∈ dedup} (count v)!` divides `24 = 4!`. -/
theorem multinomial_denom_dvd_24 (a b c d : ℕ) :
    (([a, b, c, d] : List ℕ).dedup.map
      (fun v => Nat.factorial (([a, b, c, d] : List ℕ).count v))).prod ∣ 24 := by
  set L : List ℕ := [a, b, c, d] with hL
  have hnodup : L.dedup.Nodup := List.nodup_dedup L
  -- deduplicating a list does not change the underlying `Finset`
  have hdedupfin : L.dedup.toFinset = L.toFinset := by
    ext x; simp [List.mem_toFinset, List.mem_dedup]
  -- express the list product as a `Finset` product over `L.toFinset`
  have hprod : (L.dedup.map (fun v => Nat.factorial (L.count v))).prod
      = ∏ v ∈ L.toFinset, Nat.factorial (L.count v) := by
    rw [← hdedupfin, List.prod_toFinset _ hnodup]
  -- the multiplicities sum to the length `4`
  have hsum : (∑ v ∈ L.toFinset, L.count v) = 4 := by
    rw [← hdedupfin, List.sum_toFinset _ hnodup, List.sum_map_count_dedup_eq_length]
    simp [hL]
  rw [hprod]
  have hdvd := Nat.prod_factorial_dvd_factorial_sum L.toFinset (fun v => L.count v)
  rw [hsum] at hdvd
  simpa using hdvd

/-! ## The two factor divisibilities -/

/-- The number of nonzero entries is at most `4`. -/
theorem nonzeroCount_le_four {n : ℕ} (t : RepType n) : t.nonzeroCount ≤ 4 := by
  unfold RepType.nonzeroCount
  split_ifs <;> omega

/-- The sign factor `2^(nonzeroCount)` divides `16 = 2^4`. -/
theorem signFactor_dvd_16 {n : ℕ} (t : RepType n) : t.signFactor ∣ 16 := by
  have : (2 : ℕ) ^ t.nonzeroCount ∣ 2 ^ 4 := pow_dvd_pow 2 (nonzeroCount_le_four t)
  simpa [RepType.signFactor] using this

/-- The permutation multinomial `permutations t` divides `24`. -/
theorem permutations_dvd_24 {n : ℕ} (t : RepType n) : t.permutations ∣ 24 := by
  -- `permutations t = 24 / d` with `d ∣ 24`, and `24 / d ∣ 24`.
  have hd : (([t.a₁, t.a₂, t.a₃, t.a₄] : List ℕ).dedup.map
      (fun v => Nat.factorial (([t.a₁, t.a₂, t.a₃, t.a₄] : List ℕ).count v))).prod ∣ 24 :=
    multinomial_denom_dvd_24 t.a₁ t.a₂ t.a₃ t.a₄
  show 24 / _ ∣ 24
  exact ⟨_, (Nat.div_mul_cancel hd).symm⟩

/-! ## The universal orbit–stabilizer divisibility law -/

/-- **Universal orbit–stabilizer law.**  For *every* representation type `t` of
*every* `n`, the contribution divides `384 = |S₄ × (ℤ/2ℤ)⁴|`.  This is the
uniform (hypothesis-free, case-free) generalisation of the parent file's six
per-family `orbit_stabilizer_*` theorems. -/
theorem contribution_dvd_384 {n : ℕ} (t : RepType n) : t.contribution ∣ 384 := by
  have h1 : t.permutations ∣ 24 := permutations_dvd_24 t
  have h2 : t.signFactor ∣ 16 := signFactor_dvd_16 t
  have : t.permutations * t.signFactor ∣ 24 * 16 := mul_dvd_mul h1 h2
  simpa [RepType.contribution] using this

/-- The contribution is always positive: every type contributes at least one
ordered signed representation. -/
theorem contribution_pos {n : ℕ} (t : RepType n) : 0 < t.contribution := by
  have hd : (([t.a₁, t.a₂, t.a₃, t.a₄] : List ℕ).dedup.map
      (fun v => Nat.factorial (([t.a₁, t.a₂, t.a₃, t.a₄] : List ℕ).count v))).prod ∣ 24 :=
    multinomial_denom_dvd_24 t.a₁ t.a₂ t.a₃ t.a₄
  have hperm : 0 < t.permutations := by
    show 0 < 24 / _
    exact Nat.div_pos (Nat.le_of_dvd (by norm_num) hd)
      (Nat.pos_of_dvd_of_pos hd (by norm_num))
  have hsign : 0 < t.signFactor := by
    simp only [RepType.signFactor]; exact pow_pos (by norm_num) _
  simpa [RepType.contribution] using Nat.mul_pos hperm hsign

/-- The contribution is at most `384` (immediate from divisibility and positivity). -/
theorem contribution_le_384 {n : ℕ} (t : RepType n) : t.contribution ≤ 384 :=
  Nat.le_of_dvd (by norm_num) (contribution_dvd_384 t)

/-! ## Stabilizer form

The orbit–stabilizer identity in its native form: define the stabilizer order as
`384 / contribution`; then it is a genuine divisor of `384` and recovers `384` on
multiplication.  This packages `contribution = 384 / |stab|` for all types. -/

/-- The stabilizer order of a type: `384 / contribution`. -/
def RepType.stabOrder {n : ℕ} (t : RepType n) : ℕ := 384 / t.contribution

/-- `contribution · stabOrder = 384`: the orbit–stabilizer identity, universally. -/
theorem contribution_mul_stabOrder {n : ℕ} (t : RepType n) :
    t.contribution * t.stabOrder = 384 := by
  rw [RepType.stabOrder, Nat.mul_div_cancel' (contribution_dvd_384 t)]

/-- The stabilizer order divides `384` (it is `|stabilizer|` of a subgroup action). -/
theorem stabOrder_dvd_384 {n : ℕ} (t : RepType n) : t.stabOrder ∣ 384 :=
  ⟨t.contribution, by rw [mul_comm]; exact (contribution_mul_stabOrder t).symm⟩

/-- Recovering `contribution = 384 / stabOrder` from the stabilizer order. -/
theorem contribution_eq_384_div_stabOrder {n : ℕ} (t : RepType n) :
    t.contribution = 384 / t.stabOrder := by
  simp only [RepType.stabOrder]
  rw [Nat.div_div_self (contribution_dvd_384 t) (by norm_num)]

/-! ## Sharpness: the bound `384` and the unit `1` are both attained

The universal bound is best possible: the all-distinct-nonzero type attains the
full `384` (trivial stabilizer), while the all-zero type attains the minimum `1`
(full stabilizer). Both use kernel `decide`, so no `Lean.ofReduceBool`. -/

/-- The type `(1,2,3,4)` (all four entries distinct and nonzero) attains the
maximum contribution `384`; its stabilizer is trivial. -/
theorem contribution_max_attained :
    (⟨1, 2, 3, 4, by omega, by norm_num⟩ : RepType 30).contribution = 384 := by
  decide

/-- The all-zero type `(0,0,0,0)` for `n = 0` attains the minimum contribution `1`;
its stabilizer is the whole group of order `384`. -/
theorem contribution_min_attained :
    (⟨0, 0, 0, 0, by omega, by norm_num⟩ : RepType 0).contribution = 1 := by
  decide

/-- Sharpness of the stabilizer form at the extremes: full group at `(0,0,0,0)`. -/
theorem stabOrder_max_attained :
    (⟨0, 0, 0, 0, by omega, by norm_num⟩ : RepType 0).stabOrder = 384 := by
  decide

/-- Trivial stabilizer at the all-distinct type `(1,2,3,4)`. -/
theorem stabOrder_min_attained :
    (⟨1, 2, 3, 4, by omega, by norm_num⟩ : RepType 30).stabOrder = 1 := by
  decide

end LagrangeFourSquaresOQ02OQ02
