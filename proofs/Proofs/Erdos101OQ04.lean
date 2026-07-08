/-
# Erdős Problem #101 — OQ-04: the Solymosi–Stojaković lower bound construction

This file is the S2 ACT scaffold for OQ-04 of Erdős Problem #101.
The parent `Proofs/Erdos101Problem.lean` establishes
`PlanarPointSet`, `collinear`, `NoFiveCollinear`, `fourPointLineCount`,
and the tight elementary upper bound
`fourPointLineCount P ≤ n(n-1)/12`.  Its sibling `Proofs/Erdos101OQ01.lean`
records the **open upper bound** question (the o(n²) conjecture) and
its negative-existence refutation of Erdős's Θ(n^{3/2}) conjecture
via the Solymosi–Stojaković lower bound (recorded there as a deferred
proof obligation `solymosi_stojakovic_lower_bound : ... := by sorry`).

This file focuses on the **lower-bound construction direction**:

* `Erdos101OQ04.IsLowerBoundConstruction` — a predicate identifying a
  no-five-collinear planar point set whose four-point line count is
  at least a given lower bound (the framework abstraction).
* `Erdos101OQ04.grunbaum_lower_bound_three_halves` — Grünbaum's
  pre-Solymosi–Stojaković Ω(n^{3/2}) construction, recorded as a
  `theorem ... := by sorry` so it can be cited by other theorems
  without introducing a permanent axiom.  Path B in
  `research/problems/erdos101-problem-oq-04/state.md`.
* `Erdos101OQ04.solymosi_stojakovic_lower_bound` — the modern
  n^{2−O(1/√(log n))} bound.  Re-states
  `Erdos101OQ01.solymosi_stojakovic_lower_bound` in OQ-04's
  `IsLowerBoundConstruction` packaging (re-named here for OQ-04
  provenance); both remain deferred proof obligations.
* `Erdos101OQ04.exists_four_collinear_subset_of_count_pos` —
  unconditional: a no-five-collinear `P` with at least one four-point
  line admits an explicit 4-element collinear subset of `P.points`.
  Useful as a "witness extraction" lemma for any future construction
  PR that needs to certify its lower bound.

## The OPEN content remains the construction

OQ-01's framing — "is the upper bound o(n²)?" — records the open
*upper-bound refinement* question; OQ-04's framing — "can the
construction be formalised?" — records the open *lower-bound
discharge*.  Both are sorry-bodied in their current Lean form.  This
file's primary contribution is the OQ-04 *framework*, plus the
`exists_four_collinear_subset_of_count_pos` extraction lemma that any
future lower-bound construction PR will need.

## Path inventory (state.md S2 paths)

* **Path A** (full Solymosi–Stojaković, 5-7 sessions, ~600-1000 LOC):
  random linear projection of a high-dimensional grid; measure-
  theoretic genericity of projection direction; parameter optimisation
  in d, k.  Single biggest piece of new infrastructure: a measure-zero
  certificate for algebraic varieties in projection parameter space.
* **Path B-light** (Grünbaum n^{3/2}, 2-3 sessions, ~200-400 LOC):
  `{(i, j) ∈ F_p × F_p : i² + j ≡ 0 (mod p)}` with p prime; concrete
  ℓ ≤ n^{3/2} bound.  Fully provable in Lean with the existing
  `Mathlib.Data.ZMod.Basic` + polynomial counting infrastructure.
* **Path C** (full framework scaffold, 1-2 sessions, ~200-300 LOC):
  d-dimensional grid + 4-AP enumeration + generic projection +
  framework theorem.  Front-loads multi-session investment as
  scaffolding.

This S2 PR delivers neither path's construction; it scaffolds the
**framework** and proves the **witness-extraction** lemma so the next
ACT iteration can drop in either path's construction without
re-running setup.

References
----------
* Solymosi & Stojaković (2013), *Combinatorica* 33: 247–258.
* Erdős (1995) — original Θ(n^{3/2}) conjecture (refuted).
* Grünbaum (1972), *Arrangements and Spreads*, CBMS Reg. Conf. 10.
* Brass–Moser–Pach (2005), *Research Problems in Discrete Geometry*,
  §7.2.
-/

import Proofs.Erdos101OQ01
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

namespace Erdos101OQ04

open Classical

/- ## OQ-04 framework: lower-bound constructions

A `LowerBoundConstruction` is a no-five-collinear `PlanarPointSet`
witness whose four-point line count is bounded below by a specified
ℝ-valued threshold (typically `n^α` for some α ∈ (3/2, 2]).  The
predicate lets the OPEN constructions (Grünbaum, Solymosi–Stojaković)
be expressed as existential statements about
`IsLowerBoundConstruction P threshold`. -/

/-- `IsLowerBoundConstruction P threshold` asserts that the
no-five-collinear `PlanarPointSet` `P` has at least `threshold`
four-point lines (as a real number).  The predicate is reflexive in
construction style: a witness for `threshold = n^{3/2}` is a Grünbaum-
style construction, a witness for `threshold = n^{2 - ε/√(log n)}` is
a Solymosi–Stojaković-style construction. -/
def IsLowerBoundConstruction (P : PlanarPointSet) (threshold : ℝ) : Prop :=
  NoFiveCollinear P ∧ threshold ≤ (fourPointLineCount P : ℝ)

/- ## Witness extraction (axiom-free) -/

/-- **Witness extraction**: any no-five-collinear `P` with
`fourPointLineCount P ≥ 1` admits an explicit 4-element subset of
`P.points` whose elements are pairwise on a single line (witnessed
by two distinguished anchor points `a, b ∈ S` with `a ≠ b` and all
of `S` collinear with `a, b`).  Used as the contrapositive of "if
no 4-collinear subset exists, then `fourPointLineCount = 0`". -/
theorem exists_four_collinear_subset_of_count_pos (P : PlanarPointSet)
    (h : 1 ≤ fourPointLineCount P) :
    ∃ S : Finset (ℝ × ℝ), S ⊆ P.points ∧ S.card = 4 ∧
      ∃ a b : ℝ × ℝ, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
        ∀ p ∈ S, collinear a b p := by
  -- `fourPointLineCount P ≥ 1` ⇒ the underlying powerset-filter is nonempty.
  unfold fourPointLineCount at h
  have hpos : 0 < (P.points.powerset.filter (fun S =>
      S.card = 4 ∧
      ∃ a b : ℝ × ℝ, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
        ∀ p ∈ S, collinear a b p)).card := h
  obtain ⟨S, hS⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hS
  obtain ⟨hS_pow, hcard, hwitness⟩ := hS
  exact ⟨S, Finset.mem_powerset.mp hS_pow, hcard, hwitness⟩

/-- **Lower bound vacuous below size 4**: for `P` with fewer than 4
points, no four-point line exists.  Restatement of
`fourPointLineCount_lt_four` to fix the OQ-04 namespace conventions. -/
theorem isLowerBoundConstruction_threshold_eq_zero_of_small
    (P : PlanarPointSet) (hP : NoFiveCollinear P)
    (h : P.points.card < 4) :
    IsLowerBoundConstruction P 0 := by
  refine ⟨hP, ?_⟩
  rw [fourPointLineCount_lt_four P h]
  norm_num

/- ## Grünbaum's Ω(n^{3/2}) lower bound (recorded as deferred proof)

The pre-Solymosi–Stojaković state of the art: Grünbaum (1972)
constructed point sets with no five collinear achieving at least
$c \cdot n^{3/2}$ four-point lines.  The canonical construction is
the *parabola modulo p*:

    $G_p = \{(i, j) \in (\mathbb{F}_p)^2 : 4j \equiv -i^2 \pmod p\}$

For `p` prime, $|G_p| = p$.  The bare parabola is itself a
*general-position* set: every affine line meets it in **at most two**
points (the degree-two polynomial-roots bound — see
`parabola_inter_line_card_le_two` below), so it has *no* four-point
lines on its own.  Grünbaum's $\Omega(p^{3/2})$ four-point-line witness
is built *from* this no-three-collinear base by a further sumset /
grid construction; the parabola's general-position property is the
foundational input.  The result `grunbaum_lower_bound_three_halves`
below records the asymptotic statement; the construction itself is
deferred to Path B of the state.md S2 inventory.

Note: this statement was refuted as a *tight* lower bound by
Solymosi–Stojaković, but remains valid as a *weaker* lower bound;
Grünbaum's construction continues to be the cleanest fully-explicit
witness against any sub-$n^{3/2}$ upper bound. -/

/-- **Grünbaum's Ω(n^{3/2}) lower bound** on the maximum four-point
line count.  For every `C > 0`, there exists a planar point set `P`
with no five collinear, `|P| ≥ N`, and
`fourPointLineCount P ≥ C · |P|^{3/2}` for all sufficiently large `N`.

Reference: B. Grünbaum, *Arrangements and Spreads* (1972), CBMS
Regional Conference Series in Mathematics 10, §3.3.

This lower bound was superseded by the stronger Solymosi–Stojaković
n^{2−O(1/√(log n))} bound (recorded as
`solymosi_stojakovic_lower_bound` below and in
`Erdos101OQ01.solymosi_stojakovic_lower_bound`); both refute Erdős's
Θ(n^{3/2}) conjecture in the upper direction, but only the
Solymosi–Stojaković bound goes strictly beyond Grünbaum's witness.

Recorded as `theorem ... := by sorry` so it can be cited without
introducing a permanent axiom.  Path B in `state.md` provides the
concrete F_p construction sketch. -/
theorem grunbaum_lower_bound_three_halves :
    ∀ C : ℝ, 0 < C → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ P : PlanarPointSet, P.points.card = n ∧ NoFiveCollinear P ∧
        C * (n : ℝ) ^ (3 / 2 : ℝ) ≤ (fourPointLineCount P : ℝ) := by
  sorry

/- ## Solymosi–Stojaković n^{2−O(1/√(log n))} lower bound (OQ-04 re-statement)

Re-states the Solymosi–Stojaković existential lower bound in OQ-04's
namespace, with `IsLowerBoundConstruction`-flavoured packaging.  The
statement is *cosmetically* different from
`Erdos101OQ01.solymosi_stojakovic_lower_bound` but mathematically
equivalent (the inner `IsLowerBoundConstruction P threshold` unfolds
to exactly OQ-01's `NoFiveCollinear P ∧ threshold ≤ fourPointLineCount P`).

Note: the construction itself is OPEN (Path A in state.md, ~600-1000
LOC of measure-theoretic Lean infrastructure to formalise the random
projection of a high-dimensional grid).  Both this re-statement and
OQ-01's are deferred proof obligations. -/

/-- **Solymosi–Stojaković 2013 lower bound** (OQ-04 re-statement).

For every `C > 0`, all sufficiently large `n` admit a no-five-collinear
planar point set of size `n` with `fourPointLineCount P ≥
n^{2 - C / √(log n)}`.  Packaged in `IsLowerBoundConstruction` form.

Reference: J. Solymosi and M. Stojaković, *Combinatorica* 33 (2013),
247–258.

Recorded as `theorem ... := by sorry`; the construction is OPEN
(Path A in `state.md`, deferred to multi-session ACT).  This statement
is mathematically equivalent to
`Erdos101OQ01.solymosi_stojakovic_lower_bound`. -/
theorem solymosi_stojakovic_lower_bound :
    ∀ C : ℝ, 0 < C → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ P : PlanarPointSet, P.points.card = n ∧
        IsLowerBoundConstruction P ((n : ℝ) ^ (2 - C / Real.sqrt (Real.log n))) := by
  sorry

/- ## Asymptotic comparison: Solymosi–Stojaković strictly beats Grünbaum

For every fixed `C > 0`, the Solymosi–Stojaković rate
`n^{2 - C / √(log n)}` strictly exceeds `n^{3/2}` for all sufficiently
large `n`.  This makes the OQ-04 result *strictly stronger* than the
Grünbaum result it supersedes.

The argument is the same elementary asymptotic chain used in
`Erdos101OQ01.erdos_three_halves_conjecture_refuted`: `m ≥ 3 ⟹ log m
> 1 ⟹ √(log m) > 1 ⟹ C/√(log m) < C ⟹ 2 - C/√(log m) > 2 - C`, so
choosing `C < 1/2` makes the exponent strictly greater than `3/2`.

Proved unconditionally: independent of the lower-bound sorries. -/

/-- **Solymosi–Stojaković asymptotically dominates Grünbaum**.
For every fixed `C ∈ (0, 1/2)` and every sufficiently large `n` (with
`n ≥ 3`), the Solymosi–Stojaković exponent `2 - C / √(log n)` is
strictly greater than `3/2`. -/
theorem solymosi_stojakovic_exponent_gt_three_halves
    (C : ℝ) (hC_pos : 0 < C) (hC_lt : C < 1 / 2)
    (n : ℕ) (hn : 3 ≤ n) :
    (3 / 2 : ℝ) < 2 - C / Real.sqrt (Real.log (n : ℝ)) := by
  -- Real coercion: `n ≥ 3` gives `(n : ℝ) ≥ 3`.
  have hn_real : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_gt_one : (1 : ℝ) < (n : ℝ) := by linarith
  -- `Real.log n > 1` since `n ≥ 3 > exp 1`.
  have h_exp_lt_three : Real.exp 1 < (3 : ℝ) := by
    linarith [Real.exp_one_lt_d9]
  have h_exp_lt_n : Real.exp 1 < (n : ℝ) := by linarith
  have hlog_gt_one : (1 : ℝ) < Real.log (n : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos 1) h_exp_lt_n
    rwa [Real.log_exp] at h
  -- `√(log n) > 1`.
  have hsqrt_gt_one : (1 : ℝ) < Real.sqrt (Real.log (n : ℝ)) := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hlog_gt_one
    rwa [Real.sqrt_one] at h
  have hsqrt_pos : (0 : ℝ) < Real.sqrt (Real.log (n : ℝ)) := by linarith
  -- `C / √(log n) < C < 1/2`.
  have h_frac_lt_C : C / Real.sqrt (Real.log (n : ℝ)) < C := by
    rw [div_lt_iff₀ hsqrt_pos]
    nlinarith [hsqrt_gt_one, hC_pos]
  linarith

/- ## S3-B1 (Grünbaum F_p² parabola — foundational definition + cardinality)

The Grünbaum parabola modulo `p` is the `(ZMod p)²` subset

    G_p := {(i, j) ∈ (ZMod p) × (ZMod p) : 4·j = -(i·i)}.

For `p ≥ 3` prime, the map `i ↦ (i, -i² · 4⁻¹)` is a bijection
`ZMod p ≃ G_p`, so `|G_p| = p`.

This iteration delivers only the foundational object plus its
cardinality.  The 4-collinear count bound `Ω(p^{3/2})`, the
embedding `(ZMod p)² ↪ ℝ²`, and the downstream
`IsLowerBoundConstruction` instance are deferred to S3-B2+.

Reference: Grünbaum (1972), *Arrangements and Spreads*, §3.3;
Brass–Moser–Pach (2005), *Research Problems in Discrete Geometry*,
§7.2 (orchard regime). -/

namespace Grunbaum

/-- The Grünbaum parabola in `(ZMod p) × (ZMod p)`: the set of
points satisfying `4·j = -(i·i)`. -/
def parabola (p : ℕ) [NeZero p] : Finset (ZMod p × ZMod p) :=
  Finset.univ.filter (fun x : ZMod p × ZMod p => 4 * x.2 = -(x.1 * x.1))

/-- The parameterisation `i ↦ (i, -i² · 4⁻¹)`. -/
def param (p : ℕ) : ZMod p → ZMod p × ZMod p :=
  fun i => (i, -(i * i) * (4 : ZMod p)⁻¹)

/-- The parameterisation is injective: distinct `i` give distinct first
coordinates. -/
theorem param_injective (p : ℕ) : Function.Injective (param p) := by
  intro a b hab
  simpa [param] using congrArg Prod.fst hab

/-- For `p` prime with `p ≠ 2`, the constant `(4 : ZMod p)` is nonzero.
Equivalently `p ∤ 4`, which (for prime `p`) forces `p = 2`. -/
theorem four_ne_zero (p : ℕ) [hp_fact : Fact p.Prime] (hp : p ≠ 2) :
    (4 : ZMod p) ≠ 0 := by
  have hp_prime : Nat.Prime p := hp_fact.out
  intro h
  have h' : ((4 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  have h_dvd : (p : ℕ) ∣ 4 := (ZMod.natCast_eq_zero_iff 4 p).mp h'
  have h_le : p ≤ 4 := Nat.le_of_dvd (by norm_num) h_dvd
  have h_ge : 2 ≤ p := hp_prime.two_le
  interval_cases p
  · exact hp rfl                        -- p = 2
  · norm_num at h_dvd                   -- p = 3 does not divide 4
  · exact absurd hp_prime (by decide)   -- p = 4 not prime

/-- The parameterised point `(i, -i² · 4⁻¹)` lies on the parabola.
The verification reduces to `4 · 4⁻¹ = 1`, valid since `(4 : ZMod p)`
is invertible when `p` is an odd prime. -/
theorem param_mem_parabola (p : ℕ) [NeZero p] [Fact p.Prime] (hp : p ≠ 2)
    (i : ZMod p) : param p i ∈ parabola p := by
  rw [parabola, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  show (4 : ZMod p) * (-(i * i) * (4 : ZMod p)⁻¹) = -(i * i)
  have h4 := four_ne_zero p hp
  have h_assoc : (4 : ZMod p) * (-(i * i) * (4 : ZMod p)⁻¹)
              = -(i * i) * ((4 : ZMod p) * (4 : ZMod p)⁻¹) := by ring
  rw [h_assoc, mul_inv_cancel₀ h4, mul_one]

/-- A point `x` lies on the parabola iff it equals the parameter image
of its first coordinate.  Direction `→` uses `mul_left_cancel₀` with
`(4 : ZMod p) ≠ 0`; direction `←` follows from `param_mem_parabola`. -/
theorem mem_parabola_iff_eq_param (p : ℕ) [NeZero p] [Fact p.Prime]
    (hp : p ≠ 2) (x : ZMod p × ZMod p) :
    x ∈ parabola p ↔ x = param p x.1 := by
  rw [parabola, Finset.mem_filter]
  constructor
  · rintro ⟨_, hxeq⟩
    have h4 := four_ne_zero p hp
    have hx2 : x.2 = -(x.1 * x.1) * (4 : ZMod p)⁻¹ := by
      have hmul : (4 : ZMod p) * x.2
                = (4 : ZMod p) * (-(x.1 * x.1) * (4 : ZMod p)⁻¹) := by
        rw [hxeq]
        have h_assoc : (4 : ZMod p) * (-(x.1 * x.1) * (4 : ZMod p)⁻¹)
                    = -(x.1 * x.1) * ((4 : ZMod p) * (4 : ZMod p)⁻¹) := by
          ring
        rw [h_assoc, mul_inv_cancel₀ h4, mul_one]
      exact mul_left_cancel₀ h4 hmul
    exact Prod.ext rfl hx2
  · intro hx
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hx]
    show (4 : ZMod p) * (param p x.1).2 = -((param p x.1).1 * (param p x.1).1)
    have h4 := four_ne_zero p hp
    simp only [param]
    have h_assoc : (4 : ZMod p) * (-(x.1 * x.1) * (4 : ZMod p)⁻¹)
                = -(x.1 * x.1) * ((4 : ZMod p) * (4 : ZMod p)⁻¹) := by ring
    rw [h_assoc, mul_inv_cancel₀ h4, mul_one]

/-- The parabola equals the image of the parameter map on `Finset.univ`. -/
theorem parabola_eq_image (p : ℕ) [NeZero p] [Fact p.Prime] (hp : p ≠ 2) :
    parabola p = (Finset.univ : Finset (ZMod p)).image (param p) := by
  ext x
  rw [Finset.mem_image, mem_parabola_iff_eq_param p hp]
  constructor
  · intro hx
    exact ⟨x.1, Finset.mem_univ _, hx.symm⟩
  · rintro ⟨i, _, hi⟩
    subst hi
    rfl

/-- **Cardinality of the Grünbaum parabola** (S3-B1 deliverable).

For `p` prime with `p ≠ 2`, the F_p²-parabola `G_p = {(i,j) : 4j = -i²}`
has cardinality exactly `p`, via the bijection `i ↦ (i, -i² · 4⁻¹)`. -/
theorem parabola_card (p : ℕ) [NeZero p] [Fact p.Prime] (hp : p ≠ 2) :
    (parabola p).card = p := by
  rw [parabola_eq_image p hp,
      Finset.card_image_of_injective _ (param_injective p),
      Finset.card_univ]
  exact ZMod.card p

/- ## S3-B2 (parabola secant bound — general position / no three collinear)

The Grünbaum parabola is a *general-position* set: over the field
`ZMod p` (`p` an odd prime), every affine line
`{(x,y) : α·x + β·y = γ}` with `(α,β) ≠ (0,0)` meets the parabola in
**at most two** points.  Equivalently, no three points of the parabola
are collinear.

This is the foundational "no three in a line" property that any
sumset/grid lower-bound construction built on top of the parabola
needs as input.  The proof is purely elementary (no `Polynomial`
machinery): substituting `y = -x²·4⁻¹` into the line equation yields a
quadratic `(-β)·x² + (4α)·x + (-4γ) = 0` whose leading pair `(-β, 4α)`
is nonzero, and a field-theoretic three-roots argument shows it has at
most two solutions. -/

/-- A nonzero quadratic over any field has at most two roots: there is
no triple of pairwise-distinct field elements all satisfying
`a·t² + b·t + c = 0` when `(a, b) ≠ (0, 0)`.  Elementary divided-
difference argument, no `Polynomial` import. -/
private theorem no_three_quadratic_roots {F : Type*} [Field F]
    (a b c : F) (hab : ¬ (a = 0 ∧ b = 0)) (i j k : F)
    (hi : a * i ^ 2 + b * i + c = 0) (hj : a * j ^ 2 + b * j + c = 0)
    (hk : a * k ^ 2 + b * k + c = 0)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : False := by
  -- Divided differences: `(i - j)·(a·(i+j) + b) = 0`, and `i ≠ j`.
  have e1 : a * (i + j) + b = 0 := by
    have hd : (i - j) * (a * (i + j) + b) = 0 := by linear_combination hi - hj
    rcases mul_eq_zero.mp hd with h | h
    · exact absurd (sub_eq_zero.mp h) hij
    · exact h
  have e2 : a * (j + k) + b = 0 := by
    have hd : (j - k) * (a * (j + k) + b) = 0 := by linear_combination hj - hk
    rcases mul_eq_zero.mp hd with h | h
    · exact absurd (sub_eq_zero.mp h) hjk
    · exact h
  -- Subtracting the two: `a·(i - k) = 0`, and `i ≠ k`, so `a = 0`.
  have ha : a = 0 := by
    have hd : a * (i - k) = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.mp hd with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hik
  -- Then `e1` forces `b = 0`, contradicting `(a, b) ≠ (0, 0)`.
  have hb : b = 0 := by rw [ha, zero_mul, zero_add] at e1; exact e1
  exact hab ⟨ha, hb⟩

/-- **Parabola secant bound** (S3-B2 deliverable).

For `p` an odd prime, every affine line `{(x,y) : α·x + β·y = γ}` with
`(α, β) ≠ (0, 0)` meets the Grünbaum parabola in at most two points.
Equivalently: the parabola is in general position — no three of its
points are collinear.  This is the no-three-in-a-line property that
underpins any lower-bound construction built on the parabola; the bare
parabola has *no* four-point lines. -/
theorem parabola_inter_line_card_le_two (p : ℕ) [NeZero p] [Fact p.Prime]
    (hp : p ≠ 2) (α β γ : ZMod p) (hαβ : ¬ (α = 0 ∧ β = 0)) :
    ((parabola p).filter (fun x => α * x.1 + β * x.2 = γ)).card ≤ 2 := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card_iff.mp hcon
  simp only [Finset.mem_filter] at hx hy hz
  have h4 := four_ne_zero p hp
  have h44 : (4 : ZMod p) * (4 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ h4
  -- On the parabola the second coordinate is determined by the first.
  have second : ∀ w : ZMod p × ZMod p, w ∈ parabola p →
      w.2 = -(w.1 * w.1) * (4 : ZMod p)⁻¹ := by
    intro w hw
    have h := (mem_parabola_iff_eq_param p hp w).mp hw
    have h2 := congrArg Prod.snd h
    simpa [param] using h2
  -- The first coordinate is injective on the parabola.
  have firstInj : ∀ u v : ZMod p × ZMod p, u ∈ parabola p → v ∈ parabola p →
      u.1 = v.1 → u = v := by
    intro u v hu hv h1
    rw [(mem_parabola_iff_eq_param p hp u).mp hu,
        (mem_parabola_iff_eq_param p hp v).mp hv, h1]
  -- Substituting `w.2` into the line equation gives a quadratic in `w.1`.
  have quad : ∀ w : ZMod p × ZMod p, w ∈ parabola p →
      α * w.1 + β * w.2 = γ →
      (-β) * w.1 ^ 2 + (4 * α) * w.1 + (-(4 * γ)) = 0 := by
    intro w hw hline
    rw [second w hw] at hline
    have step : (4 : ZMod p) * (β * (-(w.1 * w.1) * (4 : ZMod p)⁻¹))
        = -(β * (w.1 * w.1)) := by
      rw [show (4 : ZMod p) * (β * (-(w.1 * w.1) * (4 : ZMod p)⁻¹))
            = -(β * (w.1 * w.1)) * ((4 : ZMod p) * (4 : ZMod p)⁻¹) from by ring,
          h44, mul_one]
    have e4 : (4 : ZMod p) * (α * w.1) + (4 : ZMod p) * (β * (-(w.1 * w.1)
        * (4 : ZMod p)⁻¹)) = (4 : ZMod p) * γ := by rw [← mul_add, hline]
    rw [step] at e4
    linear_combination e4
  have qx := quad x hx.1 hx.2
  have qy := quad y hy.1 hy.2
  have qz := quad z hz.1 hz.2
  -- The first coordinates are pairwise distinct (else the points coincide).
  have hx1 : x.1 ≠ y.1 := fun h => hxy (firstInj x y hx.1 hy.1 h)
  have hx2 : x.1 ≠ z.1 := fun h => hxz (firstInj x z hx.1 hz.1 h)
  have hy2 : y.1 ≠ z.1 := fun h => hyz (firstInj y z hy.1 hz.1 h)
  -- The leading pair `(-β, 4α)` is nonzero.
  have hab : ¬ ((-β : ZMod p) = 0 ∧ (4 * α : ZMod p) = 0) := by
    rintro ⟨hb, ha⟩
    exact hαβ ⟨(mul_eq_zero.mp ha).resolve_left h4, neg_eq_zero.mp hb⟩
  exact no_three_quadratic_roots (-β) (4 * α) (-(4 * γ)) hab x.1 y.1 z.1
    qx qy qz hx1 hx2 hy2

/-- **No three collinear** (corollary restatement).  For `p` an odd
prime, the Grünbaum parabola contains no three points on a common
affine line with direction `(α, β) ≠ (0, 0)`. -/
theorem parabola_no_three_collinear (p : ℕ) [NeZero p] [Fact p.Prime]
    (hp : p ≠ 2) (α β γ : ZMod p) (hαβ : ¬ (α = 0 ∧ β = 0))
    (S : Finset (ZMod p × ZMod p)) (hS : S ⊆ parabola p)
    (hline : ∀ w ∈ S, α * w.1 + β * w.2 = γ) :
    S.card ≤ 2 := by
  refine le_trans (Finset.card_le_card ?_) (parabola_inter_line_card_le_two p hp α β γ hαβ)
  intro w hw
  rw [Finset.mem_filter]
  exact ⟨hS hw, hline w hw⟩

/- ## S3-B3 — realizing the mod-`p` arc as a concrete `PlanarPointSet` in ℝ²

The parent gallery's incidence framework (`PlanarPointSet`, `collinear`,
`NoFiveCollinear`, `fourPointLineCount`) lives over **ℝ²**, whereas the
general-position result above ("no three collinear") is proved over the
finite field `ZMod p`.  This section bridges the two: the Grünbaum
parabola lifts to an explicit `p`-point set in ℝ² that is in general
position in the gallery's *own* determinant-collinearity sense, hence
satisfies `NoFiveCollinear`.

The lift is the coordinatewise canonical-representative map
`embed (i, j) = (i.val, j.val) : ℝ × ℝ`, with `ZMod.val` taking values
in `{0, …, p-1}`.  The key arithmetic fact is that collinearity over ℝ
of three lifted points is an **integer** determinant vanishing
(`= 0` in ℤ, since all coordinates are integers), which reduces mod `p`
to collinearity over `ZMod p`.  Thus the proven `ZMod p` arc property
transfers to a *bona fide* real arc — no new geometry, only a
ℝ → ℤ → `ZMod p` cast chain.

Honest scope: the resulting set is an **arc** (no three collinear), so
its `fourPointLineCount` is `0`.  It is the verified general-position
base in ℝ² on top of which a four-point-line lower-bound construction
must be built — it is not itself a lower-bound witness. -/

/-- The canonical-representative embedding `ZMod p × ZMod p ↪ ℝ × ℝ`,
sending each coordinate to its `ZMod.val` representative in `{0,…,p-1}`
cast into ℝ. -/
noncomputable def embed {p : ℕ} (w : ZMod p × ZMod p) : ℝ × ℝ :=
  ((w.1.val : ℝ), (w.2.val : ℝ))

/-- `embed` is injective: `ZMod.val` is injective and `ℕ ↪ ℝ`. -/
theorem embed_injective (p : ℕ) [NeZero p] :
    Function.Injective (embed : ZMod p × ZMod p → ℝ × ℝ) := by
  intro x y h
  simp only [embed, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have e1 : x.1.val = y.1.val := by exact_mod_cast h1
  have e2 : x.2.val = y.2.val := by exact_mod_cast h2
  exact Prod.ext (ZMod.val_injective p e1) (ZMod.val_injective p e2)

/-- **ℝ → `ZMod p` collinearity transfer.**  If three lifted parabola
points are collinear in ℝ² (gallery determinant sense), then the
underlying `ZMod p` points satisfy the same determinant relation.  The
ℝ-determinant of integer coordinates is an integer that vanishes, hence
vanishes mod `p`. -/
theorem embed_collinear_imp_zdet (p : ℕ) [NeZero p]
    (a b c : ZMod p × ZMod p) (h : collinear (embed a) (embed b) (embed c)) :
    (b.1 - a.1) * (c.2 - a.2) = (c.1 - a.1) * (b.2 - a.2) := by
  simp only [collinear, embed] at h
  -- The ℝ equation between integer-casts forces the integer equation.
  have hint : ((b.1.val : ℤ) - a.1.val) * ((c.2.val : ℤ) - a.2.val)
            = ((c.1.val : ℤ) - a.1.val) * ((b.2.val : ℤ) - a.2.val) := by
    exact_mod_cast h
  -- Reduce mod `p`; canonical representatives cast back to themselves.
  have hz := congrArg (fun n : ℤ => (n : ZMod p)) hint
  push_cast at hz
  simpa [ZMod.natCast_zmod_val] using hz

/-- **No three collinear over `ZMod p`, determinant form.**  Three
distinct parabola points cannot satisfy the gallery determinant
collinearity relation over `ZMod p`.  Derived from
`parabola_no_three_collinear`: the determinant relation places the
three points on the common affine line through `a` and `b`. -/
theorem parabola_no_three_collinear_zdet (p : ℕ) [NeZero p] [Fact p.Prime]
    (hp : p ≠ 2) (a b c : ZMod p × ZMod p)
    (ha : a ∈ parabola p) (hb : b ∈ parabola p) (hc : c ∈ parabola p)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hdet : (b.1 - a.1) * (c.2 - a.2) = (c.1 - a.1) * (b.2 - a.2)) : False := by
  -- Line through `a`, `b`: direction `(α, β) = (b.2 - a.2, a.1 - b.1)`.
  have hαβ : ¬ ((b.2 - a.2 : ZMod p) = 0 ∧ (a.1 - b.1 : ZMod p) = 0) := by
    rintro ⟨h1, h2⟩
    exact hab (Prod.ext (sub_eq_zero.mp h2) (sub_eq_zero.mp h1).symm)
  have hsub : ({a, b, c} : Finset (ZMod p × ZMod p)) ⊆ parabola p := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> assumption
  have hline : ∀ w ∈ ({a, b, c} : Finset (ZMod p × ZMod p)),
      (b.2 - a.2) * w.1 + (a.1 - b.1) * w.2
        = (b.2 - a.2) * a.1 + (a.1 - b.1) * a.2 := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · ring
    · ring
    · linear_combination -hdet
  have hcard : ({a, b, c} : Finset (ZMod p × ZMod p)).card = 3 :=
    Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  have hle := parabola_no_three_collinear p hp (b.2 - a.2) (a.1 - b.1)
      ((b.2 - a.2) * a.1 + (a.1 - b.1) * a.2) hαβ {a, b, c} hsub hline
  rw [hcard] at hle
  omega

/-- The lifted parabola: the image of the `ZMod p` parabola under
`embed`, an explicit `p`-point subset of ℝ². -/
noncomputable def realParabola (p : ℕ) [NeZero p] : Finset (ℝ × ℝ) :=
  (parabola p).image embed

/-- The lifted parabola has exactly `p` points (`embed` injective,
`parabola` has `p` points). -/
theorem realParabola_card (p : ℕ) [NeZero p] [Fact p.Prime] (hp : p ≠ 2) :
    (realParabola p).card = p := by
  rw [realParabola, Finset.card_image_of_injective _ (embed_injective p),
      parabola_card p hp]

/-- **No three collinear in ℝ².**  Three distinct points of the lifted
parabola are never collinear in the gallery's determinant sense — the
real arc property, transferred from `ZMod p` via `embed_collinear_imp_zdet`
and `parabola_no_three_collinear_zdet`. -/
theorem realParabola_no_three_collinear (p : ℕ) [NeZero p] [Fact p.Prime]
    (hp : p ≠ 2) (A B C : ℝ × ℝ)
    (hA : A ∈ realParabola p) (hB : B ∈ realParabola p) (hC : C ∈ realParabola p)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    ¬ collinear A B C := by
  intro hcol
  rw [realParabola, Finset.mem_image] at hA hB hC
  obtain ⟨a, ha, rfl⟩ := hA
  obtain ⟨b, hb, rfl⟩ := hB
  obtain ⟨c, hc, rfl⟩ := hC
  have hab : a ≠ b := fun h => hAB (by rw [h])
  have hac : a ≠ c := fun h => hAC (by rw [h])
  have hbc : b ≠ c := fun h => hBC (by rw [h])
  exact parabola_no_three_collinear_zdet p hp a b c ha hb hc hab hac hbc
    (embed_collinear_imp_zdet p a b c hcol)

/-- **The lifted parabola as a `PlanarPointSet`** (S3-B3 deliverable).
An explicit `p`-point planar set realizing the mod-`p` Grünbaum arc in
the gallery's ℝ² incidence framework. -/
noncomputable def realParabolaSet (p : ℕ) [NeZero p] [Fact p.Prime]
    (hp : p ≠ 2) : PlanarPointSet where
  points := realParabola p
  size_pos := by
    rw [realParabola_card p hp]; exact (Fact.out : p.Prime).pos

/-- **The lifted parabola has no five collinear points** — indeed no
three.  Thus it is a valid input to the gallery's four-point-line
machinery (`NoFiveCollinear`), realized in ℝ² with `0` axioms. -/
theorem realParabolaSet_noFiveCollinear (p : ℕ) [NeZero p] [Fact p.Prime]
    (hp : p ≠ 2) : NoFiveCollinear (realParabolaSet p hp) := by
  intro A B C _ _ hA hB hC _ _ hAB hAC _ _ hBC _ _ _ _ _
  rintro ⟨hcol, -, -⟩
  exact realParabola_no_three_collinear p hp A B C hA hB hC hAB hAC hBC hcol

/-- **The lifted parabola has zero four-point lines** — formalizing the
honest scope.  Being an arc (no three collinear), a fortiori no four of
its points lie on a common line, so `fourPointLineCount` is `0`.  This
makes explicit that the bare arc is *not* a four-point-line lower-bound
witness: the Ω(p^{3/2}) count must come from the sumset/grid
construction built on top of this general-position base. -/
theorem realParabolaSet_fourPointLineCount_zero (p : ℕ) [NeZero p]
    [Fact p.Prime] (hp : p ≠ 2) :
    fourPointLineCount (realParabolaSet p hp) = 0 := by
  rw [fourPointLineCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro S hS
  simp only [Finset.mem_powerset] at hS
  rintro ⟨hScard, a, b, ha, hb, hab, hline⟩
  -- A four-element set on a common line through `a ≠ b` contains a third
  -- point `c`, giving three collinear points of the arc — impossible.
  -- `S` has four points, so it is not contained in `{a, b}`: a third
  -- point `c ∈ S` exists, distinct from both `a` and `b`.
  have hthird : ∃ c ∈ S, c ∉ ({a, b} : Finset (ℝ × ℝ)) := by
    by_contra hcon
    push_neg at hcon
    have hSsub : S ⊆ ({a, b} : Finset (ℝ × ℝ)) := fun x hx => hcon x hx
    have hle := Finset.card_le_card hSsub
    rw [hScard, Finset.card_pair hab] at hle
    omega
  obtain ⟨c, hcS, hcab⟩ := hthird
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcab
  push_neg at hcab
  exact realParabola_no_three_collinear p hp a b c (hS ha) (hS hb) (hS hcS)
    hab (fun h => hcab.1 h.symm) (fun h => hcab.2 h.symm)
    (hline c hcS)

end Grunbaum

/- ## Non-vacuous framework floor (axiom-free)

The `Grunbaum.realParabolaSet` witness above is an *arc*: it satisfies
`fourPointLineCount = 0` (`realParabolaSet_fourPointLineCount_zero`), so
it inhabits only the trivial `IsLowerBoundConstruction _ 0`.  The two
OPEN construction theorems (`grunbaum_lower_bound_three_halves`,
`solymosi_stojakovic_lower_bound`) target thresholds that *grow* with
`n`, but neither has been discharged yet.  Between the arc's zero and
those asymptotic targets there is a basic non-vacuity question the file
does not otherwise answer: is `IsLowerBoundConstruction P t` inhabited
for *any* positive threshold `t` by a set of **more than four** points
(so it is not the degenerate `≤ 4`-point regime handled vacuously by
`isLowerBoundConstruction_threshold_eq_zero_of_small`)?

This section closes that gap with the explicit 5-point set

    W = {(0,0), (1,0), (2,0), (3,0), (0,1)} ⊂ ℝ²,

whose four collinear `x`-axis points form a single four-point line and
whose fifth point `(0,1)` lies off that line.  Hence `W` has no five
collinear points and `fourPointLineCount W ≥ 1`, giving
`IsLowerBoundConstruction W 1` with `|W| = 5 > 4`.  Fully explicit,
`0` axioms — the minimal certificate that the framework floor strictly
exceeds the arc's zero. -/

/-- The explicit 5-point witness: four collinear points on the `x`-axis
plus one point off it. -/
noncomputable def witnessPoints : Finset (ℝ × ℝ) :=
  {(0, 0), (1, 0), (2, 0), (3, 0), (0, 1)}

/-- `witnessPoints` has exactly five (distinct) points. -/
theorem witnessPoints_card : witnessPoints.card = 5 := by
  rw [witnessPoints, Finset.card_insert_of_notMem]
  · rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · simp
        · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
      · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
    · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
  · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]

/-- The witness set as a `PlanarPointSet`. -/
noncomputable def witnessSet : PlanarPointSet where
  points := witnessPoints
  size_pos := by rw [witnessPoints_card]; norm_num

/-- The witness has at least one four-point line: the four `x`-axis
points `{(0,0),(1,0),(2,0),(3,0)}` are collinear through `(0,0)` and
`(1,0)`. -/
theorem witnessSet_fourPointLineCount_pos :
    1 ≤ fourPointLineCount witnessSet := by
  rw [fourPointLineCount]
  apply Finset.card_pos.mpr
  refine ⟨{(0, 0), (1, 0), (2, 0), (3, 0)}, ?_⟩
  rw [Finset.mem_filter, Finset.mem_powerset]
  refine ⟨?_, ?_, (0, 0), (1, 0), ?_, ?_, ?_, ?_⟩
  · -- subset of the witness points
    intro x hx
    show x ∈ witnessPoints
    rw [witnessPoints]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    tauto
  · -- the line has exactly four points
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · simp
        · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
      · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
    · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
  · -- (0,0) ∈ line
    simp
  · -- (1,0) ∈ line
    simp
  · -- (0,0) ≠ (1,0)
    norm_num [Prod.ext_iff]
  · -- every point of the line is collinear with (0,0), (1,0)
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp [collinear]

/-- The witness has no five collinear points: any five distinct points
are all of `W`, and `(0,0),(1,0),(0,1)` are not collinear, so they
cannot all lie on a common line. -/
theorem witnessSet_noFiveCollinear : NoFiveCollinear witnessSet := by
  intro a b c d e ha hb hc hd he hab hac had hae hbc hbd hbe hcd hce hde
  rintro ⟨hcol_c, hcol_d, hcol_e⟩
  -- {a,b,c,d,e} ⊆ witnessSet.points, and both have card 5, so they are equal.
  have hsub : ({a, b, c, d, e} : Finset (ℝ × ℝ)) ⊆ witnessSet.points := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hcard5 : ({a, b, c, d, e} : Finset (ℝ × ℝ)).card = 5 := by
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · simp
          · simp [hde]
        · simp [hcd, hce]
      · simp [hbc, hbd, hbe]
    · simp [hab, hac, had, hae]
  have heq : ({a, b, c, d, e} : Finset (ℝ × ℝ)) = witnessSet.points :=
    Finset.eq_of_subset_of_card_le hsub
      (le_of_eq (by
        show witnessSet.points.card = ({a, b, c, d, e} : Finset (ℝ × ℝ)).card
        rw [show witnessSet.points = witnessPoints from rfl, witnessPoints_card,
            hcard5]))
  -- Every witness point lies on the line through a, b.
  have hline : ∀ q ∈ witnessSet.points, collinear a b q := by
    intro q hq
    rw [← heq] at hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · unfold collinear; ring
    · unfold collinear; ring
    · exact hcol_c
    · exact hcol_d
    · exact hcol_e
  -- Apply to (0,0), (1,0), (0,1), all in witnessSet.points.
  have hmem : ∀ p ∈ witnessPoints, p ∈ witnessSet.points := fun p hp => hp
  have l00 : collinear a b (0, 0) :=
    hline _ (hmem _ (by rw [witnessPoints]; simp))
  have l10 : collinear a b (1, 0) :=
    hline _ (hmem _ (by rw [witnessPoints]; simp))
  have l01 : collinear a b (0, 1) :=
    hline _ (hmem _ (by rw [witnessPoints]; simp))
  -- Three points on the line through a ≠ b are mutually collinear.
  have hbad : collinear ((0, 0) : ℝ × ℝ) (1, 0) (0, 1) :=
    collinear_any_triple hab l00 l10 l01
  -- But (0,0), (1,0), (0,1) are not collinear: contradiction.
  simp [collinear] at hbad

/-- **Non-vacuous framework floor** (this session's deliverable).  The
explicit witness `W` satisfies `IsLowerBoundConstruction W 1`: it has no
five collinear points and at least one four-point line. -/
theorem witnessSet_isLowerBoundConstruction :
    IsLowerBoundConstruction witnessSet 1 :=
  ⟨witnessSet_noFiveCollinear, by exact_mod_cast witnessSet_fourPointLineCount_pos⟩

/-- **The framework floor exceeds the arc's zero.**  There is a planar
point set with strictly more than four points that is a lower-bound
construction for a positive threshold.  This distinguishes the
`IsLowerBoundConstruction` predicate from both the vacuous `≤ 4`-point
regime and the `fourPointLineCount = 0` arc, without depending on either
of the OPEN asymptotic construction sorries. -/
theorem exists_isLowerBoundConstruction_pos :
    ∃ P : PlanarPointSet, 4 < P.points.card ∧ IsLowerBoundConstruction P 1 :=
  ⟨witnessSet, by
    rw [show witnessSet.points = witnessPoints from rfl, witnessPoints_card]
    norm_num, witnessSet_isLowerBoundConstruction⟩

/- ## Raising the framework floor: a construction with two four-point lines

The `witnessSet` above achieves `IsLowerBoundConstruction _ 1` — one
four-point line.  A single four-point line uses only four points, so
five-point sets can carry at most one such line; indeed **no** set of
exactly five points has two four-point lines (two distinct four-point
lines meet in at most one point, so already require `4 + 4 - 1 = 7`
distinct points).  Raising the floor from `1` to `2` therefore forces a
genuinely larger, structurally different construction: the minimal one
is a *cross* of two four-point lines sharing a single point.

We use the explicit 7-point set

    X = {(0,0),(1,0),(2,0),(3,0),(0,1),(0,2),(0,3)} ⊂ ℝ²,

the union of the four `x`-axis points and three further `y`-axis points,
meeting at the origin.  Its two four-point lines are the `x`-axis
`{(0,0),(1,0),(2,0),(3,0)}` and the `y`-axis
`{(0,0),(0,1),(0,2),(0,3)}`, giving `fourPointLineCount X ≥ 2`; and it
has no five collinear points, so `IsLowerBoundConstruction X 2`.

The no-five-collinear proof is powered by two reusable "one rich
coordinate direction" lemmas about the gallery's determinant
`collinear`, both fully general (not tied to this witness):

* `collinear_snd_inj` — on a *non-horizontal* line, the second
  coordinate is injective: two collinear-with-`a,b` points sharing a
  `y`-value coincide.  Hence a non-horizontal line meets any set with
  `≤ k` distinct `y`-values in `≤ k` points.
* `collinear_snd_eq_of_horiz` — on a *horizontal* line (`a.2 = b.2`,
  `a.1 ≠ b.1`) every collinear point has that same `y`-value.

Since the cross set has only the four `y`-values `{0,1,2,3}`, a
non-horizontal line hits at most four of its points (one per `y`),
while a horizontal line hits only the four `x`-axis points; either way
fewer than five.  This remains a *constant*-size witness: the OPEN
content is the asymptotic Ω(n^{3/2}) / n^{2−o(1)} growth recorded in the
two deferred construction theorems above. -/

/-- **Second-coordinate injectivity on a non-horizontal line.**  If `p`
and `q` are both collinear with the distinct-`y` anchor pair `a, b`
(`a.2 ≠ b.2`) and share the same second coordinate, they are equal.
General-purpose collinearity lemma: a non-vertical-direction... more
precisely a *non-horizontal* line is the graph of `x` as a function of
`y`, so it meets each horizontal level in at most one point. -/
theorem collinear_snd_inj {a b p q : ℝ × ℝ} (hp : collinear a b p)
    (hq : collinear a b q) (hab : a.2 ≠ b.2) (hpq : p.2 = q.2) : p = q := by
  unfold collinear at hp hq
  have hb2 : b.2 - a.2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have key : (p.1 - q.1) * (b.2 - a.2) = 0 := by
    linear_combination hq - hp + (b.1 - a.1) * hpq
  have hp1 : p.1 = q.1 := sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hb2)
  exact Prod.ext hp1 hpq

/-- **Constant second coordinate on a horizontal line.**  If `a, b` have
equal second coordinate but distinct first coordinate (a genuinely
horizontal segment) then every point `p` collinear with `a, b` has that
same second coordinate. -/
theorem collinear_snd_eq_of_horiz {a b p : ℝ × ℝ} (hp : collinear a b p)
    (hab2 : a.2 = b.2) (hab1 : a.1 ≠ b.1) : p.2 = a.2 := by
  unfold collinear at hp
  have hb1 : b.1 - a.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hab1)
  have key : (b.1 - a.1) * (p.2 - a.2) = 0 := by
    linear_combination hp - (p.1 - a.1) * hab2
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hb1)

/-- The explicit 7-point cross: four `x`-axis points and three further
`y`-axis points, meeting at the origin. -/
noncomputable def crossPoints : Finset (ℝ × ℝ) :=
  {(0, 0), (1, 0), (2, 0), (3, 0), (0, 1), (0, 2), (0, 3)}

/-- The four second coordinates occurring in `crossPoints` are exactly
`{0, 1, 2, 3}`. -/
theorem crossPoints_snd_mem {p : ℝ × ℝ} (h : p ∈ crossPoints) :
    p.2 ∈ ({0, 1, 2, 3} : Finset ℝ) := by
  simp only [crossPoints, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

/-- Two distinct points of `crossPoints` with a common second coordinate
must both lie on the `x`-axis (`y = 0`): the levels `y = 1, 2, 3` each
contain only one point. -/
theorem crossPoints_snd_eq_zero_of_ne {p q : ℝ × ℝ} (hp : p ∈ crossPoints)
    (hq : q ∈ crossPoints) (hne : p ≠ q) (heq : p.2 = q.2) : p.2 = 0 := by
  simp only [crossPoints, Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | rfl
      | (exfalso; apply hne; rfl)
      | (exfalso; revert heq; norm_num)

/-- A point of `crossPoints` on the `x`-axis is one of the four `x`-axis
points. -/
theorem crossPoints_mem_xaxis {p : ℝ × ℝ} (hp : p ∈ crossPoints)
    (hy : p.2 = 0) : p ∈ ({(0, 0), (1, 0), (2, 0), (3, 0)} : Finset (ℝ × ℝ)) := by
  simp only [crossPoints, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · simp
  · exact absurd (show (1 : ℝ) = 0 from hy) (by norm_num)
  · exact absurd (show (2 : ℝ) = 0 from hy) (by norm_num)
  · exact absurd (show (3 : ℝ) = 0 from hy) (by norm_num)

/-- The cross set as a `PlanarPointSet`. -/
noncomputable def crossSet : PlanarPointSet where
  points := crossPoints
  size_pos := by
    rw [crossPoints]
    apply Finset.card_pos.mpr
    exact ⟨(0, 0), by simp⟩

/-- **The cross has no five collinear points.**  Any five distinct
points of the cross lying on a common line contradict its having only
four distinct `y`-values: a horizontal line hits only the four `x`-axis
points, and a non-horizontal line hits at most one point per `y`-value
(`collinear_snd_inj`), i.e. at most four. -/
theorem crossSet_noFiveCollinear : NoFiveCollinear crossSet := by
  intro a b c d e ha hb hc hd he hab hac had hae hbc hbd hbe hcd hce hde
  rintro ⟨hcol_c, hcol_d, hcol_e⟩
  -- `a` and `b` are themselves collinear with the anchor pair `a, b`.
  have caa : collinear a b a := by unfold collinear; ring
  have cab : collinear a b b := by unfold collinear; ring
  -- membership facts
  have ha' : a ∈ crossPoints := ha
  have hb' : b ∈ crossPoints := hb
  have hc' : c ∈ crossPoints := hc
  have hd' : d ∈ crossPoints := hd
  have he' : e ∈ crossPoints := he
  by_cases hab2 : a.2 = b.2
  · -- Horizontal line: all five points share the second coordinate `a.2`.
    have hab1 : a.1 ≠ b.1 := by
      intro h1; exact hab (Prod.ext h1 hab2)
    have hb0 : b.2 = a.2 := (collinear_snd_eq_of_horiz cab hab2 hab1)
    have hc0 : c.2 = a.2 := collinear_snd_eq_of_horiz hcol_c hab2 hab1
    have hd0 : d.2 = a.2 := collinear_snd_eq_of_horiz hcol_d hab2 hab1
    have he0 : e.2 = a.2 := collinear_snd_eq_of_horiz hcol_e hab2 hab1
    -- Two distinct points `a, b` share `y = a.2`, forcing `a.2 = 0`.
    have hzero : a.2 = 0 :=
      crossPoints_snd_eq_zero_of_ne ha' hb' hab (by rw [hb0])
    -- Hence all five lie on the four-point `x`-axis set.
    have hxset : ({a, b, c, d, e} : Finset (ℝ × ℝ)) ⊆
        ({(0, 0), (1, 0), (2, 0), (3, 0)} : Finset (ℝ × ℝ)) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact crossPoints_mem_xaxis ha' hzero
      · exact crossPoints_mem_xaxis hb' (by rw [hb0, hzero])
      · exact crossPoints_mem_xaxis hc' (by rw [hc0, hzero])
      · exact crossPoints_mem_xaxis hd' (by rw [hd0, hzero])
      · exact crossPoints_mem_xaxis he' (by rw [he0, hzero])
    have hcard5 : ({a, b, c, d, e} : Finset (ℝ × ℝ)).card = 5 := by
      rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · rw [Finset.card_insert_of_notMem]
            · simp
            · simp [hde]
          · simp [hcd, hce]
        · simp [hbc, hbd, hbe]
      · simp [hab, hac, had, hae]
    have hle := Finset.card_le_card hxset
    rw [hcard5] at hle
    have h4 : ({(0, 0), (1, 0), (2, 0), (3, 0)} : Finset (ℝ × ℝ)).card = 4 := by
      rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · simp
          · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
        · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
      · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
    rw [h4] at hle
    omega
  · -- Non-horizontal line: the second coordinate is injective on the five
    -- points, so their `y`-values are five distinct elements of `{0,1,2,3}`.
    have inj : ∀ x y : ℝ × ℝ, collinear a b x → collinear a b y →
        x ≠ y → x.2 ≠ y.2 := by
      intro x y hx hy hxy h2
      exact hxy (collinear_snd_inj hx hy hab2 h2)
    have yab : a.2 ≠ b.2 := hab2
    have yac : a.2 ≠ c.2 := inj a c caa hcol_c hac
    have yad : a.2 ≠ d.2 := inj a d caa hcol_d had
    have yae : a.2 ≠ e.2 := inj a e caa hcol_e hae
    have ybc : b.2 ≠ c.2 := inj b c cab hcol_c hbc
    have ybd : b.2 ≠ d.2 := inj b d cab hcol_d hbd
    have ybe : b.2 ≠ e.2 := inj b e cab hcol_e hbe
    have ycd : c.2 ≠ d.2 := inj c d hcol_c hcol_d hcd
    have yce : c.2 ≠ e.2 := inj c e hcol_c hcol_e hce
    have yde : d.2 ≠ e.2 := inj d e hcol_d hcol_e hde
    have hysub : ({a.2, b.2, c.2, d.2, e.2} : Finset ℝ) ⊆
        ({0, 1, 2, 3} : Finset ℝ) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact crossPoints_snd_mem ha'
      · exact crossPoints_snd_mem hb'
      · exact crossPoints_snd_mem hc'
      · exact crossPoints_snd_mem hd'
      · exact crossPoints_snd_mem he'
    have hycard5 : ({a.2, b.2, c.2, d.2, e.2} : Finset ℝ).card = 5 := by
      rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · rw [Finset.card_insert_of_notMem]
            · simp
            · simp [yde]
          · simp [ycd, yce]
        · simp [ybc, ybd, ybe]
      · simp [yab, yac, yad, yae]
    have hle := Finset.card_le_card hysub
    rw [hycard5] at hle
    have h4 : ({0, 1, 2, 3} : Finset ℝ).card = 4 := by
      rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · simp
          · norm_num
        · norm_num
      · norm_num
    rw [h4] at hle
    omega

/-- The cross has at least two four-point lines: the `x`-axis
`{(0,0),(1,0),(2,0),(3,0)}` and the `y`-axis `{(0,0),(0,1),(0,2),(0,3)}`
are two distinct four-element collinear subsets. -/
theorem crossSet_fourPointLineCount_ge_two :
    2 ≤ fourPointLineCount crossSet := by
  rw [fourPointLineCount]
  -- The predicate defining membership of the powerset-filter.
  set Q : Finset (ℝ × ℝ) → Prop := fun S =>
    S.card = 4 ∧ ∃ a b : ℝ × ℝ, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
      ∀ p ∈ S, collinear a b p with hQ
  -- The two witness lines.
  have hx_mem : ({(0, 0), (1, 0), (2, 0), (3, 0)} : Finset (ℝ × ℝ)) ∈
      crossSet.points.powerset.filter Q := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_, (0, 0), (1, 0), ?_, ?_, ?_, ?_⟩
    · intro x hx
      show x ∈ crossPoints
      rw [crossPoints]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      tauto
    · rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · simp
          · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
        · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
      · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
    · simp
    · simp
    · norm_num [Prod.ext_iff]
    · intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp [collinear]
  have hy_mem : ({(0, 0), (0, 1), (0, 2), (0, 3)} : Finset (ℝ × ℝ)) ∈
      crossSet.points.powerset.filter Q := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_, (0, 0), (0, 1), ?_, ?_, ?_, ?_⟩
    · intro x hx
      show x ∈ crossPoints
      rw [crossPoints]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      tauto
    · rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · simp
          · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
        · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
      · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
    · simp
    · simp
    · norm_num [Prod.ext_iff]
    · intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp [collinear]
  -- The two lines are distinct: `(1,0)` is on the `x`-axis but not the `y`-axis.
  have hne : ({(0, 0), (1, 0), (2, 0), (3, 0)} : Finset (ℝ × ℝ)) ≠
      ({(0, 0), (0, 1), (0, 2), (0, 3)} : Finset (ℝ × ℝ)) := by
    intro h
    have : ((1, 0) : ℝ × ℝ) ∈ ({(0, 0), (0, 1), (0, 2), (0, 3)} : Finset (ℝ × ℝ)) := by
      rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at this
    norm_num at this
  -- A two-element subset of the filter gives card ≥ 2.
  have hsub : ({({(0, 0), (1, 0), (2, 0), (3, 0)} : Finset (ℝ × ℝ)),
      ({(0, 0), (0, 1), (0, 2), (0, 3)} : Finset (ℝ × ℝ))} :
      Finset (Finset (ℝ × ℝ))) ⊆ crossSet.points.powerset.filter Q := by
    intro S hS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl
    · exact hx_mem
    · exact hy_mem
  have hpair : ({({(0, 0), (1, 0), (2, 0), (3, 0)} : Finset (ℝ × ℝ)),
      ({(0, 0), (0, 1), (0, 2), (0, 3)} : Finset (ℝ × ℝ))} :
      Finset (Finset (ℝ × ℝ))).card = 2 := Finset.card_pair hne
  have hle := Finset.card_le_card hsub
  rw [hpair] at hle
  exact hle

/-- **Framework floor ≥ 2** (this session's deliverable).  The explicit
7-point cross set is a no-five-collinear planar point set with at least
two four-point lines: `IsLowerBoundConstruction crossSet 2`.  This
strictly raises the framework floor above the single-line
`witnessSet_isLowerBoundConstruction`, and — because two four-point lines
cannot share more than one point — cannot be realized by any set of
fewer than seven points.  The construction remains *constant* in size;
the asymptotic growth of `fourPointLineCount` is the OPEN content of
`grunbaum_lower_bound_three_halves` and `solymosi_stojakovic_lower_bound`. -/
theorem crossSet_isLowerBoundConstruction :
    IsLowerBoundConstruction crossSet 2 :=
  ⟨crossSet_noFiveCollinear, by exact_mod_cast crossSet_fourPointLineCount_ge_two⟩

/-- **The framework floor reaches at least two.**  There is a
no-five-collinear planar point set of exactly seven points that is a
lower-bound construction for threshold `2` — two four-point lines.  With
`exists_isLowerBoundConstruction_pos` (floor `1`, five points) this shows
the `IsLowerBoundConstruction` threshold is not pinned at the minimal
non-vacuous value. -/
theorem exists_isLowerBoundConstruction_two :
    ∃ P : PlanarPointSet, P.points.card = 7 ∧ IsLowerBoundConstruction P 2 :=
  ⟨crossSet, by
    show crossPoints.card = 7
    rw [crossPoints]
    -- seven distinct points
    repeat rw [Finset.card_insert_of_notMem
      (by norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff])]
    simp, crossSet_isLowerBoundConstruction⟩

/- ## S3-B4 (framework floor 2 → 3): the 10-point asterisk

Raising the four-point-line floor from `2` to `3` needs a *third*
four-point line.  Two four-point lines already force `4 + 4 - 1 = 7`
distinct points (`crossSet`); a third line concurrent at the same
common point adds three more, giving the minimal 10-point witness.

We use the explicit "asterisk" of three lines through the origin —
the `x`-axis, the `y`-axis and the main diagonal `y = x`:

    A = {(0,0),(1,0),(2,0),(3,0),         -- x-axis
         (0,1),(0,2),(0,3),               -- y-axis (minus origin)
         (1,1),(2,2),(3,3)}               -- diagonal (minus origin).

Its three four-point lines are the `x`-axis, the `y`-axis and the
diagonal, so `fourPointLineCount A ≥ 3`.  Crucially `A` still has only
the four distinct second coordinates `{0,1,2,3}`, and every horizontal
level carries at most four of its points (four on `y = 0`, two each on
`y = 1,2,3`), so — by the same `collinear_snd_inj` /
`collinear_snd_eq_of_horiz` argument used for the cross — `A` has no
five collinear points: `IsLowerBoundConstruction A 3`.

The construction is again *constant* in size; the asymptotic growth of
`fourPointLineCount` remains the OPEN content of the two deferred
theorems above. -/

/-- The explicit 10-point asterisk: three four-point lines (`x`-axis,
`y`-axis, diagonal `y = x`) sharing the origin. -/
noncomputable def asteriskPoints : Finset (ℝ × ℝ) :=
  {(0, 0), (1, 0), (2, 0), (3, 0), (0, 1), (0, 2), (0, 3), (1, 1), (2, 2), (3, 3)}

/-- The four second coordinates occurring in `asteriskPoints` are
exactly `{0, 1, 2, 3}`. -/
theorem asteriskPoints_snd_mem {p : ℝ × ℝ} (h : p ∈ asteriskPoints) :
    p.2 ∈ ({0, 1, 2, 3} : Finset ℝ) := by
  simp only [asteriskPoints, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- An asterisk point on the `x`-axis (`y = 0`) is one of the four
`x`-axis points. -/
theorem asterisk_level0 {p : ℝ × ℝ} (hp : p ∈ asteriskPoints) (hy : p.2 = 0) :
    p ∈ ({(0, 0), (1, 0), (2, 0), (3, 0)} : Finset (ℝ × ℝ)) := by
  simp only [asteriskPoints, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · simp
  · exact absurd (show (1 : ℝ) = 0 from hy) (by norm_num)
  · exact absurd (show (2 : ℝ) = 0 from hy) (by norm_num)
  · exact absurd (show (3 : ℝ) = 0 from hy) (by norm_num)
  · exact absurd (show (1 : ℝ) = 0 from hy) (by norm_num)
  · exact absurd (show (2 : ℝ) = 0 from hy) (by norm_num)
  · exact absurd (show (3 : ℝ) = 0 from hy) (by norm_num)

/-- An asterisk point on the level `y = 1` is one of `{(0,1),(1,1)}`. -/
theorem asterisk_level1 {p : ℝ × ℝ} (hp : p ∈ asteriskPoints) (hy : p.2 = 1) :
    p ∈ ({(0, 1), (1, 1)} : Finset (ℝ × ℝ)) := by
  simp only [asteriskPoints, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd (show (0 : ℝ) = 1 from hy) (by norm_num)
  · exact absurd (show (0 : ℝ) = 1 from hy) (by norm_num)
  · exact absurd (show (0 : ℝ) = 1 from hy) (by norm_num)
  · exact absurd (show (0 : ℝ) = 1 from hy) (by norm_num)
  · simp
  · exact absurd (show (2 : ℝ) = 1 from hy) (by norm_num)
  · exact absurd (show (3 : ℝ) = 1 from hy) (by norm_num)
  · simp
  · exact absurd (show (2 : ℝ) = 1 from hy) (by norm_num)
  · exact absurd (show (3 : ℝ) = 1 from hy) (by norm_num)

/-- An asterisk point on the level `y = 2` is one of `{(0,2),(2,2)}`. -/
theorem asterisk_level2 {p : ℝ × ℝ} (hp : p ∈ asteriskPoints) (hy : p.2 = 2) :
    p ∈ ({(0, 2), (2, 2)} : Finset (ℝ × ℝ)) := by
  simp only [asteriskPoints, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd (show (0 : ℝ) = 2 from hy) (by norm_num)
  · exact absurd (show (0 : ℝ) = 2 from hy) (by norm_num)
  · exact absurd (show (0 : ℝ) = 2 from hy) (by norm_num)
  · exact absurd (show (0 : ℝ) = 2 from hy) (by norm_num)
  · exact absurd (show (1 : ℝ) = 2 from hy) (by norm_num)
  · simp
  · exact absurd (show (3 : ℝ) = 2 from hy) (by norm_num)
  · exact absurd (show (1 : ℝ) = 2 from hy) (by norm_num)
  · simp
  · exact absurd (show (3 : ℝ) = 2 from hy) (by norm_num)

/-- An asterisk point on the level `y = 3` is one of `{(0,3),(3,3)}`. -/
theorem asterisk_level3 {p : ℝ × ℝ} (hp : p ∈ asteriskPoints) (hy : p.2 = 3) :
    p ∈ ({(0, 3), (3, 3)} : Finset (ℝ × ℝ)) := by
  simp only [asteriskPoints, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd (show (0 : ℝ) = 3 from hy) (by norm_num)
  · exact absurd (show (0 : ℝ) = 3 from hy) (by norm_num)
  · exact absurd (show (0 : ℝ) = 3 from hy) (by norm_num)
  · exact absurd (show (0 : ℝ) = 3 from hy) (by norm_num)
  · exact absurd (show (1 : ℝ) = 3 from hy) (by norm_num)
  · exact absurd (show (2 : ℝ) = 3 from hy) (by norm_num)
  · simp
  · exact absurd (show (1 : ℝ) = 3 from hy) (by norm_num)
  · exact absurd (show (2 : ℝ) = 3 from hy) (by norm_num)
  · simp

/-- The asterisk set as a `PlanarPointSet`. -/
noncomputable def asteriskSet : PlanarPointSet where
  points := asteriskPoints
  size_pos := by
    rw [asteriskPoints]
    apply Finset.card_pos.mpr
    exact ⟨(0, 0), by simp⟩

/-- **The asterisk has no five collinear points.**  It has only the
four distinct second coordinates `{0,1,2,3}`; a non-horizontal line
meets it in at most one point per level (`collinear_snd_inj`), i.e. at
most four, while a horizontal line lies in a single level, each of
which holds at most four points. -/
theorem asteriskSet_noFiveCollinear : NoFiveCollinear asteriskSet := by
  intro a b c d e ha hb hc hd he hab hac had hae hbc hbd hbe hcd hce hde
  rintro ⟨hcol_c, hcol_d, hcol_e⟩
  have caa : collinear a b a := by unfold collinear; ring
  have cab : collinear a b b := by unfold collinear; ring
  have ha' : a ∈ asteriskPoints := ha
  have hb' : b ∈ asteriskPoints := hb
  have hc' : c ∈ asteriskPoints := hc
  have hd' : d ∈ asteriskPoints := hd
  have he' : e ∈ asteriskPoints := he
  have hcard5 : ({a, b, c, d, e} : Finset (ℝ × ℝ)).card = 5 := by
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · simp
          · simp [hde]
        · simp [hcd, hce]
      · simp [hbc, hbd, hbe]
    · simp [hab, hac, had, hae]
  by_cases hab2 : a.2 = b.2
  · -- Horizontal line: all five points share the second coordinate `a.2`.
    have hab1 : a.1 ≠ b.1 := fun h1 => hab (Prod.ext h1 hab2)
    have hb0 : b.2 = a.2 := collinear_snd_eq_of_horiz cab hab2 hab1
    have hc0 : c.2 = a.2 := collinear_snd_eq_of_horiz hcol_c hab2 hab1
    have hd0 : d.2 = a.2 := collinear_snd_eq_of_horiz hcol_d hab2 hab1
    have he0 : e.2 = a.2 := collinear_snd_eq_of_horiz hcol_e hab2 hab1
    have hva : a.2 ∈ ({0, 1, 2, 3} : Finset ℝ) := asteriskPoints_snd_mem ha'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hva
    -- The common level holds at most four asterisk points, so five distinct
    -- points cannot all sit on a single horizontal line.
    rcases hva with h | h | h | h
    · have hsub : ({a, b, c, d, e} : Finset (ℝ × ℝ)) ⊆
          ({(0, 0), (1, 0), (2, 0), (3, 0)} : Finset (ℝ × ℝ)) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl
        · exact asterisk_level0 ha' h
        · exact asterisk_level0 hb' (by rw [hb0]; exact h)
        · exact asterisk_level0 hc' (by rw [hc0]; exact h)
        · exact asterisk_level0 hd' (by rw [hd0]; exact h)
        · exact asterisk_level0 he' (by rw [he0]; exact h)
      have hle := Finset.card_le_card hsub
      rw [hcard5] at hle
      have h4 : ({(0, 0), (1, 0), (2, 0), (3, 0)} : Finset (ℝ × ℝ)).card = 4 := by
        rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · rw [Finset.card_insert_of_notMem]
            · simp
            · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
          · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
        · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
      rw [h4] at hle; omega
    · have hsub : ({a, b, c, d, e} : Finset (ℝ × ℝ)) ⊆
          ({(0, 1), (1, 1)} : Finset (ℝ × ℝ)) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl
        · exact asterisk_level1 ha' h
        · exact asterisk_level1 hb' (by rw [hb0]; exact h)
        · exact asterisk_level1 hc' (by rw [hc0]; exact h)
        · exact asterisk_level1 hd' (by rw [hd0]; exact h)
        · exact asterisk_level1 he' (by rw [he0]; exact h)
      have hle := Finset.card_le_card hsub
      rw [hcard5] at hle
      have h2 : ({(0, 1), (1, 1)} : Finset (ℝ × ℝ)).card = 2 := by
        rw [Finset.card_insert_of_notMem]
        · simp
        · norm_num [Finset.mem_singleton, Prod.ext_iff]
      rw [h2] at hle; omega
    · have hsub : ({a, b, c, d, e} : Finset (ℝ × ℝ)) ⊆
          ({(0, 2), (2, 2)} : Finset (ℝ × ℝ)) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl
        · exact asterisk_level2 ha' h
        · exact asterisk_level2 hb' (by rw [hb0]; exact h)
        · exact asterisk_level2 hc' (by rw [hc0]; exact h)
        · exact asterisk_level2 hd' (by rw [hd0]; exact h)
        · exact asterisk_level2 he' (by rw [he0]; exact h)
      have hle := Finset.card_le_card hsub
      rw [hcard5] at hle
      have h2 : ({(0, 2), (2, 2)} : Finset (ℝ × ℝ)).card = 2 := by
        rw [Finset.card_insert_of_notMem]
        · simp
        · norm_num [Finset.mem_singleton, Prod.ext_iff]
      rw [h2] at hle; omega
    · have hsub : ({a, b, c, d, e} : Finset (ℝ × ℝ)) ⊆
          ({(0, 3), (3, 3)} : Finset (ℝ × ℝ)) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl
        · exact asterisk_level3 ha' h
        · exact asterisk_level3 hb' (by rw [hb0]; exact h)
        · exact asterisk_level3 hc' (by rw [hc0]; exact h)
        · exact asterisk_level3 hd' (by rw [hd0]; exact h)
        · exact asterisk_level3 he' (by rw [he0]; exact h)
      have hle := Finset.card_le_card hsub
      rw [hcard5] at hle
      have h2 : ({(0, 3), (3, 3)} : Finset (ℝ × ℝ)).card = 2 := by
        rw [Finset.card_insert_of_notMem]
        · simp
        · norm_num [Finset.mem_singleton, Prod.ext_iff]
      rw [h2] at hle; omega
  · -- Non-horizontal line: the second coordinate is injective on the five
    -- points, so their `y`-values are five distinct elements of `{0,1,2,3}`.
    have inj : ∀ x y : ℝ × ℝ, collinear a b x → collinear a b y →
        x ≠ y → x.2 ≠ y.2 := by
      intro x y hx hy hxy h2
      exact hxy (collinear_snd_inj hx hy hab2 h2)
    have yab : a.2 ≠ b.2 := hab2
    have yac : a.2 ≠ c.2 := inj a c caa hcol_c hac
    have yad : a.2 ≠ d.2 := inj a d caa hcol_d had
    have yae : a.2 ≠ e.2 := inj a e caa hcol_e hae
    have ybc : b.2 ≠ c.2 := inj b c cab hcol_c hbc
    have ybd : b.2 ≠ d.2 := inj b d cab hcol_d hbd
    have ybe : b.2 ≠ e.2 := inj b e cab hcol_e hbe
    have ycd : c.2 ≠ d.2 := inj c d hcol_c hcol_d hcd
    have yce : c.2 ≠ e.2 := inj c e hcol_c hcol_e hce
    have yde : d.2 ≠ e.2 := inj d e hcol_d hcol_e hde
    have hysub : ({a.2, b.2, c.2, d.2, e.2} : Finset ℝ) ⊆
        ({0, 1, 2, 3} : Finset ℝ) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact asteriskPoints_snd_mem ha'
      · exact asteriskPoints_snd_mem hb'
      · exact asteriskPoints_snd_mem hc'
      · exact asteriskPoints_snd_mem hd'
      · exact asteriskPoints_snd_mem he'
    have hycard5 : ({a.2, b.2, c.2, d.2, e.2} : Finset ℝ).card = 5 := by
      rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · rw [Finset.card_insert_of_notMem]
            · simp
            · simp [yde]
          · simp [ycd, yce]
        · simp [ybc, ybd, ybe]
      · simp [yab, yac, yad, yae]
    have hle := Finset.card_le_card hysub
    rw [hycard5] at hle
    have h4 : ({0, 1, 2, 3} : Finset ℝ).card = 4 := by
      rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · simp
          · norm_num
        · norm_num
      · norm_num
    rw [h4] at hle; omega

/-- The asterisk has at least three four-point lines: the `x`-axis
`{(0,0),(1,0),(2,0),(3,0)}`, the `y`-axis `{(0,0),(0,1),(0,2),(0,3)}`,
and the diagonal `{(0,0),(1,1),(2,2),(3,3)}` are three distinct
four-element collinear subsets. -/
theorem asteriskSet_fourPointLineCount_ge_three :
    3 ≤ fourPointLineCount asteriskSet := by
  rw [fourPointLineCount]
  set Q : Finset (ℝ × ℝ) → Prop := fun S =>
    S.card = 4 ∧ ∃ a b : ℝ × ℝ, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
      ∀ p ∈ S, collinear a b p with hQ
  -- The `x`-axis line.
  have hx_mem : ({(0, 0), (1, 0), (2, 0), (3, 0)} : Finset (ℝ × ℝ)) ∈
      asteriskSet.points.powerset.filter Q := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_, (0, 0), (1, 0), ?_, ?_, ?_, ?_⟩
    · intro x hx
      show x ∈ asteriskPoints
      rw [asteriskPoints]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      tauto
    · rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · simp
          · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
        · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
      · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
    · simp
    · simp
    · norm_num [Prod.ext_iff]
    · intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp [collinear]
  -- The `y`-axis line.
  have hy_mem : ({(0, 0), (0, 1), (0, 2), (0, 3)} : Finset (ℝ × ℝ)) ∈
      asteriskSet.points.powerset.filter Q := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_, (0, 0), (0, 1), ?_, ?_, ?_, ?_⟩
    · intro x hx
      show x ∈ asteriskPoints
      rw [asteriskPoints]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      tauto
    · rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · simp
          · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
        · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
      · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
    · simp
    · simp
    · norm_num [Prod.ext_iff]
    · intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp [collinear]
  -- The diagonal line `y = x`.
  have hd_mem : ({(0, 0), (1, 1), (2, 2), (3, 3)} : Finset (ℝ × ℝ)) ∈
      asteriskSet.points.powerset.filter Q := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_, (0, 0), (1, 1), ?_, ?_, ?_, ?_⟩
    · intro x hx
      show x ∈ asteriskPoints
      rw [asteriskPoints]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      tauto
    · rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · simp
          · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
        · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
      · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
    · simp
    · simp
    · norm_num [Prod.ext_iff]
    · intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp [collinear]
  -- The three lines are pairwise distinct.
  have hne_xy : ({(0, 0), (1, 0), (2, 0), (3, 0)} : Finset (ℝ × ℝ)) ≠
      ({(0, 0), (0, 1), (0, 2), (0, 3)} : Finset (ℝ × ℝ)) := by
    intro h
    have : ((1, 0) : ℝ × ℝ) ∈ ({(0, 0), (0, 1), (0, 2), (0, 3)} : Finset (ℝ × ℝ)) := by
      rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at this
    norm_num at this
  have hne_xd : ({(0, 0), (1, 0), (2, 0), (3, 0)} : Finset (ℝ × ℝ)) ≠
      ({(0, 0), (1, 1), (2, 2), (3, 3)} : Finset (ℝ × ℝ)) := by
    intro h
    have : ((1, 0) : ℝ × ℝ) ∈ ({(0, 0), (1, 1), (2, 2), (3, 3)} : Finset (ℝ × ℝ)) := by
      rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at this
    norm_num at this
  have hne_yd : ({(0, 0), (0, 1), (0, 2), (0, 3)} : Finset (ℝ × ℝ)) ≠
      ({(0, 0), (1, 1), (2, 2), (3, 3)} : Finset (ℝ × ℝ)) := by
    intro h
    have : ((0, 1) : ℝ × ℝ) ∈ ({(0, 0), (1, 1), (2, 2), (3, 3)} : Finset (ℝ × ℝ)) := by
      rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at this
    norm_num at this
  -- A three-element subset of the filter gives card ≥ 3.
  have hsub : ({({(0, 0), (1, 0), (2, 0), (3, 0)} : Finset (ℝ × ℝ)),
      ({(0, 0), (0, 1), (0, 2), (0, 3)} : Finset (ℝ × ℝ)),
      ({(0, 0), (1, 1), (2, 2), (3, 3)} : Finset (ℝ × ℝ))} :
      Finset (Finset (ℝ × ℝ))) ⊆ asteriskSet.points.powerset.filter Q := by
    intro S hS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl | rfl
    · exact hx_mem
    · exact hy_mem
    · exact hd_mem
  have h3 : ({({(0, 0), (1, 0), (2, 0), (3, 0)} : Finset (ℝ × ℝ)),
      ({(0, 0), (0, 1), (0, 2), (0, 3)} : Finset (ℝ × ℝ)),
      ({(0, 0), (1, 1), (2, 2), (3, 3)} : Finset (ℝ × ℝ))} :
      Finset (Finset (ℝ × ℝ))).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem]
    · simp
    · simp only [Finset.mem_singleton]; exact hne_yd
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg; exact ⟨hne_xy, hne_xd⟩
  have hle := Finset.card_le_card hsub
  rw [h3] at hle
  exact hle

/-- **Framework floor ≥ 3** (this session's deliverable).  The explicit
10-point asterisk is a no-five-collinear planar point set with at least
three four-point lines: `IsLowerBoundConstruction asteriskSet 3`.  This
strictly raises the framework floor above the two-line `crossSet`, and
— because three four-point lines concurrent at a point already require
`3·3 + 1 = 10` distinct points — cannot be realized by fewer than ten.
The construction remains *constant* in size; the asymptotic growth of
`fourPointLineCount` is the OPEN content of
`grunbaum_lower_bound_three_halves` and `solymosi_stojakovic_lower_bound`. -/
theorem asteriskSet_isLowerBoundConstruction :
    IsLowerBoundConstruction asteriskSet 3 :=
  ⟨asteriskSet_noFiveCollinear, by exact_mod_cast asteriskSet_fourPointLineCount_ge_three⟩

/-- **The framework floor reaches at least three.**  There is a
no-five-collinear planar point set of exactly ten points that is a
lower-bound construction for threshold `3` — three four-point lines.
With `exists_isLowerBoundConstruction_two` (floor `2`, seven points)
and `exists_isLowerBoundConstruction_pos` (floor `1`, five points) this
exhibits an increasing sequence of explicit lower-bound witnesses. -/
theorem exists_isLowerBoundConstruction_three :
    ∃ P : PlanarPointSet, P.points.card = 10 ∧ IsLowerBoundConstruction P 3 :=
  ⟨asteriskSet, by
    show asteriskPoints.card = 10
    rw [asteriskPoints]
    repeat rw [Finset.card_insert_of_notMem
      (by norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff])]
    simp, asteriskSet_isLowerBoundConstruction⟩

/- ## S3-B5 (maximal 4×4 grid — floor ≥ 8 via axis-aligned lines)

The integer grid `G = {0,1,2,3} × {0,1,2,3}` is the *maximal*
no-five-collinear grid: it has only four distinct `x`-coordinates and
four distinct `y`-coordinates, so no line meets it in five points (a
horizontal line lies in a single row of four points, and any
non-horizontal line meets each of the four `y`-levels at most once, i.e.
in at most four points).  Yet `G` carries **ten** four-point lines — its
four rows, four columns and two main diagonals.  The theorems below
formalise the sixteen-point construction, prove it has no five collinear
points, and certify at least the **eight axis-aligned** four-point lines
(four rows + four columns), raising the framework floor from the
asterisk's `3` to `8` with a single constant-size witness.

Unlike the concurrent pencils `crossSet` (floor `2`) and `asteriskSet`
(floor `3`), whose lines all pass through a common point, the grid
realises its lines in *general position* — this is exactly the grid
configuration whose random linear projection underlies the
Solymosi–Stojaković lower bound (`solymosi_stojakovic_lower_bound`).
The eight-line certificate uses only the rows and columns, whose mutual
distinctness is uniform; the two diagonals (giving the full count of
`10`) are recorded in this docstring and left to a follow-up. -/

/-- The four-element set `{0,1,2,3} ⊆ ℝ` has cardinality four. -/
private theorem card_0123 : ({0, 1, 2, 3} : Finset ℝ).card = 4 := by
  rw [Finset.card_insert_of_notMem]
  · rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_insert_of_notMem]
      · simp
      · norm_num
    · norm_num
  · norm_num

/-- **Five distinct values cannot all lie in `{0,1,2,3}`.**  If
`x0,…,x4` are pairwise distinct reals each belonging to the four-element
set `{0,1,2,3}`, we reach a contradiction (`5 ≤ 4`).  This is the
combinatorial core of the grid's no-five-collinear property: the five
points of a would-be collinear quintuple inject into the four coordinate
levels. -/
private theorem five_distinct_not_subset_0123
    {x0 x1 x2 x3 x4 : ℝ}
    (m0 : x0 ∈ ({0, 1, 2, 3} : Finset ℝ)) (m1 : x1 ∈ ({0, 1, 2, 3} : Finset ℝ))
    (m2 : x2 ∈ ({0, 1, 2, 3} : Finset ℝ)) (m3 : x3 ∈ ({0, 1, 2, 3} : Finset ℝ))
    (m4 : x4 ∈ ({0, 1, 2, 3} : Finset ℝ))
    (n01 : x0 ≠ x1) (n02 : x0 ≠ x2) (n03 : x0 ≠ x3) (n04 : x0 ≠ x4)
    (n12 : x1 ≠ x2) (n13 : x1 ≠ x3) (n14 : x1 ≠ x4)
    (n23 : x2 ≠ x3) (n24 : x2 ≠ x4) (n34 : x3 ≠ x4) : False := by
  have hsub : ({x0, x1, x2, x3, x4} : Finset ℝ) ⊆ ({0, 1, 2, 3} : Finset ℝ) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact m0
    · exact m1
    · exact m2
    · exact m3
    · exact m4
  have hcard : ({x0, x1, x2, x3, x4} : Finset ℝ).card = 5 := by
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · simp
          · simp [n34]
        · simp [n23, n24]
      · simp [n12, n13, n14]
    · simp [n01, n02, n03, n04]
  have hle := Finset.card_le_card hsub
  rw [hcard, card_0123] at hle
  omega

/-- The maximal `4×4` integer grid `{0,1,2,3} × {0,1,2,3}` (16 points). -/
noncomputable def gridPoints : Finset (ℝ × ℝ) :=
  ({0, 1, 2, 3} : Finset ℝ).product ({0, 1, 2, 3} : Finset ℝ)

/-- Every grid point has first coordinate in `{0,1,2,3}`. -/
theorem gridPoints_fst_mem {p : ℝ × ℝ} (h : p ∈ gridPoints) :
    p.1 ∈ ({0, 1, 2, 3} : Finset ℝ) := by
  rw [gridPoints] at h; exact (Finset.mem_product.mp h).1

/-- Every grid point has second coordinate in `{0,1,2,3}`. -/
theorem gridPoints_snd_mem {p : ℝ × ℝ} (h : p ∈ gridPoints) :
    p.2 ∈ ({0, 1, 2, 3} : Finset ℝ) := by
  rw [gridPoints] at h; exact (Finset.mem_product.mp h).2

/-- The grid has exactly sixteen points. -/
theorem gridPoints_card : gridPoints.card = 16 := by
  rw [gridPoints, show ({0, 1, 2, 3} : Finset ℝ).product ({0, 1, 2, 3} : Finset ℝ)
        = ({0, 1, 2, 3} : Finset ℝ) ×ˢ ({0, 1, 2, 3} : Finset ℝ) from rfl,
    Finset.card_product]
  norm_num [card_0123]

/-- The `4×4` grid as a `PlanarPointSet`. -/
noncomputable def gridSet : PlanarPointSet where
  points := gridPoints
  size_pos := by
    rw [gridPoints]
    apply Finset.card_pos.mpr
    exact ⟨(0, 0), by simp [Finset.mem_product]⟩

/-- **The `4×4` grid has no five collinear points.**  With only four
distinct second coordinates `{0,1,2,3}`, a horizontal line has all five
points at one level — forcing five distinct *first* coordinates in
`{0,1,2,3}` — while a non-horizontal line meets each level once
(`collinear_snd_inj`), forcing five distinct *second* coordinates in
`{0,1,2,3}`.  Either way `five_distinct_not_subset_0123` gives a
contradiction. -/
theorem gridSet_noFiveCollinear : NoFiveCollinear gridSet := by
  intro a b c d e ha hb hc hd he hab hac had hae hbc hbd hbe hcd hce hde
  rintro ⟨hcol_c, hcol_d, hcol_e⟩
  have caa : collinear a b a := by unfold collinear; ring
  have cab : collinear a b b := by unfold collinear; ring
  have ha' : a ∈ gridPoints := ha
  have hb' : b ∈ gridPoints := hb
  have hc' : c ∈ gridPoints := hc
  have hd' : d ∈ gridPoints := hd
  have he' : e ∈ gridPoints := he
  by_cases hab2 : a.2 = b.2
  · -- Horizontal line: all five share the second coordinate `a.2`, so
    -- their first coordinates are five distinct elements of `{0,1,2,3}`.
    have hab1 : a.1 ≠ b.1 := fun h1 => hab (Prod.ext h1 hab2)
    have hb0 : b.2 = a.2 := collinear_snd_eq_of_horiz cab hab2 hab1
    have hc0 : c.2 = a.2 := collinear_snd_eq_of_horiz hcol_c hab2 hab1
    have hd0 : d.2 = a.2 := collinear_snd_eq_of_horiz hcol_d hab2 hab1
    have he0 : e.2 = a.2 := collinear_snd_eq_of_horiz hcol_e hab2 hab1
    exact five_distinct_not_subset_0123
      (gridPoints_fst_mem ha') (gridPoints_fst_mem hb') (gridPoints_fst_mem hc')
      (gridPoints_fst_mem hd') (gridPoints_fst_mem he')
      (fun h => hab (Prod.ext h hab2))
      (fun h => hac (Prod.ext h hc0.symm))
      (fun h => had (Prod.ext h hd0.symm))
      (fun h => hae (Prod.ext h he0.symm))
      (fun h => hbc (Prod.ext h (hb0.trans hc0.symm)))
      (fun h => hbd (Prod.ext h (hb0.trans hd0.symm)))
      (fun h => hbe (Prod.ext h (hb0.trans he0.symm)))
      (fun h => hcd (Prod.ext h (hc0.trans hd0.symm)))
      (fun h => hce (Prod.ext h (hc0.trans he0.symm)))
      (fun h => hde (Prod.ext h (hd0.trans he0.symm)))
  · -- Non-horizontal line: the second coordinate is injective on the
    -- five points, giving five distinct elements of `{0,1,2,3}`.
    have inj : ∀ x y : ℝ × ℝ, collinear a b x → collinear a b y →
        x ≠ y → x.2 ≠ y.2 :=
      fun x y hx hy hxy h2 => hxy (collinear_snd_inj hx hy hab2 h2)
    exact five_distinct_not_subset_0123
      (gridPoints_snd_mem ha') (gridPoints_snd_mem hb') (gridPoints_snd_mem hc')
      (gridPoints_snd_mem hd') (gridPoints_snd_mem he')
      hab2
      (inj a c caa hcol_c hac) (inj a d caa hcol_d had) (inj a e caa hcol_e hae)
      (inj b c cab hcol_c hbc) (inj b d cab hcol_d hbd) (inj b e cab hcol_e hbe)
      (inj c d hcol_c hcol_d hcd) (inj c e hcol_c hcol_e hce)
      (inj d e hcol_d hcol_e hde)

/-- Two point-finsets differ if some point lies in one but not the other. -/
private theorem grid_line_ne {s t : Finset (ℝ × ℝ)} (x : ℝ × ℝ)
    (hxs : x ∈ s) (hxt : x ∉ t) : s ≠ t :=
  fun h => hxt (h ▸ hxs)

/-- **The `4×4` grid has at least eight four-point lines** — its four
rows and four columns.  Each is a four-element collinear subset of the
grid, and the eight are pairwise distinct (rows are separated by their
common second coordinate, columns by their common first coordinate, and
a row differs from a column because a row contains two points with
distinct first coordinates while a column's points all share theirs). -/
theorem gridSet_fourPointLineCount_ge_eight :
    8 ≤ fourPointLineCount gridSet := by
  rw [fourPointLineCount]
  set Q : Finset (ℝ × ℝ) → Prop := fun S =>
    S.card = 4 ∧ ∃ a b : ℝ × ℝ, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
      ∀ p ∈ S, collinear a b p with hQ
  -- The four rows and four columns.
  have hR0 : ({(0, 0), (1, 0), (2, 0), (3, 0)} : Finset (ℝ × ℝ)) ∈
      gridSet.points.powerset.filter Q := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_, (0, 0), (1, 0), ?_, ?_, ?_, ?_⟩
    · intro x hx
      show x ∈ gridPoints
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp [gridPoints, Finset.mem_product]
    · rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · simp
          · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
        · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
      · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
    · simp
    · simp
    · norm_num [Prod.ext_iff]
    · intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp [collinear]
  have hR1 : ({(0, 1), (1, 1), (2, 1), (3, 1)} : Finset (ℝ × ℝ)) ∈
      gridSet.points.powerset.filter Q := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_, (0, 1), (1, 1), ?_, ?_, ?_, ?_⟩
    · intro x hx
      show x ∈ gridPoints
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp [gridPoints, Finset.mem_product]
    · rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · simp
          · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
        · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
      · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
    · simp
    · simp
    · norm_num [Prod.ext_iff]
    · intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp [collinear]
  have hR2 : ({(0, 2), (1, 2), (2, 2), (3, 2)} : Finset (ℝ × ℝ)) ∈
      gridSet.points.powerset.filter Q := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_, (0, 2), (1, 2), ?_, ?_, ?_, ?_⟩
    · intro x hx
      show x ∈ gridPoints
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp [gridPoints, Finset.mem_product]
    · rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · simp
          · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
        · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
      · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
    · simp
    · simp
    · norm_num [Prod.ext_iff]
    · intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp [collinear]
  have hR3 : ({(0, 3), (1, 3), (2, 3), (3, 3)} : Finset (ℝ × ℝ)) ∈
      gridSet.points.powerset.filter Q := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_, (0, 3), (1, 3), ?_, ?_, ?_, ?_⟩
    · intro x hx
      show x ∈ gridPoints
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp [gridPoints, Finset.mem_product]
    · rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · simp
          · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
        · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
      · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
    · simp
    · simp
    · norm_num [Prod.ext_iff]
    · intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp [collinear]
  have hC0 : ({(0, 0), (0, 1), (0, 2), (0, 3)} : Finset (ℝ × ℝ)) ∈
      gridSet.points.powerset.filter Q := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_, (0, 0), (0, 1), ?_, ?_, ?_, ?_⟩
    · intro x hx
      show x ∈ gridPoints
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp [gridPoints, Finset.mem_product]
    · rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · simp
          · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
        · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
      · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
    · simp
    · simp
    · norm_num [Prod.ext_iff]
    · intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp [collinear]
  have hC1 : ({(1, 0), (1, 1), (1, 2), (1, 3)} : Finset (ℝ × ℝ)) ∈
      gridSet.points.powerset.filter Q := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_, (1, 0), (1, 1), ?_, ?_, ?_, ?_⟩
    · intro x hx
      show x ∈ gridPoints
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp [gridPoints, Finset.mem_product]
    · rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · simp
          · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
        · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
      · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
    · simp
    · simp
    · norm_num [Prod.ext_iff]
    · intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp [collinear]
  have hC2 : ({(2, 0), (2, 1), (2, 2), (2, 3)} : Finset (ℝ × ℝ)) ∈
      gridSet.points.powerset.filter Q := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_, (2, 0), (2, 1), ?_, ?_, ?_, ?_⟩
    · intro x hx
      show x ∈ gridPoints
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp [gridPoints, Finset.mem_product]
    · rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · simp
          · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
        · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
      · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
    · simp
    · simp
    · norm_num [Prod.ext_iff]
    · intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp [collinear]
  have hC3 : ({(3, 0), (3, 1), (3, 2), (3, 3)} : Finset (ℝ × ℝ)) ∈
      gridSet.points.powerset.filter Q := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_, (3, 0), (3, 1), ?_, ?_, ?_, ?_⟩
    · intro x hx
      show x ∈ gridPoints
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp [gridPoints, Finset.mem_product]
    · rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · simp
          · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
        · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
      · norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
    · simp
    · simp
    · norm_num [Prod.ext_iff]
    · intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp [collinear]
  -- The eight lines form an eight-element subfamily of the filter.
  have hsub : ({({(0, 0), (1, 0), (2, 0), (3, 0)} : Finset (ℝ × ℝ)),
      {(0, 1), (1, 1), (2, 1), (3, 1)}, {(0, 2), (1, 2), (2, 2), (3, 2)},
      {(0, 3), (1, 3), (2, 3), (3, 3)}, {(0, 0), (0, 1), (0, 2), (0, 3)},
      {(1, 0), (1, 1), (1, 2), (1, 3)}, {(2, 0), (2, 1), (2, 2), (2, 3)},
      {(3, 0), (3, 1), (3, 2), (3, 3)}} : Finset (Finset (ℝ × ℝ))) ⊆
      gridSet.points.powerset.filter Q := by
    intro S hS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hR0
    · exact hR1
    · exact hR2
    · exact hR3
    · exact hC0
    · exact hC1
    · exact hC2
    · exact hC3
  have h8 : ({({(0, 0), (1, 0), (2, 0), (3, 0)} : Finset (ℝ × ℝ)),
      {(0, 1), (1, 1), (2, 1), (3, 1)}, {(0, 2), (1, 2), (2, 2), (3, 2)},
      {(0, 3), (1, 3), (2, 3), (3, 3)}, {(0, 0), (0, 1), (0, 2), (0, 3)},
      {(1, 0), (1, 1), (1, 2), (1, 3)}, {(2, 0), (2, 1), (2, 2), (2, 3)},
      {(3, 0), (3, 1), (3, 2), (3, 3)}} : Finset (Finset (ℝ × ℝ))).card = 8 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem]
    · simp
    · -- C2 ∉ {C3}
      simp only [Finset.mem_singleton]
      exact grid_line_ne (2, 0) (by simp)
        (by norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff])
    · -- C1 ∉ {C2, C3}
      simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
      exact ⟨grid_line_ne (1, 0) (by simp)
          (by norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]),
        grid_line_ne (1, 0) (by simp)
          (by norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff])⟩
    · -- C0 ∉ {C1, C2, C3}
      simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
      refine ⟨grid_line_ne (0, 0) (by simp)
          (by norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]),
        grid_line_ne (0, 0) (by simp)
          (by norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]),
        grid_line_ne (0, 0) (by simp)
          (by norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff])⟩
    · -- R3 ∉ {C0, C1, C2, C3}
      simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
      refine ⟨grid_line_ne (1, 3) (by simp)
          (by norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]),
        grid_line_ne (0, 3) (by simp)
          (by norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]),
        grid_line_ne (0, 3) (by simp)
          (by norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]),
        grid_line_ne (0, 3) (by simp)
          (by norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff])⟩
    · -- R2 ∉ {R3, C0, C1, C2, C3}
      simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
      refine ⟨grid_line_ne (0, 2) (by simp)
          (by norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]),
        grid_line_ne (1, 2) (by simp)
          (by norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]),
        grid_line_ne (0, 2) (by simp)
          (by norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]),
        grid_line_ne (0, 2) (by simp)
          (by norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]),
        grid_line_ne (0, 2) (by simp)
          (by norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff])⟩
    · -- R1 ∉ {R2, R3, C0, C1, C2, C3}
      simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
      refine ⟨grid_line_ne (0, 1) (by simp)
          (by norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]),
        grid_line_ne (0, 1) (by simp)
          (by norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]),
        grid_line_ne (1, 1) (by simp)
          (by norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]),
        grid_line_ne (0, 1) (by simp)
          (by norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]),
        grid_line_ne (0, 1) (by simp)
          (by norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]),
        grid_line_ne (0, 1) (by simp)
          (by norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff])⟩
    · -- R0 ∉ {R1, R2, R3, C0, C1, C2, C3}
      simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
      refine ⟨grid_line_ne (0, 0) (by simp)
          (by norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]),
        grid_line_ne (0, 0) (by simp)
          (by norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]),
        grid_line_ne (0, 0) (by simp)
          (by norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]),
        grid_line_ne (1, 0) (by simp)
          (by norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]),
        grid_line_ne (0, 0) (by simp)
          (by norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]),
        grid_line_ne (0, 0) (by simp)
          (by norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]),
        grid_line_ne (0, 0) (by simp)
          (by norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff])⟩
  have hle := Finset.card_le_card hsub
  rw [h8] at hle
  exact hle

/-- **Framework floor ≥ 8** (this session's deliverable).  The explicit
sixteen-point `4×4` grid is a no-five-collinear planar point set with at
least eight four-point lines — its four rows and four columns —
`IsLowerBoundConstruction gridSet 8`.  This more than doubles the
asterisk's floor of `3`, and does so with lines in general position
(the grid whose projection underlies Solymosi–Stojaković), rather than a
concurrent pencil.  The construction is still *constant* in size: the
asymptotic growth of `fourPointLineCount` remains the OPEN content of
`grunbaum_lower_bound_three_halves` and `solymosi_stojakovic_lower_bound`. -/
theorem gridSet_isLowerBoundConstruction :
    IsLowerBoundConstruction gridSet 8 :=
  ⟨gridSet_noFiveCollinear, by exact_mod_cast gridSet_fourPointLineCount_ge_eight⟩

/-- **The framework floor reaches at least eight.**  There is a
no-five-collinear planar point set of exactly sixteen points that is a
lower-bound construction for threshold `8`.  Together with the pencil
witnesses `exists_isLowerBoundConstruction_three` (floor `3`, ten
points), `_two` (floor `2`) and `_pos` (floor `1`), this is the largest
explicit constant-size lower-bound witness in the file. -/
theorem exists_isLowerBoundConstruction_eight :
    ∃ P : PlanarPointSet, P.points.card = 16 ∧ IsLowerBoundConstruction P 8 :=
  ⟨gridSet, gridPoints_card, gridSet_isLowerBoundConstruction⟩

end Erdos101OQ04
