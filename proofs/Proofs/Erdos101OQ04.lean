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
  n^{2−O(1/√(log n))} bound.  Strengthens
  `Erdos101OQ01.solymosi_stojakovic_lower_bound` only cosmetically
  (re-named here for OQ-04 provenance); reduces to it by
  `solymosi_stojakovic_lower_bound_via_oq01`.
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
  exact le_refl 0

/- ## Grünbaum's Ω(n^{3/2}) lower bound (recorded as deferred proof)

The pre-Solymosi–Stojaković state of the art: Grünbaum (1972)
constructed point sets with no five collinear achieving at least
$c \cdot n^{3/2}$ four-point lines.  The canonical construction is
the *parabola modulo p*:

    $G_p = \{(i, j) \in (\mathbb{F}_p)^2 : 4j \equiv -i^2 \pmod p\}$

For `p` prime, $|G_p| = p$, and the construction admits
$\Omega(p^{3/2})$ four-point lines (each "secant line" of the parabola
hits at most four points by the degree-two polynomial-roots bound).
The result `grunbaum_lower_bound_three_halves` below records the
asymptotic statement; the construction itself is deferred to Path B
of the state.md S2 inventory.

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
equivalent; the bridge lemma
`solymosi_stojakovic_lower_bound_via_oq01` shows that OQ-04's
formulation reduces to OQ-01's.

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
`Erdos101OQ01.solymosi_stojakovic_lower_bound`; the bridge is
`solymosi_stojakovic_lower_bound_via_oq01` below. -/
theorem solymosi_stojakovic_lower_bound :
    ∀ C : ℝ, 0 < C → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ P : PlanarPointSet, P.points.card = n ∧
        IsLowerBoundConstruction P ((n : ℝ) ^ (2 - C / Real.sqrt (Real.log n))) := by
  sorry

/-- **Bridge**: OQ-04's `IsLowerBoundConstruction`-flavoured re-statement
reduces directly to OQ-01's `solymosi_stojakovic_lower_bound`.  This
lemma is the asymptotic equivalence between the two formulations and
shows that OQ-04's `solymosi_stojakovic_lower_bound` is a deferred
proof obligation only because OQ-01's is.

Recorded *unconditionally* (no sorry): the implication holds even
when both sides are open. -/
theorem solymosi_stojakovic_lower_bound_via_oq01 :
    Erdos101OQ01.solymosi_stojakovic_lower_bound →
      Erdos101OQ04.solymosi_stojakovic_lower_bound := by
  -- Both are `Prop`-typed; the OQ-01 statement directly produces the
  -- witness `P` with `fourPointLineCount P ≥ n^{2 - C / √(log n)}`,
  -- which is precisely the `IsLowerBoundConstruction` payload.
  intro h C hC
  obtain ⟨N, hN⟩ := h C hC
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨P, hcard, hno5, hlb⟩ := hN n hn
  -- The OQ-04 existential unfolds to `∃ P, P.points.card = n ∧
  -- IsLowerBoundConstruction P threshold`, where the inner predicate
  -- is `NoFiveCollinear P ∧ threshold ≤ (fourPointLineCount P : ℝ)`.
  exact ⟨P, hcard, hno5, hlb⟩

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
    rw [div_lt_iff hsqrt_pos]
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

end Grunbaum

end Erdos101OQ04
