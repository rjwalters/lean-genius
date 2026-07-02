import Mathlib

/-
# Factor/Remainder Theorem OQ-05-OQ-02: Existence of the Lagrange Interpolating Polynomial

## Research Problem: factor-remainder-theorem-oq-05-oq-02

The parent problem `factor-remainder-theorem-oq-05` proves the **uniqueness** half of
polynomial interpolation over an integral domain: via the root-count bound
`Polynomial.card_roots'`, a polynomial of degree `< n` that vanishes at `n` distinct points
must be the zero polynomial, hence two such polynomials agreeing on `n` points are equal.

This file supplies the complementary **existence** half over a *field*: for any finite set
of `n` distinct nodes and any prescribed values, there *exists* a polynomial of degree `< n`
taking those values. Combined with uniqueness this gives the classical

  **Lagrange interpolation theorem**: through `n` distinct points there is one and only one
  polynomial of degree `< n` with the prescribed values.

## Mathematical Content

The explicit witness is Lagrange's formula

  L(x) = ∑_{i} r_i · ℓ_i(x),   ℓ_i(x) = ∏_{j ≠ i} (x − v_j)/(v_i − v_j),

packaged in Mathlib as the linear map `Lagrange.interpolate s v`. Its two defining
properties are that it reproduces the data at the nodes
(`Lagrange.eval_interpolate_at_node`) and that its degree is `< #s`
(`Lagrange.degree_interpolate_lt`). Feeding these into `ExistsUnique` yields the headline
`∃!` statement.

We give the result in two forms — an abstract indexed form (`v : ι → F` injective on a
finset `s`) and the concrete classical form over a finite set of field points
(`ι = F`, `v = id`) — then record two structural consequences:

* **Superposition**: interpolation is `F`-linear in the prescribed values, because
  `Lagrange.interpolate s v` is literally a `LinearMap` (`interpolate_add`, `interpolate_smul`).
* **Evaluation is a linear isomorphism** `degreeLT F #s ≃ₗ[F] (s → F)`
  (`Lagrange.funEquivDegreeLT`): evaluation at `n` distinct nodes is a bijection between
  degree-`< n` polynomials and value tuples. This is the coordinate-free form of the
  invertibility of the Vandermonde matrix, and is exactly the existence-and-uniqueness
  statement upgraded to an `F`-linear equivalence.

The field hypothesis is essential for *existence*: the denominators `v_i − v_j` in the
Lagrange basis must be invertible. (Uniqueness, by contrast, only needs an integral domain,
which is what the parent uses.)

## References
- Lagrange (1795): interpolation formula.
- Mathlib: `Lagrange.interpolate`, `Lagrange.eval_interpolate_at_node`,
  `Lagrange.degree_interpolate_lt`, `Lagrange.eq_interpolate_iff`,
  `Lagrange.funEquivDegreeLT`.
-/

open Polynomial

namespace FactorRemainderTheoremOQ05OQ02

open scoped Finset

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → F}

/-! ## Part I: Existence over a field (abstract indexed form)

Given distinct nodes `v i` (`i ∈ s`) and any target values `r`, the Lagrange polynomial is a
concrete witness of degree `< #s` taking the prescribed values. -/

/-- **Existence of an interpolating polynomial.** Over a field, for any injective node map
and any prescribed values there is a polynomial of degree `< #s` matching the data at every
node. The witness is Lagrange's `interpolate`. -/
theorem exists_interpolating (hvs : Set.InjOn v s) (r : ι → F) :
    ∃ p : F[X], p.degree < s.card ∧ ∀ i ∈ s, p.eval (v i) = r i :=
  ⟨Lagrange.interpolate s v r, Lagrange.degree_interpolate_lt r hvs,
    fun _ hi => Lagrange.eval_interpolate_at_node r hvs hi⟩

/-- The Lagrange polynomial has degree strictly below the number of interpolation nodes. -/
theorem interpolate_degree_lt (hvs : Set.InjOn v s) (r : ι → F) :
    (Lagrange.interpolate s v r).degree < s.card :=
  Lagrange.degree_interpolate_lt r hvs

/-- The Lagrange polynomial reproduces the data at each node. -/
theorem interpolate_eval_node (hvs : Set.InjOn v s) (r : ι → F) {i : ι} (hi : i ∈ s) :
    (Lagrange.interpolate s v r).eval (v i) = r i :=
  Lagrange.eval_interpolate_at_node r hvs hi

/-! ## Part II: Existence AND uniqueness — the Lagrange interpolation theorem -/

omit [DecidableEq ι] in
/-- **Uniqueness of the interpolant** (the parent's half, restated over a field). Two
polynomials of degree `< #s` that agree at all `#s` distinct nodes are equal. Only an
integral-domain structure is needed here — exactly the setting of the parent problem. -/
theorem interpolate_unique (hvs : Set.InjOn v s) {p q : F[X]}
    (hp : p.degree < s.card) (hq : q.degree < s.card)
    (h : ∀ i ∈ s, p.eval (v i) = q.eval (v i)) : p = q :=
  Polynomial.eq_of_degrees_lt_of_eval_index_eq s hvs hp hq h

/-- **Lagrange interpolation theorem (existence + uniqueness).** Over a field, given `#s`
distinct nodes and any target values, there is a *unique* polynomial of degree `< #s`
realizing those values. -/
theorem existsUnique_interpolating (hvs : Set.InjOn v s) (r : ι → F) :
    ∃! p : F[X], p.degree < s.card ∧ ∀ i ∈ s, p.eval (v i) = r i := by
  refine ⟨Lagrange.interpolate s v r,
    ⟨Lagrange.degree_interpolate_lt r hvs,
      fun _ hi => Lagrange.eval_interpolate_at_node r hvs hi⟩, ?_⟩
  intro q hq
  exact (Lagrange.eq_interpolate_iff r hvs).mp ⟨hq.1, hq.2⟩

/-! ## Part III: The concrete classical statement over field points

Specializing to `ι = F` and `v = id` recovers the textbook formulation: distinct
`x`-coordinates drawn from a finset `S ⊆ F`, arbitrary `y`-values. -/

/-- **Classical Lagrange interpolation.** For a finite set `S` of distinct points of a field
`F` and any value function `y`, there is a unique polynomial of degree `< #S` passing through
`(x, y x)` for every `x ∈ S`. -/
theorem existsUnique_interpolating_points [DecidableEq F] (S : Finset F) (y : F → F) :
    ∃! p : F[X], p.degree < S.card ∧ ∀ x ∈ S, p.eval x = y x := by
  have hvs : Set.InjOn (id : F → F) (S : Set F) := Set.injOn_id _
  simpa using existsUnique_interpolating (s := S) (v := id) hvs y

/-- Existence form of the classical statement: a polynomial of degree `< #S` through any
`#S` distinct field points with arbitrary prescribed values. -/
theorem exists_interpolating_points [DecidableEq F] (S : Finset F) (y : F → F) :
    ∃ p : F[X], p.degree < S.card ∧ ∀ x ∈ S, p.eval x = y x := by
  have hvs : Set.InjOn (id : F → F) (S : Set F) := Set.injOn_id _
  simpa using exists_interpolating (s := S) (v := id) hvs y

/-- Uniqueness form of the classical statement (bridges to the parent's root-count proof):
two polynomials of degree `< #S` agreeing on `#S` distinct field points coincide. -/
theorem eq_of_degree_lt_of_eval_eq_points {S : Finset F} {p q : F[X]}
    (hp : p.degree < S.card) (hq : q.degree < S.card)
    (h : ∀ x ∈ S, p.eval x = q.eval x) : p = q :=
  Polynomial.eq_of_degrees_lt_of_eval_finset_eq S hp hq h

/-! ## Part IV: Structural consequences -/

/-- **Superposition principle.** Interpolation is additive in the prescribed values: the
interpolant of a sum of data is the sum of the interpolants. This is immediate because
`Lagrange.interpolate s v` is an `F`-linear map. -/
theorem interpolate_add (r r' : ι → F) :
    Lagrange.interpolate s v (r + r') =
      Lagrange.interpolate s v r + Lagrange.interpolate s v r' :=
  map_add _ r r'

/-- Interpolation commutes with scaling of the data. -/
theorem interpolate_smul (c : F) (r : ι → F) :
    Lagrange.interpolate s v (c • r) = c • Lagrange.interpolate s v r :=
  map_smul _ c r

/-- **Evaluation is a linear isomorphism.** Evaluation at `#s` distinct nodes is an
`F`-linear bijection from degree-`< #s` polynomials onto value tuples `s → F`. This is the
coordinate-free invertibility of the Vandermonde matrix, and packages existence and
uniqueness simultaneously as a single equivalence. -/
theorem eval_funEquivDegreeLT_bijective (hvs : Set.InjOn v s) :
    Function.Bijective (Lagrange.funEquivDegreeLT hvs) :=
  (Lagrange.funEquivDegreeLT hvs).bijective

end FactorRemainderTheoremOQ05OQ02

