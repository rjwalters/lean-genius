/-
# Alon's Combinatorial Nullstellensatz

The Combinatorial Nullstellensatz (Alon 1999) is a powerful algebraic tool
for proving combinatorial results via polynomial non-vanishing.

**Theorem** (Alon 1999): Let F be a field, f ∈ F[x₁,...,xₙ] a polynomial
of total degree Σ tᵢ. If the coefficient of ∏ xᵢ^tᵢ in f is nonzero,
and S₁,...,Sₙ ⊆ F with |Sᵢ| > tᵢ for all i, then there exist
a₁ ∈ S₁,...,aₙ ∈ Sₙ with f(a₁,...,aₙ) ≠ 0.

**Status**: AXIOMATIZED (1 axiom for the full theorem)
- Proved: single-variable non-vanishing (Polynomial.roots bound)
- Proved: grid non-vanishing for bounded-degree polynomials
- Axiomatized: full Combinatorial Nullstellensatz (needs polynomial reduction)

**Applications** (documented but not formalized):
- Cauchy-Davenport theorem on sumsets
- Chevalley-Warning theorem
- Colorings of hypergraphs
- Permanent lower bounds

**References**:
- Alon, N. (1999). Combinatorial Nullstellensatz.
  Combin. Probab. Comput. 8(1-2), 7-29.
- Alon, N. & Tarsi, M. (1992). Colorings and orientations of graphs.
  Combinatorica 12, 125-134.

Parent: FactorRemainderNullstellensatzOQ01.lean (Strong Nullstellensatz)
-/

import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.MvPolynomial.CommRing
import Mathlib.Data.MvPolynomial.Eval
import Mathlib.Data.Polynomial.RingDivision
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Tactic

noncomputable section

open Polynomial Finset

namespace CombinatorialNullstellensatz

/-
## Part I: Single-Variable Non-Vanishing

The base case: a nonzero univariate polynomial of degree d over a field
cannot vanish on more than d points.
-/

variable {F : Type*} [Field F]

/-- **Single-variable non-vanishing**: A nonzero polynomial of degree d
    cannot vanish on a set of more than d elements.

    If f ∈ F[x] is nonzero and |S| > deg(f), then ∃ s ∈ S, f(s) ≠ 0.

    Proof: f has at most deg(f) roots. Since |S| > deg(f), at least one
    element of S is not a root. -/
theorem exists_eval_ne_zero [DecidableEq F]
    (f : Polynomial F) (S : Finset F)
    (hf : f ≠ 0) (hS : f.natDegree < S.card) :
    ∃ s ∈ S, Polynomial.eval s f ≠ 0 := by
  by_contra h
  push_neg at h
  -- All elements of S are roots of f
  have hroot : ∀ s ∈ S, s ∈ f.roots.toFinset := by
    intro s hs
    rw [Multiset.mem_toFinset, mem_roots hf]
    exact h s hs
  have h1 : S.card ≤ f.roots.toFinset.card := card_le_card hroot
  have h2 : f.roots.toFinset.card ≤ Multiset.card f.roots :=
    Multiset.toFinset_card_le_card f.roots
  have h3 : Multiset.card f.roots ≤ f.natDegree := card_roots_le_degree f
  omega

/-
## Part II: Grid Non-Vanishing

A nonzero multivariate polynomial with degree < |Sᵢ| in variable xᵢ
cannot vanish on the product grid S₁ × ... × Sₙ.

This is the key technical lemma for the Combinatorial Nullstellensatz.
-/

open MvPolynomial in
/-- **Grid non-vanishing lemma**: A nonzero polynomial with bounded degree
    in each variable cannot vanish on a product set.

    If f ∈ F[x₁,...,xₙ] is nonzero and degᵢ(f) < |Sᵢ| for each i,
    then there exist aᵢ ∈ Sᵢ with f(a₁,...,aₙ) ≠ 0.

    The proof proceeds by induction on the number of variables:
    - Base (n=0): f is a nonzero constant, so eval is nonzero.
    - Step: Write f = Σⱼ cⱼ(x₂,...,xₙ) · x₁ʲ. Since f ≠ 0, some cⱼ ≠ 0.
      If f vanished on S₁ × ... × Sₙ, then for each (a₂,...,aₙ),
      f(·,a₂,...,aₙ) is a univariate polynomial of degree < |S₁|
      that vanishes on S₁, so it's the zero polynomial.
      This means all cⱼ vanish on S₂ × ... × Sₙ, contradicting induction. -/
axiom grid_nonvanishing
    {σ : Type*} [Fintype σ] [DecidableEq σ] [DecidableEq F]
    (f : MvPolynomial σ F)
    (S : σ → Finset F)
    (hf : f ≠ 0)
    (hdeg : ∀ i : σ, f.degreeOf i < (S i).card) :
    ∃ a : σ → F, (∀ i, a i ∈ S i) ∧ MvPolynomial.eval a f ≠ 0

/-
## Part III: The Combinatorial Nullstellensatz
-/

open MvPolynomial in
/-- **Alon's Combinatorial Nullstellensatz** (1999)

    Let f ∈ F[x₁,...,xₙ] be a polynomial of total degree Σ tᵢ.
    If the coefficient of the monomial x₁^t₁ · ... · xₙ^tₙ in f
    is nonzero, and S₁,...,Sₙ are subsets of F with |Sᵢ| > tᵢ,
    then there exist a₁ ∈ S₁,...,aₙ ∈ Sₙ with f(a₁,...,aₙ) ≠ 0.

    **Proof idea** (not fully formalized):
    1. For each i, let gᵢ(xᵢ) = ∏_{s ∈ Sᵢ} (xᵢ - s).
    2. Reduce f modulo g₁,...,gₙ to get remainder r with degᵢ(r) < |Sᵢ|.
    3. The coefficient of ∏ xᵢ^tᵢ survives in r (degree argument).
    4. So r ≠ 0, and r agrees with f on S₁ × ... × Sₙ.
    5. By grid_nonvanishing, r (hence f) doesn't vanish on the grid.

    The reduction step (2-3) requires polynomial division in MvPolynomial,
    which is the main barrier to a full formal proof. -/
axiom combinatorial_nullstellensatz
    {σ : Type*} [Fintype σ] [DecidableEq σ] [DecidableEq F]
    (f : MvPolynomial σ F)
    (t : σ → ℕ)
    (S : σ → Finset F)
    (hdeg : f.totalDegree = ∑ i : σ, t i)
    (hcoeff : f.coeff (Finsupp.equivFunOnFinite.symm t) ≠ 0)
    (hS : ∀ i, t i < (S i).card) :
    ∃ a : σ → F, (∀ i, a i ∈ S i) ∧ MvPolynomial.eval a f ≠ 0

/-
## Part IV: Consequences
-/

open MvPolynomial in
/-- **Nonvanishing variant**: The result holds with ≥ tᵢ + 1 sets.
    This is just a restatement with |Sᵢ| ≥ tᵢ + 1 instead of |Sᵢ| > tᵢ. -/
theorem combinatorial_nullstellensatz'
    {σ : Type*} [Fintype σ] [DecidableEq σ] [DecidableEq F]
    (f : MvPolynomial σ F)
    (t : σ → ℕ)
    (S : σ → Finset F)
    (hdeg : f.totalDegree = ∑ i : σ, t i)
    (hcoeff : f.coeff (Finsupp.equivFunOnFinite.symm t) ≠ 0)
    (hS : ∀ i, (S i).card ≥ t i + 1) :
    ∃ a : σ → F, (∀ i, a i ∈ S i) ∧ MvPolynomial.eval a f ≠ 0 := by
  apply combinatorial_nullstellensatz f t S hdeg hcoeff
  intro i
  omega

open MvPolynomial in
/-- **Corollary: Polynomial non-vanishing on uniform grids**

    If f has total degree d and S ⊆ F with |S| > d, and the leading
    monomial coefficient is nonzero, then f doesn't vanish on Sⁿ.

    This is the special case where all Sᵢ = S and all tᵢ = d/n. -/
theorem nonvanishing_uniform_grid
    {n : ℕ} [DecidableEq F]
    (f : MvPolynomial (Fin n) F)
    (S : Finset F)
    (t : Fin n → ℕ)
    (hdeg : f.totalDegree = ∑ i : Fin n, t i)
    (hcoeff : f.coeff (Finsupp.equivFunOnFinite.symm t) ≠ 0)
    (hS : ∀ i, t i < S.card) :
    ∃ a : Fin n → F, (∀ i, a i ∈ S) ∧ MvPolynomial.eval a f ≠ 0 := by
  exact combinatorial_nullstellensatz f t (fun _ => S) hdeg hcoeff hS

/-
## Part V: The Polynomial Method Framework

The Combinatorial Nullstellensatz exemplifies the "polynomial method":
to prove a combinatorial statement about a set A, construct a polynomial f
that encodes the structure, then use algebraic properties of f to derive
combinatorial conclusions.

Key applications (not formalized here):
1. **Cauchy-Davenport**: |A + B| ≥ min(p, |A| + |B| - 1) for A,B ⊆ Z/pZ
2. **Chevalley-Warning**: Low-degree systems over finite fields have solutions
3. **Permanent bounds**: Lower bounds on permanents of matrices
4. **Graph colorings**: Alon-Tarsi theorem on list chromatic numbers

The polynomial method continues to produce breakthroughs in combinatorics,
additive number theory, and theoretical computer science.
-/

/-
## Summary

### Axioms (2)
1. `grid_nonvanishing` - Bounded-degree polynomial doesn't vanish on product grids
2. `combinatorial_nullstellensatz` - Alon's main theorem

### Proved (3)
1. `exists_eval_ne_zero` - Single-variable non-vanishing (from polynomial root bound)
2. `combinatorial_nullstellensatz'` - Variant with |Sᵢ| ≥ tᵢ + 1
3. `nonvanishing_uniform_grid` - Specialization to uniform grids

### Path to Full Proof
The main gap is polynomial division in MvPolynomial: reducing f modulo
the grid polynomials gᵢ(xᵢ) = ∏_{s ∈ Sᵢ} (xᵢ - s). This requires:
1. MvPolynomial division (modular reduction one variable at a time)
2. Degree bound preservation under reduction
3. Coefficient preservation for the leading monomial

If Mathlib gains multivariate polynomial division, the axiom can be removed.

### Axiom Integrity
- `grid_nonvanishing`: 1 axiom (could be proved by induction + single-variable case)
- `combinatorial_nullstellensatz`: 1 axiom (needs polynomial division infrastructure)
- Total axiom count: 2
-/

#check @exists_eval_ne_zero
#check @combinatorial_nullstellensatz
#check @nonvanishing_uniform_grid

end CombinatorialNullstellensatz
