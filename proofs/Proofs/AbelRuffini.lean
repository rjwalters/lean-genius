import Mathlib.FieldTheory.AbelRuffini
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.FieldTheory.Galois.Basic

/-!
# Abel-Ruffini Theorem

## What This Proves
There is no general solution in radicals to polynomial equations of degree
five or higher. We show that solvability by radicals requires a solvable
Galois group, and that S₅ (and A₅) are not solvable.

## Approach
- **Foundation (from Mathlib):** Mathlib provides the complete Galois theory
  infrastructure including `IsSolvableByRad`, `solvableByRad.isSolvable'`,
  and the non-solvability of alternating groups.
- **Original Contributions:** Pedagogical wrappers composing Mathlib's solvability
  theory into an accessible walkthrough: the Galois-theoretic bridge, contrapositive
  form of Abel-Ruffini, S₅/A₅ non-solvability, and solvability of small symmetric
  groups (all mathematical weight carried by Mathlib).

## Mathlib Dependencies
- `IsSolvableByRad` : Definition of solvable by radicals
- `solvableByRad.isSolvable'` : Solvable by radicals ⟹ solvable Galois group
- `Equiv.Perm.not_solvable` : Sₙ is not solvable for n ≥ 5
- `alternatingGroup.isSimpleGroup_five` : A₅ is simple
- `FieldTheory.Galois` : Galois theory foundations

Historical Note: Proven by Niels Henrik Abel in 1824, later illuminated by
Évariste Galois's theory connecting solvability to group structure.
-/

namespace AbelRuffini

/-!
## Part I: Solvable by Radicals

An element α of an extension field E/F is *solvable by radicals* if it can be
expressed using only:
1. Elements from the base field F
2. Field operations: +, -, ×, ÷
3. nth roots of elements already constructed

Mathlib defines this inductively via `IsSolvableByRad`.
-/

variable {F : Type*} [Field F]
variable {E : Type*} [Field E] [Algebra F E]

/-!
## Part II: The Galois-Theoretic Bridge

The key theorem connecting solvability by radicals to group theory:
if α is solvable by radicals, then the Galois group of its minimal
polynomial is a solvable group. This is Galois's fundamental insight.
-/

/--
**Galois's Theorem (from Mathlib):**
If α ∈ E is solvable by radicals over F, and q is an irreducible polynomial
over F with q(α) = 0, then the Galois group of q is a solvable group.
-/
theorem galois_bridge (α : E) (q : Polynomial F) (hq : Irreducible q)
    (hroot : Polynomial.aeval α q = 0) (hrad : IsSolvableByRad F α) :
    IsSolvable q.Gal :=
  solvableByRad.isSolvable' hq hroot hrad

/-!
## Part III: Non-Solvability of Large Symmetric Groups

The symmetric group Sₙ is not solvable for n ≥ 5. This is because
Aₙ (for n ≥ 5) is a simple non-abelian group, so the derived series
of Sₙ gets stuck at Aₙ.
-/

/-- The symmetric group on 5 or more elements is not solvable.
    This is the group-theoretic heart of Abel-Ruffini. -/
theorem symmetric_group_not_solvable (n : ℕ) (hn : 5 ≤ n) :
    ¬ IsSolvable (Equiv.Perm (Fin n)) := by
  have h : 5 ≤ Cardinal.mk (Fin n) := by
    simp only [Cardinal.mk_fintype, Fintype.card_fin]
    exact_mod_cast hn
  exact Equiv.Perm.not_solvable (Fin n) h

/-- S₅ is not solvable. The specific case n = 5. -/
theorem s5_not_solvable : ¬ IsSolvable (Equiv.Perm (Fin 5)) :=
  symmetric_group_not_solvable 5 le_rfl

/-- S₆ is not solvable. The case n = 6. -/
theorem s6_not_solvable : ¬ IsSolvable (Equiv.Perm (Fin 6)) :=
  symmetric_group_not_solvable 6 (by omega)

/-- A₅ is simple: it has no non-trivial normal subgroups.
    This is the fundamental reason S₅ is not solvable - the derived series
    S₅ ▷ A₅ ▷ ... gets stuck at A₅ since A₅ has no proper normal subgroups. -/
theorem a5_is_simple : IsSimpleGroup (alternatingGroup (Fin 5)) :=
  alternatingGroup.isSimpleGroup_five

/-!
## Part IV: Solvability of Small Symmetric Groups

The trivial permutation group S₀ is solvable (it's the trivial group).
S₁ is also solvable (also trivial). For S₂, S₃, S₄, Mathlib does not
currently provide IsSolvable instances, though these groups are mathematically
solvable. The derived series are:
- S₂: {e} ◁ S₂ (abelian, done)
- S₃: {e} ◁ A₃ ◁ S₃ (A₃ is cyclic of order 3)
- S₄: {e} ◁ V₄ ◁ A₄ ◁ S₄ (V₄ is Klein four group, all quotients abelian)

For n ≥ 5, Sₙ is NOT solvable because Aₙ is simple and non-abelian.
-/

/-- S₀ (trivial group on empty type) is solvable. -/
theorem s0_solvable : IsSolvable (Equiv.Perm (Fin 0)) := inferInstance

/-- S₁ (trivial group on single element) is solvable. -/
theorem s1_solvable : IsSolvable (Equiv.Perm (Fin 1)) := inferInstance

/-!
## Part V: The Abel-Ruffini Theorem

Combining Parts II and III: if a polynomial has Galois group Sₙ for n ≥ 5,
then its roots cannot be expressed by radicals.

The contrapositive: if α is solvable by radicals and q is its irreducible
minimal polynomial, then Gal(q) is solvable. Since S₅ is not solvable,
any polynomial with Galois group S₅ cannot have roots solvable by radicals.
-/

/-- Statement: there exists a degree-5 polynomial over ℚ. -/
theorem exists_quintic :
    ∃ p : Polynomial ℚ, p.natDegree = 5 := by
  use Polynomial.X ^ 5
  simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one]

/--
**Abel-Ruffini (contrapositive form):**
If the Galois group of an irreducible polynomial q is not solvable,
and α is a root of q, then α is NOT solvable by radicals.

This is the contrapositive of `galois_bridge`: solvable by radicals implies
solvable Galois group, so unsolvable Galois group implies not solvable by radicals.
-/
theorem not_solvable_by_rad_of_not_solvable_gal (α : E) (q : Polynomial F)
    (hq : Irreducible q) (hroot : Polynomial.aeval α q = 0)
    (hns : ¬ IsSolvable q.Gal) : ¬ IsSolvableByRad F α := by
  intro hrad
  exact hns (galois_bridge α q hq hroot hrad)

/-!
## Part VI: The Threshold at Degree 5

The key insight of Galois theory is that degree 5 is precisely the threshold:
- For n ≤ 4: Sₙ is solvable, so the general degree-n polynomial CAN be
  solved by radicals (quadratic formula, cubic formula, quartic formula)
- For n ≥ 5: Sₙ is NOT solvable, so the general degree-n polynomial
  CANNOT be solved by radicals

This is because A₅ is the smallest non-abelian simple group (with 60 elements).
A₄ has the Klein four-group V₄ as a normal subgroup, so A₄ is solvable.
A₅ has NO proper normal subgroups at all (it is simple), so A₅ is not solvable.
-/

/-!
## Part VII: Historical Significance

The Abel-Ruffini theorem was revolutionary:

1. **Impossibility result**: Before Abel, mathematicians sought *the* quintic formula
   like the quadratic formula. Abel showed no such formula exists.

2. **Birth of group theory**: Galois's insight that solvability relates to
   group structure laid foundations for modern algebra.

3. **Methodology**: This was one of the first major "impossibility proofs" -
   showing something *cannot* be done, rather than constructing a solution.

4. **Contrast with numerics**: Quintic equations DO have solutions (by FTA),
   and we CAN compute them numerically. We just can't write them with radicals.

5. **Precise characterization**: Galois theory doesn't just say "quintics are
   unsolvable" - it precisely characterizes WHICH polynomials of any degree
   are solvable by radicals (those with solvable Galois groups).
-/

end AbelRuffini
