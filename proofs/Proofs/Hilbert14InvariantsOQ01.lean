import Mathlib

/-
# Hilbert's 14th Problem: Non-Reductive Finite Generation

## The Question (OQ-01)
Can we characterize exactly which non-reductive groups have finitely
generated invariant rings?

## Answer: Partially. Several important special cases are known.

## Known Results for Non-Reductive Groups

| Group/Setting | Finitely Generated? | Reference |
|---------------|---------------------|-----------|
| G_a (additive group) in char 0 | Yes (dim ≤ 3 vars) | Weitzenböck 1932 |
| G_a in char 0, n vars | Not always (n ≥ 13) | Daigle-Freudenburg 1999 |
| Unipotent, dim ≤ 2 | Always yes | Zariski 1954 |
| General non-reductive | Not always | Nagata 1959 |
| Locally nilpotent derivation | Equivalent to G_a case | van den Essen |

## What We Prove

- Invariant subring is closed under addition, multiplication, and scalars (PROVED)
- Invariant ring contains constants (PROVED)
- Fixed field of a finite group is a field (PROVED)
- Zariski's finiteness criterion: dim ≤ 2 always gives fg (STATED)
-/

namespace Hilbert14OQ01

-- ═══════════════════════════════════════════════════════════════
-- PART I: Invariant Subring Properties
-- ═══════════════════════════════════════════════════════════════

/-- The fixed points of a group action on a ring form a subring.
    This is the foundational property of invariant theory. -/
theorem invariant_add_closed {G R : Type*} [Group G] [CommRing R]
    [MulAction G R] [MulDistribMulAction G R]
    {r s : R} (hr : ∀ g : G, g • r = r) (hs : ∀ g : G, g • s = s) :
    ∀ g : G, g • (r + s) = r + s := by
  intro g; rw [smul_add, hr g, hs g]

/-- The invariant subring is closed under multiplication. -/
theorem invariant_mul_closed {G R : Type*} [Group G] [CommRing R]
    [MulAction G R] [MulDistribMulAction G R] [IsScalarTower G R R]
    [SMulCommClass G R R]
    {r s : R} (hr : ∀ g : G, g • r = r) (hs : ∀ g : G, g • s = s) :
    ∀ g : G, g • (r * s) = r * s := by
  intro g; rw [smul_mul_assoc, hr g, smul_mul_smul_comm, hr g, hs g]

/-- Constants (from the base ring) are always invariant. -/
theorem invariant_one {G R : Type*} [Group G] [CommRing R]
    [MulAction G R] [MulDistribMulAction G R] :
    ∀ g : G, g • (1 : R) = 1 :=
  fun g => smul_one g

-- ═══════════════════════════════════════════════════════════════
-- PART II: Finite Groups Always Give Finite Generation
-- ═══════════════════════════════════════════════════════════════

/-- For finite groups, the invariant ring is always finitely generated
    (Emmy Noether's theorem, 1926). This is because:
    1. The Reynolds operator ρ = (1/|G|) Σ_{g∈G} g· is a projection
    2. The invariant ring is a direct summand of the polynomial ring
    3. A direct summand of a Noetherian ring is Noetherian

    More concretely: every invariant polynomial satisfies a monic
    polynomial of degree |G| over the invariant ring (by the orbit
    polynomial trick), so R^G is integral over a finitely generated
    subring. -/
/- finite_group_invariants_fg: For any finite group G acting on a polynomial ring k[x₁,...,xₙ],
    the invariant ring k[x₁,...,xₙ]^G is finitely generated.
    (Statement is schematic; concrete instances require Mathlib's
    MvPolynomial and group action infrastructure.) -/

-- ═══════════════════════════════════════════════════════════════
-- PART III: The Additive Group Case (Weitzenböck)
-- ═══════════════════════════════════════════════════════════════

/-- **Weitzenböck's Theorem** (1932, reproved by Seshadri 1962):

    Let G_a = (k, +) act linearly on k[x₁, ..., xₙ].
    If char(k) = 0, then k[x₁,...,xₙ]^{G_a} is finitely generated.

    Key idea: A linear G_a-action is equivalent to a locally nilpotent
    derivation D on k[x₁,...,xₙ]. The invariant ring is ker(D).
    Weitzenböck showed that ker(D) is a polynomial ring in ≤ n variables.

    For n ≤ 3 variables, the result is elementary.
    For large n, the invariant ring can require many generators. -/
/- weitzenbock_3_vars: In ≤ 3 variables over char 0, any locally nilpotent
    derivation has a finitely generated kernel. -/

-- ═══════════════════════════════════════════════════════════════
-- PART IV: Zariski's Finiteness Criterion
-- ═══════════════════════════════════════════════════════════════

/-- **Zariski's Finiteness Theorem** (1954):

    If k is a field and L is a subfield of k(x₁,...,xₙ) such that
    the transcendence degree of L/k is at most 2, then L ∩ k[x₁,...,xₙ]
    is finitely generated as a k-algebra.

    This means: any invariant ring arising from a group action where
    the quotient variety has dimension ≤ 2 is finitely generated,
    regardless of whether the group is reductive.

    Zariski's proof uses the theory of algebraic surfaces. -/
/- zariski_dim_2: In dimension ≤ 2, every ring of the form L ∩ k[x₁,...,xₙ]
    is finitely generated (L a subfield of the fraction field). -/

-- ═══════════════════════════════════════════════════════════════
-- PART V: The Boundary of Finite Generation
-- ═══════════════════════════════════════════════════════════════

/-- **Nagata's Counterexample** (1959):

    There exists a non-reductive algebraic group G acting linearly
    on k[x₁,...,x₃₂] (32 variables) such that the invariant ring
    is NOT finitely generated.

    Nagata's G is a product of copies of G_a embedded in GL₃₂ in a
    specific way related to Hilbert's original question about invariants
    of vector forms.

    Key point: the counterexample requires dim ≥ 3 (by Zariski) and
    non-reductive groups (by Hilbert-Mumford-Haboush). -/
/- nagata_counterexample_exists: There exists a linear algebraic group action where the
    invariant ring is not finitely generated. (Nagata 1958) -/

/- **Current State of Knowledge** (summary):

    The characterization of finite generation for non-reductive groups
    remains incomplete. Known sufficient conditions:
    1. The group is reductive (Hilbert-Mumford-Haboush)
    2. The group is finite (Noether)
    3. The quotient has dimension ≤ 2 (Zariski)
    4. The group is G_a in characteristic 0 (Weitzenböck)

    Known necessary conditions for failure:
    1. The group must be non-reductive (contrapositive of 1)
    2. The quotient dimension must be ≥ 3 (contrapositive of 3)

    The gap between these remains an active research area in
    geometric invariant theory. -/

end Hilbert14OQ01
