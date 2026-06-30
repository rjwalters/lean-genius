/-
Equivariant Index of Non-Free Z/p Actions: The Localization Collapse

Open Question (borsuk-ulam-oq-02-oq-04):
"For non-free Z/p actions: does the equivariant index still control vanishing,
 or does control pass to the fixed-point set?"

Answer: For NON-FREE Z/p actions (p prime) the Fadell-Husseini / Dold
cohomological index DEGENERATES to the trivial value (the index ideal is 0,
equivalently the numerical height is +infinity). It therefore no longer
controls vanishing in any discriminating way: it returns the same value for
EVERY space with a fixed point. The genuine obstruction collapses onto the
fixed-point set, which is always nonempty for a non-free Z/p-action on a
mod-p homology sphere (Smith theory). Vanishing is still forced, but trivially,
by the fixed point: any Z/p-map of a fixed-point space into a fixed-point-free
representation W sends the fixed point x0 into W^{Z/p} = {0}.

Background:
For a FREE Z/p-space the Fadell-Husseini index
  iota(X) = sup { k : the k-th power of the Euler class survives in H^*_G(X) }
is a finite number that grows with the topological complexity of X; it is the
engine behind every Borsuk-Ulam bound (iota(S^n) = n for the antipodal action,
iota(S^{2k-1}) = 2k-1 for the standard free rotation), and equivariant maps are
monotone for it (X -> Y forces iota(X) <= iota(Y)). See OQ02OQ03 (Dold) and
OQ02OQ01OQ04 (Fadell-Husseini) for the free theory.

The Localization Theorem (Borel) explains the collapse: if X has a Z/p-fixed
point x0, the inclusion {x0} -> X splits the structure map
  H^*(BZ/p) -> H^*_{Z/p}(X)
(restriction to x0 is a retraction), so this map is INJECTIVE. Hence no power
of the Euler class is killed and iota(X) = +infinity. The index ideal
Ind_{Z/p}(X) = ker(H^*(BG) -> H^*_G(X)) is therefore 0 -- it carries no
obstruction.

This file axiomatizes the index together with the localization property and
derives the dichotomy. We model the index as a value in WithTop Nat, with
the top element TOP standing for "+infinity = trivial index = no obstruction".

Axiom count: 10 (4 carrier declarations + 1 sphere family + 1 test-map relation
+ 4 structural properties). Status: axiomatized.
Theorem count: 11 consequences proved from the axioms.

References:
- Fadell & Husseini, "An ideal-valued cohomological index theory" (1988)
- Dold, "Simple proofs of some Borsuk-Ulam results" (1983)
- P.A. Smith, "Transformations of finite period" (1938) -- fixed-point theory
- A. Borel, "Seminar on Transformation Groups" (1960) -- localization
- Matousek, "Using the Borsuk-Ulam Theorem" (2003), Chapter 6
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.WithBot
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace BorsukUlamOQ02OQ04

-- ============================================================
-- PART I: The Index Theory (Axiomatized Carriers)
-- ============================================================

/-- The carrier type of Z/p-spaces under consideration (mod-p homology spheres
    with a continuous Z/p-action). Abstracted; we axiomatize the structure we
    need rather than building equivariant cohomology. -/
axiom Space : Type

/-- The Fadell-Husseini / Dold cohomological index iota(X), valued in
    `WithTop Nat`. A finite value `n` is the numerical height of the surviving
    Euler-class powers; the top element `TOP` means "+infinity", i.e. the
    index ideal is 0 and the index carries no obstruction. -/
axiom idx : Space → WithTop ℕ

/-- `GMap X Y` holds when a Z/p-equivariant continuous map `X -> Y` exists. -/
axiom GMap : Space → Space → Prop

/-- `HasFixedPoint X` holds when the Z/p-action on `X` has a fixed point,
    i.e. `X^{Z/p}` is nonempty. For p prime this is exactly the failure of
    freeness (every nonidentity element of Z/p generates the whole group, so a
    point fixed by one nonidentity element is fixed by all of Z/p). -/
axiom HasFixedPoint : Space → Prop

/-- The standard FREE Z/p-sphere `freeSphere n` = `S^n` with a fixed-point-free
    action (antipodal for p = 2; standard rotation for odd p). This is the unit
    sphere `S(W)` of a fixed-point-free representation `W`. -/
axiom freeSphere : ℕ → Space

/-- `ZeroAvoidingMap X m` holds when there is a Z/p-map `X -> W \ {0}`, where `W`
    is the fixed-point-free representation whose unit sphere is `freeSphere m`.
    Its negation, `¬ ZeroAvoidingMap X m`, says every Z/p-map `X -> W` has a
    zero -- i.e. vanishing is forced. -/
axiom ZeroAvoidingMap : Space → ℕ → Prop

-- ============================================================
-- PART II: Axiomatized Properties
-- ============================================================

/-- Free-sphere index: `iota(freeSphere n) = n`. The free action gives a finite,
    dimension-sensitive obstruction -- the content of Borsuk-Ulam / Yang. -/
axiom idx_freeSphere (n : ℕ) : idx (freeSphere n) = (n : WithTop ℕ)

/-- **Monotonicity (the engine of Borsuk-Ulam).** A Z/p-map `X -> Y` forces
    `iota(X) <= iota(Y)`: equivariant maps can only increase the index. -/
axiom idx_mono {X Y : Space} (h : GMap X Y) : idx X ≤ idx Y

/-- **Localization collapse (Borel + Smith).** If `X` has a Z/p-fixed point then
    the structure map `H^*(BG) -> H^*_G(X)` is split-injective, so no Euler-class
    power dies and `iota(X) = +infinity = TOP`. This is the crux: a single fixed
    point trivializes the index. -/
axiom idx_localization {X : Space} (h : HasFixedPoint X) : idx X = ⊤

/-- **Test-map scheme.** A zero-avoiding Z/p-map `X -> W \ {0}` is the same datum
    as a Z/p-map into the unit sphere `freeSphere m = S(W)` (radial deformation
    retraction). This is how the index controls vanishing. -/
axiom zeroAvoiding_iff (X : Space) (m : ℕ) :
    ZeroAvoidingMap X m ↔ GMap X (freeSphere m)

-- ============================================================
-- PART III: The Free Theory -- the index DOES control
-- ============================================================

/-- **Borsuk-Ulam bound (free case).** For `m < n` there is no Z/p-map
    `freeSphere n -> freeSphere m`: the index obstruction `n > m` blocks it.
    This is the classical antipodal Borsuk-Ulam (p = 2) and Yang's theorem
    (odd p), recovered as the free, finite-index regime. -/
theorem index_controls_free (n m : ℕ) (h : m < n) :
    ¬ GMap (freeSphere n) (freeSphere m) := by
  intro hmap
  have hle : idx (freeSphere n) ≤ idx (freeSphere m) := idx_mono hmap
  rw [idx_freeSphere, idx_freeSphere] at hle
  have : n ≤ m := by exact_mod_cast hle
  omega

/-- The free index is a genuine (finite) obstruction: `iota(freeSphere n) ≠ TOP`. -/
theorem free_index_finite (n : ℕ) : idx (freeSphere n) ≠ ⊤ := by
  rw [idx_freeSphere]; simp

/-- The free index DISCRIMINATES: distinct dimensions give distinct indices.
    This is the discriminating power that the non-free case will lose. -/
theorem index_discriminates_free (n m : ℕ) (h : n ≠ m) :
    idx (freeSphere n) ≠ idx (freeSphere m) := by
  rw [idx_freeSphere, idx_freeSphere]
  exact fun hh => h (by exact_mod_cast hh)

/-- Strict monotonicity of the free index in the dimension. -/
theorem free_index_strict_mono (n m : ℕ) (h : n < m) :
    idx (freeSphere n) < idx (freeSphere m) := by
  rw [idx_freeSphere, idx_freeSphere]
  exact_mod_cast h

-- ============================================================
-- PART IV: The Non-Free Collapse -- the index does NOT control
-- ============================================================

/-- **Index trivializes on fixed-point spaces.** Restatement of localization as
    a named result: any non-free `X` (one with a Z/p-fixed point) has
    `iota(X) = +infinity`. -/
theorem index_trivial_of_fixedPoint {X : Space} (h : HasFixedPoint X) :
    idx X = ⊤ := idx_localization h

/-- **No discrimination.** Any two fixed-point spaces have the SAME index `TOP`.
    The index has lost all power to distinguish non-free Z/p-spaces -- it is the
    constant `+infinity` on this entire class. -/
theorem index_no_discrimination {X Y : Space}
    (hX : HasFixedPoint X) (hY : HasFixedPoint Y) : idx X = idx Y := by
  rw [idx_localization hX, idx_localization hY]

/-- **Fixed-point spaces admit no equivariant map to a free sphere.** If `X` has
    a fixed point, the index `TOP` exceeds every finite `m`, so monotonicity
    forbids a Z/p-map `X -> freeSphere m`. (A fixed point of `X` cannot map to
    the free, fixed-point-free sphere.) -/
theorem no_map_to_free_sphere_of_fixedPoint {X : Space}
    (hfp : HasFixedPoint X) (m : ℕ) : ¬ GMap X (freeSphere m) := by
  intro hmap
  have hle : idx X ≤ idx (freeSphere m) := idx_mono hmap
  rw [idx_localization hfp, idx_freeSphere] at hle
  -- TOP ≤ ↑m  forces  ↑m = TOP, impossible; `simp` discharges via top_le_iff.
  simp at hle

/-- **Vanishing is forced for non-free actions.** If `X` has a Z/p-fixed point,
    then for every fixed-point-free representation `W` (sphere `freeSphere m`)
    NO zero-avoiding map exists: every Z/p-map `X -> W` has a zero. -/
theorem vanishing_forced_of_fixedPoint {X : Space}
    (hfp : HasFixedPoint X) (m : ℕ) : ¬ ZeroAvoidingMap X m := by
  rw [zeroAvoiding_iff]
  exact no_map_to_free_sphere_of_fixedPoint hfp m

-- ============================================================
-- PART V: The Dichotomy -- the answer to OQ-02-OQ-04
-- ============================================================

/-- **Main dichotomy.** For a non-free Z/p-space `X` (one with a fixed point):
    the index degenerates to `TOP` (carrying no obstruction), yet vanishing is
    still forced for every fixed-point-free target. The two facts together say
    the *index* no longer controls vanishing -- control has passed to the
    fixed-point set, whose nonemptiness alone forces the zero. -/
theorem index_control_dichotomy {X : Space} (hfp : HasFixedPoint X) :
    idx X = ⊤ ∧ ∀ m, ¬ ZeroAvoidingMap X m :=
  ⟨idx_localization hfp, fun m => vanishing_forced_of_fixedPoint hfp m⟩

/-- **Sharp contrast at fixed complexity.** Take any free sphere `freeSphere n`
    and any non-free space `X`. Their indices are never equal: the free one is
    finite (`n`), the non-free one is `TOP`. The index cleanly separates the two
    regimes, but is informative only in the free one. -/
theorem free_vs_nonfree_index {X : Space} (hfp : HasFixedPoint X) (n : ℕ) :
    idx (freeSphere n) ≠ idx X := by
  rw [idx_freeSphere, idx_localization hfp]
  simp

/-- **Control passes to the fixed-point set.** Equivalent packaging of the
    answer: "does the index control vanishing?" For non-free `X` the index is
    constant (`= idx Y` for every other non-free `Y`), so it cannot be what
    distinguishes which maps vanish; nevertheless every map into a free target
    vanishes. The discriminating data is `HasFixedPoint` itself. -/
theorem control_passes_to_fixedPoints {X Y : Space}
    (hX : HasFixedPoint X) (hY : HasFixedPoint Y) :
    idx X = idx Y ∧ (∀ m, ¬ ZeroAvoidingMap X m) ∧ (∀ m, ¬ ZeroAvoidingMap Y m) :=
  ⟨index_no_discrimination hX hY,
   fun m => vanishing_forced_of_fixedPoint hX m,
   fun m => vanishing_forced_of_fixedPoint hY m⟩

-- ============================================================
-- PART VI: Formalizability Assessment
-- ============================================================

/-
## Answer to OQ-02-OQ-04

**For non-free Z/p actions the equivariant index does NOT control vanishing.**
It collapses (by localization) to the constant value +infinity on every
fixed-point space, losing all discriminating power. Vanishing is still forced,
but trivially: the genuine obstruction migrates to the fixed-point set
`X^{Z/p}`, which is nonempty by Smith theory. In symbols, for `HasFixedPoint X`:

  iota(X) = +infinity   (no index obstruction)
  yet  every Z/p-map  X -> W \ {0}  fails to exist  (vanishing forced)

because the fixed point `x0` satisfies `f(x0) in W^{Z/p} = {0}`.

This is the exact opposite of the FREE regime (OQ02OQ03, OQ02OQ01OQ04), where
iota is finite, dimension-sensitive, and is precisely the obstruction governing
which equivariant maps exist.

### Available in Mathlib (as of v4.x):
1. Group actions, fixed-point sets (`MulAction`, `MulAction.fixedPoints`)
2. `ZMod p`, primality (`Nat.Prime`)
3. `WithTop`/`ENat` order theory (used here for the +infinity value)

### Missing from Mathlib (to remove the axioms):
1. Borel equivariant cohomology `H^*_G(-)` and the Euler class (~1300 lines)
2. The localization theorem: a fixed point splits `H^*(BG) -> H^*_G(X)` (~250)
3. Smith theory: a non-free Z/p-action on a mod-p homology sphere has nonempty
   fixed-point set (~400 lines)
4. The Fadell-Husseini index and its monotonicity (~300 lines)

### Highest-value path:
The single axiom doing the real work is `idx_localization` (the splitting). With
a Borel-cohomology layer in place it is a 1-line consequence of the retraction
`X -> {x0} -> X`. Everything else here is order arithmetic on `WithTop Nat`.
-/

end BorsukUlamOQ02OQ04
