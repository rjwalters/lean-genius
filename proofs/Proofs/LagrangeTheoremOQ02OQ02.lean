import Mathlib
import Proofs.LagrangeTheoremOQ02

/-
  The Class Equation for Finite Groups (lagrange-theorem-oq-02-oq-02)

  For a finite group G, the class equation states:

    |G| = |Z(G)| + Σ_{x ∉ Z(G), one per non-central class} [G : C_G(x)]

  where:
  - Z(G) = center of G (elements commuting with all of G)
  - Each conjugacy class [x] = {gxg⁻¹ : g ∈ G} is an orbit under conjugation
  - Non-central classes have more than one element
  - Each non-central class has size [G : C_G(x)] by orbit-stabilizer

  ## Proof chain:
  (1) G is partitioned into conjugacy classes via ConjClasses.mk : G → ConjClasses G
  (2) |[x]| = [G : C_G(x)] by orbit-stabilizer applied to the conjugation action
  (3) Singleton classes ↔ x ∈ Z(G) (since gxg⁻¹ = x for all g iff x is central)
  (4) Splitting: |G| = |Z(G)| + Σ_{non-central classes c} |c|

  ## Key applications:
  - p-Group center: p | |G| ≡ |Z(G)| (mod p) → Z(G) is nontrivial for p-groups
  - Groups of order p² are abelian
  - Sylow classification of groups of order pq

  ## Hierarchy:
    Lagrange → Orbit-Stabilizer → Burnside → Class Equation → p-Group Theory

  References:
  - Dummit & Foote, "Abstract Algebra", §4.3
  - Rotman, "An Introduction to the Theory of Groups", §2.5
  - Mathlib: Mathlib.GroupTheory.ClassEquation

  Tags: group-theory, algebra, class-equation, conjugacy-classes, p-groups, orbit-stabilizer
-/

set_option maxHeartbeats 800000

namespace LagrangeTheoremOQ02OQ02

open Subgroup ConjClasses MulAction

-- ============================================================================
-- Part I: The Class Equation (from Mathlib.GroupTheory.ClassEquation)
-- ============================================================================

/-- **The Class Equation**: for any group G,
    |Z(G)| + Σ_{c ∈ noncenter G} |c| = |G|.

    `noncenter G` is the set of conjugacy classes with non-central elements
    (equivalently, classes [x] with |[x]| > 1).

    For finite G, the finitely-supported sum ∑ᶠ equals an ordinary Σ.

    Source: `Group.nat_card_center_add_sum_card_noncenter_eq_card` in
    `Mathlib.GroupTheory.ClassEquation`. -/
theorem class_equation {G : Type*} [Group G] :
    Nat.card (center G) + ∑ᶠ c ∈ noncenter G, Nat.card c.carrier = Nat.card G :=
  Group.nat_card_center_add_sum_card_noncenter_eq_card G

/-- Equivalent form: |G| = |Z(G)| + Σ_{non-central classes c} |c|. -/
theorem class_equation_symm {G : Type*} [Group G] :
    Nat.card G = Nat.card (center G) + ∑ᶠ c ∈ noncenter G, Nat.card c.carrier :=
  class_equation.symm

-- ============================================================================
-- Part II: Orbit-Stabilizer for the Conjugation Action
-- ============================================================================

section ConjugationAction

variable {G : Type*} [Group G]

/-- The orbit of x under ConjAct G equals the carrier of the conjugacy class of x.

    Both equal {gxg⁻¹ : g ∈ G}:
    - orbit: {c • x : c : ConjAct G} where `ConjAct.toConjAct g • x = g * x * g⁻¹`
    - carrier of ConjClasses.mk x: {y | IsConj x y} = {y | ∃ g, g * x = y * g} -/
theorem conj_orbit_eq_carrier (x : G) :
    orbit (ConjAct G) x = (ConjClasses.mk x).carrier := by
  ext y
  simp only [mem_orbit_iff, ConjClasses.mem_carrier_iff_isConj, IsConj, SemiconjBy]
  constructor
  · rintro ⟨c, hc⟩
    -- hc : c • x = y; use g = ConjAct.ofConjAct c to witness SemiconjBy
    refine ⟨ConjAct.ofConjAct c, ?_⟩
    rw [ConjAct.smul_def] at hc
    -- hc : ConjAct.ofConjAct c * x * (ConjAct.ofConjAct c)⁻¹ = y
    -- Need: ConjAct.ofConjAct c * x = y * ConjAct.ofConjAct c
    calc ConjAct.ofConjAct c * x
        = ConjAct.ofConjAct c * x * (ConjAct.ofConjAct c)⁻¹ * ConjAct.ofConjAct c := by group
      _ = y * ConjAct.ofConjAct c := by rw [hc]
  · rintro ⟨g, hg⟩
    -- hg : g * x = y * g; use ConjAct.toConjAct g as witness
    refine ⟨ConjAct.toConjAct g, ?_⟩
    rw [ConjAct.toConjAct_smul]
    -- Goal: g * x * g⁻¹ = y
    calc g * x * g⁻¹ = y * g * g⁻¹ := by rw [← hg]
      _ = y := by group

/-- The stabilizer of x under conjugation, pulled back to G, equals C_G(x).

    g stabilizes x ↔ g * x * g⁻¹ = x ↔ g * x = x * g ↔ g ∈ C_G(x). -/
theorem conj_stabilizer_eq_centralizer (x : G) :
    (stabilizer (ConjAct G) x).comap ConjAct.toConjAct = centralizer {x} := by
  ext g
  simp only [Subgroup.mem_comap, mem_stabilizer_iff, ConjAct.toConjAct_smul,
             mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  -- Goal: g * x * g⁻¹ = x ↔ g * x = x * g
  constructor
  · intro h
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [h]
  · intro h
    calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [← h]
      _ = x := by group

/-- **Orbit-Centralizer Formula**: the conjugacy class of x has size [G : C_G(x)].

    By orbit-stabilizer: |[x]| × |C_G(x)| = |G|, so |[x]| = [G : C_G(x)].

    This is the quantitative backbone of the class equation:
    each non-central class contributes exactly [G : C_G(x)] ≥ 2. -/
theorem card_conjClass_eq_centralizer_index [Fintype G] (x : G) :
    Nat.card (ConjClasses.mk x).carrier = (centralizer {x}).index := by
  rw [← conj_orbit_eq_carrier]
  -- orbit-stabilizer: Nat.card orbit * Nat.card stabilizer = Nat.card G
  -- with stabilizer (via toConjAct) = centralizer {x}
  -- so Nat.card orbit = centralizer index
  sorry -- HARD: finalize via Nat.card orbit-stabilizer and index arithmetic

/-- A conjugacy class is a singleton iff the element is central. -/
theorem card_conjClass_eq_one_iff_mem_center [Fintype G] (x : G) :
    Nat.card (ConjClasses.mk x).carrier = 1 ↔ x ∈ center G := by
  rw [← conj_orbit_eq_carrier]
  constructor
  · intro h
    rw [Nat.card_eq_one_iff_unique] at h
    rw [mem_center_iff]
    intro g
    -- The orbit is a singleton; both x and ConjAct.toConjAct g • x lie in it
    have huniq : ∀ a b : orbit (ConjAct G) x, a = b := fun a b =>
      (h.uniq a).trans (h.uniq b).symm
    have heq := congr_arg Subtype.val
      (huniq ⟨ConjAct.toConjAct g • x, mem_orbit _ _⟩ ⟨x, mem_orbit_self _⟩)
    -- heq : ConjAct.toConjAct g • x = x, i.e., g * x * g⁻¹ = x
    rw [ConjAct.toConjAct_smul] at heq
    -- heq : g * x * g⁻¹ = x; derive g * x = x * g
    have key : g * x = x * g := by
      calc g * x = g * x * g⁻¹ * g := by group
        _ = x * g := by rw [heq]
    exact key.symm
  · intro hx
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨⟨x, mem_orbit_self _⟩, fun ⟨y, c, hc⟩ => by
      simp only [Subtype.mk.injEq]
      -- hc : c • x = y (c : ConjAct G); show y = x using hx ∈ Z(G)
      rw [← hc, ConjAct.smul_def]
      -- Goal: ConjAct.ofConjAct c * x * (ConjAct.ofConjAct c)⁻¹ = x
      have hcomm : ConjAct.ofConjAct c * x = x * ConjAct.ofConjAct c :=
        (mem_center_iff.mp hx (ConjAct.ofConjAct c)).symm
      calc ConjAct.ofConjAct c * x * (ConjAct.ofConjAct c)⁻¹
          = x * ConjAct.ofConjAct c * (ConjAct.ofConjAct c)⁻¹ := by rw [hcomm]
        _ = x := by group⟩⟩

end ConjugationAction

-- ============================================================================
-- Part III: Applications to p-Groups
-- ============================================================================

section PGroupApplications

variable {p : ℕ} [hp : Fact p.Prime] {G : Type*} [Group G] [Fintype G]

/-- **p-Group Fixed Point Theorem**: when a p-group G acts on a finite set X,
    |X| ≡ |Fix(G, X)| (mod p).

    Non-trivial orbits have size divisible by p (divide |G| = p^k and are > 1).
    So |X| = |Fix| + Σ(divisible-by-p) ≡ |Fix| (mod p).

    Applied to conjugation: |G| ≡ |Z(G)| (mod p). -/
theorem pgroup_fixed_point (hG : IsPGroup p G) {X : Type*} [Fintype X] [MulAction G X] :
    Nat.card X ≡ Nat.card (fixedPoints G X) [MOD p] :=
  IsPGroup.card_modEq_card_fixedPoints hG X

/-- **Nontrivial Center**: the center of a nontrivial p-group is nontrivial.

    p | |G| and |G| ≡ |Z(G)| (mod p) → p | |Z(G)| → |Z(G)| ≥ p > 1. -/
theorem center_nontrivial_of_pgroup (hG : IsPGroup p G) (hnt : Nontrivial G) :
    Nontrivial (center G) :=
  IsPGroup.center_nontrivial hG

/-- **Groups of Order p² Are Abelian**: if G is a p-group with |G| = p², then G is abelian.

    If |Z(G)| = p²: G = Z(G) is abelian.
    If |Z(G)| = p: G/Z(G) has order p (cyclic) → G is abelian. -/
theorem p_sq_group_comm (hG : IsPGroup p G) (hcard : Fintype.card G = p ^ 2) :
    ∀ (a b : G), a * b = b * a := by
  have hcomm : CommGroup G := IsPGroup.commGroupOfCardEqPrimeSq hG hcard
  exact fun a b => mul_comm a b

end PGroupApplications

-- ============================================================================
-- Part IV: Concrete Computations for A₄
-- ============================================================================

section A4

abbrev A4 := alternatingGroup (Fin 4)

/-- |A₄| = 4!/2 = 12. -/
theorem card_A4 : Fintype.card A4 = 12 := by native_decide

/-- A₄ has exactly 4 conjugacy classes:
    - {e}                              (size 1: center)
    - {(12)(34), (13)(24), (14)(23)}   (size 3: double transpositions)
    - {(123), (134), (243), (142)}     (size 4: 3-cycles clockwise)
    - {(132), (143), (234), (124)}     (size 4: 3-cycles counterclockwise)
    Class equation: 12 = 1 + 3 + 4 + 4. -/
theorem card_conjClasses_A4 : Fintype.card (ConjClasses A4) = 4 := by native_decide

/-- Z(A₄) = {e}: trivial center. Class equation: 12 = 1 + (3+4+4) = 1 + 11. -/
theorem card_center_A4 : Fintype.card (center A4) = 1 := by native_decide

/-- A₄ is not abelian (consistent with trivial center). -/
theorem A4_not_comm : ¬ ∀ (a b : A4), a * b = b * a := by decide

end A4

/-
  ## Results Summary

  | Theorem | Statement | Status |
  |---------|-----------|--------|
  | `class_equation` | \|Z(G)\| + Σ_{noncenter} \|c\| = \|G\| | Proved (Mathlib) |
  | `class_equation_symm` | \|G\| = \|Z(G)\| + Σ_{noncenter} \|c\| | Proved |
  | `conj_orbit_eq_carrier` | orbit (ConjAct G) x = conjugacy class carrier | Proved |
  | `conj_stabilizer_eq_centralizer` | stabilizer of conjugation = centralizer | Proved |
  | `card_conjClass_eq_centralizer_index` | \|[x]\| = [G : C\_G(x)] | 1 sorry (HARD) |
  | `card_conjClass_eq_one_iff_mem_center` | \|[x]\| = 1 ↔ x ∈ Z(G) | Proved |
  | `pgroup_fixed_point` | \|X\| ≡ \|Fix(G,X)\| (mod p) | Proved (Mathlib) |
  | `center_nontrivial_of_pgroup` | Z(nontrivial p-group) ≠ \{1\} | Proved (Mathlib) |
  | `p_sq_group_comm` | \|G\| = p² → G abelian | Proved (Mathlib) |
  | `card_A4` | \|A₄\| = 12 | native\_decide |
  | `card_conjClasses_A4` | A₄ has 4 conjugacy classes | native\_decide |
  | `card_center_A4` | \|Z(A₄)\| = 1 | native\_decide |
  | `A4_not_comm` | A₄ is not abelian | decide |

  **Sorries**: 1 (HARD: orbit-to-index connection for card_conjClass_eq_centralizer_index)
  **Axioms**: 0
-/

end LagrangeTheoremOQ02OQ02
