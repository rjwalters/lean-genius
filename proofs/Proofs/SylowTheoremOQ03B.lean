import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.Constructions
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
import Proofs.SylowTheoremOQ02
import Proofs.SylowTheoremOQ03

/-
# OQ-03 Candidate B: Discharge of `sylowProP_inter_trivial`

This file is `sylow-theorems-oq-03` Candidate B (S6 ACT): a discharge of
the OQ-02 axiom `ProfiniteSylow.sylowProP_inter_trivial` (declared at
`SylowTheoremOQ02.lean:133`).

## Mathematical content

The OQ-02 axiom states: for a profinite group `G` and distinct primes
`p ≠ q`, the intersection of a Sylow pro-p subgroup `P` and a Sylow
pro-q subgroup `Q` is trivial.

This file proves it via finite-quotient reduction:

1. By contradiction, take `x ∈ P ⊓ Q` with `x ≠ 1`.
2. Since `G` is T2 + TDS + Compact + TopologicalGroup, there is a
   clopen neighborhood of `1` not containing `x` (via the fact that
   `{x}` is closed in a T2 space).
3. By `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one`,
   there is an open normal subgroup `N ⊂ {x}ᶜ`, so `x ∉ N`.
4. The quotient `G ⧸ N` is finite + discrete.
5. By the continuity-enhanced `sylowProP_projects_pgroup_continuous`
   (already proved in `SylowTheoremOQ03.lean`), the image of `P` in
   `G ⧸ N` is a p-group, and the image of `Q` is a q-group.
6. `x.mk` (the class of `x` in `G ⧸ N`) lies in both images, so its
   order divides both `p^a` and `q^b` for some `a, b`.
7. For distinct primes, `gcd(p^a, q^b) = 1`, so the order is 1, hence
   `x.mk = 1`, hence `x ∈ N`. Contradiction.

## Effect on `SylowTheoremOQ02.lean`

If this file builds successfully, the axiom `sylowProP_inter_trivial`
at `SylowTheoremOQ02.lean:133` becomes derivable and can be removed in
a follow-on PR. Net OQ-02 axiom count: 4 → 3.

## References

- `Mathlib/Topology/Algebra/ClopenNhdofOne.lean:44` —
  `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one`
- `Mathlib/Topology/Algebra/OpenSubgroup.lean:298` —
  `(U : OpenSubgroup G) : Finite (G ⧸ U.toSubgroup)` instance
- `Mathlib/GroupTheory/PGroup.lean:26` — `IsPGroup` definition
- `Mathlib/GroupTheory/OrderOfElement.lean:248` — `orderOf_eq_one_iff`
- `Mathlib/Data/Nat/Prime/Basic.lean:201` — `Nat.coprime_pow_primes`
- `Mathlib/Topology/Separation/Basic.lean:341` — `isClosed_singleton`
-/

namespace ProfiniteSylow

set_option linter.unusedVariables false

section SylowInterTrivial

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- **Discharge of axiom `sylowProP_inter_trivial`** (OQ-02 line 133):
    Sylow pro-p subgroups for distinct primes have trivial intersection.

    Proof goes via finite quotients: project to `G ⧸ N` for an open
    normal `N` not containing `x`, use Candidate A* to argue that the
    projected images are p- and q-groups, conclude that the projected
    element has order dividing both `p^a` and `q^b` (hence 1), so the
    original element lies in `N` — contradiction. -/
theorem sylowProP_inter_trivial_via_quotient
    (hpf : IsProfiniteGroup G) (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (P : SylowProP G p) (Q : SylowProP G q) :
    P.toSubgroup ⊓ Q.toSubgroup = ⊥ := by
  -- Typeclass bridges from `hpf : IsProfiniteGroup G`.
  haveI : CompactSpace G := hpf.isCompact
  haveI : T2Space G := hpf.isT2
  haveI : TotallyDisconnectedSpace G := hpf.isTotallyDisc
  haveI : ContinuousMul G := ⟨hpf.continuous_mul⟩
  haveI : ContinuousInv G := ⟨hpf.continuous_inv⟩
  haveI : IsTopologicalGroup G := {}
  -- Reduce `⊓ = ⊥` to "every element of the intersection is 1".
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨hxP, hxQ⟩ := hx
  by_contra hne
  -- `{x}` is closed (T2), so `{x}ᶜ` is open and contains `1`.
  have hcompl_open : IsOpen (({x}ᶜ) : Set G) := isClosed_singleton.isOpen_compl
  have hone_in : (1 : G) ∈ (({x}ᶜ) : Set G) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h; exact hne h.symm
  -- Get an open normal `N` contained in `{x}ᶜ`, so `x ∉ N`.
  obtain ⟨N, hN_sub⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hcompl_open hone_in
  have hx_not_in_N : x ∉ N.toOpenSubgroup.toSubgroup := by
    intro hmem
    have : x ∈ (({x}ᶜ) : Set G) := hN_sub hmem
    simp at this
  -- The quotient is finite and discrete.
  haveI hfin : Finite (G ⧸ N.toOpenSubgroup.toSubgroup) := inferInstance
  haveI : Fintype (G ⧸ N.toOpenSubgroup.toSubgroup) := Fintype.ofFinite _
  haveI : DiscreteTopology (G ⧸ N.toOpenSubgroup.toSubgroup) :=
    QuotientGroup.discreteTopology N.toOpenSubgroup.isOpen
  -- The quotient map and its continuity.
  let φ : G →* G ⧸ N.toOpenSubgroup.toSubgroup := QuotientGroup.mk' _
  have hφ_cont : Continuous φ := continuous_quotient_mk'
  -- Apply Candidate A* (already proved in SylowTheoremOQ03.lean) to get
  -- that the images of P and Q in `G ⧸ N` are p- and q-groups.
  have hP_img : IsPGroup p (P.toSubgroup.map φ) :=
    sylowProP_projects_pgroup_continuous P φ hφ_cont
  have hQ_img : IsPGroup q (Q.toSubgroup.map φ) :=
    sylowProP_projects_pgroup_continuous Q φ hφ_cont
  -- `φ x` is in both images.
  have hxP_img : φ x ∈ P.toSubgroup.map φ :=
    Subgroup.mem_map.mpr ⟨x, hxP, rfl⟩
  have hxQ_img : φ x ∈ Q.toSubgroup.map φ :=
    Subgroup.mem_map.mpr ⟨x, hxQ, rfl⟩
  -- Get `(φ x)^(p^a) = 1` and `(φ x)^(q^b) = 1` in the quotient.
  obtain ⟨a, ha⟩ := hP_img ⟨φ x, hxP_img⟩
  obtain ⟨b, hb⟩ := hQ_img ⟨φ x, hxQ_img⟩
  -- Move from subgroup-typed equation to the ambient quotient equation.
  have ha' : (φ x) ^ (p ^ a) = 1 := by
    have h := congrArg (Subtype.val) ha
    simpa using h
  have hb' : (φ x) ^ (q ^ b) = 1 := by
    have h := congrArg (Subtype.val) hb
    simpa using h
  -- Use coprime-pow argument: `orderOf (φ x)` divides both `p^a` and `q^b`.
  have hdvd_p : orderOf (φ x) ∣ p ^ a := orderOf_dvd_of_pow_eq_one ha'
  have hdvd_q : orderOf (φ x) ∣ q ^ b := orderOf_dvd_of_pow_eq_one hb'
  have hcoprime : Nat.Coprime (p ^ a) (q ^ b) :=
    Nat.coprime_pow_primes a b hp.out hq.out hpq
  have hdvd_gcd : orderOf (φ x) ∣ Nat.gcd (p ^ a) (q ^ b) :=
    Nat.dvd_gcd hdvd_p hdvd_q
  rw [hcoprime.gcd_eq_one] at hdvd_gcd
  have hord_one : orderOf (φ x) = 1 := Nat.dvd_one.mp hdvd_gcd
  have hφx_eq : φ x = 1 := orderOf_eq_one_iff.mp hord_one
  -- `φ x = 1` means `x ∈ N`, contradicting `x ∉ N`.
  have hx_in_N : x ∈ N.toOpenSubgroup.toSubgroup := by
    have : (QuotientGroup.mk x : G ⧸ N.toOpenSubgroup.toSubgroup) = 1 := hφx_eq
    exact (QuotientGroup.eq_one_iff x).mp this
  exact hx_not_in_N hx_in_N

end SylowInterTrivial

end ProfiniteSylow

#check @ProfiniteSylow.sylowProP_inter_trivial_via_quotient
