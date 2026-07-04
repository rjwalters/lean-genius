import Mathlib

/-
# Extension-closure of solvable groups, packaged (abel-ruffini-oq-06-oq-01-oq-03)

The parent entry `Proofs.AbelRuffiniOQ06OQ01` proves `A₄` solvable by an inline
short-exact-sequence argument: it exhibits the Klein-four subgroup `V₄ ⊴ A₄`, checks
`IsSolvable V₄` and `IsSolvable (A₄ ⧸ V₄)`, and then feeds the two into Mathlib's general
`solvable_of_ker_le_range` on the maps `V₄.subtype` and `QuotientGroup.mk' V₄`, discharging
the side condition `ker (mk' V₄) ≤ range (V₄.subtype)` by hand. Its third open question asks
to abstract this recurring boilerplate into a single reusable lemma — the standard
**extension-closure of solvable groups**:

    given `N ⊴ G` with `N` solvable and `G ⧸ N` solvable, `G` itself is solvable.

Mathlib supplies the *general* extension lemma `solvable_of_ker_le_range` (phrased for an
arbitrary pair of homomorphisms with `ker g ≤ range f`) and the two one-sided corollaries
`solvable_of_solvable_injective` (subgroups) and `solvable_of_surjective` (quotients), but it
does **not** package the symmetric normal-subgroup/quotient form. This entry provides it.

  * `isSolvable_of_normal_of_quotient` — the packaged lemma, instance-driven: from
    `[N.Normal]`, `[IsSolvable N]`, `[IsSolvable (G ⧸ N)]` conclude `IsSolvable G`. It is the
    `solvable_of_ker_le_range` specialization to `f = N.subtype`, `g = QuotientGroup.mk' N`,
    where `ker (mk' N) = N = range N.subtype` makes the side condition an equality.
  * `isSolvable_of_normal_of_isSolvable_quotient` — the same statement with the two
    solvability facts as explicit hypotheses rather than instances (convenient when they are
    produced as terms, e.g. by `isSolvable_of_comm`).
  * `isSolvable_of_isSolvable_commutator` — a corollary capturing the *metabelian* pattern in
    one step: a group is solvable as soon as its commutator subgroup is. Here the quotient
    factor is automatic — `G ⧸ commutator G` is abelian by definition of the commutator
    (`quotient_commutative_iff_commutator_le` with `commutator G ≤ commutator G`).
  * `alternatingFinFour_isSolvable` — the prototypical instance, re-deriving the parent's
    `A₄` result through the packaged lemma. The `solvable_of_ker_le_range` invocation and its
    hand-rolled `ker ≤ range` side goal disappear into a single `exact`.

Status: 0 sorries, 0 axioms, no `native_decide`. `#print axioms` on the four declarations
reports only `propext, Classical.choice, Quot.sound`.
-/

namespace AbelRuffiniOQ06OQ01OQ03

open Equiv

/-- **Extension-closure of solvable groups (packaged).** If `N` is a normal subgroup of `G`
with both `N` and the quotient `G ⧸ N` solvable, then `G` is solvable. This is the standard
"solvable-by-solvable is solvable" closure property; it specializes Mathlib's general
`solvable_of_ker_le_range` to the inclusion `N.subtype` and the projection `mk' N`, whose
range and kernel both equal `N`, turning the `ker ≤ range` side condition into `N ≤ N`. -/
theorem isSolvable_of_normal_of_quotient {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    [IsSolvable N] [IsSolvable (G ⧸ N)] : IsSolvable G :=
  solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
    (le_of_eq (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype]))

/-- **Extension-closure, hypothesis form.** The same statement as
`isSolvable_of_normal_of_quotient` but taking the solvability of `N` and of `G ⧸ N` as
explicit term arguments. Useful when those facts are obtained constructively (for instance
from `isSolvable_of_comm` on an abelian kernel and quotient) rather than resolved by instance
search. -/
theorem isSolvable_of_normal_of_isSolvable_quotient {G : Type*} [Group G] (N : Subgroup G)
    [N.Normal] (hN : IsSolvable N) (hQ : IsSolvable (G ⧸ N)) : IsSolvable G :=
  haveI := hN
  haveI := hQ
  isSolvable_of_normal_of_quotient N

/-- **Metabelian criterion.** A group is solvable whenever its commutator subgroup is. This
is the one-step form of extension-closure: the quotient factor `G ⧸ commutator G` is abelian
for free — by the very definition of the commutator subgroup
(`quotient_commutative_iff_commutator_le` applied to `commutator G ≤ commutator G`) — so only
the solvability of the derived subgroup must be supplied. Iterating this reproves that a group
with a terminating derived series is solvable. -/
theorem isSolvable_of_isSolvable_commutator {G : Type*} [Group G]
    (h : IsSolvable (commutator G)) : IsSolvable G := by
  haveI := h
  haveI : IsSolvable (G ⧸ commutator G) :=
    isSolvable_of_comm fun a b =>
      (Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl).comm a b
  exact isSolvable_of_normal_of_quotient (commutator G)

/-- **`A₄ = alternatingGroup (Fin 4)` is solvable, via the packaged lemma.** The prototypical
instance of extension-closure and the source of this generalization. `V₄ = kleinFour (Fin 4)`
is normal in `A₄`, is solvable because it has exponent two hence is abelian, and gives an
abelian (hence solvable) quotient `A₄ ⧸ V₄ ≅ ℤ/3` because it is exactly the commutator
subgroup. The parent entry closed this with a bare `solvable_of_ker_le_range` plus a
hand-written `ker ≤ range` side goal; here those collapse into one application of
`isSolvable_of_normal_of_quotient`. -/
theorem alternatingFinFour_isSolvable : IsSolvable (alternatingGroup (Fin 4)) := by
  have hα4 : Nat.card (Fin 4) = 4 := Nat.card_eq_fintype_card.trans (Fintype.card_fin 4)
  set N := alternatingGroup.kleinFour (Fin 4) with hN
  haveI hNnormal : N.Normal := alternatingGroup.normal_kleinFour hα4
  -- V₄ has exponent two, hence is abelian, hence solvable.
  have hexp : Monoid.exponent N = 2 := by
    rw [hN]; exact alternatingGroup.exponent_kleinFour_of_card_eq_four hα4
  haveI hNsolv : IsSolvable N :=
    isSolvable_of_comm (fun a b => mul_comm_of_exponent_two hexp a b)
  -- A₄ / V₄ is abelian because V₄ is the commutator subgroup of A₄.
  have hcomm_le : commutator (alternatingGroup (Fin 4)) ≤ N :=
    le_of_eq (alternatingGroup.kleinFour_eq_commutator hα4).symm
  haveI hQsolv : IsSolvable (alternatingGroup (Fin 4) ⧸ N) :=
    isSolvable_of_comm fun a b =>
      (Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm_le).comm a b
  -- Extension-closure on 1 → V₄ → A₄ → A₄/V₄ → 1, packaged in one step.
  exact isSolvable_of_normal_of_quotient N

end AbelRuffiniOQ06OQ01OQ03
