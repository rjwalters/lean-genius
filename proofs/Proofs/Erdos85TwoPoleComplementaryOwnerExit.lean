import Proofs.Erdos85TwoPoleOwnerRoutingAlternative
import Proofs.Erdos85OwnerComplementSpecialContribution

/-!
# The complementary owner has a concrete ordinary exit

An odd ordinary owner vector determines the unique owner coordinate in which
a special correction is needed: the complement of its charged owner.  The
two-pole occurrence-routing alternative realizes that correction in the
non-through horn, because both owner-indexed poles then have ordinary exits.
-/

namespace Erdos85

noncomputable section

/-- **Complementary owner exit (`73rnz_cjibkzq`).**  For an odd ordinary
owner vector and a fixed-point-free pairing of two pole occurrences, either
the poles form the direct cross-owner through, or the uniquely required
complementary owner has a concrete ordinary exit.  Its owner unit is exactly
the unique correction which produces diagonal demand. -/
theorem twoPole_crossOwner_or_existsUnique_complementaryOrdinaryExit
    {O : Type*} [DecidableEq O]
    (ordinaryMass : Bool → ZMod 2)
    (hodd : (∑ i : Bool, ordinaryMass i) = 1)
    (mate : O → O) (S : Finset O) (pole : Bool → O)
    (hpole : ∀ owner, pole owner ∈ S)
    (hpoles : Function.Injective pole)
    (hclosed : ∀ o ∈ S, mate o ∈ S)
    (hinvol : ∀ o ∈ S, mate (mate o) = o)
    (hfree : ∀ o ∈ S, mate o ≠ o) :
    mate (pole false) = pole true ∨
      ∃! charged : Bool,
        ordinaryMass charged = 1 ∧
        twoPoleOwnerExit mate pole (!charged) ∈
          twoPoleOrdinaryOccurrences S (pole false) (pole true) ∧
        ∀ special : Bool → ZMod 2,
          (∀ j, ordinaryMass j + special j = 1) ↔
            special = boolOwnerUnit (!charged) := by
  rcases twoPoleOwnerExit_crossOwner_or_injective_ordinary
    mate S pole hpole hpoles hclosed hinvol hfree with hthrough | hexits
  · exact Or.inl hthrough
  · right
    obtain ⟨_hinjective, hordinary⟩ := hexits
    obtain ⟨charged, hcharged, hunique⟩ :=
      existsUnique_owner_eq_one_of_sum_eq_one ordinaryMass hodd
    have hvector : ordinaryMass = boolOwnerUnit charged :=
      eq_boolOwnerUnit_of_sum_eq_one_of_apply_eq_one
        ordinaryMass hodd charged hcharged
    refine ⟨charged, ⟨hcharged, hordinary (!charged), ?_⟩, ?_⟩
    · intro special
      rw [hvector]
      exact add_eq_one_iff_eq_complementOwnerUnit charged special
    · intro i hi
      exact hunique i hi.1

end


end Erdos85

#print axioms Erdos85.twoPole_crossOwner_or_existsUnique_complementaryOrdinaryExit
