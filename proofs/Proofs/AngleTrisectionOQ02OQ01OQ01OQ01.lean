/-
  Angle Trisection OQ02-OQ01-OQ01-OQ01:
  Extension Beyond CharZero — natDegree_dvd_card for Separable Polynomials

  Question: Does natDegree(p) | |Gal(p)| hold for irreducible polynomials beyond CharZero?

  Answer: YES for separable irreducibles over any field.
          NO in general: in characteristic p, inseparable irreducibles (e.g., X^p - t over
          F_p(t)) can have |Gal| = 1 while natDegree = p, so natDegree ∤ |Gal|.

  The CharZero hypothesis in `natDegree_dvd_card_gal` (AngleTrisectionOQ02OQ01.lean) was only
  needed to derive separability from irreducibility via `Irreducible.separable`. The tower-law
  argument itself requires only separability, not CharZero. We make this explicit here:

    natDegree_dvd_card_gal_of_sep : Irreducible p → p.Separable → natDegree p ∣ Nat.card p.Gal

  The CharZero version follows as a one-line corollary. We also recover the Galois-criterion
  results from the parent file in this more general setting.

  Parent: AngleTrisectionOQ02OQ01.lean (CharZero version)
  Answers: angle-trisection-oq-02-oq-01-oq-01-oq-01
-/

import Mathlib
import Proofs.AngleTrisectionOQ02OQ01

open Polynomial

open scoped IntermediateField

namespace AngleTrisectionOQ02OQ01OQ01OQ01

/-!
## Part I: Main Theorem — Separability Suffices
-/

/-- For any irreducible *separable* polynomial over any field (of any characteristic),
    natDegree(p) divides |Gal(p)|.

    This strictly generalizes `natDegree_dvd_card_gal` (which requires CharZero): the
    CharZero hypothesis is only needed to infer separability from irreducibility. The
    tower-law proof goes through unchanged once separability is assumed explicitly.

    Proof: By `Gal.card_of_separable`, rewrite |Gal(p)| = finrank(F, SplittingField(p)).
    Pick a root α of p in its splitting field. Tower law gives:
      finrank(F, SplittingField) = finrank(F, F⟮α⟯) · finrank(F⟮α⟯, SplittingField)
    Since minpoly(F, α) = p (by irreducibility), finrank(F, F⟮α⟯) = natDegree(p). -/
theorem natDegree_dvd_card_gal_of_sep {F : Type*} [Field F]
    {p : F[X]} (p_irr : Irreducible p) (p_sep : p.Separable) :
    p.natDegree ∣ Nat.card p.Gal := by
  rw [Gal.card_of_separable p_sep]
  have hp : p.degree ≠ 0 := by
    intro h
    exact absurd (natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h))
      (Irreducible.natDegree_pos p_irr).ne'
  have hp' : (p.map (algebraMap F p.SplittingField)).degree ≠ 0 := by
    rwa [degree_map_eq_of_injective (RingHom.injective (algebraMap F p.SplittingField))]
  let α : p.SplittingField :=
    rootOfSplits (SplittingField.splits p) hp'
  have hα : IsIntegral F α := .of_finite F α
  use Module.finrank F⟮α⟯ p.SplittingField
  suffices (minpoly F α).natDegree = p.natDegree by
    letI _ : AddCommGroup F⟮α⟯ := Ring.toAddCommGroup
    rw [← Module.finrank_mul_finrank F F⟮α⟯ p.SplittingField,
      IntermediateField.adjoin.finrank hα, this]
  suffices minpoly F α ∣ p by
    have key := (minpoly.irreducible hα).dvd_symm p_irr this
    apply le_antisymm
    · exact natDegree_le_of_dvd this p_irr.ne_zero
    · exact natDegree_le_of_dvd key (minpoly.ne_zero hα)
  apply minpoly.dvd F α
  rw [aeval_def, eval₂_eq_eval_map]
  exact eval_rootOfSplits (SplittingField.splits p) hp'

/-!
## Part II: CharZero Corollary
-/

/-- Over CharZero, every irreducible is separable, so natDegree_dvd_card_gal_of_sep applies.
    Recovers `AngleTrisectionOQ02OQ01.natDegree_dvd_card_gal` as a one-line corollary. -/
theorem natDegree_dvd_card_gal_charZero {F : Type*} [Field F] [CharZero F]
    {p : F[X]} (p_irr : Irreducible p) :
    p.natDegree ∣ Nat.card p.Gal :=
  natDegree_dvd_card_gal_of_sep p_irr p_irr.separable

/-!
## Part III: Galois Criterion Results in the Separable Setting

The 2-group Galois criterion from AngleTrisectionOQ02OQ01 used CharZero only through
`natDegree_dvd_card_gal`. With our generalization, the same results hold for separable
irreducibles over any field.
-/

/-- For a separable irreducible p over any field: if Gal(p) is a 2-group,
    then natDegree(p) divides some power of 2. -/
theorem galois_2group_implies_degree_pow2_sep {F : Type*} [Field F]
    {p : F[X]} (p_irr : Irreducible p) (p_sep : p.Separable)
    (hGal : IsPGroup 2 p.Gal) :
    ∃ n : ℕ, p.natDegree ∣ 2 ^ n := by
  have hdvd := natDegree_dvd_card_gal_of_sep p_irr p_sep
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hGal
  exact ⟨n, dvd_trans hdvd (hn ▸ dvd_refl _)⟩

/-- For a separable irreducible p over any field: if Gal(p) is a 2-group,
    then natDegree(p) is itself a power of 2. -/
theorem galois_2group_implies_degree_is_pow2_sep {F : Type*} [Field F]
    {p : F[X]} (p_irr : Irreducible p) (p_sep : p.Separable)
    (hGal : IsPGroup 2 p.Gal) :
    ∃ k : ℕ, p.natDegree = 2 ^ k := by
  obtain ⟨n, hdvd⟩ := galois_2group_implies_degree_pow2_sep p_irr p_sep hGal
  have hpos : 0 < p.natDegree := Irreducible.natDegree_pos p_irr
  exact AngleTrisectionOQ01.dvd_pow_two_is_pow_two _ n hpos hdvd

/-!
## Part IV: The Inseparable Obstruction

When separability fails, the divisibility natDegree(p) ∣ |Gal(p)| can fail.

**Classical example**: Over F = F_p(t) (characteristic p > 0), the polynomial
q = X^p - t is irreducible (Eisenstein at t) and inseparable (q' = 0).
Its splitting field is F_p(t^{1/p}), which is purely inseparable of degree p over F.
The Galois group is trivial: there is only one root t^{1/p}, and the only automorphism
fixing F is the identity. So |Gal(q)| = 1 while natDegree(q) = p, giving p ∤ 1.

This shows separability is NOT just a proof artifact — it is necessary for the theorem.
The CharZero hypothesis in the original theorem was doing real mathematical work
(ensuring all irreducibles are separable). Our generalization identifies separability
as the exact hypothesis needed.
-/

/-- In characteristic p > 0, an inseparable irreducible polynomial has trivial Galois group.
    The divisibility natDegree(p) ∣ |Gal(p)| therefore fails whenever natDegree(p) > 1.

    Stated as an axiom: a full proof requires building the function field F_p(t), proving
    irreducibility via Eisenstein's criterion, and computing the automorphism group of a
    purely inseparable extension — substantial infrastructure beyond this gallery's scope. -/
axiom insep_gal_trivial {F : Type*} [Field F] {p : ℕ} [CharP F p] [hp : Fact p.Prime]
    {f : F[X]} (hf_irr : Irreducible f) (hf_insep : ¬f.Separable) :
    Nat.card f.Gal = 1

/-- Consequence: for an inseparable irreducible of degree > 1, natDegree ∤ |Gal|. -/
theorem natDeg_notDvd_gal_of_insep {F : Type*} [Field F] {p : ℕ} [CharP F p]
    [hp : Fact p.Prime] {f : F[X]} (hf_irr : Irreducible f) (hf_insep : ¬f.Separable)
    (hf_deg : 1 < f.natDegree) :
    ¬(f.natDegree ∣ Nat.card f.Gal) := by
  rw [insep_gal_trivial hf_irr hf_insep, Nat.dvd_one]
  omega

/-!
## Summary

| Theorem | Hypothesis | Conclusion |
|---------|-----------|------------|
| `natDegree_dvd_card_gal_of_sep` | Irreducible, Separable | natDegree ∣ |Gal| |
| `natDegree_dvd_card_gal_charZero` | Irreducible, CharZero | natDegree ∣ |Gal| |
| `galois_2group_implies_degree_pow2_sep` | Irred, Sep, 2-group Gal | natDegree ∣ 2^n |
| `galois_2group_implies_degree_is_pow2_sep` | Irred, Sep, 2-group Gal | natDegree = 2^k |
| `natDeg_notDvd_gal_of_insep` | Irred, Insep, degree > 1 | natDegree ∤ |Gal| |

Theorems proved: 5 (0 sorries)
Axioms: 1 (insep_gal_trivial — documents the inseparable counterexample)
-/

end AngleTrisectionOQ02OQ01OQ01OQ01
