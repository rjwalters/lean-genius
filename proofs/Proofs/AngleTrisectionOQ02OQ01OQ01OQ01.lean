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
## Part IV: The Inseparable Obstruction (axiom-free)

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

**Integrity history**: an earlier revision encoded the obstruction via an axiom
`insep_gal_trivial` asserting "inseparable irreducible ⇒ |Gal| = 1". That axiom is
**mathematically false** (refuted in the OQ-01 descendant by `X⁴ + X² + a` over `F₂(a)`,
which has |Gal| = 2). It has now been **deleted** and replaced by the honest,
axiom-free `gal_card_one_of_purelyInseparable_splitting` (purely-inseparable *splitting
field* hypothesis) and its consequence
`natDeg_notDvd_gal_of_purelyInseparable_splitting`. The classical `X^p - t` example
satisfies the purely-inseparable-splitting-field hypothesis, so the obstruction it
illustrates is fully covered by the axiom-free theorem.
-/

/-- In characteristic `p`, `(a - b) ^ (p ^ n) = a ^ (p ^ n) - b ^ (p ^ n)` — the iterated
    Frobenius `x ↦ x ^ (p ^ n)` is a ring hom, so it commutes with subtraction. Ported from
    the OQ-01 descendant (which imports this file and so cannot be imported here). -/
lemma sub_pow_char_pow_eq {K : Type*} [CommRing K] {p : ℕ} [CharP K p] [hp : Fact p.Prime]
    (a b : K) (n : ℕ) : (a - b) ^ p ^ n = a ^ p ^ n - b ^ p ^ n := by
  simpa [iterateFrobenius_def] using map_sub (iterateFrobenius K p n) a b

/-- A purely inseparable F-algebra automorphism of a field `K` is the identity.

    Each `x ∈ K` satisfies `x ^ p ^ n = algebraMap F K c` for some `c : F` and `n`
    (purely-inseparable lift); `σ` fixes that element, so `(σ x - x) ^ p ^ n = 0` by the
    char-`p` freshman's dream, and `K` being a field forces `σ x = x`.

    Ported from the OQ-01 descendant (`AngleTrisectionOQ02OQ01OQ01OQ01OQ01.lean`), which
    cannot be imported here (it imports this file). -/
theorem algEquiv_eq_refl_of_isPurelyInseparable {F K : Type*} [Field F] [Field K]
    [Algebra F K] {p : ℕ} [CharP K p] [hp : Fact p.Prime]
    [IsPurelyInseparable F K] (σ : K ≃ₐ[F] K) :
    σ = (AlgEquiv.refl : K ≃ₐ[F] K) := by
  ext x
  show σ x = x
  haveI hF_p : CharP F p := (Algebra.charP_iff F K p).mpr inferInstance
  obtain ⟨n, c, hc⟩ : ∃ n : ℕ, ∃ c : F, algebraMap F K c = x ^ p ^ n := by
    obtain ⟨n, hn⟩ := IsPurelyInseparable.pow_mem F p x
    obtain ⟨c, hc⟩ := hn
    exact ⟨n, c, hc⟩
  have hfixed : σ (x ^ p ^ n) = x ^ p ^ n := by
    rw [← hc]; exact σ.commutes c
  have hpow : σ x ^ p ^ n = x ^ p ^ n := by rw [← map_pow σ x, hfixed]
  have hzero : (σ x - x) ^ p ^ n = 0 := by
    rw [sub_pow_char_pow_eq (σ x) x n, hpow, sub_self]
  have hne : p ^ n ≠ 0 := pow_ne_zero _ (Nat.Prime.pos hp.out).ne'
  exact sub_eq_zero.mp (pow_eq_zero_iff hne |>.mp hzero)

/-- **Correct replacement for the (now-deleted) false axiom `insep_gal_trivial`.**

    If `f.SplittingField` is purely inseparable over `F`, then `|Gal(f)| = 1`. The honest
    hypothesis is a *purely-inseparable splitting field*, NOT mere inseparability of `f`:
    the naive "inseparable irreducible ⇒ |Gal| = 1" claim is false (e.g. `X⁴ + X² + a`
    over `F₂(a)` is irreducible and inseparable yet has `|Gal| = 2` via the Artin–Schreier
    automorphism `α^{1/2} ↦ α^{1/2} + 1`; see `insep_gal_trivial_refuted` in the OQ-01
    descendant). Proved here without axioms by porting the descendant's argument. -/
theorem gal_card_one_of_purelyInseparable_splitting {F : Type*} [Field F]
    {p : ℕ} [CharP F p] [hp : Fact p.Prime]
    (f : F[X]) [hK : IsPurelyInseparable F f.SplittingField] :
    Nat.card f.Gal = 1 := by
  haveI : CharP f.SplittingField p :=
    (Algebra.charP_iff F f.SplittingField p).mp inferInstance
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun σ τ => (algEquiv_eq_refl_of_isPurelyInseparable σ).trans
                      (algEquiv_eq_refl_of_isPurelyInseparable τ).symm⟩,
          ⟨(AlgEquiv.refl : f.SplittingField ≃ₐ[F] f.SplittingField)⟩⟩

/-- Honest consequence (replacing the false-axiom-backed `natDeg_notDvd_gal_of_insep`):
    for `f` of degree > 1 with purely-inseparable splitting field, `natDegree ∤ |Gal|`
    since `|Gal| = 1`. -/
theorem natDeg_notDvd_gal_of_purelyInseparable_splitting {F : Type*} [Field F] {p : ℕ}
    [CharP F p] [hp : Fact p.Prime] (f : F[X])
    [IsPurelyInseparable F f.SplittingField] (hf_deg : 1 < f.natDegree) :
    ¬(f.natDegree ∣ Nat.card f.Gal) := by
  rw [gal_card_one_of_purelyInseparable_splitting f]
  intro h
  have : f.natDegree ≤ 1 := Nat.le_of_dvd Nat.one_pos h
  omega

/-!
## Summary

| Theorem | Hypothesis | Conclusion |
|---------|-----------|------------|
| `natDegree_dvd_card_gal_of_sep` | Irreducible, Separable | natDegree ∣ |Gal| |
| `natDegree_dvd_card_gal_charZero` | Irreducible, CharZero | natDegree ∣ |Gal| |
| `galois_2group_implies_degree_pow2_sep` | Irred, Sep, 2-group Gal | natDegree ∣ 2^n |
| `galois_2group_implies_degree_is_pow2_sep` | Irred, Sep, 2-group Gal | natDegree = 2^k |
| `sub_pow_char_pow_eq` | char `p` | `(a-b)^(p^n) = a^(p^n) - b^(p^n)` |
| `algEquiv_eq_refl_of_isPurelyInseparable` | purely insep `F ≤ K` | every `σ : K ≃ₐ[F] K` is `refl` |
| `gal_card_one_of_purelyInseparable_splitting` | purely insep splitting field | |Gal| = 1 |
| `natDeg_notDvd_gal_of_purelyInseparable_splitting` | purely insep splitting, degree > 1 | natDegree ∤ |Gal| |

Theorems/lemmas proved: 8 (0 sorries)
Axioms: 0

## Integrity Note (S3 ACT 2026-06-12 — false axiom removed)

The axiom `insep_gal_trivial` ("inseparable irreducible ⇒ |Gal| = 1") was
**mathematically false** (the OQ-01 descendant `AngleTrisectionOQ02OQ01OQ01OQ01OQ01.lean`
refuted it: `X⁴+X²+a` over `F₂(a)` has |Gal|=2). It had been retained as a placeholder.

This iteration **deletes the false axiom** and its false-axiom-backed consequence
`natDeg_notDvd_gal_of_insep`, porting the descendant's axiom-free
`algEquiv_eq_refl_of_isPurelyInseparable` and `gal_card_one_of_purelyInseparable_splitting`
into this file (the descendant cannot be imported — it imports this file) and restating
the obstruction honestly as `natDeg_notDvd_gal_of_purelyInseparable_splitting`. The file
is now **axiom-free** (axiomCount 1 → 0, 0 sorries).
-/

end AngleTrisectionOQ02OQ01OQ01OQ01
