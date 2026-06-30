/-
  Explicit quintic with Galois group S₅ — `X⁵ − 4X + 2` over ℚ
  (Open Question OQ-01 of abel-ruffini-galois-extensions:
   "construct a specific degree-5 polynomial and prove Gal ≅ S₅")

  ## What this file establishes (0 sorry, 0 axiom)

  The parent proof `AbelRuffiniGaloisExtensions.lean` develops the *abstract*
  Abel–Ruffini theory (Sₙ solvable ⟺ n ≤ 4; A₅ simple; non-solvable Galois group ⟹
  not solvable by radicals). The sibling `AbelRuffiniOQ07NotSolvable.lean` formalizes
  the *conclusion* for `X⁵ − X − 1`, but only **conditionally** on an unproved
  isomorphism `f.Gal ≃* S₅`: that witness has **four** non-real roots, so complex
  conjugation is a double-transposition, and pinning its Galois group to all of S₅ needs
  the Dedekind–Frobenius machinery Mathlib v4.26 lacks.

  This file removes that gap by switching to the classical witness `Φ = X⁵ − 4X + 2`,
  which has **exactly three real roots** (hence two non-real, complex-conjugate roots).
  For such an irreducible prime-degree polynomial, complex conjugation is a genuine
  transposition, and Mathlib's `galActionHom_bijective_of_prime_degree'` makes the
  action of `Gal` on the five complex roots the *full* symmetric group. We package that
  bijection into an explicit group isomorphism and read off the consequences:

    * `galEquivS5` — the headline isomorphism `(X⁵ − 4X + 2).Gal ≃* Equiv.Perm (Fin 5)`,
      i.e. the Galois group **is** S₅ (constructed, not assumed).
    * `gal_card` — consequently `|Gal| = 120`.
    * `gal_not_solvable` — `Gal` is not solvable (S₅ is not, transported across the iso).
    * `root_not_solvableByRad` — **unconditionally**, no complex root of `X⁵ − 4X + 2`
      is solvable by radicals (Mathlib's `solvableByRad.isSolvable'` applied to the
      Eisenstein-irreducible Φ).
    * `exists_root_not_solvableByRad` — a concrete algebraic number not solvable by
      radicals.

  Unlike the OQ-07 entry, **nothing here is conditional on an open isomorphism**: the
  `Gal ≃* S₅` iso is produced.

  ## Provenance

  The polynomial `Φ`, its irreducibility (Eisenstein at 2), the real-root count
  (`≤ 3` via Rolle/derivative bounds, `≥ 2` via the intermediate value theorem) and the
  resulting `Bijective (galActionHom Φ ℂ)` reproduce T. Browning's development in
  Mathlib's `Archive/Wiedijk100Theorems/AbelRuffini.lean` (the `Archive` library is not
  importable from a downstream Mathlib client, so the relevant lemmas are reproduced
  here). The **new** content is the explicit packaging of `Bijective (galActionHom …)`
  into the group isomorphism `Gal ≃* Equiv.Perm (Fin 5)` and the resulting unconditional
  S₅ / unsolvability statements, which connect the parent abstract theory to a concrete
  witness.

  ## References
  - Browning, T. `Archive/Wiedijk100Theorems/AbelRuffini.lean`, Mathlib.
  - Mathlib, `Mathlib/Analysis/Complex/Polynomial/Basic.lean`
    (`Polynomial.Gal.galActionHom_bijective_of_prime_degree'`).
  - Mathlib, `Mathlib/FieldTheory/AbelRuffini.lean` (`solvableByRad.isSolvable'`).
-/

import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.AbelRuffini
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.GroupTheory.Solvable

namespace AbelRuffiniGaloisExtensionsOQ01

open Function Polynomial Polynomial.Gal Ideal

open scoped Polynomial

attribute [local instance] splits_ℚ_ℂ

/-! ## Part I — the witness `Φ = X⁵ − a·X + b` and its key properties

These lemmas reproduce T. Browning's development in
`Archive/Wiedijk100Theorems/AbelRuffini.lean` (the `Archive` library is not on the import
path of a downstream Mathlib client, so they are reproduced verbatim here). -/

variable (R : Type*) [CommRing R] (a b : ℕ)

/-- A quintic polynomial `X⁵ − a·X + b` that we will specialize to `a = 4, b = 2`. -/
noncomputable def Φ : R[X] :=
  X ^ 5 - C (a : R) * X + C (b : R)

variable {R}

@[simp]
theorem map_Phi {S : Type*} [CommRing S] (f : R →+* S) : (Φ R a b).map f = Φ S a b := by simp [Φ]

@[simp]
theorem coeff_zero_Phi : (Φ R a b).coeff 0 = (b : R) := by simp [Φ, coeff_X_pow]

@[simp]
theorem coeff_five_Phi : (Φ R a b).coeff 5 = 1 := by
  simp [Φ, -map_natCast]

variable [Nontrivial R]

theorem degree_Phi : (Φ R a b).degree = ((5 : ℕ) : WithBot ℕ) := by
  suffices degree (X ^ 5 - C (a : R) * X) = ((5 : ℕ) : WithBot ℕ) by
    rwa [Φ, degree_add_eq_left_of_degree_lt]
    convert (degree_C_le (R := R)).trans_lt (WithBot.coe_lt_coe.mpr (show 0 < 5 by simp))
  rw [degree_sub_eq_left_of_degree_lt] <;> rw [degree_X_pow]
  exact (degree_C_mul_X_le (a : R)).trans_lt (WithBot.coe_lt_coe.mpr (show 1 < 5 by simp))

theorem natDegree_Phi : (Φ R a b).natDegree = 5 :=
  natDegree_eq_of_degree_eq_some (degree_Phi a b)

theorem leadingCoeff_Phi : (Φ R a b).leadingCoeff = 1 := by
  rw [Polynomial.leadingCoeff, natDegree_Phi, coeff_five_Phi]

theorem monic_Phi : (Φ R a b).Monic :=
  leadingCoeff_Phi a b

theorem irreducible_Phi (p : ℕ) (hp : p.Prime) (hpa : p ∣ a) (hpb : p ∣ b) (hp2b : ¬p ^ 2 ∣ b) :
    Irreducible (Φ ℚ a b) := by
  rw [← map_Phi a b (Int.castRingHom ℚ), ← IsPrimitive.Int.irreducible_iff_irreducible_map_cast]
  on_goal 1 =>
    apply irreducible_of_eisenstein_criterion
    · rwa [span_singleton_prime (Int.natCast_ne_zero.mpr hp.ne_zero), Int.prime_iff_natAbs_prime]
    · rw [leadingCoeff_Phi, mem_span_singleton]
      exact mod_cast mt Nat.dvd_one.mp hp.ne_one
    · intro n hn
      rw [mem_span_singleton]
      rw [degree_Phi] at hn; norm_cast at hn
      interval_cases n <;>
      simp +decide only [Φ, coeff_X_pow, coeff_C, Int.natCast_dvd_natCast.mpr,
        hpb, if_true, coeff_C_mul, if_false, coeff_X_zero, hpa, coeff_add, zero_add, mul_zero,
        coeff_sub, add_zero, zero_sub, dvd_neg, neg_zero, dvd_mul_of_dvd_left]
    · simp only [degree_Phi, ← WithBot.coe_zero]
      decide
    · rw [coeff_zero_Phi, span_singleton_pow, mem_span_singleton]
      exact mt Int.natCast_dvd_natCast.mp hp2b
  all_goals exact Monic.isPrimitive (monic_Phi a b)

attribute [local simp] map_ofNat in -- use `ofNat` simp theorem with bad keys
theorem real_roots_Phi_le : Fintype.card ((Φ ℚ a b).rootSet ℝ) ≤ 3 := by
  rw [← map_Phi a b (algebraMap ℤ ℚ), Φ, ← one_mul (X ^ 5), ← C_1]
  apply (card_rootSet_le_derivative _).trans
    (Nat.succ_le_succ ((card_rootSet_le_derivative _).trans (Nat.succ_le_succ _)))
  suffices (Polynomial.rootSet (C (20 : ℚ) * X ^ 3) ℝ).Subsingleton by
    norm_num [Fintype.card_le_one_iff_subsingleton, ← mul_assoc] at *
    exact this
  rw [rootSet_C_mul_X_pow] <;>
  norm_num

theorem real_roots_Phi_ge_aux (hab : b < a) :
    ∃ x y : ℝ, x ≠ y ∧ aeval x (Φ ℚ a b) = 0 ∧ aeval y (Φ ℚ a b) = 0 := by
  let f : ℝ → ℝ := fun x : ℝ => aeval x (Φ ℚ a b)
  have hf : f = fun x : ℝ => x ^ 5 - a * x + b := by simp [f, Φ]
  have hc : ∀ s : Set ℝ, ContinuousOn f s := fun s => (Φ ℚ a b).continuousOn_aeval
  have ha : (1 : ℝ) ≤ a := Nat.one_le_cast.mpr (Nat.one_le_of_lt hab)
  have hle : (0 : ℝ) ≤ 1 := zero_le_one
  have hf0 : 0 ≤ f 0 := by simp [hf]
  by_cases hb : (1 : ℝ) - a + b < 0
  · have hf1 : f 1 < 0 := by simp [hf, hb]
    have hfa : 0 ≤ f a := by
      simp_rw [hf, ← sq]
      refine add_nonneg (sub_nonneg.mpr (pow_right_mono₀ ha ?_)) ?_ <;> norm_num
    obtain ⟨x, ⟨-, hx1⟩, hx2⟩ := intermediate_value_Ico' hle (hc _) (Set.mem_Ioc.mpr ⟨hf1, hf0⟩)
    obtain ⟨y, ⟨hy1, -⟩, hy2⟩ := intermediate_value_Ioc ha (hc _) (Set.mem_Ioc.mpr ⟨hf1, hfa⟩)
    exact ⟨x, y, (hx1.trans hy1).ne, hx2, hy2⟩
  · replace hb : (b : ℝ) = a - 1 := by linarith [show (b : ℝ) + 1 ≤ a from mod_cast hab]
    have hf1 : f 1 = 0 := by simp [hf, hb]
    have hfa :=
      calc
        f (-a) = (a : ℝ) ^ 2 - (a : ℝ) ^ 5 + b := by
          norm_num [hf, ← sq, sub_eq_add_neg, add_comm, Odd.neg_pow (by decide : Odd 5)]
        _ ≤ (a : ℝ) ^ 2 - (a : ℝ) ^ 3 + (a - 1) := by gcongr <;> linarith
        _ = -((a : ℝ) - 1) ^ 2 * (a + 1) := by ring
        _ ≤ 0 := by nlinarith
    have ha' := neg_nonpos.mpr (hle.trans ha)
    obtain ⟨x, ⟨-, hx1⟩, hx2⟩ := intermediate_value_Icc ha' (hc _) (Set.mem_Icc.mpr ⟨hfa, hf0⟩)
    exact ⟨x, 1, (hx1.trans_lt zero_lt_one).ne, hx2, hf1⟩

theorem real_roots_Phi_ge (hab : b < a) : 2 ≤ Fintype.card ((Φ ℚ a b).rootSet ℝ) := by
  have q_ne_zero : Φ ℚ a b ≠ 0 := (monic_Phi a b).ne_zero
  obtain ⟨x, y, hxy, hx, hy⟩ := real_roots_Phi_ge_aux a b hab
  have key : ↑({x, y} : Finset ℝ) ⊆ (Φ ℚ a b).rootSet ℝ := by
    simp [Set.insert_subset, mem_rootSet_of_ne q_ne_zero, hx, hy]
  convert Fintype.card_le_of_embedding (Set.embeddingOfSubset _ _ key)
  simp only [Finset.coe_sort_coe, Fintype.card_coe, Finset.card_singleton,
    Finset.card_insert_of_notMem (mt Finset.mem_singleton.mp hxy)]

theorem complex_roots_Phi (h : (Φ ℚ a b).Separable) : Fintype.card ((Φ ℚ a b).rootSet ℂ) = 5 :=
  (card_rootSet_eq_natDegree h (IsAlgClosed.splits _)).trans (natDegree_Phi a b)

theorem gal_Phi (hab : b < a) (h_irred : Irreducible (Φ ℚ a b)) :
    Bijective (galActionHom (Φ ℚ a b) ℂ) := by
  apply galActionHom_bijective_of_prime_degree' h_irred
  · simp only [natDegree_Phi]; decide
  · rw [complex_roots_Phi a b h_irred.separable, Nat.succ_le_succ_iff]
    exact (real_roots_Phi_le a b).trans (Nat.le_succ 3)
  · simp_rw [complex_roots_Phi a b h_irred.separable, Nat.succ_le_succ_iff]
    exact real_roots_Phi_ge a b hab

/-! ## Part II — the explicit witness `X⁵ − 4X + 2` and its Galois group `S₅`

This is the new content of OQ-01: packaging `Bijective (galActionHom Φ ℂ)` into a group
isomorphism `Gal ≃* Equiv.Perm (Fin 5)` and deducing the unconditional conclusions. -/

/-- The classical Abel–Ruffini witness `q = X⁵ − 4X + 2 ∈ ℚ[X]`. -/
noncomputable def q : ℚ[X] := Φ ℚ 4 2

theorem q_eq : q = X ^ 5 - C (4 : ℚ) * X + C (2 : ℚ) := rfl

/-- `X⁵ − 4X + 2` is irreducible over `ℚ` (Eisenstein at `p = 2`). -/
theorem q_irreducible : Irreducible q :=
  irreducible_Phi 4 2 2 Nat.prime_two (by norm_num) (by norm_num) (by decide)

/-- `X⁵ − 4X + 2` is separable (it is irreducible over a field of characteristic zero). -/
theorem q_separable : q.Separable := q_irreducible.separable

/-- The splitting field of `X⁵ − 4X + 2` contains exactly `5` complex roots. -/
theorem q_card_complex_roots : Fintype.card (q.rootSet ℂ) = 5 :=
  complex_roots_Phi 4 2 q_separable

/-- The Galois group of `X⁵ − 4X + 2` acts **bijectively** — hence as the full symmetric
group — on its five complex roots. -/
theorem q_galActionHom_bijective : Bijective (galActionHom q ℂ) :=
  gal_Phi 4 2 (by norm_num) q_irreducible

/-- Relabelling the carrier of a permutation group along an equivalence of types is a
group isomorphism. -/
def permCongrMulEquiv {α β : Type*} (e : α ≃ β) : Equiv.Perm α ≃* Equiv.Perm β :=
  { e.permCongr with
    map_mul' := fun σ τ => by
      ext x
      simp [Equiv.Perm.mul_apply, Equiv.permCongr_apply] }

/-- **Main theorem (OQ-01).** The Galois group of `X⁵ − 4X + 2` over `ℚ` is the full
symmetric group `S₅`, exhibited as an explicit group isomorphism.

The action homomorphism `galActionHom q ℂ : q.Gal →* Equiv.Perm (q.rootSet ℂ)` is
bijective (`q_galActionHom_bijective`), so `MulEquiv.ofBijective` turns it into an
isomorphism onto `Equiv.Perm (q.rootSet ℂ)`; relabelling the five-element root set as
`Fin 5` (`q_card_complex_roots`) identifies that with `Equiv.Perm (Fin 5) = S₅`. -/
noncomputable def galEquivS5 : q.Gal ≃* Equiv.Perm (Fin 5) :=
  (MulEquiv.ofBijective (galActionHom q ℂ) q_galActionHom_bijective).trans
    (permCongrMulEquiv (Fintype.equivFinOfCardEq q_card_complex_roots))

/-- The Galois group of `X⁵ − 4X + 2` has order `5! = 120`. -/
theorem gal_card : Nat.card q.Gal = 120 := by
  rw [Nat.card_congr galEquivS5.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
    Fintype.card_fin]
  decide

/-- The Galois group of `X⁵ − 4X + 2` is **not solvable**: `S₅` is not solvable
(`Equiv.Perm.fin_5_not_solvable`), and solvability transfers across the surjection
`galEquivS5`, so a solvable `q.Gal` would make `S₅` solvable. -/
theorem gal_not_solvable : ¬ IsSolvable q.Gal := by
  intro h
  haveI : IsSolvable q.Gal := h
  have hsurj : Function.Surjective galEquivS5.toMonoidHom :=
    fun y => ⟨galEquivS5.symm y, by simp⟩
  exact Equiv.Perm.fin_5_not_solvable (solvable_of_surjective hsurj)

/-- **Unconditional Abel–Ruffini conclusion.** No complex root of `X⁵ − 4X + 2` is
solvable by radicals: such a root would force the Galois group to be solvable
(Mathlib's `solvableByRad.isSolvable'` for the irreducible `q`), contradicting
`gal_not_solvable`. Unlike the `X⁵ − X − 1` entry, this needs **no** assumed isomorphism. -/
theorem root_not_solvableByRad {x : ℂ} (hx : aeval x q = 0) : ¬ IsSolvableByRad ℚ x :=
  fun h => gal_not_solvable (solvableByRad.isSolvable' q_irreducible hx h)

/-- A concrete algebraic number that is **not** solvable by radicals: any complex root of
`X⁵ − 4X + 2`. -/
theorem exists_root_not_solvableByRad :
    ∃ x : ℂ, IsAlgebraic ℚ x ∧ ¬ IsSolvableByRad ℚ x := by
  obtain ⟨x, hx⟩ := (IsAlgClosed.splits (Φ ℂ 4 2)).exists_eval_eq_zero (by simp [degree_Phi])
  rw [← map_Phi 4 2 (algebraMap ℚ ℂ), eval_map] at hx
  have hx' : aeval x q = 0 := hx
  exact ⟨x, ⟨q, (monic_Phi 4 2).ne_zero, hx'⟩, root_not_solvableByRad hx'⟩

end AbelRuffiniGaloisExtensionsOQ01
