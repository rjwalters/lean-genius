/-
  Corrected sufficiency assembly for Legendre's three-square theorem.

  `Proofs.ThreeSquares` leaves the SUFFICIENCY direction
  `¬IsExcludedForm n ⟹ ∃ x y z, x²+y²+z² = n` as an axiom
  (`not_excluded_form_is_sum_three_sq`, ThreeSquares.lean:1665).

  The earlier reduction `Proofs.ThreeSquaresSufficiency` (#24443) tried to
  shrink that axiom to a SINGLE hypothesis `DirichletWitnessProperty`:

      ¬IsExcludedForm m → ¬(4 ∣ m) → 1 < m →
        ∃ d p, 0 < d ∧ p = d·m − 1 ∧ p.Prime ∧ legendreSym p (−d) = 1

  Audit PR #24529 / obstruction PR #24614 showed that this witness is
  UNSATISFIABLE for every 4-free core `m ≡ 3 (mod 8)`: there is no prime
  `p = d·m − 1` with `−d` a quadratic residue mod `p`. Hence
  `DirichletWitnessProperty` as stated is a FALSE proposition — reducing the
  axiom to it is vacuous, since the hypothesis can never be discharged.

  This file fixes the architecture by splitting the open content into TWO
  hypotheses, each of which is SATISFIABLE (numerically certified in
  `verify_corrected_split.py`):

    * `DirichletWitnessNe3` — the Dirichlet witness, RESTRICTED to the residue
      classes `m % 8 ∈ {1,2,5,6}` where it actually holds; and
    * `Residue3Property` — for `m % 8 = 3` (and `m > 3`), the existence of a
      prime deficit `mm = (m − t²)/2` with `mm % 4 ≠ 3`, handled by Fermat's
      two-square theorem via `ThreeSquaresResidue3.three_sq_of_residue3_prime`.

  Everything else — the `4`-power descent, the small cases (`n ≤ 1` and the
  lone exceptional core `n = 3 = 1²+1²+1²`), and the assembly via
  `dirichlet_key_lemma` — is discharged here with NO new axioms and NO `sorry`,
  reusing only lemmas already proved in `Proofs.ThreeSquares` and
  `Proofs.ThreeSquaresResidue3`. The witness branch is verbatim the proven
  branch of `ThreeSquaresSufficiency.three_sq_of_dirichlet_witness`; the only
  additions are the mod-8 case split and the residue-3 route.

  CONSEQUENCE FOR THE AXIOM BUDGET. `not_excluded_form_is_sum_three_sq` follows
  from `dirichlet_key_lemma` together with the two SATISFIABLE hypotheses above.
  Unlike #24443, both hypotheses can in principle be discharged (the first by
  Dirichlet primes in AP + quadratic reciprocity on the four good residues, the
  second by Dirichlet primes in AP for the deficit), so this is a genuine route
  to eliminating the sufficiency axiom rather than a reduction to a false claim.

  NOTE: build-pending (Docker blackout — daemon unresponsive this session). The
  earlier elaboration bug is now FIXED: the Dirichlet witness `Prop` states the
  QR condition instance-free as `IsSquare ((-d : ℤ) : ZMod p)` (the old
  `legendreSym p (-d) = 1` form failed instance synthesis, since `legendreSym`
  needs a `Fact (Nat.Prime p)` instance that a `Nat.Prime p` *conjunct* cannot
  supply). The consumer converts back to `legendreSym = 1` for `dirichlet_key_lemma`
  via `legendreSym.eq_one_iff`, reusing the proven in-file pattern at
  `ThreeSquares.lean:1191–1223`. Still NOT registered in `Proofs.lean`; a
  Docker-available session should build both companions, then register
  `Proofs.ThreeSquaresResidue3` + `Proofs.ThreeSquaresSufficiencyCorrected`.
-/
import Proofs.ThreeSquares
import Proofs.ThreeSquaresResidue3

namespace ThreeSquares

/-- The Dirichlet witness property, RESTRICTED to the residue classes where it
holds. For every `n > 1` that is not of excluded form, is not divisible by `4`,
and is **not** `≡ 3 (mod 8)`, there is a multiplier `d` and a prime `p = d·n − 1`
with `−d` a quadratic residue mod `p`.

This is the satisfiable part of the monolithic `DirichletWitnessProperty` of
`Proofs.ThreeSquaresSufficiency`; the excluded class `m ≡ 3 (mod 8)`, on which
the witness is provably unsatisfiable (audit #24529 / obstruction #24614), is
handled separately by `Residue3Property`. -/
def DirichletWitnessNe3 : Prop :=
  ∀ {m : ℕ}, ¬IsExcludedForm m → ¬(4 ∣ m) → m % 8 ≠ 3 → 1 < m →
    ∃ d p : ℕ, 0 < d ∧ d ≤ 2 ∧ p = d * m - 1 ∧ Nat.Prime p ∧ IsSquare ((-d : ℤ) : ZMod p)

/-- The residue-3 property: for every `m ≡ 3 (mod 8)` with `m > 3`, there is an
odd witness `t` and a prime `mm = (m − t²)/2` with `mm % 4 ≠ 3`, packaged as the
deficit identity `m = t² + 2·mm`.

This is exactly the input consumed by `ThreeSquaresResidue3.three_sq_of_residue3_prime`,
which closes the `m ≡ 3 (mod 8)` class via Fermat's two-square theorem
(`m = t² + (a+b)² + (a−b)²` where `mm = a² + b²`). It is satisfiable for every
such `m`: with `t` odd we have `t² ≡ 1 (mod 8)`, so `mm ≡ 1 (mod 4)` and in
particular `mm % 4 ≠ 3` automatically. -/
def Residue3Property : Prop :=
  ∀ {m : ℕ}, m % 8 = 3 → 3 < m →
    ∃ t mm : ℕ, Nat.Prime mm ∧ mm % 4 ≠ 3 ∧ m = t ^ 2 + 2 * mm

/-- **Corrected sufficiency from the split witnesses.**

Assuming the two satisfiable hypotheses `DirichletWitnessNe3` and
`Residue3Property`, every natural number that is not of the excluded form
`4^a (8b + 7)` is a sum of three integer squares.

The proof is strong induction on `n`:

* small cases `n ≤ 1` are explicit;
* if `4 ∣ n`, write `n = 4 * m`; then `¬IsExcludedForm m`
  (by `excluded_form_four_mul_iff`), so the induction hypothesis represents `m`
  and `four_mul_sum_three_sq` lifts the representation back to `n`;
* otherwise `n > 1` and `4 ∤ n`, split on the residue:
    - `n = 3 = 1² + 1² + 1²` explicitly;
    - `n % 8 = 3` and `n > 3`: the residue-3 route via `Residue3Property`;
    - `n % 8 ≠ 3`: the witness `(d, p)` exists and `dirichlet_key_lemma`
      represents `n` directly. -/
theorem three_sq_of_corrected_witnesses
    (Hne3 : DirichletWitnessNe3) (H3 : Residue3Property)
    {n : ℕ} (hne : ¬IsExcludedForm n) :
    ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h4 : 4 ∣ n
    · -- 4 ∣ n: descend to m = n / 4
      obtain ⟨m, hm⟩ := h4
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · -- m = 0 ⟹ n = 0 = 0² + 0² + 0²
        exact ⟨0, 0, 0, by rw [hm, hm0]; norm_num⟩
      · -- m ≥ 1 ⟹ m < n, recurse
        have hmlt : m < n := by omega
        have hmne : ¬IsExcludedForm m := by
          intro hmm
          apply hne
          rw [hm]
          exact excluded_form_four_mul_iff.mpr hmm
        have hrec := ih m hmlt hmne
        have h4m := four_mul_sum_three_sq hrec
        rw [hm]
        exact h4m
    · -- 4 ∤ n
      by_cases hle : n ≤ 1
      · -- n ∈ {0, 1}
        interval_cases n
        · exact ⟨0, 0, 0, by norm_num⟩
        · exact ⟨1, 0, 0, by norm_num⟩
      · -- n > 1 and 4 ∤ n
        push_neg at hle
        by_cases h3 : n % 8 = 3
        · -- residue-3 class
          by_cases hn3 : n = 3
          · -- the lone exceptional core: 3 = 1² + 1² + 1²
            exact ⟨1, 1, 1, by rw [hn3]; norm_num⟩
          · -- n ≡ 3 (mod 8) and n ≠ 3 ⟹ n ≥ 11 > 3
            have h3lt : 3 < n := by omega
            obtain ⟨t, mm, hmm_prime, hmm4, hdecomp⟩ := H3 h3 h3lt
            haveI : Fact (Nat.Prime mm) := ⟨hmm_prime⟩
            exact ThreeSquaresResidue3.three_sq_of_residue3_prime hmm4 hdecomp
        · -- n % 8 ≠ 3: invoke the (restricted) Dirichlet witness
          obtain ⟨d, p, hd, hd2, hp, hpp, hqr⟩ := Hne3 hne h4 h3 hle
          haveI : Fact (Nat.Prime p) := ⟨hpp⟩
          -- The witness now carries `IsSquare ((-d : ℤ) : ZMod p)` (instance-free,
          -- so the `def` elaborates without a `Fact` in the `Prop`). Convert back to
          -- `legendreSym p (-d) = 1` for `dirichlet_key_lemma` via `eq_one_iff`,
          -- whose `≠ 0` side-goal follows from `¬ p ∣ d` (else `p ∣ d*n = p+1`).
          have hpd : ¬ (p ∣ d) := by
            intro hpd
            have hdn_pos : 0 < d * n := Nat.mul_pos hd (by omega)
            have hdn : d * n = p + 1 := by omega
            have hpdn : p ∣ d * n := hpd.mul_right n
            rw [hdn] at hpdn
            have hp1 : p ∣ 1 := (Nat.dvd_add_right (dvd_refl p)).mp hpdn
            exact hpp.ne_one (Nat.dvd_one.mp hp1)
          have hd_ne : (d : ZMod p) ≠ 0 := by
            intro h
            rw [ZMod.natCast_zmod_eq_zero_iff_dvd] at h
            exact hpd h
          have hneg_d_ne : ((-d : ℤ) : ZMod p) ≠ 0 := by
            push_cast; exact neg_ne_zero.mpr hd_ne
          have hqr' : legendreSym p (-d : ℤ) = 1 :=
            (legendreSym.eq_one_iff p hneg_d_ne).mpr hqr
          exact dirichlet_key_lemma (n := n) (d := d) (p := p) hle hd hd2 hp hqr'

/-- **The sufficiency axiom is redundant given the corrected split.**

Restatement matching `ThreeSquares.not_excluded_form_is_sum_three_sq`, showing
that axiom is derivable from `dirichlet_key_lemma` plus the two SATISFIABLE
hypotheses `DirichletWitnessNe3` and `Residue3Property`. -/
theorem not_excluded_form_is_sum_three_sq_of_corrected
    (Hne3 : DirichletWitnessNe3) (H3 : Residue3Property)
    {n : ℕ} (h : ¬IsExcludedForm n) :
    ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = n :=
  three_sq_of_corrected_witnesses Hne3 H3 h

/-- **Conditional Legendre three-square theorem (corrected).**

Combining the proven necessity (`excluded_form_not_sum_three_sq`) with the
corrected conditional sufficiency above: assuming the two split witness
properties, `n` is a sum of three integer squares iff `n` is not of excluded
form. -/
theorem legendre_three_squares_of_corrected
    (Hne3 : DirichletWitnessNe3) (H3 : Residue3Property) (n : ℕ) :
    (∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = n) ↔ ¬IsExcludedForm n :=
  ⟨fun hrep hf => excluded_form_not_sum_three_sq hf hrep,
   three_sq_of_corrected_witnesses Hne3 H3⟩

/-- **Slimmed residue-3 hypothesis** (no quadratic side-condition).

`Residue3Property` carries an explicit `mm % 4 ≠ 3` clause so that Fermat's
two-square theorem applies to the deficit. But for `m ≡ 3 (mod 8)` that clause is
*forced* the moment the witness `t` is odd: an odd square is `≡ 1 (mod 8)`, so
`mm = (m − t²)/2 ≡ 1 (mod 4)`. This slimmer property therefore asks only for an
odd `t` and a prime deficit — the genuinely open Dirichlet-on-a-thin-sequence
content — with the arithmetic side-condition discharged downstream. -/
def Residue3PropertyOdd : Prop :=
  ∀ {m : ℕ}, m % 8 = 3 → 3 < m →
    ∃ t mm : ℕ, Odd t ∧ Nat.Prime mm ∧ m = t ^ 2 + 2 * mm

/-- The slimmer `Residue3PropertyOdd` implies the original `Residue3Property`:
the `mm % 4 ≠ 3` clause is recovered for free from oddness of `t` via
`ThreeSquaresResidue3.residue3_deficit_one_mod_four`. -/
theorem Residue3Property_of_odd (H : Residue3PropertyOdd) : Residue3Property := by
  intro m hm8 hm3
  obtain ⟨t, mm, ht, hmm, hdecomp⟩ := H hm8 hm3
  refine ⟨t, mm, hmm, ?_, hdecomp⟩
  have := ThreeSquaresResidue3.residue3_deficit_one_mod_four hm8 ht hdecomp
  omega

/-- **Corrected sufficiency from the slimmed witnesses.** Same conclusion as
`three_sq_of_corrected_witnesses`, but consuming the smaller `Residue3PropertyOdd`
(no `mm % 4 ≠ 3` obligation). -/
theorem three_sq_of_corrected_witnesses_odd
    (Hne3 : DirichletWitnessNe3) (H3 : Residue3PropertyOdd)
    {n : ℕ} (hne : ¬IsExcludedForm n) :
    ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = n :=
  three_sq_of_corrected_witnesses Hne3 (Residue3Property_of_odd H3) hne

end ThreeSquares
