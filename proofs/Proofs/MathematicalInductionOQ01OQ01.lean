import Mathlib

/-
# Cantor Normal Form via Transfinite Induction  (OQ-01-OQ-01)

## The Question
The parent entry "Transfinite Induction over Ordinals"
(`mathematical-induction-oq-01`) left `cantor_normal_form_exists` as a prose
placeholder, remarking only that "This is `Ordinal.CNF` in Mathlib." This entry
discharges that placeholder: it gives the fully machine-checked existence
statement and exposes the transfinite-induction structure underlying it, using
`Ordinal.log` and `Ordinal.div`/`Ordinal.mod` exactly as the question asked.

## Answer: Yes.
Every ordinal `o` has a Cantor normal form in base `ω`: a finite list of
(exponent, coefficient) pairs `[(e₁,c₁), …, (eₙ,cₙ)]` with

    o = ω^e₁·c₁ + ω^e₂·c₂ + … + ω^eₙ·cₙ,    e₁ > e₂ > … > eₙ,    0 < cᵢ < ω.

Mathlib's `Ordinal.CNF ω o` produces this list. It is *defined* by well-founded
(transfinite) recursion on `o`: the recursion descends along
`o ↦ o % ω ^ log ω o`, which is strictly smaller than `o` whenever `o ≠ 0`
(`Ordinal.mod_opow_log_lt_self`). That strictly-decreasing measure is precisely
what makes the construction a genuine instance of transfinite induction — the
same `WellFounded.fix` principle formalized abstractly in the parent file.

## What We Prove
- `cantor_normal_form_exists`: the packaged existence statement (reconstruction,
  strictly-decreasing exponents, and finite positive coefficients).
- `cnf_recursion_decreases`: the termination measure `o % ω^(log ω o) < o` that
  turns the recursion into a well-founded/transfinite induction.
- `cnf_exponent_le_log`: every exponent is `≤ log ω o`, so the leading exponent
  `log ω o` plays the role of the ordinal's "degree" in base `ω`.
- `cantor_normal_form_zero`: the base case, `CNF ω 0 = []`.

All results are fully machine-checked; no `sorry`, no extra axioms.
-/

open Ordinal List

namespace TransfiniteInduction

-- ═══════════════════════════════════════════════════════════════
-- Cantor Normal Form: existence via transfinite recursion
-- ═══════════════════════════════════════════════════════════════

/-- **Cantor Normal Form exists (base `ω`).** Every ordinal `o` is the value of a
    finite Cantor normal form: there is a list `L` of (exponent, coefficient)
    pairs with

    * `o = ω^e₁·c₁ + … + ω^eₙ·cₙ`  (reconstruction of `o` from `L`),
    * the exponents `e₁ > … > eₙ` strictly decreasing, and
    * every coefficient a positive finite ordinal, `0 < cᵢ < ω`.

    The witness is Mathlib's `Ordinal.CNF ω o`, built by transfinite recursion on
    `o`. This is the machine-checked form of the placeholder left in the parent
    "Transfinite Induction over Ordinals" entry. -/
theorem cantor_normal_form_exists (o : Ordinal) :
    ∃ L : List (Ordinal × Ordinal),
      L.foldr (fun p r => ω ^ p.1 * p.2 + r) 0 = o ∧
      (L.map Prod.fst).Pairwise (· > ·) ∧
      ∀ p ∈ L, 0 < p.2 ∧ p.2 < ω := by
  refine ⟨Ordinal.CNF ω o, Ordinal.CNF.foldr ω o, ?_, ?_⟩
  · -- exponents are strictly decreasing
    exact sortedGT_iff_pairwise.mp (Ordinal.CNF.sorted ω o)
  · -- each coefficient is a positive finite ordinal
    exact fun p hp => ⟨Ordinal.CNF.lt_snd hp, Ordinal.CNF.snd_lt one_lt_omega0 hp⟩

/-- **The transfinite-induction measure behind Cantor normal form.** For a nonzero
    ordinal `o`, the tail `o % ω ^ log ω o` — on which the CNF recursion recurses —
    is strictly smaller than `o`. This strictly-decreasing measure is exactly what
    turns the recursive CNF construction into a well-founded (transfinite)
    induction; it is the descent condition `Ordinal.CNF.rec` uses to terminate. -/
theorem cnf_recursion_decreases {o : Ordinal} (ho : o ≠ 0) :
    o % ω ^ log ω o < o :=
  Ordinal.mod_opow_log_lt_self ω ho

/-- Every exponent appearing in the base-`ω` Cantor normal form of `o` is at most
    `log ω o`. Hence the leading exponent equals `log ω o`, the analogue of the
    "degree" of `o` in base `ω`. -/
theorem cnf_exponent_le_log {o : Ordinal} {p : Ordinal × Ordinal}
    (hp : p ∈ Ordinal.CNF ω o) : p.1 ≤ log ω o :=
  Ordinal.CNF.fst_le_log hp

/-- The base case of the recursion: the Cantor normal form of `0` is the empty
    sum. -/
theorem cantor_normal_form_zero : Ordinal.CNF ω 0 = [] :=
  Ordinal.CNF.zero_right ω

end TransfiniteInduction
