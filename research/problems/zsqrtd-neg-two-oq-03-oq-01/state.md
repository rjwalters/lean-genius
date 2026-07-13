# Current State

**Phase**: COMPLETE (pending merge) — the gap is DISCHARGED and Docker-verified in **open PR #24888**
**Since**: 2026-06-16
**Iteration**: 4 (S4 reconciliation, researcher-3)

> **S4 correction (2026-06-16, researcher-3):** the "single remaining gap" and "dual
> blackout / Aristotle target / do not write blind" framing below is **STALE**. The gap
> `exists_eisenstein_norm_eq_prime` was discharged **by hand** (the Eisenstein UFD
> norm-split, steps 4–7) and **Docker-verified GREEN** (7744 jobs) by researcher-2 in
> **PR #24888** (branch `research/zsqrtd-oq030101-norm-realisation`, base `main`, label
> `research`, currently **OPEN** awaiting the deployer). Verified by inspection of that
> branch: file has **0 code sorries / 0 axioms**, `exists_eisenstein_norm_eq_prime` now
> carries a real proof, and the file is **registered** at `proofs/Proofs.lean:3072`.
> `main` still shows the old 1-sorry version only because #24888 has not merged yet.
> **Do NOT re-attempt the discharge — it would duplicate the open PR.** The remaining
> sections are retained for historical context. The only outstanding non-merge item is
> the gallery entry `src/data/proofs/zsqrtd-neg-two-oq-03-oq-01/` (none exists yet —
> an enricher follow-up, not a research gap).

## Target

`Proofs/ZsqrtdNegTwoOQ03OQ01.lean` (tracked, **unregistered**, build-pending):
prove the Fermat `n=3` theorem
`sq_add_three_sq_of_prime_one_mod_three : p.Prime → p % 3 = 1 → ∃ a b : ℤ, (p:ℤ) = a² + 3·b²`
— the Heegner-number analogue of the parent gallery entry `ZsqrtdNegTwo.lean` (`n=2`,
`p = a² + 2b²`). Built on the parent `Proofs/ZsqrtdNegTwoOQ03.lean` Eisenstein-integer
infrastructure (`Proofs.Eisenstein`, `instEuclideanDomain`, `legendreSym_neg_three_eq_one_iff`).

## What is DONE (proved, 0 sorry/0 axiom in those lemmas)

- **Form conversion** `eisenstein_form_to_x_sq_add_three_y_sq` (#24787): every value
  `a² − ab + b²` of the Eisenstein norm form is some `x² + 3y²`. Pure ℤ, parity
  case analysis with explicit witnesses (`4(a²−ab+b²) = (2a−b)² + 3b²` + order-6
  unit rotations). `ring`-closed in each branch.
- **Splitting step 2** `eisensteinSqrtNegThree_sq` (#24836): `θ² = −3` for
  `θ = ⟨1,2⟩ = 1 + 2ω`. Direct coordinate computation.
- **Splitting step 3** `ofInt_sub_sqrt_mul_add_sqrt` (#24836): `(c−θ)(c+θ) = c²+3`,
  turning `p ∣ c²+3` into a factored divisibility in `ℤ[ω]`.
- **Main assembly** `sq_add_three_sq_of_prime_one_mod_three`: proved **modulo** the
  single gap below (picks `z` with `N(z)=p`, applies form conversion).

## The single remaining gap

`exists_eisenstein_norm_eq_prime {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
   ∃ z : Eisenstein, Eisenstein.norm z = (p : ℤ)`  — `sorry` (line ~175).

The HARD splitting argument, isolated to the UFD `prime ↔ irreducible` norm-split
extraction (steps 4–7 of the in-file plan; steps 1–3 are the QR input + the two
concrete algebra lemmas already proved). Plan recorded in the lemma's docstring:

4. `p ∤` either factor `ofInt c ∓ θ` (their ω-coords are `∓2`, `p ∤ 2`) ⇒ `p` not
   prime in `ℤ[ω]`.
5. `ℤ[ω]` is a `EuclideanDomain` ⇒ UFD; `(p:Eisenstein) ≠ 0`, non-unit (`N(p)=p²≠1`),
   non-prime ⇒ factorisation `p = α·β`, both non-units.
6. `norm_mul`: `p² = N(α)·N(β)`, both `> 1` ⇒ (p prime in ℤ) `N(α)=N(β)=p`.
7. `z := α` ⇒ `N(z) = p`. ∎

Standard algebraic number theory, tedious to formalise. **This is the designated
`aristotle_prove` target.**

## Blockers

- **Dual blackout (this session, researcher-1)**: Aristotle `prove_file` live-probed
  → `404 "Resource not found"`; Docker 8-container saturated (~111MB host free) so no
  build/verify. Cannot discharge the gap (Aristotle) nor verify+register (Docker).
- Do **NOT** write the steps 4–7 UFD extraction blind — it is intricate Mathlib API
  work (Eisenstein `norm_mul`, `EuclideanDomain → UFD`, `prime ↔ irreducible`,
  unit/norm bridges) that cannot be checked while Docker is down; blind writing risks
  a broken registered build.

## Next Action

1. When **Aristotle backend returns** (non-404): submit `exists_eisenstein_norm_eq_prime`
   via `prove`/`prove_file` (context = parent `ZsqrtdNegTwoOQ03.lean` + this file's
   proved supporting lemmas). The two concrete algebra ingredients (steps 2–3) are
   already in place to anchor the prover.
2. When **Docker ≤ 2 free**: after the sorry is discharged, `docker-build.sh
   Proofs.ZsqrtdNegTwoOQ03OQ01`, register in `proofs/Proofs.lean`, and add the gallery
   entry `src/data/proofs/zsqrtd-neg-two-oq-03-oq-01/` (none exists yet).

## Attempt Counts

- Total attempts: 3 (S1 reduce-to-one-lemma + form conversion #24787; S2 splitting
  steps 2–3 #24836; S3 frontier reconciliation — this entry).
- Approaches tried: 1 (Eisenstein-integer UFD norm-splitting — the standard route).
