# Current State

**Phase**: OBSERVE
**Since**: 2026-05-12 (S1)
**Iteration**: 1

## Current Focus

S1 (researcher-12, 2026-05-12): survey the lone axiom
`three_dvd_gal_card` (line 309 of `proofs/Proofs/InverseGaloisA5.lean`),
classify the three discharge routes (R1/R2/R3), map the relevant
Mathlib ramification-inertia API, and propose a concrete S2-S3 plan
based on R1 (specialised Dedekind at `p = 7`).

The parent file's status is **`axiomatized`** (1 axiom, 0 sorries,
84 theorems, 2067 lines). Eliminating `three_dvd_gal_card` would
upgrade the parent to **`verified`** (badge `original`, axiomCount 0)
— a flagship status change for the gallery's first non-solvable
inverse-Galois realisation.

## Active Approach

**Recommended path: R1 — specialised Dedekind at `(q, p) = (q, 7)`.**

The parent's Part XII (lines 715-884) already contains the **decidable**
half of the argument:
- `q_root_mod7_at_5`, `q_root_mod7_at_6` (linear factors at `5, 6 ∈ F₇`),
- `cubic_factor_no_roots_mod7` (cubic factor irreducible over `F₇`).

S2 will introduce a new companion file
`proofs/Proofs/InverseGaloisA5Dedekind.lean` with the
**Frobenius-construction-and-cycle-type bridge**:

1. `seven_unramified` — disc(q) = 32000² ⇒ 7 unramified;
2. `𝔭₃` — explicit prime ideal of `𝓞 K` above 7 with `f(𝔭/7) = 3`;
3. `frob₃` — Frobenius automorphism at `𝔭₃`, generating its
   decomposition group (cyclic of order 3 since 7 is unramified);
4. `frob₃_order_eq_three` — `orderOf frob₃ = 3`;
5. `three_dvd_gal_card_proved : 3 ∣ Fintype.card q.Gal` via
   `orderOf_dvd_card`.

S3 will discharge the four sorries from S2 (`seven_unramified`,
`𝔭₃` and its inertia degree, `frob₃` and its order). S4 will
splice the proved theorem into the parent file
(`axiom three_dvd_gal_card` → `theorem three_dvd_gal_card := three_dvd_gal_card_proved`)
and bump the parent's meta.json.

## Blockers

None mathematical: Dedekind's theorem is classical, and the specialised
form needed for `(q, 7)` is a routine ramification-inertia computation.

Practical:
- **Mathlib API exploration**: `Mathlib.NumberTheory.RamificationInertia.Galois`
  contains the Frobenius framework but the exact API surface for
  extracting an explicit prime ideal and its Frobenius generator
  needs verification at the pinned revision. S2 will spend the first
  ~30 lines on import-and-API-probing.
- **Docker build cost**: S3 / S4 PRs that touch `InverseGaloisA5.lean`
  (2067 lines, with the heavy Vandermonde Parts VIII–XV) will rebuild
  in ~25-30 minutes once the Mathlib cache is warm. Plan `(build pending)`
  PRs per gallery convention for the parent-change diff.
- **Worktree `.lake` symlink**: known broken on this worktree (per
  memory entry `Researcher — broken proofs/.lake symlink`); any S2-S3
  PR runs `docker-build` ⇒ ≥45 min build window. Consider deferring
  build verification to the deployer.

## Next Action

**S2 (any researcher): R1 ORIENT — Lean skeleton + sorry-filled
Frobenius bridge in `InverseGaloisA5Dedekind.lean`.**

Three deliverables in a single PR:

1. **Create companion file** `proofs/Proofs/InverseGaloisA5Dedekind.lean`
   (~80 lines, 4 sorries):
   ```lean
   import Proofs.InverseGaloisA5
   import Mathlib.NumberTheory.RamificationInertia.Galois
   import Mathlib.GroupTheory.Perm.Cycle.Type

   namespace InverseGaloisA5Dedekind

   open Polynomial InverseGaloisA5

   local notation "K" => q.SplittingField

   theorem seven_unramified : ¬ 7 ∣ Polynomial.disc q := by sorry
   noncomputable def 𝔭₃ : Ideal (𝓞 K) := sorry
   theorem 𝔭₃_inertia_deg : Ideal.inertiaDeg 𝔭₃ (7 : ℤ) = 3 := sorry
   noncomputable def frob₃ : q.Gal := sorry
   theorem frob₃_order_eq_three : orderOf frob₃ = 3 := sorry
   theorem three_dvd_gal_card_proved : 3 ∣ Fintype.card q.Gal := by
     rw [← frob₃_order_eq_three]; exact orderOf_dvd_card

   end InverseGaloisA5Dedekind
   ```

2. **Update `proofs/Proofs.lean`** to include the new file in the
   auto-import list.

3. **No parent-file changes yet** (parent still uses `axiom three_dvd_gal_card`).
   The axiom replacement happens in S4 after S3 proves the supporting
   theorems.

S2 estimated effort: 1 session, ~80 lines Lean, 4 sorries (statement-only
scaffold). Build verification optional (declarations only, no proof bodies
beyond the trivial `three_dvd_gal_card_proved`).

## Session Log

| Step | Action | Outcome |
|------|--------|---------|
| 1 | Verified no open PR / remote branch / recent merge for slug | safe to claim |
| 2 | `claim-problem.sh claim inverse-galois-a5-oq-01` from `$REPO_ROOT` | claimed |
| 3 | `git checkout -b research/inverse-galois-a5-oq-01-s1-observe-<ts> origin/main` (fresh base) | clean branch |
| 4 | Read parent `Proofs/InverseGaloisA5.lean` lines 260-310 + 715-810 (Part XII) | identified the axiom + supporting decidables |
| 5 | Surveyed Mathlib `RamificationInertia.*` modules + `Perm.Cycle.Type` | API map drafted |
| 6 | Drafted three discharge routes R1/R2/R3 with effort estimates | strategy clear |
| 7 | Wrote problem.md, knowledge.md, state.md, and JSON gallery entry | S1 OBSERVE complete |
| 8 | (pending) Commit + push + PR with label `research` | next |

## Honest Calibration

S1 produces:

- One **survey markdown** (`problem.md`, ~280 lines) with three-route
  classification and Mathlib gap map;
- One **knowledge file** (`knowledge.md`, ~200 lines) with parent
  inventory, API survey, Lean skeleton, and decomposition plan;
- This `state.md` capturing the OBSERVE state;
- One **gallery JSON** entry (`src/data/research/problems/inverse-galois-a5-oq-01.json`).

S1 does **not**:
- Change any Lean file;
- Modify parent meta.json or any other gallery data;
- Add or remove axioms/sorries.

The next iteration (S2 ORIENT) is where Lean changes begin. The
**realistic estimate** for closing the OQ is 3-4 sessions
(S2 scaffold → S3 Frobenius discharge → S4 parent integration),
delivering a `verified`-status upgrade for the parent
`inverse-galois-a5` flagship proof.

## References Captured

- Dummit & Foote (2004), §14.8: standard Dedekind theorem statement.
- Neukirch (1999), Theorem I.9.6: Frobenius element framework.
- Lang (1994), §I.7: decomposition group at unramified primes.
- Cohen (1993), §6.4: computational algorithm (useful for R1 specialisation).
- Mathlib modules: `NumberTheory.NumberField.Basic`,
  `NumberTheory.NumberField.Discriminant`,
  `NumberTheory.RamificationInertia.*`,
  `GroupTheory.Perm.Cycle.Type`.

See `knowledge.md` for the full Mathlib-gap table and Lean skeleton.
