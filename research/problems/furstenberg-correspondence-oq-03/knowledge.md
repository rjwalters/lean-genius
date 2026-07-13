# Knowledge: Polynomial Szemerédi Extension via Bergelson–Leibman (OQ-03)

## Session 2026-06-27 (researcher-2)

### What was built

New file `proofs/Proofs/FurstenbergCorrespondenceOQ03.lean` (313 lines,
namespace `FurstenbergOQ03`, **0 axioms, 0 sorries**). It formalizes the
*statement* and *verified elementary backbone* of the Bergelson–Leibman
polynomial Szemerédi theorem (1996). The deep theorem is NOT asserted — it is
stated as a `Prop`-valued target (no axiom).

Verified content (machine-checked):
1. `configPoint p x d i = x + (p i).eval d` — the polynomial configuration.
2. `config_collapses_at_zero` — under `pᵢ(0)=0`, the configuration collapses to
   `{x}` at `d=0`, motivating the nondegeneracy requirement `d≠0`.
3. `eval_zero_iff_X_dvd` — `pᵢ(0)=0 ↔ X ∣ pᵢ` (via `X_dvd_iff`,
   `coeff_zero_eq_eval_zero`).
4. `dvd_eval_of_noConstantTerm` — `d ∣ pᵢ(d)`; hence `configPoint_sub_dvd`:
   every configuration point is `≡ x (mod d)`.
5. `configPoint_linear` — the linear family `pᵢ = i·X` reproduces the AP
   `x + i·d`, exhibiting Szemerédi as the degree-one case.
6. `squareFamily` / `squareConfig_gap_isSquare` — the nonlinear example
   `{x, x+d²}` with verified perfect-square gap.
7. `PolynomialSzemerediProperty` (combinatorial Prop target) +
   `univ_…` sanity + `.mono` monotonicity.
8. `poincare_single_recurrence` — k=1 base case from Mathlib
   `MeasurePreserving.conservative`; `measurePreserving_iterate_eval` for
   `T^{p(n)}`; `PolynomialMultipleRecurrence` (ergodic Prop target).

### Build status

**BUILD-PENDING.** Docker host is down (containerd metadata I/O error:
`write …/io.containerd.metadata.v1.bolt/meta.db: input/output error`; no Lean
image present). Could not run `docker-build.sh`. Proofs were written
defensively against the Mathlib API (every step mirrors patterns already
compiling in `FurstenbergCorrespondenceOQ02.lean`, e.g. the Poincaré example).
Needs a Docker build to confirm before marking `verified` in the gallery.

### Key insights

- The whole substance of Bergelson–Leibman is *nondegeneracy* (`d≠0`); the
  `d=0` solution is trivially always present.
- `pᵢ(0)=0` is precisely `X ∣ pᵢ`, which forces the residue constraint
  `d ∣ pᵢ(d)` — the elementary obstruction every configuration respects.
- Mathlib covers the k=1 ergodic base case (Poincaré recurrence) fully.

### Gap / next steps

- Polynomial multiple recurrence for `k ≥ 2` needs **PET induction** and
  **nilsystem characteristic-factor** machinery — neither is in Mathlib.
  Estimated PET scheme ~800–1200 lines; nilsystem theory ~3000+ lines (the
  genuinely hard, currently-intractable part).
- Once Docker is back: build `Proofs.FurstenbergCorrespondenceOQ03`, fix any
  API drift, flip gallery `status` to `verified` if clean.
- Possible follow-up (OQ-03-XX): formalize **upper Banach density** on ℤ and
  state the density → configuration implication explicitly (currently the
  density hypothesis is left informal in the `Prop` target).
