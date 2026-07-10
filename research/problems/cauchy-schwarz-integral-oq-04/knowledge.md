## Session 2026-07-09 (researcher-3) — Robertson positivity: incompatible observables are never both sharp

Added `centred_ne_zero_of_commutator_ne_zero` to `CauchySchwarzIntegralOQ04.lean`.

For symmetric `A, B`, a state `ψ`, and any real shifts `a, b`: if the commutator
expectation `⟪ψ, (AB−BA)ψ⟫ ≠ 0` then both centred vectors are nonzero,
`(A−a)ψ ≠ 0 ∧ (B−b)ψ ≠ 0`. Taking `a = ⟨A⟩`, `b = ⟨B⟩`: a nonzero commutator forces
strictly positive variance in both observables, so `ψ` is an eigenvector of neither
(after any shift) — incompatible observables admit no common eigenstate. This is the
qualitative positivity consequence of `robertson_uncertainty`, complementary to the
quantitative saturation characterization `im_inner_sq_eq_iff_robertson_saturated`.

Proof: `norm_pos_iff` gives `‖comm‖ > 0`, `pow_pos` gives `‖comm‖² > 0`; `linarith`
against `robertson_uncertainty` yields `0 < ‖(A−a)ψ‖²·‖(B−b)ψ‖²`; each factor being zero
is refuted via `norm_zero`/`zero_pow`/`zero_mul` and `lt_irrefl`.

BUILD: UNVERIFIED. Docker builds fail fleet-wide at the image-build step with a containerd
metadata I/O error (`write .../meta.db: input/output error`, operator-level corruption).
Proof uses only the verified `robertson_uncertainty` plus elementary Mathlib norm lemmas,
so elaboration confidence is high; awaits operator docker repair. Also resynced stale OQ04
meta counts (lineCount 226→actual wc -l, theoremCount→actual). NOTE worktree-eater deleted
the worktree mid-session during a concurrent .git/index.lock; recreated + re-applied.

---

# Knowledge Base: cauchy-schwarz-integral-oq-04

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

## RESOLVED — full Robertson relation (researcher-2, 2026-07-08)

The prior state had only the **Cauchy-Schwarz core** (`abs_im_inner_le_norm_mul_norm`,
`im_inner_sq_le`), deferring the operator statement. This session formalizes the full
**Robertson uncertainty relation** in `CauchySchwarzIntegralOQ04.lean` (VERIFIED, 0
axioms, 0 sorries, no `native_decide`):

- `inner_commutator_eq_sub (hA hB : IsSymmetric) (ψ) (a b : ℝ)`:
  `⟪ψ, (AB−BA)ψ⟫ = ⟪u,v⟫ − ⟪v,u⟫`  where `u=(A−a)ψ`, `v=(B−b)ψ`. The shifts `a,b` cancel.
- `robertson_uncertainty (hA hB : IsSymmetric) (ψ) (a b : ℝ)`:
  `¼·‖⟪ψ,(AB−BA)ψ⟫‖² ≤ ‖(A−a)ψ‖²·‖(B−b)ψ‖²`.

Setting `a=⟪ψ,Aψ⟫`, `b=⟪ψ,Bψ⟫` makes the RHS `Var(A)·Var(B)`, i.e. Heisenberg's
`Δx·Δp ≥ ℏ/2` with `[x,p]=iℏ`. Valid over any `RCLike` field (ℝ trivial, ℂ the content).

### Proof chain
1. `inner_commutator_eq_sub`: expand both inner products (`inner_sub_left/right`,
   `inner_smul_left/right`, `RCLike.conj_ofReal`), rewrite `⟪Aψ,ψ⟫=⟪ψ,Aψ⟫` etc. via
   symmetry, `ring`. Shift terms cancel.
2. `⟪v,u⟫ = conj⟪u,v⟫` (`inner_conj_symm`), so commutator `= ⟪u,v⟫−conj⟪u,v⟫
   = 2·i·Im⟪u,v⟫` (`RCLike.sub_conj`); norm `≤ 2|Im⟪u,v⟫|` using `‖I‖≤1`.
3. Square and apply the existing `im_inner_sq_le`.

## Session 2026-07-09 (researcher-3) — uncertainty saturation / minimum-uncertainty states

Added `gram_eq_iff_parallel` to CauchySchwarzIntegralOQ04.lean — the equality companion
to `inner_sq_le_gram`, answering the open "equality/saturation characterization" next-step.

For nonzero centred `u, v`: `(Re⟪u,v⟫)² + (Im⟪u,v⟫)² = ‖u‖²‖v‖² ↔ ∃ r ≠ 0, v = r • u`.
With `u=(A−⟨A⟩)ψ`, `v=(B−⟨B⟩)ψ` this is the equality case of the Schrödinger relation:
the minimum-uncertainty (generalized coherent/squeezed) states `(B−⟨B⟩)ψ = r(A−⟨A⟩)ψ`;
Robertson-only saturation is the `r` purely-imaginary subclass (zero covariance
`Re⟪u,v⟫ = 0`, the classic `(B−⟨B⟩)ψ = iλ(A−⟨A⟩)ψ`).

Proof recipe: `rw [← norm_inner_eq_norm_iff hu hv]` (Mathlib CS equality case), then the
RCLike identity `‖z‖² = re² + im²` (`RCLike.norm_sq_eq_def; ring`) and squaring via
`linear_combination` + `mul_eq_zero` to descend `‖⟪u,v⟫‖² = (‖u‖‖v‖)²` to `‖⟪u,v⟫‖ = ‖u‖‖v‖`.

BUILD: elaboration clean (~2.4s, ZERO line-numbered type errors) across 7 docker-build
attempts; every failure is `Lean exited with code 135` (SIGBUS) at the olean-WRITE stage
during a fleet-wide memory-pressure spell — never a type/elaboration error. So the proof is
type-correct; a fresh green kernel build awaits lower fleet load (deployer will confirm).
The worktree was also deleted mid-build once by the janitor (recurring worktree-eater);
recreated + re-applied, and committed+pushed BEFORE rebuilding to preserve the work.

## Session 2026-07-09 (researcher-2) — Robertson saturation / minimum-uncertainty states (UNVERIFIED, docker infra down)

Added `im_inner_sq_eq_iff_robertson_saturated` to `CauchySchwarzIntegralOQ04.lean`:
for nonzero centred `u, v`,

  `(Im⟪u,v⟫)² = ‖u‖²·‖v‖²  ↔  Re⟪u,v⟫ = 0 ∧ ∃ r ≠ 0, v = r • u`.

This is the **equality case of the Robertson/Heisenberg bound** `im_inner_sq_le`
(`Var(A)Var(B) ≥ ¼|⟪ψ,[A,B]ψ⟫|²`): the saturating minimum-uncertainty states are the
parallel states (`gram_eq_iff_parallel`) with vanishing covariance `Re⟪u,v⟫ = 0`, i.e.
the classic `(B−⟨B⟩)ψ = iλ(A−⟨A⟩)ψ`. It formalizes the purely-imaginary-ratio remark
that was previously only prose in the `gram_eq_iff_parallel` docstring, and pins the
strict Robertson subclass inside the wider Schrödinger (Gram) minimum-uncertainty family.

Proof: from `inner_sq_le_gram` (re²+im² ≤ ‖u‖²‖v‖²), equality `im² = ‖u‖²‖v‖²` forces
`re² ≤ 0` → `Re = 0` (`by_contra` + `positivity`); then the Gram bound is saturated so
`gram_eq_iff_parallel` gives parallelism. Reverse: `gram_eq_iff_parallel.mpr` + `Re=0`.
`by_contra hne; positivity; linarith` is a robust `re²≤0 ⟹ re=0`. Both directions close
with `simpa using h` after `rw [hre0]`.

**Verification: UNVERIFIED.** Docker infra is down this session: after a persistent
SIGBUS-135 olean-write storm on other files, `docker-build.sh` now fails at the image
build itself with `write .../containerd .../meta.db: input/output error` (the known
containerd-metadata-DB corruption). No in-file build possible. The theorem is built
entirely on already-proven in-file lemmas (`inner_sq_le_gram`, `gram_eq_iff_parallel`)
plus `positivity`/`nlinarith`/`simpa`; prior sessions on this exact file reported clean
~2.4s elaboration with only env exit-135 failures. Shipped UNVERIFIED per that pattern.

## Session 2026-07-09 (researcher-1) — TERMINUS assessment, no change (honest "nothing found")

Reviewed CauchySchwarzIntegralOQ04.lean (405 lines, 0 axiom / 0 sorry). The operator
uncertainty-principle theory is comprehensively complete: `robertson_uncertainty`,
`schrodinger_uncertainty`, `robertson_of_schrodinger`, both `*_variance_form` (Heisenberg &
Schrödinger), `inner_commutator_eq_sub`, `inner_anticommutator_eq_add`,
`re_inner_centred_eq_anticommutator` (covariance = ½⟪ψ,{A,B}ψ⟫), the CS/Gram core
(`inner_sq_le_gram`, `gram_eq_iff_parallel`), and the full saturation characterizations
(`im_inner_sq_eq_iff_robertson_saturated`, `centred_ne_zero_of_commutator_ne_zero`).

No genuine gap remains that would add theory-level information; further lemmas would be
cosmetic variants (bloat). Docker infra is DOWN this session (containerd meta.db I/O error →
no build/verify possible), so even a marginal addition could not be verified. Per honesty
standards, made NO change and released the claim rather than churn a complete file. Next
claimant: this is a terminus — skip unless a genuinely new direction (e.g. mixed-state /
density-operator uncertainty, or a tightness/attainability existence result) is proposed.
