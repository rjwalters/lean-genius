# Research State: cauchy-schwarz-oq-02-oq-03

## Current State
**Phase**: ACT (Session 1)
**Path**: full
**Since**: 2026-05-08
**Iteration**: 1

## Current Focus
Session 1 (researcher-10): drafted full Lean proof of the complex polarization identity in Mathlib convention, with per-component recovery lemmas and explicit physics-convention bridge theorems. Proofs delegate to standard Mathlib idioms (`norm_add_sq`, `inner_smul_right`, `inner_neg_right`, `inner_conj_symm`, `Complex.re_add_im`); structurally analogous to the real polarization in `CauchySchwarzOQ02`.

## Active Approach
Decomposition via `Complex.re_add_im`: write $\langle x, y \rangle_{\mathbb{C}} = (\mathrm{re}\langle x,y \rangle : \mathbb{C}) + (\mathrm{im}\langle x,y \rangle : \mathbb{C}) \cdot i$, then substitute the per-component formulas $\mathrm{re}\langle x,y \rangle = (\|x+y\|^2 - \|x-y\|^2)/4$ and $\mathrm{im}\langle x,y \rangle = (\|x-iy\|^2 - \|x+iy\|^2)/4$. Finish with `push_cast; ring`. The convention-mismatch theorem uses `inner_conj_symm` to show the physics-formula computes $\langle y, x \rangle = \overline{\langle x, y \rangle}$.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (Complex.re_add_im decomposition — drafted, build pending)

## Blockers
**Build pending**: the worktree's `proofs/.lake` is a recursive self-symlink (per `feedback_researcher_lake_symlink_broken.md`), forcing Docker builds to fresh-clone Mathlib (~10–15 min) + cache get (~10 min) — total ~45 min. PR is opened as draft following the convention from PR #16936 and other recent build-pending session-1 PRs.

## Next Action
- Run `./proofs/scripts/docker-build.sh Proofs.CauchySchwarzOQ02OQ03` from a worktree with warm Mathlib cache.
- If build succeeds, mark PR ready-for-review and request enricher follow-up.
- If build fails, identify and fix the failing tactic step. Most likely failure points:
  1. `linarith` in `norm_sub_sq_complex` (needs `sub_eq_add_neg` rewrite to align)
  2. The `simp` set in `mathlib_minus_physics` and `physics_polarization_eq_inner_swap` for `Complex.conj_re/im` decomposition
  3. `Complex.re_add_im` exact name (may be `Complex.re_add_im_mul_I` or similar in 4.26)

## Future Sessions
- **Session 2**: unify with parent OQ-02 real polarization via `RCLike` quantification. Mathlib's `inner_eq_sum_norm_sq_div_four` (if present) may subsume both directly.
- **Session 3**: operator polarization identity — for $T : E \to E$ bounded linear, $\langle Tx, y \rangle = (Q(x+y) - Q(x-y) + iQ(x+iy) - iQ(x-iy))/4$ where $Q(z) := \langle Tz, z \rangle$. Application: $T$ self-adjoint $\Leftrightarrow$ $Q$ real-valued.
- **Session 4**: phase-retrieval connection — formal statement that $\langle x, y \rangle$ is determined by the four norm-squared values $\|x \pm y\|^2, \|x \pm iy\|^2$, framed as a uniqueness/recovery theorem.
