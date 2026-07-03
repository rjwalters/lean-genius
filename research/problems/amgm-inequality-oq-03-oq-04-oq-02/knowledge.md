# amgm-inequality-oq-03-oq-04-oq-02 — Tsallis-entropy analogue of the AM-GM information identity

**Status**: COMPLETED (graduated) · **Phase**: COMPLETED
**Lean file**: `proofs/Proofs/AmgmInequalityOQ03OQ04OQ02.lean` (228 lines, 0 sorries, 0 axioms, 6 theorems, 3 defs)
**Gallery**: `src/data/proofs/amgm-inequality-oq-03-oq-04-oq-02/`

## Problem

The parent entry `amgm-inequality-oq-03-oq-04` unified Rényi entropy and power-mean
monotonicity via the identity **H_α(p) = −log(M_{α−1}(p,p))**, and its own
open-questions list asked: *"Is there an analogous identity for the Tsallis entropy
(which uses arithmetic instead of geometric operations)?"* This problem answers that.

## Resolution

Replace the ordinary logarithm by the **q-deformed logarithm**
`ln_q(x) = (x^{1−q}−1)/(1−q)` and define Tsallis entropy
`S_q(p) = (1 − Σ pᵢ^q)/(q−1)`. Proved (all fully machine-checked):

1. **qLog_mul** — pseudo-additive law: `ln_q(xy) = ln_q(x)+ln_q(y)+(1−q)·ln_q(x)·ln_q(y)`.
2. **tsallis_eq_neg_sum_qLog** — escort form: `S_q(p) = −Σ pᵢ^q·ln_q(pᵢ)` (exact q-analogue of Shannon `H = −Σ pᵢ log pᵢ`).
3. **tsallis_eq_qLog_exp_renyi** — Rényi bridge: `S_q(p) = ln_q(exp(H_q(p)))` (direct analogue of the parent's `H_α = −log(M_{α−1})`).
4. **tsallis_pseudo_additive** — non-extensivity: `S_q(p⊗r) = S_q(p)+S_q(r)+(1−q)·S_q(p)·S_q(r)`.
5. **qLog_tendsto_log** — q→1 limit: `ln_q(x) → log(x)`, recovering Shannon.

---

## Session 2026-07-03 (Session 1) — Full formalization

**Mode**: FRESH
**Outcome**: completed

### What I Did
- Selected from the 19-problem available pool (all EMPTY knowledge); chose this one for
  tractability — the parent is clean rpow algebra and the OQ is fully provable.
- Wrote `Proofs/AmgmInequalityOQ03OQ04OQ02.lean` from scratch: q-logarithm, Tsallis
  entropy, and the five results above.
- Built successfully via Docker (`Proofs.AmgmInequalityOQ03OQ04OQ02`, exit 0): 0 sorries, 0 axioms, no `native_decide`.
- Authored gallery data (meta.json, annotations.json, tacticStates.json).

### Key Findings
- The parent's exp/log pair generalizes cleanly to the q-exp/q-log pair; the Rényi bridge
  is one `rpow_def_of_pos` + `exp_log` away.
- Non-extensivity is *exact* algebra: it reduces to the factorization of the escort sum
  over a product distribution (`Finset.sum_product` + `Finset.sum_mul_sum`).
- The q→1 recovery is a derivative/slope computation: `ln_q(x)` is the slope of `u ↦ x^u`
  at 0, handled via `hasDerivAt_iff_tendsto_slope` on the punctured nbhd `𝓝[≠] 1`, with a
  reparametrization `q ↦ 1−q` mapping `𝓝[≠] 1 → 𝓝[≠] 0`.

### Blocker discovered (parent bit-rot — NOT this problem)
- `Proofs/AmgmInequalityOQ03OQ04.lean` (the parent, a merged "verified" entry) **no longer
  compiles** against the current Mathlib pin (v4.26.0): failures at ~lines 108/124/221/230
  (`Real.rpow_add` application, `Real.log_rpow`/`ring`, `renyi_sum_eq_powerMean_sum` pattern,
  a `renyi_eq_neg_log_powerMean` type mismatch on `2-1` vs `1`). The file is byte-identical
  to `origin/main`, so this is genuine Mathlib API drift, not a local edit.
- **Mitigation**: this entry re-declares `renyiEntropy` locally so it is self-contained and
  does not depend on the broken parent. **The parent needs a Mechanic repair** (flagged in
  the problem JSON `mathlibGaps`).

### Files Modified
- `proofs/Proofs/AmgmInequalityOQ03OQ04OQ02.lean` (new)
- `src/data/proofs/amgm-inequality-oq-03-oq-04-oq-02/{meta,annotations,tacticStates}.json` (new)
- `src/data/research/problems/amgm-inequality-oq-03-oq-04-oq-02.json` (new)

### Next Steps
- Lift the q→1 recovery from `ln_q` to the full entropy (`S_q → Shannon` by `Tendsto.sum`).
- Study monotonicity/concavity of `S_q` in `q`.
- Open a repair task for the bit-rotted parent `amgm-inequality-oq-03-oq-04`.
