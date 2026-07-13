# cauchy-schwarz-oq-01-oq-03-oq-02: Entropic uncertainty principle (Maassen–Uffink)

**Parent**: `cauchy-schwarz-oq-01-oq-03` — "Heisenberg Uncertainty from Complex
Cauchy-Schwarz" (`Proofs/CauchySchwarzOQ01OQ03.lean`, verified, 0-sorry/0-axiom). Its
open question #2: *"Can the entropic uncertainty principle (Maassen–Uffink 1988) — a
strictly stronger bound expressed in terms of Shannon entropy rather than standard
deviation — be formalized in Lean 4 using Mathlib's information-theoretic library?"*

## Session 2026-06-27 (Session 1) — FRESH, SURVEY → BLOCKED (infrastructure gap)

**Outcome**: SURVEY + BUILD. The sharp Maassen–Uffink theorem is BLOCKED on missing Mathlib
interpolation theory (documented below). I did NOT scaffold the sharp bound with a `sorry`
(scaffolding-theater); instead I formalized the genuinely provable finite-dim entropy
infrastructure as a new verified gallery entry. Depth-3 slug ⇒ no follow-up questions (guard).

### Built (new entry, 0-axiom/0-sorry, offline-verified EXIT 0)
`Proofs/CauchySchwarzOQ01OQ03OQ02.lean` (91L, ns `CauchySchwarzOQ01OQ03OQ02`):
- `shannonEntropy p := ∑ i, Real.negMulLog (p i)`;
- `shannonEntropy_nonneg` (entries in [0,1] ⇒ 0 ≤ H);
- `shannonEntropy_le_log_card` — **max-entropy bound** H(p) ≤ log n via
  `Real.concaveOn_negMulLog.le_map_sum` (Jensen, uniform weights 1/n) + `le_of_mul_le_mul_left`;
- `shannonEntropy_uniform` — uniform attains H = log n (sharp).
Plus gallery `meta.json` (status verified, badge mathlib, honest "toward entropic
uncertainty" framing). `pnpm build` enrichment ran over the entry with no schema error
(build later failed only at `tsc`/missing node_modules — worktree env, not data).

### Target (precise)
For an `n`-dimensional complex inner-product space with two orthonormal bases
`{aᵢ}`, `{bⱼ}` and a unit vector `ψ`, set the outcome distributions
`pᵢ = |⟨aᵢ, ψ⟩|²`, `qⱼ = |⟨bⱼ, ψ⟩|²` and the maximal overlap
`c = maxᵢⱼ |⟨aᵢ, bⱼ⟩|`. The **Maassen–Uffink (1988)** entropic uncertainty relation:

  H(p) + H(q) ≥ −2 ln c,    where  H(p) = Σᵢ negMulLog pᵢ = −Σᵢ pᵢ ln pᵢ.

Its precursor **Deutsch (1983)** gives the weaker (interpolation-free) bound
H(p) + H(q) ≥ −2 ln((1+c)/2).

### Mathlib inventory (pinned v4.26.0)
HAS (verified by grep of `.lake/packages/mathlib`):
- `negMulLog` and `Real.negMulLog` with `negMulLog_nonneg`, `concaveOn_negMulLog`,
  `strictConcaveOn_negMulLog` (`Analysis/SpecialFunctions/Log/NegMulLog.lean`).
- Jensen's inequality (`Analysis/Convex/Jensen.lean`), mean inequalities
  (`Analysis/MeanInequalities*.lean`), `L2Space`, and the Fourier transform *definition*
  (`Analysis/Fourier/FourierTransform.lean`).
- Complex Cauchy–Schwarz `abs_inner_le_norm` / `inner_mul_le_norm_mul_sq` (parent's basis).

LACKS (the blocker):
- **No Hausdorff–Young inequality, no Riesz–Thorin / Marcinkiewicz interpolation, no
  Lp→Lp' Fourier norm bound.** `grep -i "interpolat|RieszThorin|HausdorffYoung"` over all
  of Mathlib returns nothing. The sharp Maassen–Uffink constant `−2 ln c` follows from the
  (2 → ∞) operator norm of the overlap matrix, i.e. exactly a Riesz–Thorin interpolation
  argument. Building that is foundational (>1000 lines) — genuine BLOCK, not laziness.
- No general Shannon entropy of a probability vector / measure (`measureEntropy` absent);
  only the scalar `negMulLog`.

### Why BLOCKED (buildability assessed)
The sharp theorem is interpolation-gated. The honest classifications:
- **Sharp Maassen–Uffink**: BLOCKED (needs Hausdorff–Young ⇐ Riesz–Thorin; >1000 lines).
- **Deutsch's bound** `≥ −2 ln((1+c)/2)`: tractable in principle (variational/concavity
  argument, no interpolation) but still a substantial standalone formalization and itself
  nontrivial; a reasonable future DEEP-DIVE if someone first builds finite-dim entropy infra.

### Recommended tractable sub-target (for a future session)
Build finite-dimensional Shannon-entropy infrastructure from `negMulLog` first — it is the
reusable prerequisite for any version here and is fully provable with current Mathlib:
- `def shannonEntropy (p : Fin n → ℝ) : ℝ := ∑ i, Real.negMulLog (p i)`.
- `0 ≤ shannonEntropy p` (from `negMulLog_nonneg`, given `0 ≤ pᵢ ≤ 1`).
- `shannonEntropy p ≤ Real.log n` for a probability vector (Jensen on `concaveOn_negMulLog`
  — the maximum-entropy bound). This is the clean, verifiable "entropy" deliverable.
Only after that does Deutsch/Maassen–Uffink become approachable.

### Files Modified
- `proofs/Proofs/CauchySchwarzOQ01OQ03OQ02.lean` (new, verified 0-axiom/0-sorry)
- `src/data/proofs/cauchy-schwarz-oq-01-oq-03-oq-02/meta.json` (new gallery entry)

### Next Steps
- Either: upstream/await Hausdorff–Young in Mathlib, then formalize sharp Maassen–Uffink.
- Or: a future session builds the finite-dim `shannonEntropy` + max-entropy bound
  (provable now) as a sibling gallery entry, then attempts Deutsch's bound.

## Session 2026-06-27 (Session 3, researcher-9) — Gibbs ⇒ max-entropy bridge [VERIFIED, 0-axiom]

**Outcome**: BUILD. Added two theorems unifying the file's two halves (entropy ceiling
and Gibbs positivity), making the "Gibbs is the engine" docstring claim an actual proof.

### Built (added to `Proofs/CauchySchwarzOQ01OQ03OQ02.lean`, now 250L, 8 theorems)
- `klDivergence_uniform {p} (hsum : ∑ p i = 1) : D(p ‖ uniform) = log n − H(p)`.
  Pure algebra (no positivity needed): each KL summand
  `pᵢ(log pᵢ − log(1/n)) = pᵢ·log n − negMulLog pᵢ` (`Real.log_inv` + `Real.negMulLog`,
  `ring`); sum via `Finset.sum_sub_distrib`, `← Finset.sum_mul`, `hsum`, then `rfl`
  recognizes `∑ negMulLog (p i) = shannonEntropy p`.
- `shannonEntropy_le_log_card_of_gibbs [Nonempty ι] {p} (h0) (hsum)` : H(p) ≤ log n,
  **re-derived from Gibbs**: instantiate `klDivergence_nonneg` with `q = uniform`
  (hac trivial since `1/n > 0`), `rw [klDivergence_uniform hsum]`, `linarith`.
  Independent of the Jensen-based `shannonEntropy_le_log_card` — same bound, two routes.

### Verification
`lake env lean` on the worktree file: EXIT 0, no errors. `#print axioms` on both new
theorems = `[propext, Classical.choice, Quot.sound]` only (0 counting-axioms, no
`sorryAx`/`Lean.ofReduceBool`). meta.json bumped theoremCount 6→8, lineCount 211→250,
added `gibbs-bridge` section (211–249). status stays `verified`/`mathlib`/axiomCount 0.

### GOTCHA (cost me several build cycles)
Build commands MUST `cd` into the **worktree** proofs dir
(`.loom/worktrees/researcher-9/proofs`), NOT `/Users/rwalters/GitHub/lean-genius/proofs`
(the MAIN repo). I mistakenly built/`cp`-restored the main copy — which other agents were
concurrently editing — so my edits appeared to "vanish" and `#print axioms` reported the
new constants as *unknown* (it was checking a stale 211-line main file). The worktree
`proofs/.lake` is a symlink to main's `.lake`, so oleans resolve fine from the worktree.
Use a uniquely-named throwaway check file (`R9CSGibbsCheck.lean`) for `#print axioms`
rather than append/restore on the real file (avoids races with concurrent agents).

### Next Steps (unchanged)
- Deutsch's interpolation-free bound `H(p)+H(q) ≥ −2 ln((1+c)/2)` on top of this infra.
- Await Mathlib Hausdorff–Young/Riesz–Thorin for sharp Maassen–Uffink.
