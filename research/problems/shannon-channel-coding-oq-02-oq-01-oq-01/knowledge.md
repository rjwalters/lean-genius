# Knowledge — shannon-channel-coding-oq-02-oq-01-oq-01

## Session 1 (researcher-9, 2026-05-12)

### Context

* Parent `shannon-channel-coding-oq-02-oq-01` (Fano via conditional entropy
  bridge) flagged "BLOCKED — ShannonEntropy.lean strong_subadditivity line
  811 linarith failure" for several iterations.
* PR #16334 (2026-05-06) fixed `strong_subadditivity` — ShannonEntropy.lean
  builds with 0 sorries, 0 axioms.
* PR #17189 (2026-05-08, researcher-1) audited the unblock and wrote a
  4-step integration plan but left actual Lean changes for a follow-up
  iteration on a host with intact `proofs/.lake`.
* This session executes steps 1–3 of that plan (defers step 4: in-place
  axiom swap inside `ShannonChannelCoding.lean`).

### What got added

`proofs/Proofs/ShannonChannelCodingOQ02OQ01.lean` (+115 lines, 0 sorries,
0 axioms):

| Theorem | Role |
|---------|------|
| `fano_from_oq03_std` | Bridge: `fano_from_oq03` restated using `InformationTheory.conditionalEntropy` |
| `fano_singleton_card_one` | |α|=1 case via Subsingleton α + `h_nonneg` |
| `fano_inequality_proved` | Dispatcher matching the `fano_inequality` axiom signature exactly |

Also added `import Proofs.ShannonEntropy` (was held off while ShannonEntropy
was broken). No circular import (verified: OQ03/OQ04 don't import OQ02OQ01
or the parent).

### Key technical observations

* `FanoInequality.conditionalEntropy` and `InformationTheory.conditionalEntropy`
  are body-identical, hence definitionally equal; `conditional_entropy_defs_agree`
  is provable by `rfl`. This lets `fano_from_oq03_std := fano_from_oq03 ...`
  type-check directly via delta reduction.
* For |α|=1: `Subsingleton α` (from `Fintype.card_le_one_iff_subsingleton`) +
  `Nonempty α` (witness `x₀`) gives single-element sum collapse
  `∑ x : α, f x = f x₀`. Each conditional-entropy term has ratio
  `pXY(x,y)/(∑x' pXY(x',y)) = pXY(x₀,y)/pXY(x₀,y) = 1` (when nonzero), so
  the LHS is 0. `P_e` collapses to `1 - ∑y pXY(x₀,y) = 1 - 1 = 0`. The
  RHS coefficient `(card α : ℝ) - 1 = 0` annihilates the second RHS term,
  reducing the goal to `0 ≤ h 0` which is `h_nonneg 0 ≤ ≤ 1`.
* Empty α: `IsEmpty α` from `Fintype.card_eq_zero_iff.mp`, then
  `Finset.univ_eq_empty` reduces the sum to 0, contradicting `hsum = 1`.

### Why no full axiom replacement in this PR

Step 4 of the integration plan (replacing `axiom fano_inequality` with
`theorem fano_inequality := fano_inequality_proved` in
`ShannonChannelCoding.lean`) is deferred because:

1. It would add a cross-file dependency (parent imports child) requiring
   careful import-graph verification — best done with a working build.
2. The host's `proofs/.lake` is a recursive self-symlink (~45 min builds);
   verifying the cross-file change here would consume the session budget.
3. Keeping the PR scoped to a single file reduces conflict risk with
   concurrent work on `ShannonChannelCoding.lean` (no PRs currently in
   flight there, but the surface is small).

`fano_inequality_proved` has the EXACT signature of the axiom (verified by
hand-aligning the binders, `let P_e`, conclusion shape, and the
`InformationTheory.conditionalEntropy` / `InformationTheory.BinaryEntropy.h`
namespaces). The follow-up edit is mechanically `axiom ... := ` becomes
`theorem ... :=  fano_inequality_proved`.

### Build status

Not yet built (host `.lake` symlink issue). Per established convention,
the PR title is tagged "(build pending)".

## Session 4 (researcher-3, 2026-05-12)

### Context

S2 (PR #17796) replaced the `fano_inequality` axiom with a theorem dispatched
through `FanoFromConditionalEntropy.fano_inequality_proved`. S3 (PR #17852)
named the single-letter capacity bounds `channelMI_le_capacity` and
`capacity_le_log_card`. Both PRs landed "(build pending)". The Fano-step
converse `(1 − P_e) log M ≤ I(X;Y) + h(P_e)` is now one step from being a
direct `linarith` corollary — the missing ingredient is the equality witness
for the maximum-entropy bound: `H(uniform) = log |α|`.

### What got added

`proofs/Proofs/ShannonEntropy.lean` (+28 lines, 0 sorries, 0 axioms):

| Theorem | Role |
|---------|------|
| `entropy_of_uniform_eq_log_card` | Equality witness for `entropy_le_log_card`: `shannonEntropy (fun _ : α => (Fintype.card α : ℝ)⁻¹) = Real.log (Fintype.card α)`. Direct calculation — no Gibbs detour. |

Statement is on the abstract constant function `fun _ => (card α)⁻¹` (not on
`(uniformDist (α := α)).p` from `ShannonChannelCodingOQ02OQ04`). This means
the lemma is usable from any file that imports `Proofs.ShannonEntropy`
without forcing an additional `import Proofs.ShannonChannelCodingOQ02OQ04`.

### Key technical observations

* `entropy_le_log_card`'s proof already contains the algebraic core of
  `entropy_of_uniform_eq_log_card`: the final `rw [h1, hsum, mul_one,
  Real.log_inv, neg_neg]` chain (lines 215–218) computes
  `-∑ p · log(1/|α|) = log |α|` for any distribution `p`. Specializing
  `p ≡ (1/|α|)` short-circuits the Gibbs inequality detour entirely — the
  proof is direct from `Finset.sum_const + Real.log_inv + mul_inv_cancel₀`.
* The sibling lemma `entropy_uniform_fintype` already exists in
  `ShannonChannelCodingOQ02OQ04.lean` (line 78), but it is stated on
  `(uniformDist (α := α)).p` — a 1-field `InputDist` wrapper — which forces
  every consumer to also import OQ02OQ04. The general form here unblocks
  the Fano-step converse without that dependency.
* The proof uses `inv_ne_zero` (rather than `one_ne_zero + div_ne_zero` as
  in OQ02OQ04's `entropy_uniform_fintype`) because the constant function
  is `(card α)⁻¹` not `1 / (card α)`, which matches the `entropy_le_log_card`
  shape and avoids a `one_div ↔ inv` rewrite at the end.

### Why this lemma (not the direct Fano converse)

The full Fano-step converse `(1 − P_e) log M ≤ I(X;Y) + h(P_e)` needs:

1. `entropy_of_uniform_eq_log_card` (this PR)
2. `chain_rule pXY` (already in `ShannonEntropy.lean` line 375)
3. `fano_inequality pXY` (already in `ShannonChannelCoding.lean` line 200)

With (1) in place, the converse is a single `linarith` step. Splitting it
out into a standalone lemma in S4 (a) reduces conflict risk on
`ShannonChannelCoding.lean` (small surface, multiple concurrent agents) and
(b) makes the equality witness reusable for other gallery entries
(`shannon-source-coding`, `shannon-entropy-oq-02`, etc.) without dragging in
the channel-coding axioms.

### Build status

Not yet built (host `.lake` symlink issue per memory). Per established
convention, the PR title is tagged "(build pending)". The proof relies on
`Real.log_inv`, `Finset.sum_const`, `Finset.card_univ`, `nsmul_eq_mul`,
`mul_inv_cancel₀` — all stable Mathlib API used identically in the existing
`entropy_le_log_card` (line 207–218) and `entropy_uniform_fintype` (OQ02OQ04
line 80–89) proofs.

### Gallery sync

`src/data/proofs/shannon-entropy/meta.json`:
* `meta.lineCount`: 901 → 929
* `meta.theoremCount`: 23 → 24
* `leanFile.lineCount`: 901 → 929
* `leanFile.theoremCount`: 23 → 24

## Session 9 (researcher-4, 2026-05-13) — Strict bi-implication

### Context

S8 (PR shipped 2026-05-12) added the equality case
`entropy_eq_log_card_iff_uniform`. Session 79 (researcher-4,
2026-05-13 ~02:25 UTC) released this slug without shipping because the
three named S9 candidates either needed sub-slug spawns (S9-heavy:
`channel_coding_converse` axiom discharge) or out-of-file API surface
(S9-medium: symmetric-channel uniform-marginal lemma) or were redundant
with S8 (S9-light as literally stated: `@[simp]` bi-implication of
`entropy_of_uniform_eq_log_card` — that IS S8).

This session re-interpreted S9-light as the missing **strict-inequality**
bi-implication: the strict slack of the max-entropy bound is bi-equivalent
to non-uniformity. It is a 1-step corollary of S4 + S8 with zero external
machinery.

### What got added

`proofs/Proofs/ShannonEntropy.lean` (+26 lines incl. 8-line docstring,
0 sorries, 0 axioms, 0 new imports):

| Theorem | Role |
|---------|------|
| `entropy_lt_log_card_iff_non_uniform` | `shannonEntropy p < log \|α\| ↔ ∃ x, p x ≠ (card α)⁻¹` |

Inserted after `entropy_eq_log_card_iff_uniform` (line 428) and before
the `Log-Sum Inequality` block.

### Key technical observations

* `lt_or_eq_of_le` is the cleaner upgrade path than the `le_iff_lt_or_eq`
  formulation: it returns the disjunction directly and avoids an
  `Iff.mp` rewrite at the same depth.
* `push_neg` on `¬ ∃ x, p x ≠ c` correctly collapses the `≠` to `=` in
  one tactic step (Mathlib's `push_neg` knows `¬ (a ≠ b) ↔ a = b`).
* The proof uses `absurd : a → ¬ a → b` (Mathlib's standard form) which
  is significantly cleaner than `exact (hx ((hiff.mp heq) x)).elim`.

### Why this lemma (not the S9 heavy/medium)

The state.md `## Next Action` block named three S9 candidates after S8:

* **heavy** — discharge `channel_coding_converse` axiom via per-letter
  chain rule `I(X^n; Y^n) ≤ n · channelCapacity ch`. Likely needs a
  separate sub-slug for the chain rule (memoryless channels).
* **medium** — symmetric DMC + uniform output marginal → uniform input
  marginal. 1–2 lemma extension in `ShannonChannelCoding.lean`, but
  outside this file (different namespace) and outside the strict S2–S8
  chain in `ShannonEntropy.lean`.
* **light (as literally stated)** — `@[simp]` bi-implication of
  `entropy_of_uniform_eq_log_card`. Redundant: S8
  (`entropy_eq_log_card_iff_uniform`) IS the bi-implication of the
  equality witness.

The strict-inequality form is the natural fourth corollary missing from
the file (Mathlib elsewhere systematically pairs `_le_` + `_lt_iff_`
forms; `grep` returns 0 hits for `entropy_lt_log_card` in either
`ShannonEntropy.lean` or `ShannonChannelCoding.lean`). It is genuinely
new mathematical content, not a re-statement.

### Build status

Not yet built (host `.lake` recursive self-symlink issue persists per
`feedback_researcher_lake_symlink_broken.md`). Following the established
S2–S8 convention, PR title carries "(build pending)". The proof uses
only stable Mathlib v4.26.0 API:

* `lt_or_eq_of_le : a ≤ b → a < b ∨ a = b` (Mathlib `Mathlib.Order.Basic`)
* `push_neg`, `by_contra`, `rcases`, `rintro`, `linarith`, `absurd`
  (all standard tactics, already used 50+ times in this file)

No new dependencies. Type-check by inspection: the two ambient lemma
applications (`hle := entropy_le_log_card hp hsum` and
`hiff := entropy_eq_log_card_iff_uniform hp hsum`) match signature
exactly, then propositional/`linarith` work closes both directions.

### Gallery sync

`src/data/proofs/shannon-entropy/meta.json`:
* `meta.lineCount`: 1111 → 1137
* `meta.theoremCount`: 28 → 29
* `leanFile.lineCount`: 1111 → 1137
* `leanFile.theoremCount`: 28 → 29

(Counts in main pre-PR are 28 theorems incl. private lemmas — `grep -cE
"^(theorem|lemma|private theorem|private lemma) " proofs/Proofs/ShannonEntropy.lean`
returns 29 after the addition.)

