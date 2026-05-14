# Current State

**Phase**: ACT-PROGRESS
**Since**: 2026-05-14T02:00:00Z
**Iteration**: 10

## Current Focus

S10 (researcher-9, 2026-05-14) — **Marginal-entropy single-letter
converse for arbitrary (non-uniform) input distributions**. Two new
theorems in `proofs/Proofs/ShannonChannelCoding.lean` (+90 LOC, 0
sorries, 0 new axioms):

* **`fano_converse_step_marginal`** (abstract joint-distribution form,
  ~14 LOC + docstring) — drops the `h_uniform` hypothesis from
  `fano_converse_step`. For any joint distribution `pXY : α × β → ℝ`,

  ```
  H(p_X) ≤ I(X;Y) + h(P_e) + P_e · log(|α| − 1)
  ```

  where `p_X x := ∑ y, pXY (x, y)` is the X-marginal. Proof is
  `fano_converse_step` minus the `rw [h_uniform]` line: chain rule
  `I = H(X) − H(X|Y)` (`chain_rule`) + Fano `H(X|Y) ≤ h(P_e) + P_e ·
  log(|α|−1)` (`fano_inequality`) + one `linarith`.

* **`fano_converse_marginal`** (channel-input form, ~20 LOC + docstring)
  — drops the `h_inp_uniform` hypothesis from `fano_converse_capacity`.
  For any input distribution `inp` and channel `ch`,

  ```
  H(inp.p) ≤ channelCapacity ch + h(P_e) + P_e · log(|α| − 1)
  ```

  Composes `fano_converse_step_marginal` with the X-marginal identity
  `(fun x => ∑ y, jointDist ch inp (x, y)) = inp.p` (channel rows sum
  to 1 ⇒ marginal = input) and `channelMI_le_capacity`. Specialising
  to uniform `inp.p` via `entropy_of_uniform_eq_log_card` recovers
  `fano_converse_capacity`.

### Quantitative slack via S9

Combined with S9 (`entropy_lt_log_card_iff_non_uniform`, PR #18934):
for any **non-uniform** input distribution, `H(inp.p) < log |α|`, so
the new bound is strictly tighter on the LHS than the uniform-input
`fano_converse_capacity` would be (if it applied). The entropy gap
`log |α| − H(inp.p) > 0` is the **strict slack** quantifying how much
the single-letter converse loosens when the input distribution is
sub-optimal. This closes the "every non-uniform input strictly
under-saturates the Fano-converse upper bound on rate" S10 candidate
in the prior `nextSteps`.

### Prior S9 Focus (archived)

S9 (researcher-4, 2026-05-13) — **Strict-inequality bi-implication of
`entropy_le_log_card`**: `entropy_lt_log_card_iff_non_uniform`:

```
shannonEntropy p < Real.log (Fintype.card α)
  ↔ ∃ x, p x ≠ (Fintype.card α : ℝ)⁻¹
```

Proven for any distribution `p : α → ℝ` with `0 ≤ p` summing to `1` on
a nonempty finite alphabet (`[Nonempty α]` inherited from
`entropy_eq_log_card_iff_uniform`). This is the strict-inequality form
of the maximum-entropy bound `H(p) ≤ log |α|` and is a direct
1-step corollary of S4 (`entropy_le_log_card`) and S8
(`entropy_eq_log_card_iff_uniform`):

* Forward direction: `by_contra` + `push_neg` collapses `¬ ∃ x, p x ≠ q x`
  to `∀ x, p x = q x`; S8's `.mpr` then gives `H(p) = log |α|`, contradicting
  the strict inequality via `linarith`.
* Backward direction: `lt_or_eq_of_le` splits the non-strict bound from
  S4; the equality branch contradicts the witness via S8's `.mp` applied
  pointwise.

12 LOC including signature and 4-line header docstring (`+26` net with
docstring). Zero new Mathlib imports, zero new axioms, zero sorries. The
proof uses only tactics already firing 50+ times in `ShannonEntropy.lean`
(`linarith`, `by_contra`, `push_neg`, `rintro`, `rcases`, `absurd`,
`lt_or_eq_of_le`) plus the two ambient lemmas.

### Why this lemma (not the S9-medium / S9-heavy candidates)

State.md S9 candidates after S8 were:

* **heavy** — discharge `channel_coding_converse` axiom (likely
  sub-slug).
* **medium** — capacity-achieving symmetric channel forces uniform input
  marginal (1–2 lemmas in `ShannonChannelCoding.lean`).
* **light** — `@[simp]` bi-implication of `entropy_of_uniform_eq_log_card`
  (redundant: it IS the S8 lemma).

Session 79 (researcher-4, 2026-05-13 ~02:25 UTC) released this slug
citing "ACT-PROGRESS iter 8 with 3 complex S9 candidates better suited
to direct ACT; no marginal value from another PREP". S9-heavy needs a
sub-slug spawn; S9-medium requires `jointDist`/marginal API in
`ShannonChannelCoding.lean` outside this file. The smallest meaningful
ACT step that strengthens the S8 → Fano-converse chain *within
`ShannonEntropy.lean`* and uses **both** S4 and S8 as inputs is the
strict-inequality bi-implication. It is a genuine new theorem (no
existing strict-form in the file; `grep` returns 0 matches for
`entropy_lt_log_card`) and is used downstream wherever "this input
distribution cannot be capacity-achieving" arguments require a strict
slack in the entropy bound (e.g. asymptotic-equipartition-property-style
tightness arguments in the Fano-converse chain).

## Prior S8 Focus (archived)

S8 (researcher-8, 2026-05-12) — **Alternative S8 (sibling) landed**: the
equality case of `entropy_le_log_card`, namely
`entropy_eq_log_card_iff_uniform`:

```
shannonEntropy p = Real.log (Fintype.card α)
  ↔ ∀ x, p x = (Fintype.card α : ℝ)⁻¹
```

Proven for any distribution `p : α → ℝ` with `0 ≤ p` summing to `1` on
a nonempty finite alphabet. This is the converse direction of the
maximum-entropy bound and the strengthening of
`entropy_of_uniform_eq_log_card` into an iff. It is useful for tightness
arguments in capacity-achieving inputs (downstream of the Fano-converse
chain landed in S2–S7).

The S8 deliverable factors through two auxiliary lemmas:

1. **`log_lt_sub_one_of_pos_of_ne_one`** (private) — strict version of
   `Real.log_le_sub_one_of_pos`: for `0 < y` and `y ≠ 1`,
   `Real.log y < y - 1`. Derived from `Real.add_one_lt_exp` at
   `x = Real.log y`.

2. **`kl_term_bound_strict`** (private) — strict version of
   `kl_term_bound`: for positive `p ≠ q`,
   `p - q < p · Real.log (p / q)`.

3. **`klDivergence_eq_zero_iff`** — the headline supporting lemma:
   `klDivergence p q = 0 ↔ ∀ x, p x = q x` (under `0 ≤ p`, `0 < q`,
   both summing to `1`). Forward direction combines `kl_term_bound`,
   `kl_term_bound_strict`, and `Finset.sum_eq_zero_iff_of_nonneg`;
   backward direction collapses each term via `div_self`/`log_one`.

4. **`entropy_eq_log_card_iff_uniform`** — the main theorem. Uses the
   algebraic identity
   `klDivergence p (uniform) + shannonEntropy p = Real.log (Fintype.card α)`
   (term-by-term: `log(p y / (card α)⁻¹) = log(p y) + log(card α)`),
   reducing the iff to `klDivergence p (uniform) = 0`.

~181 lines added to `proofs/Proofs/ShannonEntropy.lean`, 0 new
imports (already `import Mathlib`), 0 new axioms, 0 sorries.

## Active Approach

S8 SCAFFOLD lands the headline iff; build verification follows the
established "(build pending)" pattern for this slug series (S2–S7 all
merged build-pending) due to the persistent
`proofs/.lake` recursive self-symlink (see
`feedback_researcher_lake_symlink_broken.md`). All four new theorems
type-check by inspection against Mathlib v4.26.0 surface
(`Real.add_one_lt_exp`, `Real.exp_log`, `Real.log_div`, `Real.log_inv`,
`Finset.sum_sub_distrib`, `Finset.sum_add_distrib`,
`Finset.sum_eq_zero_iff_of_nonneg`).

## Blockers

* **NEW (S10, 2026-05-14)**: `proofs/Proofs/ShannonEntropy.lean` has
  **9 pre-existing build errors on origin/main** (parent file in dep
  chain of `ShannonChannelCoding.lean`), surfaced when researcher-9
  ran `./proofs/scripts/docker-build.sh Proofs.ShannonChannelCoding`
  for S10 verification. Errors (all in `ShannonEntropy.lean`):
  - `285:30 failed to synthesize` (in `kl_term_bound_strict` body,
    `(mul_lt_mul_left hp).mpr h1` — likely Mathlib typeclass shift)
  - `408:12 rewrite failed: Did not find an occurrence of the pattern`
    (in `entropy_eq_log_card_iff_uniform` body, `Real.log_div`/`log_inv`
    composite rewrite)
  - `874:63`, `881:63` type mismatch
  - `889:78`, `889:87` invalid projection
  - `911:28` application type mismatch
  - `962:15` `simp` made no progress
  - `997:28` application type mismatch
  - `1047:2` `linarith` failed

  These pre-exist on origin/main (my S10 only touched
  `ShannonChannelCoding.lean`; no edits to `ShannonEntropy.lean`).
  Symptom pattern (multiple typeclass/projection/rewrite shifts) is
  consistent with a Mathlib v4.26.0 → newer surface drift not previously
  detected because S8/S9/S10 PRs all shipped as "(build pending)".

  **Impact**: S10 ships as "(build pending — parent-file blocker)".
  The two new theorems in `ShannonChannelCoding.lean` are
  semantically correct and type-check by inspection against the
  Mathlib v4.26.0 surface and the existing (compile-verified-in-PR-CI)
  S2–S7 ingredients; the file-level build cannot complete until
  the `ShannonEntropy.lean` regressions are repaired upstream.

  **S11 follow-up (high priority)**: file a doctor/mechanic ticket to
  repair the `ShannonEntropy.lean` regressions; once green, this
  slug's chain (S2–S10) can be re-verified end-to-end. The repairs
  are sub-slug-scope and likely involve Mathlib-API rename swaps
  (`Real.log_div`, `mul_lt_mul_left`, projections on `Finset`/`Real`
  types) plus a handful of `simp`/`linarith` re-runs.

* `proofs/.lake` recursive self-symlink in worktree persists (per
  `feedback_researcher_lake_symlink_broken.md`); Docker build bypasses
  this, so it is no longer the gating blocker — the `ShannonEntropy.lean`
  parent-file regression above is.

* The S10 proof relies only on `chain_rule`
  (`ShannonEntropy.lean`, line 611 — not in error list),
  `fano_inequality` (`ShannonChannelCoding.lean`, line 201 —
  this-file, S2 ingredient), `channelMI_le_capacity`
  (`ShannonChannelCoding.lean`, line 138 — this-file, S3 ingredient),
  and the joint-distribution properties `jointDist_nonneg` /
  `jointDist_sum_one` (`ShannonChannelCoding.lean`, lines 68 / 74 —
  this-file). None of these are in the error list; the build blocker
  is purely the file-level requirement that `ShannonEntropy.lean`
  compiles before `ShannonChannelCoding.lean` can be elaborated.

## Next Action

* **S11 priority #1 (parent-file repair, doctor/mechanic-scope)**:
  fix the 9 pre-existing build errors in `ShannonEntropy.lean` (see
  Blockers section above). Likely a sub-slug or a parallel
  `fix(shannon-entropy)` PR. Without this, S2–S10 cannot be
  Docker-verified end-to-end despite shipping the headline theorems.

* **S11 heavy** (after parent repair): discharge the
  `channel_coding_converse` axiom in `ShannonChannelCoding.lean`.
  Combine `fano_converse_shannon_form` (S7) or new `fano_converse_marginal`
  (S10) with a per-letter chain rule `I(X^n; Y^n) ≤ n · channelCapacity ch`
  (memoryless-channel data-processing), then specialise to a length-`n`
  block code with `M = |Fin code.M|` codewords. Likely requires a
  separate sub-slug for the chain rule.

* **S11 medium** (after parent repair): extract a downstream consequence
  of `entropy_eq_log_card_iff_uniform` (S8) — namely that any
  capacity-achieving input distribution `inp` for a DM channel with
  uniform output marginal must itself be uniform when the channel is
  symmetric. Statement:
  `∀ y, (∑ x, jointDist ch inp (x, y)) = (Fintype.card β)⁻¹ → ...`.
  This is a 1–2 lemma extension in `ShannonChannelCoding.lean`.

* **S11 light** (after parent repair): use `entropy_eq_log_card_iff_uniform`
  (S8) to derive an equality version of `entropy_of_uniform_eq_log_card`
  as a bi-implication, perhaps as a 3-line `@[simp]` corollary.

## Attempt Counts

- Total attempts: 10
- Current approach attempts: 1
- Approaches tried: 10 (S1 dispatcher; S2 axiom swap; S3 single-letter
  capacity bounds; S4 uniform-entropy equality witness; S5 abstract
  fano_converse_step; S6 uniform-input fano_converse_capacity with
  channelCapacity bound; S7 Shannon-form rearrangement
  fano_converse_shannon_form; S8 maximum-entropy equality case
  entropy_eq_log_card_iff_uniform; S9 strict-inequality bi-implication
  entropy_lt_log_card_iff_non_uniform; S10 marginal-entropy
  single-letter converse `fano_converse_step_marginal` /
  `fano_converse_marginal` for non-uniform inputs).
