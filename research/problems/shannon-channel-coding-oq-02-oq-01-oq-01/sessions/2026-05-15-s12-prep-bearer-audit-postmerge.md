# S12 PREP — bearer audit + S12-light paste-ready skeleton + post-merge sequencing for #19061

**Author**: researcher-3
**Date**: 2026-05-15
**Type**: doc-only PREP (strictly conflict-free with PR #19061)
**Phase predecessor**: S11 ACT parent-file unblocker (PR #19061, researcher-8)

## 1. Coordination context

PR #19061 (S11 ACT parent-file unblocker, researcher-8, +148/-69) repairs
9 v4.26.0 surface regressions in `proofs/Proofs/ShannonEntropy.lean` and
is **Docker-verified `7743/7743 jobs`**. It is the gating prerequisite
for S12 candidates (light/medium/heavy) enumerated in `state.md`
§Next Action.

Status snapshot at session start (2026-05-15 ~04:10Z):

| PR | Title | mergeStateStatus | Open since | Stuck because |
|----|-------|-----------------|------------|---------------|
| #19061 | S11 ACT parent-file unblocker | CLEAN | 2026-05-14T14:25Z (~13.7h) | Deployer-stall (system-wide) |

System-wide signal: most-recent merge to `origin/main` is 2026-05-14T03:03:38Z
(PR #18980), giving a deployer dormancy of **~25.1 hours** at session start.
Per memory `feedback_researcher_deployer_stall_coordination_prep_pattern`,
this PREP ships a doc-only artifact to:

1. **Pre-stage** S12-light proof body so the next session is a ~1-iter
   Docker-verify rather than a fresh design+verify cycle once #19061 lands.
2. **Audit** Mathlib bearers for S12-light/medium at the lake-pinned SHA
   so the planned ACT does not snag on hidden v4.26.0 surface drift.
3. **Map** post-#19061 line shifts so the next session's ACT lands at
   the correct file offset without re-reading the entire repaired
   `ShannonEntropy.lean`.

This PREP follows decision-matrix entry "1 open MERGEABLE PR + deployer
stall → proceed with orthogonal+new content angle". The fresh angle is
"paste-ready S12-light skeleton + bearer/line-shift audit"; PR #19061
contributes neither.

## 2. Three S12 candidates (recap from state.md §Next Action)

| Variant | Statement | LOC budget | Bearer surface |
|---------|-----------|-----------|----------------|
| **S12-light** | `@[simp]`-style iff corollary of `entropy_of_uniform_eq_log_card`: `H(p) = log\|α\| ↔ p = (card α)⁻¹` (function-extensional form of S8) | ~5-10 LOC, 1 Docker iter | 0 new Mathlib bearers (uses S8 + `funext` + `congrFun`) |
| **S12-medium** | Symmetric-channel ⇒ capacity-achieving input uniform: if `ch` is symmetric and `inp` is capacity-achieving, then `∀ x, inp.p x = (card α)⁻¹` | ~30-60 LOC, 2-3 Docker iters | 1-2 new bearers: `Equiv.Perm` for row-permutation defn; existing channel API |
| **S12-heavy** | Discharge `channel_coding_converse` axiom (line 492, `ShannonChannelCoding.lean`): for `R > C`, error prob bounded below by some `δ > 0` for all sufficiently long codes | ~200-400 LOC, multi-session sub-slug | Per-letter chain rule for memoryless channels (likely new sub-slug `…-converse-chain-rule`) |

This PREP focuses concretely on **S12-light** (paste-ready) and sketches
**S12-medium**; S12-heavy is documented for completeness but is sub-slug-scope.

## 3. S12-light: paste-ready Lean skeleton

Insertion point: end of the "Maximum Entropy: Equality Case (Converse)"
section in `proofs/Proofs/ShannonEntropy.lean`, immediately after
`entropy_lt_log_card_iff_non_uniform` (origin/main line 454; identical
line number post-#19061 since #19061 touches lines 285, 408, 832-1085
only — see §5).

```lean
-- Function-extensional restatement of `entropy_eq_log_card_iff_uniform`:
-- H(p) = log|α| ↔ p IS (definitionally) the uniform distribution.
-- This is the equality-case strengthening of `entropy_of_uniform_eq_log_card`
-- (the one-direction equality witness): the maximum-entropy bound is
-- achieved iff `p` itself equals the constant function `fun _ => (card α)⁻¹`.
--
-- Useful downstream when the uniform-input hypothesis is a function-equality
-- (e.g., `inp.p = fun _ => …`) rather than a pointwise statement — sidesteps
-- a `funext` step at the call site. The pointwise form
-- `entropy_eq_log_card_iff_uniform` remains the primitive.
theorem entropy_eq_log_card_iff_eq_uniform {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] {p : α → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    shannonEntropy p = Real.log (Fintype.card α) ↔
    p = (fun _ : α => (Fintype.card α : ℝ)⁻¹) :=
  (entropy_eq_log_card_iff_uniform hp hsum).trans
    ⟨funext, fun h x => congrFun h x⟩
```

**Why this term-mode proof works at v4.26.0**:

* `entropy_eq_log_card_iff_uniform hp hsum : H(p) = log|α| ↔ ∀ x, p x = (card α)⁻¹`
  — this is line 379 of `ShannonEntropy.lean`, unaffected by #19061 (only
  the internal `rw` at line 408 changes; the signature is untouched).
* `Iff.trans : (P ↔ Q) → (Q ↔ R) → (P ↔ R)` — Lean core.
* `⟨funext, fun h x => congrFun h x⟩ : (∀ x, p x = q x) ↔ (p = q)`:
  - `funext : (∀ x, p x = q x) → p = q` — Lean core `Init.Core.lean:2238`
    at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Used already at
    `ShannonChannelCoding.lean:305, 309` (S6 body), so v4.26.0 surface is
    stable.
  - `congrFun : p = q → ∀ x, p x = q x` — Lean core primitive. The lambda
    `fun h x => congrFun h x` η-reduces to `congrFun` but is written
    explicitly for clarity.

**No `@[simp]` attribute**: the LHS `shannonEntropy p = Real.log (Fintype.card α)`
is a hypothesis-driven equation, not a normal-form rewriting target, so
adding `@[simp]` would risk simp-set bloat without payoff. The
`_iff_eq_uniform` suffix mirrors Mathlib's naming convention (cf.
`Finset.eq_singleton_iff_unique_mem` etc.).

**Optional one-liner alternative** (slightly tighter, equally robust):

```lean
theorem entropy_eq_log_card_iff_eq_uniform {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] {p : α → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    shannonEntropy p = Real.log (Fintype.card α) ↔
    p = (fun _ : α => (Fintype.card α : ℝ)⁻¹) := by
  rw [entropy_eq_log_card_iff_uniform hp hsum]
  exact ⟨funext, fun h x => congrFun h x⟩
```

Either form is acceptable; the term-mode version above is preferred for
zero-cost composition.

## 4. Mathlib bearer audit (lake SHA `2df2f015...`)

S12-light bearer table:

| Bearer | Origin | Status at v4.26.0 | Notes |
|--------|--------|-------------------|-------|
| `entropy_eq_log_card_iff_uniform` | `proofs/Proofs/ShannonEntropy.lean:379` | this-file (S8) | Signature unchanged by #19061; only line 408 body changes (`Real.log_div`/`Real.log_inv` swap → `Real.log_mul`). |
| `Iff.trans` | Lean core | stable | Standard, used 100+ times in repo. |
| `funext` | Lean core `Init/Core.lean:2238` (verified at SHA `2df2f015...`) | stable | Already used at `ShannonChannelCoding.lean:305, 309`; v4.26.0 surface stable. |
| `congrFun` | Lean core primitive | stable | Companion of `funext`. |

**Bearer count**: 0 new Mathlib imports; 0 new this-file dependencies
beyond the existing S8 chain. The `@[simp]` decision is deferred (not
added — see §3 rationale).

S12-medium bearer sketch (for ~30-60 LOC ACT):

| Bearer | Origin | Purpose |
|--------|--------|---------|
| Symmetric-channel definition | new `def` in `ShannonChannelCoding.lean` | `ch.W` rows are permutations of `ch.W default` (or equivalently: ∃ σ, ch.W x y = ch.W default (σ y)) |
| `entropy_eq_log_card_iff_eq_uniform` (S12-light, above) | from this PREP | Convert capacity-achievement to uniform-input equality |
| `mutual_info_symm` | `ShannonEntropy.lean:760` | I(X;Y) = I(Y;X) |
| `entropy_of_uniform_eq_log_card` | `ShannonEntropy.lean:233` | H(uniform) = log\|α\| |

**S12-medium hand-wave**: For a symmetric channel, the output marginal
`p_Y(y) = ∑ x, inp.p x · ch.W x y` is uniform when input is uniform (rows
sum-permute), so the conditional `H(Y|X)` is constant in the input
distribution. Capacity is then achieved when `H(Y)` is maximized, i.e.,
when output is uniform, which happens iff input is uniform (under
symmetry). The proof formalizes this in two steps: (a) define symmetric
channel via row-permutation; (b) show H(Y) is concave in `inp.p` with
unique maximum at uniform. Step (b) requires concavity of `shannonEntropy`
which is not currently in `ShannonEntropy.lean` — would be a useful
companion lemma, likely sub-slug.

## 5. Post-#19061 line-shift map for `ShannonEntropy.lean`

PR #19061 modifies 3 hunks (per `gh pr diff 19061`):

| Hunk | Origin/main lines | Post-#19061 effect | Net Δ |
|------|-------------------|---------------------|-------|
| Hunk A | 285 (`mul_lt_mul_left` → `mul_lt_mul_of_pos_left`) | Same line; bare-rewrite swap | 0 |
| Hunk B | 408 (`Real.log_div` + `Real.log_inv` → `Real.log_mul`) | Same line; single-line replacement | 0 |
| Hunk C | 832-1085 (extract `marginal_telescope` private lemma; refactor `strong_subadditivity` body) | Insert ~17 LOC for `marginal_telescope` at line 835; remove ~16-LOC `have htele` block from inside body; rework simp_rw chain at lines 962/1047; add canonicalization step at end | +36 net (`+82/-46`) |

**Anchors that DO NOT shift** (line numbers identical pre/post #19061):

| Theorem | Line | Used by |
|---------|------|---------|
| `entropy_le_log_card` | 195 | S4, S8, S9 |
| `entropy_of_uniform_eq_log_card` | 233 | S4 (witness for max-entropy) |
| `klDivergence_eq_zero_iff` | 310 | S8 |
| `entropy_eq_log_card_iff_uniform` | 379 | S8 (target bearer for S12-light) |
| `entropy_lt_log_card_iff_non_uniform` | 438 | S9 |
| `log_sum_inequality` | 463 | Available for future use |
| `mutual_info_nonneg` | 552 | S6/S7 |
| `chain_rule` | 611 | S5, S10 (`fano_converse_step` ingredient) |
| `conditioning_reduces_entropy` | 685 | Available |
| `mutual_info_symm` | 760 | S12-medium candidate |

**Anchors that SHIFT post-#19061**:

| Theorem | Pre-merge | Predicted post-merge | Confidence |
|---------|-----------|----------------------|------------|
| `strong_subadditivity` | 835 | ~852 | high (single +17 insertion at line 835) |
| Decls below `strong_subadditivity` end | varies | shift by net Δ = +36 | high |

**S12-light insertion point**: After `entropy_lt_log_card_iff_non_uniform`
ends at line 454, before the `============= Log-Sum Inequality =============`
section header at line 456. Insert 5-10 LOC; downstream decls (starting
at line 463 `log_sum_inequality`) shift by the insertion length. Both
pre-merge and post-merge anchors at this offset are identical (insertion
is above Hunk C).

## 6. Post-merge sequencing — three options

After PR #19061 lands, the following sequences are viable:

**Option A — S12-light only, single PR** (recommended for next session):
1. Wait for #19061 to merge.
2. Branch from new `main` (with `marginal_telescope` lemma present).
3. Apply S12-light skeleton from §3 verbatim. Insert at line ~454.
4. `./proofs/scripts/docker-build.sh Proofs.ShannonEntropy` — expect
   `7744/7744 jobs` clean (one extra job for the new theorem).
5. Update `state.md` § Active Approach + bump `Iteration: 11 → 12`.
6. Ship as **`S12 ACT — entropy_eq_log_card_iff_eq_uniform (build verified)`**.

Estimated cost: ~20-30 min, 1 Docker iter, +5-10 LOC.

**Option B — S12-light + S12-medium combined, single PR**:
1-4 as Option A.
5. Add symmetric-channel definition + 1-2 capacity-achieving lemmas (~30-60 LOC).
6. Docker-verify; expected 1-2 iters with v4.26.0 surface checks.
7. Ship combined.

Estimated cost: ~60-90 min, 2-3 Docker iters, +35-70 LOC.

**Option C — Sequential PREP+ACT for S12-medium symmetric-channel sub-question**:
1. Land Option A first (S12-light).
2. Separately PREP S12-medium definition design + concavity-of-entropy
   lemma audit. May spawn sub-slug `…-symmetric-channel-uniform-input`.
3. ACT on S12-medium.

**Recommendation**: **Option A** for the next session. S12-medium and
S12-heavy each warrant their own session given moderate-to-substantial
bearer-design surface (concavity of `shannonEntropy`, per-letter chain
rule). Bundling them risks scope creep + slower Docker turnaround.

## 7. Conflict-free guarantees with PR #19061 and other open PRs

This PREP touches **only one new file**:
`research/problems/shannon-channel-coding-oq-02-oq-01-oq-01/sessions/2026-05-15-s12-prep-bearer-audit-postmerge.md`.

PR #19061 modifies:
- `proofs/Proofs/ShannonEntropy.lean` ✗ this PREP does NOT touch
- `research/problems/shannon-channel-coding-oq-02-oq-01-oq-01/state.md` ✗ this PREP does NOT touch
- `src/data/research/problems/shannon-channel-coding-oq-02-oq-01-oq-01.json` ✗ this PREP does NOT touch

No other open PRs reference this slug (verified at session start via
`gh pr list -R rjwalters/lean-genius --search "shannon-channel-coding-oq-02-oq-01-oq-01 in:title" --state open` → 1 result, that being #19061).

**Merge safety**: This PREP can land before, after, or interleaved with
#19061 with zero conflict risk. If both are queued behind the stalled
deployer, the merge order does not matter.

## 8. Latent-bug surface check (negative result)

A scan of S2-S10 PR diffs for the same v4.26.0 trap patterns that
#19061 surfaced (specifically: `mul_lt_mul_left` → `mul_lt_mul_of_pos_left`,
`Real.log_div`/`Real.log_inv` → `Real.log_mul` re-direction, `have`-bound
universe-polymorphic lemmas, `Finset.single_le_sum` with implicit
function-argument metavariables, simp-rw rewrite-direction ordering)
across `proofs/Proofs/ShannonChannelCoding.lean` (S2-S10 entry points):

| Theorem | Pattern check | Result |
|---------|---------------|--------|
| `fano_inequality` (line 201) | `mul_lt_mul_left`? | No occurrence |
| `fano_converse_step` (line 236) | `Real.log_div`/`Real.log_inv` composite rewrite? | No occurrence (no log manipulation) |
| `fano_converse_capacity` (line 290) | `have`-bound universe-polymorphic helper? | No (uses `funext` + concrete `α`) |
| `fano_converse_shannon_form` (line 349) | implicit-`f`-arg `Finset.single_le_sum`? | No occurrence |
| `fano_converse_step_marginal` (line 395) | simp-rw inner-factor ordering? | No occurrence |
| `fano_converse_marginal` (line 438) | any of the above? | No occurrence |

**Conclusion**: S2-S10 entry points in `ShannonChannelCoding.lean` are
free of the specific v4.26.0 trap patterns that #19061 surfaced in
`ShannonEntropy.lean`. The end-to-end Docker verification of the S2-S10
chain (gated on #19061 merge) should pass without additional repair.
However, the file has not been Docker-built since its v4.26.0 toolchain
bump; an unrelated surface drift cannot be ruled out without a fresh
baseline. The next session's S12-light ACT will surface any such latent
issue as a build-side-effect at zero additional cost.

## 9. References

* PR #19061 (researcher-8, 2026-05-14): S11 ACT parent-file unblocker
  — `proofs/Proofs/ShannonEntropy.lean` v4.26.0 9-error kit.
* state.md § Next Action: S11-light / S11-medium / S11-heavy candidates
  (the file calls them "S11" but they all gate on the #19061 parent
  repair, so this PREP refers to them as **S12-***).
* Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0 lake-pinned).
* Lean core `Init/Core.lean:2238` for `funext` at v4.26.0.
* Memory: `feedback_researcher_deployer_stall_coordination_prep_pattern` —
  doc-only PREP during deployer stall when stuck PR is CLEAN MERGEABLE
  and would advance state.md "Next Action".

## 10. Acceptance signature

| Property | Value |
|----------|-------|
| New file count | 1 (`sessions/2026-05-15-s12-prep-bearer-audit-postmerge.md`) |
| Modified file count | 0 |
| Lean LOC delta | 0 (doc-only) |
| Docker build required | No |
| Conflict with PR #19061 | None (orthogonal file sets) |
| Conflict with main | None (new file, no prior path) |

End of S12 PREP.
