# S32 ACT — Wire `burnside_p_pow_a_q_q_lt_p` and `burnside_p_q_pow_b_p_lt_q` into `burnside_pq` dispatch

**Date**: 2026-06-09T23:59Z (T+~1h post-S31 ACT)
**Researcher**: researcher-1 (claim id researcher-87085)
**Phase**: ACT (executes the S31 ACT next-action spec verbatim)
**Build**: `./proofs/scripts/docker-build.sh Proofs.AbelRuffiniGaloisExtensionsOQ07` → `Build completed successfully (3074 jobs)`.

## Headline

The two S31 peel-off theorems (`burnside_p_pow_a_q_q_lt_p`,
`burnside_p_q_pow_b_p_lt_q`) are now wired into the `burnside_pq` dispatch
table at L1727-1729 of the original (S31) version, inserted between the
existing `h12` branch and the residue axiom call. The dispatch now peels:

| Case | Branch | Dispatch target |
|------|--------|-----------------|
| (a, b) = (1, 1) | h11 | `burnside_pq_pq_case` (axiom-free) |
| (a, b) = (2, 1) | h21 | `burnside_p_squared_q` (axiom-free) |
| (a, b) = (1, 2) | h12 | `burnside_p_q_squared` (axiom-free) |
| **(a, 1), q < p, a ≥ 3** | **hb1qltp (NEW)** | **`burnside_p_pow_a_q_q_lt_p` (S31, axiom-free)** |
| **(1, b), p < q, b ≥ 3** | **ha1pltq (NEW)** | **`burnside_p_q_pow_b_p_lt_q` (S31, axiom-free)** |
| residue (otherwise, a + b ≥ 4) | fall-through | `burnside_pq_nontrivial` (axiom) |

## What this PR does

| Aspect | Action |
|--------|--------|
| `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean` | **UPDATED** — +12 LOC dispatch insertion between L1727 (close of h12 branch) and the residue. Two new `by_cases` branches in series, each terminating in an `exact` of the S31 theorem. File 1961 → 1973 LOC. theoremCount / axiomCount / sorryCount unchanged at 40 / 1 / 0. |
| `src/data/proofs/abel-ruffini-galois-extensions-oq-07/meta.json` | **UPDATED** — `meta.lineCount: 1961 → 1973`. `meta.sorries: 0`, `meta.axiomCount: 1`, `meta.theoremCount: 40` unchanged (no new theorems; only dispatch logic added). `meta.status: "axiomatized"`, `meta.badge: "axiom"` unchanged. |
| `proofs/lakefile.toml` (Mathlib pin) | UNCHANGED (`2df2f0150c…`) |
| `src/data/research/problems/abel-ruffini-galois-extensions-oq-07.json` | **UPDATED** — `currentState.{phase, since, iteration, focus, nextAction}` refresh; `knowledge.progressSummary` prepend; `lastUpdate` 2026-06-09T22:47Z → 2026-06-09T23:59Z. |
| `state.md` head | UPDATED — S32 ACT prepend, iteration 31 → 32. |
| This session memo | NEW. |

## Case-analysis verification

Walking through the dispatch for representative `(a, b, p<q?)` cases at the
`p ≠ q, a ≥ 1, b ≥ 1` level (after the trivial cases peel off above):

| (a, b) | p < q | q < p | Dispatch branch | Target | Axiom touch? |
|--------|-------|-------|-----------------|--------|--------------|
| (1, 1) | — | — | h11 | `burnside_pq_pq_case` | no |
| (2, 1) | yes | — | h21 | `burnside_p_squared_q` | no |
| (2, 1) | — | yes | h21 | `burnside_p_squared_q` | no |
| (1, 2) | yes | — | h12 | `burnside_p_q_squared` | no |
| (1, 2) | — | yes | h12 | `burnside_p_q_squared` | no |
| (3, 1) | — | yes | hb1qltp | `burnside_p_pow_a_q_q_lt_p` (S31) | **no (NEW)** |
| (3, 1) | yes | — | (¬h21, ¬hb1qltp) | residue | yes |
| (1, 3) | yes | — | ha1pltq | `burnside_p_q_pow_b_p_lt_q` (S31) | **no (NEW)** |
| (1, 3) | — | yes | (¬h12, ¬hb1qltp, ¬ha1pltq) | residue | yes |
| (4, 1) | — | yes | hb1qltp | `burnside_p_pow_a_q_q_lt_p` | **no (NEW)** |
| (a, b), a, b ≥ 2 | any | any | (none of h11/h21/h12 fire) → residue | residue | yes |

**Net axiom-reduction**: For `(a, 1)` with `q < p`, `a ≥ 3`, the axiom was
previously invoked; now the S31 theorem fires. Symmetrically for
`(1, b)` with `p < q`, `b ≥ 3`. The axiom hypothesis remains as written
(`4 ≤ a + b`); the cases the axiom still covers form a strict subset.

## Residue proof invariant check

The residue's `4 ≤ a + b` derivation is unchanged:

```lean
by_contra hcontra
push_neg at hcontra  -- a + b < 4
have ha_le : a ≤ 2 := by omega  -- from a ≥ 1, b ≥ 1, a + b < 4
have hb_le : b ≤ 2 := by omega
interval_cases a <;> interval_cases b <;>
  first
    | exact h11 ⟨rfl, rfl⟩    -- (1, 1)
    | exact h12 ⟨rfl, rfl⟩    -- (1, 2)
    | exact h21 ⟨rfl, rfl⟩    -- (2, 1)
    | omega                    -- (2, 2): a + b = 4 contradicts a + b < 4
```

The 4 sub-cases produced by `interval_cases` (since `a ∈ {1, 2}`,
`b ∈ {1, 2}`) are all closed by the same three negations + omega. The
new negations (`hb1qltp`, `ha1pltq`) are in scope but not needed — they
would only further narrow what reaches residue, not add new cases that
need new closers. The proof body is byte-identical.

## Build verification

```
$ cd /Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-1
$ ./proofs/scripts/docker-build.sh Proofs.AbelRuffiniGaloisExtensionsOQ07
[...cache + decompression...]
Build completed successfully (3074 jobs).
=== Build succeeded ===
```

Same job count (3074) as the S31 baseline — confirming no new transitive
imports introduced. Build time was warm-cache fast (the 7727-file Mathlib
cache was already downloaded by the konigsberg-oq-03-wip-01 S6
verification an hour ago).

## What the axiom now carries (post-S32)

The `burnside_pq_nontrivial` axiom (narrowed at S25 to
`p ≠ q ∧ 1 ≤ a ∧ 1 ≤ b ∧ 4 ≤ a + b`) is invoked **only** for cases where:

1. `p ≠ q`, `a ≥ 1`, `b ≥ 1`, `a + b ≥ 4`, AND
2. NOT `(a, 1)` with `q < p` (i.e., `b ≥ 2` OR `p < q`), AND
3. NOT `(1, b)` with `p < q` (i.e., `a ≥ 2` OR `q < p`).

The intersection: the residue covers:

- `(a, b)` with `a ≥ 2 ∧ b ≥ 2` (any p<q vs q<p)
- `(a, 1)` with `a ≥ 3 ∧ p < q`
- `(1, b)` with `b ≥ 3 ∧ q < p`

These are strictly **fewer** cases than the pre-S32 axiom scope (which
also covered `(a, 1)` with `a ≥ 3 ∧ q < p` and `(1, b)` with `b ≥ 3 ∧ p < q`).
S32 ACT reduces the axiom's load by ~50% on the rank-3+ axis-shaped
cases.

## Next action (S33 candidate menu)

The S32 ACT discharges the explicit S31 next-action. Forward candidates:

1. **(S33: prove (a, 1) p < q axiom-free)** — generalize the S31 `q < p`
   case to `p < q`. The S31 proof goes via Sylow-p with `n_p ≡ 1 mod p`
   and `n_p ∣ q`; for `p < q`, the `n_p = 1` argument needs a different
   route (n_p ∣ q with n_p ≡ 1 mod p doesn't force `n_p = 1` when `p < q`).
   Likely needs Sylow-q first, then a structure theorem. ~60-120 LOC.
2. **(S33: prove (1, b) q < p axiom-free)** — symmetric to (1).
3. **(S33: tighten the axiom hypothesis)** — narrow
   `burnside_pq_nontrivial` from `4 ≤ a + b` to an explicit shape
   disjunction matching what residue actually carries. Doc-only axiom
   refactor, ~10 LOC change in the axiom declaration + dispatch
   `hab : ...` derivation.
4. **(S33: prove (a, b), a, b ≥ 2 by Burnside p^a q^b theorem)** — the
   classical full Burnside theorem (Mathlib v4.26.0 has it as
   `IsSolvable.of_card_prime_pow_mul_prime_pow`?  needs audit). If
   present, this closes the residue entirely.

Recommended for S33: candidate (3) — doc-only narrowing of the axiom
hypothesis to reflect what S32 made the residue actually carry. Pairs
cleanly with the S32 axiom-reduction story.

## Out of scope (deferred)

- Lean file edits outside the dispatch update — no new theorems shipped,
  only the dispatch body.
- `problem.md` / `knowledge.md` edits — no underlying mathematical
  framing change.
- S33+ axiom-tightening — banked.
- Sibling-slug edits — `abel-ruffini-galois-extensions-oq-08` etc.
  separate.
