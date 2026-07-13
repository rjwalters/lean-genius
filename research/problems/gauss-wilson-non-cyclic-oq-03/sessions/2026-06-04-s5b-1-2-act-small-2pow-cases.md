# S5b.1 + S5b.2 ACT — small power-of-2 unit-side counts (k = 1, k = 2)

**Slug**: `gauss-wilson-non-cyclic-oq-03`
**Iteration**: S5b.1 + S5b.2 (ACT, batched)
**Date**: 2026-06-04
**Researcher**: researcher-1
**Phase**: ACT
**Build**: pending (PR CI; researcher worktree `.lake` symlink loop
prevents local docker verification)
**Mathlib pin**: `inputRev v4.26.0`, lake-manifest rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

## 1. Summary

Implements the batched proposal from S5b PREP `#18648` (researcher-8,
2026-05-13, doc-only) for the two small even-prime-power cases.

Two new theorems added in a new Section 8 of
`proofs/Proofs/GaussWilsonNonCyclicOQ03.lean`:

| Theorem | Statement | Proof |
| ------- | --------- | ----- |
| `card_filter_sq_eq_one_units_zmod_two` | `#{u : (ZMod 2)ˣ | u² = 1} = 1` | `decide` |
| `card_filter_sq_eq_one_units_zmod_four` | `#{u : (ZMod 4)ˣ | u² = 1} = 2` | `decide` |

Both proofs are pure `decide`: the unit groups have decidable equality
and computable Fintype instances, so the filter cardinality reduces to
a concrete numeric equality at elaboration time.

**File delta**: 335 → 396 lines (+61). +2 theorems, +1 section header
docstring (~30 lines of explanation including the count table from
the S5b PREP and the mathematical rationale linking these to the
two-adic correction `ε₂(n) ∈ {0, 1}`).

**Sorry / axiom delta**: 0 / 0 (the main theorem
`card_sqrts_one_eq_numSqrtsOne` sorry is unchanged; this iteration
adds two fully-closed lemmas).

## 2. Why this batching

The S5b PREP §3.1 and §3.2 explicitly recommended batching S5b.1 and
S5b.2 into a single Lean PR (~25 LOC of Lean code, ~70 LOC total
including docstrings). This iteration follows that recommendation:

> S5b PREP §8 Recommendation 2: "S5b.1 ACT next session: trivial,
> can be batched with S5b.2 into a single Lean PR (~25 LOC total)."

The PREP also verified at the pinned Mathlib commit
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` that the necessary decls
exist (`isCyclic_units_two`, `isCyclic_units_four`,
`ZMod.card_units_eq_totient`), though for the `decide`-only route
adopted here, none of these decls are invoked by name — the proof is
fully automatic at elaboration time.

## 3. Choice of proof tactic — `decide` vs the S4 generic route

The PREP §3.2 sketched two alternative proofs for S5b.2 (`k = 2`):

* **A — S4 generic + IsCyclic**: instantiate the merged
  `card_filter_sq_eq_one_cyclic_even` at `(ZMod 4)ˣ`, providing the
  `IsCyclic (ZMod 4)ˣ` instance and the `2 ∣ Fintype.card (ZMod 4)ˣ`
  hypothesis. Estimated ~15-20 LOC.
* **B — pure `decide`**: rely on the computable Fintype instance.
  Estimated ≤ 5 LOC.

This ACT picks **B** for both `k = 1` and `k = 2`:

* For `k = 1`, the S4 generic theorem **does not apply** (the group
  has order 1, so `2 ∤ |G|`); a different argument would be needed.
  `decide` handles this trivially.
* For `k = 2`, `decide` is strictly simpler than the IsCyclic plumbing
  and equally robust at this small size.

The docstring on `card_filter_sq_eq_one_units_zmod_four` documents the
S4 generic alternative for reference, since it remains the canonical
mathematical justification (cyclic of even order → exactly 2 square
roots of 1).

## 4. Build verification status

**Local docker build**: NOT performed.

The researcher worktree `.lake` symlink is a self-loop — the same trap
documented in many prior sessions on this slug. Local
`./proofs/scripts/docker-build.sh Proofs.GaussWilsonNonCyclicOQ03`
cannot run from the worktree without manual setup that risks
clobbering the cache volume.

**PR CI**: will run on the merge commit. The two `decide` proofs are
the only Lean changes; everything else is documentation (Section 8
header docstring + the two theorem docstrings).

**Risk assessment**: low.

* `decide` on `(Finset.univ.filter (predicate)).card = constant` is a
  standard Lean idiom for finite types. The parent file
  `GaussWilsonNonCyclic.lean` uses the same pattern (lines 94-109)
  for natural-number computations.
* The Fintype instances for `(ZMod 2)ˣ` and `(ZMod 4)ˣ` are
  Mathlib-canonical (via `Units.instFintype` + `ZMod.instFintype`).
* The DecidableEq instance for ZMod n is canonical for `n ≥ 1`.

If `decide` unexpectedly times out at elaboration time, the immediate
fallback is `native_decide` (faster via compiled bytecode); if even
that fails, the S4 generic route remains available.

## 5. Race-safety

`gh pr list --search "gauss-wilson-non-cyclic-oq-03 in:title" --state open`
returns: (none — confirmed at iteration start).

No other open PRs on this slug; conflict-free.

The five sibling PREPs (`#18356`, `#18423`, `#18465`, `#18510`,
`#18597`, `#18648`) have all merged. This ACT is the **first Lean
change** on this slug since S5 ACT `#18233` (2026-05-12).

## 6. Estimated next-step LOC ledger (post-merge)

After S5b.1 + S5b.2 land:

| Sub-iter | Status | New theorems | Lean LOC delta |
| -------- | ------ | ------------ | -------------- |
| S5b.1    | **MERGED THIS PR** | +1 | +1 LOC of proof + ~25 LOC docstring |
| S5b.2    | **MERGED THIS PR** | +1 | +1 LOC of proof + ~30 LOC docstring |
| S5b.3    | next ACT (S5b PREP §3.3) | +1 + auxiliaries | ~60-90 LOC |
| S6       | after S5b.3 (S6 PREP) | CRT multiplicativity | ~80 LOC |
| S7       | after S6 (S7 PREP) | induction assembly | ~40 LOC |

**This PR alone closes 2 of 3 per-prime-power inputs** that S6 needs.

## 7. Honesty (§10 of researcher role)

* **No `lake build` performed**: the worktree `.lake` symlink loop
  precludes local docker build in this iteration. PR CI will verify.
* **Mathlib decl validity**: the PREP `#18648` audited each decl at
  the pinned commit, but this ACT does not invoke any of them by name
  — the `decide` route bypasses them. The risk surface is the
  computable Fintype + DecidableEq infrastructure for ZMod units,
  which is Mathlib-canonical and used throughout the repo.
* **No new mathematical content** beyond what the S5b PREP and S5b
  OBSERVE already laid out. This iteration is implementation work.
* **Section 8 header docstring** is the only original prose; it
  reproduces the count table and links it to the eventual `ε₂(n)`
  correction (already documented in `knowledge.md`).
