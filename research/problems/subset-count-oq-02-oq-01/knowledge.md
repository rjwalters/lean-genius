# subset-count-oq-02-oq-01 — Distinct Submultiset Count ∏(mᵢ + 1)

## Problem Summary

Open question: *Can the DISTINCT submultiset count `∏ a ∈ s.toFinset, (s.count a + 1)`
be formalized in Lean using Mathlib's `Multiset.toFinset` and multiplicity counting?*

This is the deduplicated companion to `multiset_powerset_card` (in `SubsetCountOQ02.lean`),
which counts submultisets **with multiplicity** and gives `2 ^ s.card`. The distinct count
collapses repeated occurrences: a multiset where value `a` appears `mᵢ` times contributes a
factor `(mᵢ + 1)` (choose 0, 1, …, mᵢ copies), so the number of *distinct* submultisets is
`∏ (mᵢ + 1)`, not `2 ^ n`.

Worked example: `{a,a,b}` has distinct submultisets `{}, {a}, {a,a}, {b}, {a,b}, {a,a,b}` =
6 = (2+1)(1+1). ✓

## Status: SOLVED (build-unverified)

A complete formalization already exists at `proofs/Proofs/SubsetCountOQ02OQ01.lean`
(namespace `SubsetCountDistinct`, wired into the build at `Proofs.lean:2834`). It reports
**0 sorries, 0 axioms, 10 theorems**.

## Key Findings

- **Answer is YES, and the proof is one line.** The formula is exactly Mathlib's
  `Multiset.card_Iic`:
  ```
  Multiset.card_Iic [DecidableEq α] (s : Multiset α) :
      (Finset.Iic s).card = ∏ i ∈ s.toFinset, (s.count i + 1)
  ```
  Here `Finset.Iic s = {t : Multiset α | t ≤ s}` is precisely the finset of distinct
  submultisets. The gallery theorem `distinct_submultisets_count` is `:= Multiset.card_Iic s`.
- Mathlib derives `card_Iic` from the `LocallyFiniteOrder (Multiset α)` instance, ultimately
  via `DFinsupp.card_Icc` and the `Multiset ≃ (α →₀ ℕ)`-style support correspondence.
- The existing file goes beyond the bare formula and also proves: empty/singleton/replicate
  instances, the set-case specialization `distinct_submultisets_nodup` (`2 ^ s.card` when
  `s.Nodup`), `native_decide` numeric checks, and **multiplicativity over disjoint support**
  (`distinct_submultisets_disjoint`). This is a genuinely complete, polished entry.

## Tracker Discrepancy Fixed This Session

The research-pool status was stale-`available`, which kept a fully-solved problem in the
claimable pool (risk of duplicate-claim churn — cf. the euler-totient-oq-04-oq-01
already-proved incident). Flipped to `completed` and populated knowledge fields.

## Build Verification Caveat

Could **not** run `lake build` this session: Docker daemon is down (verification blackout,
2026-06-13) and Mathlib is not vendored in this worktree's `.lake`, so `Multiset.card_Iic`
could not be grep-confirmed locally. The proof rests entirely on that single Mathlib lemma,
which is a real declaration in `Mathlib/Order/Interval/Finset/Multiset.lean`. The gallery
meta `status`/`badge` were left `null` (NOT promoted to `verified`) — promote only after a
Docker build confirms the file compiles clean.

## Next Steps

1. When Docker is restored: `./proofs/scripts/docker-build.sh Proofs.SubsetCountOQ02OQ01`.
2. If it compiles: set gallery `src/data/proofs/subset-count-oq-02-oq-01/meta.json`
   `status="verified"`, `badge="verified"`, `axiomCount=0`.
3. No further mathematical work needed — the open question is resolved.

## Session Log

### 2026-06-13 (Session 1) — SURVEY / status-sync (researcher-5)

**Mode**: FRESH · **Outcome**: solved-already (recorded), tracker corrected

- Claimed stale-`available` problem; grepped `proofs/Proofs/` and found the open question
  already fully formalized via `Multiset.card_Iic`.
- Confirmed the proof file is build-wired (`Proofs.lean:2834`) and reports 0 sorry / 0 axiom.
- Could not build-verify (Docker down). Recorded findings, flipped research status
  `available → completed`, left gallery verified-promotion pending a build.
