# S27 ACT — S11b sound/complete decomposition: bridge sorry discharged

**Date**: 2026-07-24
**Agent**: researcher-2
**Mode**: REVISIT (RICH, score 62)
**Outcome**: `engelsmaSearchPruned_eq_false_iff` proved — file 1 → 0 sorries.

## What was proved (new S27 section, ~275 LOC)

1. `card_image_mod_lt_of_avoids` / `exists_avoided_residue_of_card_image_mod_lt`
   — the two converters between "H avoids a residue class mod p" and
   "|H.image (% p)| < p" (via `(Finset.range p).erase r` and
   `Finset.exists_mem_notMem_of_card_lt_card`).
2. `searchAux_sound` (S11b-β): search success at `(primes, candidates,
   chosen)` yields a k-element `H` with `chosen ⊆ H ⊆ chosen ∪ candidates`
   avoiding one residue class per remaining prime. Invariants:
   `(chosen ++ candidates).Nodup` (the S26 disjointness requirement) and
   `chosen.length ≤ k`. Leaf witness: `chosen ++ candidates.take (k - |chosen|)`.
3. `searchAux_complete` (S11b-γ): every such witness is found — at each
   prime the search tries the avoided residue `r`, `chosen` survives the
   filter intact (`List.filter_eq_self`), and `H` survives into the
   filtered pool.
4. `engelsmaSearchPruned_eq_true_iff` (S11b-δ): entry-point assembly at
   `primes = primesUpTo k`, `candidates = (range w).filter (≠ 0)`,
   `chosen = [0]`, using `entry_pool_nodup` / `entry_pool_toFinset` and the
   S11b-α combiner `IsAdmissible_iff_residue_disjoint_primesUpTo`.
5. `engelsmaSearchPruned_eq_false_iff`: negation of (4) — the sorried
   statement, now proved with the statement byte-identical (downstream
   consumer `engelsma_lower_bound_of_engelsmaSearchPruned_false` untouched).

## Key design points

- **No well-founded-recursion pain**: both invariants are proved by plain
  structural induction on the `primes` list (generalizing
  `candidates`/`chosen`), because `searchAux` only recurses on the tail of
  `primes`. The `termination_by` clause never surfaces in the proofs;
  `simp only [searchAux]` applies the equation lemmas cleanly.
- **The S26 lesson is encoded as `(chosen ++ candidates).Nodup`** — one
  hypothesis carrying both `chosen ∩ candidates = ∅` and internal
  distinctness. It is exactly what makes the leaf count
  `|chosen| + |take (k - |chosen|) candidates| = k` correct.
- The mathematical heart (why pruning by one residue per prime ≤ k is
  complete): a k-element set avoiding one residue class mod p for each
  prime p ≤ k has `|image| ≤ p - 1 < p` there, and `|image| ≤ k < p` for
  p > k — which is the α combiner's residue-disjoint reformulation of
  admissibility. Conversely an admissible H misses some residue mod each
  p ≤ k by counting (`|image| < p = |range p|`).
- `tryBranch`'s shrink-guard gives soundness for free: in the surviving
  branch `chosen.filter (· % p ≠ r)` has full length, and
  `Sublist.eq_of_length` upgrades that to `= chosen`, yielding the
  "prefix avoids r" fact both directions need.

## Lean notes

- `List.filter_eq_self : filter p l = l ↔ ∀ a ∈ l, p a = true` with the
  `decide`-coerced predicate — unwrap with `simpa`.
- `split at h` on `(if c then false else X) = true` + `Bool.noConfusion h`
  for the dead branch; `rename_i hns` to grab the inaccessible guard.
- `simp only [tryBranch] at htb` zeta-reduces the `let`s; the filter term
  then matches a `rw` with the same surface syntax.
- `omega` handles the `min` from `List.length_take` directly.

## Remaining (next sessions)

- **S12**: `engelsmaSearchPruned 246 50 = false := by native_decide` —
  the compute step consuming this bridge; eliminates the
  `engelsma_lower_bound` axiom (axiomCount 1 → 0 per S10b convention,
  `Lean.ofReduceBool` not counted per gallery convention, disclose it).
  Risk: native_decide wall-clock/memory at (246, 50) is untested; if
  infeasible, profile smaller (w, k) scaling first (deferred S7 datapoint
  (30, 10) is the natural probe).
- Optional: replace the remaining `native_decide` sanity tests with kernel
  `decide` where feasible (memory: kernel decide works on naive search).

## Verification

Host `lake env lean` + Docker build — see PR.
