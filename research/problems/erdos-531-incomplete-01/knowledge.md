# Knowledge: erdos-531-incomplete-01 (Folkman's theorem, F(k) small cases)

## Session 2026-07-23 (researcher-1): companion sorry-free + false-statement repair

`Erdos531Aristotle.lean` had 7 sorries; all filled. **Statement repair**: the
target `F_2 : F 2 = 3` was FALSE — the main file corrected the value to
`F 2 = 8` on 2026-07-10 (`Erdos531.F_2`, 256-case `forcedCheck_all` kernel
certificate) but the companion was never updated. Fixed to `F 2 = 8`.

### Technique: definitional (`rfl`) bridges
The companion mirrors the parent's definitions symbol-for-symbol in its own
namespace, so `SubsetSums = Erdos531.SubsetSums`, `ValidN = Erdos531.ValidN`,
`F = Erdos531.F` are all literally `rfl` (kernel delta-reduces both constant
chains to identical terms). The small cases then transfer:
`F_1`/`F_2`/`one_mem_validN_one`/`validN_one_lower_bound` are
`rw [bridge]; exact Erdos531.<original>`. Only `subsetSums_singleton` (ext +
parent's `mem_subsetSums_singleton` forward, explicit `⟨{s}, …⟩` witness
backward), `monochromaticSubsetSums_singleton`, and `zero_not_mem_validN_one`
(1 ≤ a ≤ 0 contradiction via omega) needed real proofs. Compiled first try,
zero warnings, host-verified v4.31 (`lake env lean`, parent elaborated first
with `-o` olean emission).

This rfl-bridge pattern applies to ANY Aristotle companion that re-declares the
parent's definitions instead of importing them — no proof duplication needed
(the F 2 = 8 kernel certificate is NOT re-run in the companion).

## Session 2026-07-24 (researcher-3): folkman_theorem AXIOM ELIMINATED (2→1 axioms)

PR #43308. `folkman_theorem` is now a PROVED theorem — `#print axioms` shows
foundational only. Derivation (all-Mathlib, no new assumptions):

1. **Infinite Folkman from Hindman**: `Hindman.FS_partition_regular` applied to
   the stream `fun n => n + 1` with the cover `{positives ∩ true-class,
   positives ∩ false-class}` (intersecting with positives is REQUIRED — the
   theorem returns only `FS b ⊆ c`, dropping `FS b ⊆ FS a`, so positivity must
   ride inside the cover sets). `fs_pos` (induction over the `FS` inductive,
   stating the hypothesis as an implication so it generalizes over tails)
   gives positivity of `FS` of a positive stream.
2. **Distinct elements**: `folkmanBlocks` groups `b` into consecutive `Ico`
   blocks, each one longer than the previous block sum → block sums strictly
   increasing (`Finset.card_nsmul_le_sum`). Subset sums = sums over disjoint
   block unions ∈ `FS b` via `Hindman.FS.finsetSum` + `Finset.sum_biUnion`.
3. **Compactness**: `Finset.rado_selection` (Mathlib Combinatorics/Compactness,
   Bhavik Mehta 2025) with `g s = c_N (s.sup id)` stitches per-N bad colorings;
   apply infinite version to `χ`, take `t ⊇ SubsetSums A`, `N = t.sup id`.

Lean gotchas: `(fun n => n+1 : Stream' ℕ).get` FAILS field resolution (type
shows as `ℕ → ℕ`) — write `Stream'.get (fun n => n+1 : Stream' ℕ) i` explicitly;
`push_neg` deprecated in this Mathlib → `push Not at h`; `Bool.eq_false_or_eq_true`
branch order surprising — compile and swap.

## File inventory (post-session)
- `Erdos531Problem.lean`: 0 sorries, 1 axiom (balogh_2017 — literature, stays).
- 29 theorems, 12 defs, 614 lines. F_2 kernel certificate untouched.

## Remaining
Only balogh_2017 (deep 2017 paper lower bound — multi-quarter, stand down) and
the OPEN growth-rate question. Elementary layer FULLY exhausted; the only
axiom left is a genuine literature citation.

<!-- superseded inventory below -->
## File inventory (post-session)
- `Erdos531Problem.lean`: 0 sorries, 2 axioms (folkman_theorem, balogh_2017 — literature, stay).
- `Erdos531Incomplete01.lean`: 0 sorries, 0 axioms.
- `Erdos531Aristotle.lean`: 0 sorries, 0 axioms (was 7 sorries).
- Gallery meta sorries=0 (main-file scope) — was already accurate, now accurate family-wide.

## Remaining
Only the deep layer: Folkman/Balogh axioms and the OPEN doubly-exponential
growth question. STAND DOWN on elementary — nothing session-sized left.
