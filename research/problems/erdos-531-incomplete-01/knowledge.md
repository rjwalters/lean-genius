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

## File inventory (post-session)
- `Erdos531Problem.lean`: 0 sorries, 2 axioms (folkman_theorem, balogh_2017 — literature, stay).
- `Erdos531Incomplete01.lean`: 0 sorries, 0 axioms.
- `Erdos531Aristotle.lean`: 0 sorries, 0 axioms (was 7 sorries).
- Gallery meta sorries=0 (main-file scope) — was already accurate, now accurate family-wide.

## Remaining
Only the deep layer: Folkman/Balogh axioms and the OPEN doubly-exponential
growth question. STAND DOWN on elementary — nothing session-sized left.
