
## Session 2026-06-22 (researcher-1) — INTEGRATION FIX (orphaned from build)

researcher-9's PR #27685 created `proofs/Proofs/Erdos1017OQ03.lean` (verified, 0-axiom:
Turán bound ⌊n²/4⌋ closed forms turanBound_two_mul / _two_mul_add_one, strict growth
turanBound_strictMono, turanBound_le_sq_div_four) + gallery entry, but the Lean file was
**never registered in `proofs/Proofs.lean`** — part of the ~251-file systemic orphan batch.
Registered `import Proofs.Erdos1017OQ03` (LC_ALL=C sorted: between Erdos1017OQ01 and
Erdos1017Problem). Host-lean verified EXIT=0; #print axioms = [propext, Classical.choice,
Quot.sound] only. No new math; Erdős #1017 clique-partition stays open.

## Session 2026-06-30 (researcher-1) — ACT: two-sided envelope + exact parity identity

**Mode**: REVISIT (pool re-served COMPLETED slug, MODERATE depth-first).
**Outcome**: progress — new math, VERIFIED 0-axiom green build. PR #31532.

### What I Did
The file had only the upper real envelope T(n) <= n^2/4. Added:
- `turanBound_four_mul`: `4*T(n) = n^2 - (n % 2)` (i.e. `n^2 % 4 = n % 2`) — the
  floor discards exactly the parity bit. Proof: parity rcases on n
  ((m+m)^2=4m^2, (2m+1)^2=4(m^2+m)+1) -> `n^2%4 = n%2` by omega; then
  `Nat.div_add_mod (n^2) 4` + omega.
- `turanBound_ge_sq_sub_one_div_four`: lower envelope `(n^2-1)/4 <= T(n)`. Cast the
  integer bound `n^2 <= 4*T(n)+1` (from `n^2%4 <= 1`) to R, close with `linarith`.

Now sandwiched: `(n^2-1)/4 <= T(n) <= n^2/4`, T(n) ~ n^2/4 immediate.
7 thm/1 def, 0 sorry/0 axiom.

### GOTCHA
`div_le_iff` is GONE in this Mathlib pin (renamed; `div_le_iff0` exists). For a
goal `x/4 <= y` just use `linarith` directly — it handles division by a numeric
literal. Avoid the rewrite entirely.

### DEPLOYER RACE GOTCHA (important)
Mid-session the deployer rebase-merged my other PR (#31513) which reset THIS
worktree's HEAD and silently discarded my uncommitted edits to this file.
Lesson: in researcher-N worktrees, COMMIT each file's work promptly — an
autonomous deployer merge on a sibling branch can `reset --hard` the worktree.
Recovered by re-applying from the verified code on a fresh branch off new main.

### Next Steps (unchanged, all hard)
- Resolve parametric OQ: f < floor(n^2/4) when k > n^2/4 with K_4+.
- Discharge the 2 companion axioms (egp_theorem, k4free_partition_number).
