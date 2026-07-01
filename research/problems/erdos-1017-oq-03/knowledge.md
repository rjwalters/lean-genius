
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

## Session 2026-06-30 (researcher-9) — ACT: algebraic structure of T (quarter-square + convexity)

**Mode**: FRESH (claimed graduated/COMPLETED slug, MODERATE depth-first).
**Outcome**: progress — 3 new VERIFIED 0-axiom theorems. Build green host-lean.

### What I Did
The file had closed forms + monotonicity + envelope but no *algebraic structure*.
Added (all over the re-declared `turanBound n = n^2/4`):
- `turanBound_quarter_square` (m n) (h : n ≤ m): `T(m+n) = T(m-n) + m*n`. The
  classical **quarter-square multiplication identity** `T(m+n) − T(m−n) = m·n`.
  Proof: `Nat.exists_eq_add_of_le` substitutes `m = n+d`, reducing to
  `T(2n+d) = T(d) + (n+d)*n`; then feed omega the two `turanBound_four_mul`
  facts, the ring identity `(2n+d)^2 = d^2 + 4*((n+d)*n)`, and the parity match
  `(2n+d)%2 = d%2`. omega treats the squares/product as opaque atoms linked
  linearly by the ring fact — division-by-4 done by omega.
- `turanBound_second_diff`: `T(n+2)+T(n) = 2*T(n+1) + (n+1)%2` (Δ²T = 1 at even
  n, 0 at odd n). Telescopes two `turanBound_succ_diff` calls.
- `turanBound_convex`: `2*T(n+1) ≤ T(n+2)+T(n)` — T is a convex integer seq.

### GOTCHAS
- omega sees `turanBound (n+2)` and `turanBound (n+1+1)` as DISTINCT atoms; the
  type-ascription `have hd2 : ... (n+2) ... := turanBound_succ_diff (n+1)` unifies
  them by defeq (n+1+1 ≡ n+2).
- Truncated Nat subtraction in `turanBound_succ_diff` lets omega posit
  `T(n) > T(n+1)` in the `(n+1)/2 = 0` (n=0) branch, breaking second_diff. Fix:
  feed explicit monotonicity `hle : T k ≤ T (k+1)` via
  `Nat.div_le_div_right (Nat.pow_le_pow_left (Nat.le_succ k) 2)`.

### Outcome / status
10 thm/1 def, 0 sorry/0 axiom (propext/Choice/Quot only). Erdős #1017
clique-partition core stays OPEN; this only enriches the extremal bound T.
