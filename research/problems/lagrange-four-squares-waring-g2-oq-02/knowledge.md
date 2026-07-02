# Knowledge — lagrange-four-squares-waring-g2-oq-02

Open question: **"What is `G(k)` for `k ≥ 3`?"** (the *hard* Waring number).

## S1 (researcher-4, 2026-07-02) — ACT: elementary congruence lower bounds, 0-axiom

**Mode**: FRESH (EMPTY) · **Outcome**: new verified file
`proofs/Proofs/WaringGgLowerBoundsOQ02.lean` (183 L, 11 thm, 2 def, 0 axiom) +
full gallery entry. **Phase**: NEW → ACT/COMPLETED (lower-bound side).

### Problem framing (important — the two Waring numbers)

- `g(k)` (**easy**): least `s` with *every* `n` a sum of `s` `k`-th powers.
  Completely known; `g(k) = 2^k + ⌊(3/2)^k⌋ − 2`. Covered by the **parent** entry
  and **sibling OQ-01** (`…OQ01ExactValue.lean`, `…OQ01General.lean`).
- `G(k)` (**hard**): least `s` working for *all sufficiently large* `n`. **Open for
  almost all `k`.** Only `G(2)=4` (Lagrange) and `G(4)=16` (Davenport 1939) known
  exactly; `4 ≤ G(3) ≤ 7`. **This is what OQ-02 asks about.**

The exact value is genuinely open (a famous problem), so it is NOT provable. The
tractable, honest contribution is the classical **lower bounds via congruence
obstructions**, which this session formalizes end-to-end with no axioms.

### What was proved (all 0-axiom, kernel `decide` only — NOT native_decide)

- **`G(3) ≥ 4`** (`waringG_three_ge_four`): cubes are `≡ 0,±1 (mod 9)`, so
  `∀ a b c : ZMod 9, a³+b³+c³ ≠ 4` (`three_cubes_ne_four`, one-line `decide`).
  Any `n ≡ 4 (mod 9)` is not a sum of 3 cubes; `9N+4` gives arbitrarily large such
  `n`; padding monotonicity kills all `s ≤ 3`. This is the **sharp lower half** of
  `4 ≤ G(3) ≤ 7`.
- **`G(4) ≥ 15`** (`waringG_four_ge_fifteen`): fourth powers are `≡ 0,1 (mod 16)`
  (`fourth_pow_zmod16` by `decide`; sharpened to `a⁴ % 16 = a % 2`,
  `fourth_pow_mod16`). Via `Finset.sum_nat_mod`, a sum of `s ≤ 14` fourth powers
  reduces mod 16 to `∑ f i % 2` = #odd summands `≤ s ≤ 14 < 16`, so never `≡ 15`.
  `16N+15` gives large representatives. **One short of Davenport's `G(4)=16`.**
- Scaffold: `IsSumOfKthPowers s k n`, `UniversalForLarge s k` (least witness = `G(k)`),
  `isSumOfKthPowers_succ/_mono` (append 0^k, monotone in `s`),
  `natCast_zmod_of_modEq` (ModEq → ZMod cast helper).

### Recipe / reusable technique

**decide-then-cast obstruction pattern** for Waring lower bounds:
1. Pick modulus `m` where `k`-th powers occupy few residues; prove
   `∀ (vars) : ZMod m, ∑ vars^k ≠ r` (or the per-term membership) by `decide`.
2. Bridge to ℕ: `Fin.sum_univ_three` + `push_cast` (small `s`), or
   `Finset.sum_nat_mod` + a per-term `%`-lemma (large `s`, counting argument).
3. Infinitude: `mN + r` gives arbitrarily large members of the forbidden class;
   `Nat.ModEq` unfolds to `omega`.
4. Padding monotonicity turns "no `s ≤ B`" into "defeat `s = B`".
Generalises to `G(2^m) ≥ 2^{m+2}` (mod `2^{m+2}`), `G(3) ≥ 4` (mod 9), etc.

**ZMod numeral-cast fragility**: `push_cast [ZMod.natCast_self]` does NOT reliably
fire on numerals like `(9 : ZMod 9)`. Use `natCast_zmod_of_modEq` via
`ZMod.natCast_eq_natCast_iff` + `Nat.ModEq` (omega) instead — robust.

### Honesty / axiom accounting

`0` axioms, `0` sorries, `0` structure-encoded assumptions. `decide` is **kernel**
reduction over `ZMod 9`/`ZMod 16` (finite), so `Lean.ofReduceBool` is NOT incurred
(that would only apply to `native_decide`). Status = **verified / original**.
The bounds are lower bounds only; the matching upper bounds (`G(3) ≤ 7` Linnik,
`G(4) = 16` Davenport) are deep and deliberately NOT claimed here.

### Infra notes (2026-07-02, disk-pressure day)

- Host `lake env lean` **unusable**: concurrent docker builds mounting the shared
  main repo continuously **corrupt** `proofs/.lake/packages/mathlib/.lake/build`
  (`error: failed to read file '…/*.ir', invalid header`; segfault 139 / 0 bytes).
  A different `.ir` was corrupt on each retry → not fixable while others build.
- Fresh worktree's `.lake/packages/mathlib` git was **corrupt** ("could not resolve
  HEAD") → docker build there failed. Built instead via `docker-build.sh` from the
  **main** repo (valid mathlib git + `cache get` fetches clean oleans in-container).
- Real worktree created OUTSIDE repo tree at `/Users/rwalters/lg-r4-waring-oq02`
  with `--lock` (in-tree worktrees get reaped).

### Follow-ups generated (depth guard: slug depth = 1, OK)

1. General Maillet–Hurwitz `G(2^m) ≥ 2^{m+2}` for all `m ≥ 1` (unify the
   mod-`2^{m+2}` obstruction; this entry does `m=2` up to the one-off `+1` gap).
2. Sharpen to `G(4) ≥ 16` (the `s=15` case: a large `n ≡ 15 (mod 16)` cannot be
   fifteen odd fourth powers summing correctly), matching Davenport from below.
