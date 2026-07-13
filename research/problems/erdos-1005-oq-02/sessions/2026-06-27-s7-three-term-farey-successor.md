# Session 2026-06-27 (s7) — §9: the three-term Farey successor (consecutiveness bridge)

**Researcher**: researcher-6
**Mode**: REVISIT (continuing depth on erdos-1005-oq-02)
**Phase**: FORMALIZED (verified successor recurrence; open constant remains open)
**Outcome**: progress (verified, 0-axiom — added §9, +6 theorems)

## What I Did

- Closed the explicit gap §8 left open. §8 showed *mediant* chains are similarly
  ordered but its own preamble flagged that those chains are **not consecutive**
  in `F_n` (e.g. `1/2, 1/3` are separated in `F_5`), and the open `1/12` constant
  is about runs of *consecutive* Farey fractions. §9 supplies the actual Farey
  successor.
- Formalized the classical three-term Farey neighbour recurrence (Hardy–Wright,
  *Theory of Numbers*, Thm 28–30): for consecutive `a/b < c/d` in `F_n` the next
  fraction is `e = k·c − a`, `f = k·d − b` with `k = ⌊(n+b)/d⌋`. Carried it in
  **addition form** `e+a=k·c`, `f+b=k·d` to avoid truncated ℕ subtraction.
- Six theorems, all 0-axiom (`#print axioms` = propext / Classical.choice /
  Quot.sound only):
  - `farey_succ_unimodular` — the step **preserves unimodularity**
    (`d·e = c·f + 1`); the successor is again a genuine Farey neighbour, so
    iterating walks along consecutive fractions.
  - `farey_succ_lt` — `c·f < d·e` (`c/d < e/f`).
  - `farey_three_term` — symmetric law `d·(a+e) = c·(b+f)`; the middle term is
    the exact `k`-section, the Farey form of `b_{k−1}+b_{k+1} = k·b_k`.
  - `farey_succ_denom_le_iff` — order-`n` cap `f ≤ n ↔ k·d ≤ n+b`.
  - `simOrd_succ_controlling` (**headline**) — a *consecutive* step `c/d → e/f`
    is similarly ordered **iff** `(a+c−k·c)·(b+d−k·d) ≥ 0`.
  - `simOrd_succ_k_eq_one` — the `k=1` step is always similarly ordered
    (product collapses to `a·b ≥ 0`).

## Key Findings

- **The recurrence preserves unimodularity** by a one-line
  `linear_combination d·he − c·hf + h` (after `zify`): `d·e − c·f = b·c − a·d = 1`
  is the residue of the three-term identity. So the Farey walk is closed —
  consecutiveness is now formal, not asserted.
- **The open problem is now an explicit arithmetic inequality.** Whether a
  consecutive step keeps similar ordering is exactly `(a+c−k·c)(b+d−k·d) ≥ 0`,
  controlled by the single successive quotient `k`. The `1/12`–`1/4` gap lives
  entirely in steps with `k ≥ 2`; every `k=1` step is free
  (`simOrd_succ_k_eq_one`, product `= a·b ≥ 0`).
- This reframes van Doorn's `(1/12−o(1))n` lower bound as a *density of `k=1`
  steps* statement — the natural next Lean target (a chained-successor run-length
  lemma).

## Gotchas Hit

- **Concurrent worktree reset wiped the file mid-session.** First Edit landed and
  compiled clean (EXIT=0), then a concurrent process reverted the worktree copy
  back to 638 lines (the known "worktree reset" gotcha). Recovered by creating a
  fresh branch `research/erdos-1005-oq-02-farey-successor` off `origin/main`,
  re-applying, and committing **immediately**.
- **Edited the MAIN-repo `state.md` by mistake** (shared path
  `research/problems/...` exists in both main repo and worktree). Reverted the
  main-repo edit; all changes belong in the worktree.
- `linear_combination` needs a ring → `zify` the ℕ `Unimodular` goal first.
- `linarith` *does* prove the equality `(e:ℤ) = k·c − a` from `(e:ℤ)+a = k·c`.

## Verification

- `lake env lean Proofs/Erdos1005ProblemOQ02.lean` → EXIT 0, no warnings
  (Docker image build is contended/unreliable under the shared host; used the
  `lake env lean` path against the main-repo Mathlib `.olean` cache, as in s5/s6).
- `#print axioms` on all six new theorems → only propext / Classical.choice /
  Quot.sound. 0 sorry / 0 axiom / no `native_decide`.

## Files Modified

- `proofs/Proofs/Erdos1005ProblemOQ02.lean` (638 → 745 lines, +§9, +6 theorems)
- `src/data/proofs/erdos-1005-oq-02/meta.json` (lineCount 745, theoremCount 45,
  +§9 section, +4 originalContributions)
- `research/problems/erdos-1005-oq-02/state.md` (Iteration 7, new Next Action)

## Next Steps

Chained-successor run-length lemma: a finite list of quotients all `= 1` yields a
consecutive Farey block that is step-wise similarly ordered, denominators `≤ n`
via `farey_succ_denom_le_iff`. Converts §9's single-step criterion into a
run-length statement — the last formal step before attacking the constant.
