# Current State

**Phase**: FORMALIZED (verified infrastructure; open problem itself remains open)
**Since**: 2026-06-25
**Iteration**: 14

## Current Focus

Formalized the exact arithmetic of mediant insertion on Farey gaps:
`proofs/Proofs/Erdos1005ProblemOQ02.lean` (389 lines, 24 theorems, 1 def,
0 sorries, 0 axioms; #print axioms reports only propext / Classical.choice /
Quot.sound).

## Active Approach

Two verified threads:
1. **Gap-splitting calculus** — a unimodular gap `1/(bd)` splits under its
   mediant into `1/(b(b+d))` and `1/(d(b+d))`; these sum back to `1/(bd)`,
   stand in ratio `d:b`, and each is strictly smaller than the whole. Each
   half is again unimodular (recursive Stern–Brocot insertion).
2. **Minimal-denominator theorem (headline)** — every fraction `p/q` strictly
   between two unimodular neighbours `a/b < c/d` has `q ≥ b+d`, with equality
   forcing `p/q = (a+c)/(b+d)`. The mediant is the unique smallest-denominator
   fraction in the gap; `b+d` is a hard lower bound on any refinement.

## Blockers

The actual open question — improving the lower bound `f(n) ≥ (1/12 − o(1))n`
on the longest run of *similarly ordered* Farey fractions — is **not**
addressed. That constant `c ∈ [1/12, 1/4]` remains open. This session
formalizes the verified mediant calculus that such constructions rest on, not
a resolution of the bound.

## Iteration 3 addition (verified)

Added **§5 (strict denominator growth + depth-two refinement)**, 0-sorry /
0-axiom: `interior_denom_gt_max` (every in-gap fraction has denominator
> max(b,d) — refinement strictly raises the smallest denominator);
`denom_ge_left_subgap`/`denom_ge_right_subgap` (each sub-gap is again
unimodular, giving depth-two bounds q ≥ 2b+d, q ≥ b+2d); and the headline
`denom_ge_of_between_ne_mediant` — the mediant is the *unique* denominator-(b+d)
point, and the next admissible denominator jumps by ≥ min(b,d). This is the
strict-growth step the counting argument rests on; the 1/12 run constant itself
remains open.

## Iteration 4 addition (design/knowledge — build host down)

Recorded `sessions/2026-06-27-s4-counting-roadmap-and-literature.md`: pins the
literature to **van Doorn 2025, arXiv:2509.00121** (lower `(1/12−o(1))n`,
explicit upper `n/4 + 5`, sharpening the parent knowledge.md's `n/4 + O(1)`),
maps each verified lemma (minimal-denominator `q ≥ b+d`, strict growth, depth-
two `q ≥ 2b+d` / `b+2d`) onto a counting-argument roadmap, and fixes the precise
next Lean target: a **depth-`k` Fibonacci denominator bound** (0-axiom
induction over nested mediant insertions ⇒ `O(log_φ n)` refinement depth under
the order-`n` cap). No Lean change this cycle: Docker build host data volume is
100% full (containerd meta.db I/O error; `docker-build.sh` false-exits 0), so
an unverified inductive proof would risk the file's clean 0-axiom status.

## Iteration 5 addition (verified, 0-axiom — build host still down, used `lake env lean`)

Added **§6 (iterated one-sided insertion — exact linear denominator growth)**,
0-sorry / 0-axiom (verified by `lake env lean` against the main-repo Mathlib
`.olean` cache; Docker still unusable). Five theorems:
`unimodular_iterate_left`/`_right` (k-fold one-sided insertion stays unimodular,
`a/b < (k·a+c)/(k·b+d)`, by scale-invariance of `bc=ad+1` — no induction);
`denom_ge_iterate_left`/`_right` (depth-`k` interior denominator bound
`q ≥ (k+1)·b+d`); `iterate_left_denom_linear` (the exact `(k+1)·b+d`).

**Key correction.** The Iteration-4 "depth-`k` Fibonacci ⇒ `O(log n)` refinement
depth" target was **mathematically wrong as a universal claim**: the one-sided
chain `0/1, 1/2, 1/3, …, 1/n` has only LINEAR denominator growth and fits
`Θ(n)` refinement levels under the order-`n` cap. Exponential `φ^k` growth (hence
`O(log n)` depth) is special to *balanced/alternating* chains — the opposite
extreme from this linear worst case. §6 formalizes the linear extreme and the
file/meta now record the correction. A sharp run-length count toward `1/12` must
distinguish the two extremes.

## Iteration 6 addition (verified, 0-axiom — Docker still down, used `lake env lean`)

Added **§8 (mediant chains are similarly ordered — the bridge to f(n))**,
0-sorry / 0-axiom (verified via `lake env lean` against the main-repo Mathlib
`.olean` cache; Docker image build still fails with the containerd `meta.db`
I/O error). This is the **first link in the file between the metric mediant
calculus (§1–7) and the ordering relation that defines the problem.** Eight
theorems + one definition:

- `SimOrd a b c d` — raw-integer form of `similarlyOrdered`
  (`Erdos1005ProblemProvable.lean`): numerator and denominator differences share
  a weak sign. `simOrd_iff_prod` proves it `↔ (a−c)(b−d) ≥ 0`; `simOrd_symm`,
  `simOrd_refl`.
- `simOrd_mediant_left` / `_right` — the mediant `(a+c)/(b+d)` is similarly
  ordered with **both** parents (insertion never breaks similar ordering).
- `simOrd_iterate_left_chain` / `_right_chain` (headline) — the **entire**
  one-sided §6 chain `eₖ = (k·a+c)/(k·b+d)` is **pairwise** similarly ordered.
  So the Θ(n)-long one-sided chain is a similarly ordered family — the order-side
  engine of the linear lower bound on `f(n)`.
- `simOrd_chain_admissible` — packages the above with the §6 cap: under
  `k·b+d ≤ n` the depth-≤k terms are pairwise similarly ordered and of order ≤ n.

**Honest boundary recorded in the section preamble:** chain members are *not*
consecutive in `F_n` (e.g. `1/2, 1/3` separated in `F_5`), so this does **not**
prove `f(n) ≳ n`. Supplying consecutiveness is exactly the open `1/12`–`1/4`
step.

## Iteration 7 addition (verified, 0-axiom — `lake env lean`, Docker contended)

Added **§9 (the three-term Farey neighbour recurrence — the consecutiveness
bridge)**, 0-sorry / 0-axiom (verified by `lake env lean` against the main-repo
Mathlib `.olean` cache; `#print axioms` reports only propext / Classical.choice /
Quot.sound on every new theorem). This **closes the §8 honest gap**: §8's
mediant chains were similarly ordered but *not consecutive* in `F_n`; §9 uses the
actual Farey successor `e = k·c − a`, `f = k·d − b` with `k = ⌊(n+b)/d⌋`
(Hardy–Wright Thm 28–30), carried in addition form `e+a=k·c`, `f+b=k·d`. Six
theorems:

- `farey_succ_unimodular` — the recurrence **preserves unimodularity**
  (`d·e = c·f + 1`), so `c/d, e/f` are again *consecutive*: iterating walks along
  genuinely adjacent Farey fractions (`linear_combination d·he − c·hf + h` after
  `zify`).
- `farey_succ_lt` — `c·f < d·e` (the successor lies strictly to the right).
- `farey_three_term` — symmetric law `d·(a+e) = c·(b+f)`: the middle term is the
  exact `k`-section, the Farey form of `b_{k−1}+b_{k+1} = k·b_k`.
- `farey_succ_denom_le_iff` — order-`n` cap `f ≤ n ↔ k·d ≤ n+b`, which selects
  `k = ⌊(n+b)/d⌋` as the largest admissible step.
- `simOrd_succ_controlling` (**headline**) — a *consecutive* step `c/d → e/f` is
  similarly ordered **iff** `(a+c−k·c)·(b+d−k·d) ≥ 0`. The open-problem quantity
  is now an explicit arithmetic inequality on the successive quotient `k`, not a
  vague appeal to "consecutiveness".
- `simOrd_succ_k_eq_one` — the `k=1` step is *always* similarly ordered (product
  collapses to `a·b ≥ 0`); runs can break **only** at quotients `k ≥ 2`,
  localizing exactly where the `1/12`–`1/4` optimization lives.

File: 638 → 745 lines, 39 → 45 theorems, 2 defs (no new def).

## Iterations 8–12 (verified, 0-axiom — `lake env lean`)

§10–§12 advanced the run criterion from single steps to length-4 blocks:
- **§10** `unimodular_simOrd` — EVERY Farey-adjacent pair is similarly ordered
  (the §9 controlling product is *unconditionally* ≥ 0). So a single step never
  breaks a run; the obstruction is entirely NON-ADJACENT.
- **§11** `simOrd_triple` — a length-3 run breaks iff the outer window
  `(2a−k·c)(2b−k·d) ≥ 0` fails (break interval width `2/(c·d)`).
- **§12** `simOrd_long_iff` / `simOrd_quad` — a length-4 run's long-range pair
  is governed by the Stern–Brocot product `k₁·k₂−1`; the full run criterion is
  the conjunction of two §11 windows and this one.

## Iteration 13 addition (verified, 0-axiom — `lake env lean`, Docker down)

Added **§13 (length-5 runs — three quotients and the continuant Kₘ)**,
0-sorry / 0-axiom (`#print axioms` reports only propext / Classical.choice /
Quot.sound on both new theorems; verified by `lake env lean` against the
worktree Mathlib `.olean` cache — Docker `docker info` hangs). Two theorems:

- `simOrd_long3_iff` — iterating the §9 successor *three* times collapses the
  fifth term to `i = (k₁k₂k₃−k₁−k₃)·c − (k₂k₃−1)·a` (and parallel for `j`), so
  the endpoints `a/b, i/j` are similarly ordered **iff**
  `(k₂k₃·a − (k₁k₂k₃−k₁−k₃)·c)·(k₂k₃·b − (k₁k₂k₃−k₁−k₃)·d) ≥ 0`. The controlling
  quantity is the **continuant** `K(k₁,k₂,k₃) = k₁k₂k₃−k₁−k₃` — the order-side
  shadow of the very recurrence `xₘ₊₁ = kₘ·xₘ − xₘ₋₁` that generates Farey
  numerators/denominators. The §11/§12/§13 windows are exactly the continuant
  ladder `K()=1, K(k)=k, K(k₁,k₂)=k₁k₂−1, K(k₁,k₂,k₃)=k₁k₂k₃−k₁−k₃`.
- `simOrd_quint` (headline) — a length-5 run is pairwise similarly ordered iff
  all SIX non-adjacent windows hold: three §11 (triples) + two §12 (quadruples)
  + the new §13 continuant window. Four adjacent pairs free (§10).

File: 1017 → 1146 lines, 55 → 57 theorems, 2 defs (no new def).

## Iteration 14 addition (verified, 0-axiom — `lake env lean`, Docker down)

Added **§14 (the continuant — the run-length criterion for *every* length)**,
0-sorry / 0-axiom (verified by `lake env lean` against the shared main-repo
Mathlib `.olean` cache — the worktree `proofs/.lake` symlinks to it; `#print
axioms` reports only propext / Classical.choice / Quot.sound on every new
theorem). **This delivers the §13 "Next Action" exactly: the per-length §11/§12/
§13 windows are now ONE statement valid for arbitrary run length.** Three defs +
ten theorems:

- `Continuant : List ℤ → ℤ` — the minus-sign continuant with the head-two-element
  recurrence `K(k₁ :: k₂ :: ks) = k₁·K(k₂ :: ks) − K(ks)`, bases `K([])=1`,
  `K([k])=k`. `secondCont : List ℤ → ℤ` — the trailing continuant (coefficient of
  `a`), `secondCont (k::ks)=K(ks)`, `secondCont []=0`. The `0`-base is the precise
  fix for the one-element continuant edge case.
- `continuant_cons` — the UNIFIED single-step recurrence
  `K(k::ks) = k·K(ks) − secondCont ks`, holding in *every* case (the naive "two
  shorter tails" form wrongly gives `k−1` at `ks=[]`; `secondCont []=0` repairs it).
- `stepSeq a c ks` — the iterated §9 successor, applying `tₘ₊₁=kₘ·tₘ−tₘ₋₁` once
  per quotient in `ks`.
- `stepSeq_eq_continuant` (**headline**) — the closed form
  `stepSeq a c ks = K(ks)·c − secondCont(ks)·a`, proved by induction on `ks`
  (the §13-targeted general term formula). Collapses `e=k·c−a`,
  `g=(k₁k₂−1)·c−k₂·a`, `i=(k₁k₂k₃−k₁−k₃)·c−(k₂k₃−1)·a` into one line.
- `endpoint_window` — the general endpoint product factors as
  `(a−pₘ)(b−qₘ) = ((1+secondCont ks)a − K·c)·((1+secondCont ks)b − K·d)`.
- `simOrd_run_iff` (**headline**) — a length-`(|ks|+1)` run's endpoints `a/b, p/q`
  (`p=stepSeq a c ks`, `q=stepSeq b d ks`) are similarly ordered **iff** that one
  continuant-controlled window is `≥ 0`. The run-length criterion as a continuant
  positivity condition — the structural form the §13 Next Action called for.
- Ladder/subsumption checks: `continuant_two/_three`, `secondCont_one/_two/_three`
  reproduce the §11/§12/§13 constants `1,k,k₁k₂−1,k₁k₂k₃−k₁−k₃` and coefficients
  `1,k₂,k₂k₃−1`; `endpoint_window_one/_two/_three` prove the general window
  *literally specializes* to the §11 `(2a−kc)`, §12 `((k₂+1)a−(k₁k₂−1)c)`, §13
  `(k₂k₃·a−(k₁k₂k₃−k₁−k₃)c)` windows at `|ks|=1,2,3`.

File: 1146 → 1317 lines, 57 → 71 theorems, 2 → 5 defs.

**Honest boundary (unchanged).** This is the structural run criterion; it does
*not* bound the density of `k`-values for which the windows hold, which is the
actual `1/12`–`1/4` optimization. What §14 buys is that the optimization is now a
single quantified statement (continuant positivity over a quotient list) rather
than an unbounded family of per-length inequalities.

## Next Action

Bound the *density* side. With `simOrd_run_iff` the run-length criterion is a
continuant positivity condition `((1+secondCont ks)a − K(ks)c)·(…) ≥ 0` over a
quotient list `ks`. Two concrete next Lean targets: (1) **continuant positivity /
monotonicity** — prove `K(ks) ≥ 1` (and `secondCont ks ≥ 0`) for all-`≥1`
quotient lists by induction on `continuant_cons`, certifying the windows' sign
structure; (2) **a "no long all-`k=1` run" or "break forced by a large quotient"
lemma** — characterize, via the continuant, which quotient lists keep ALL
non-adjacent windows nonnegative, isolating the extremal configurations that a
density count toward `1/12` must sum over. The continuant matrix identity
`[[k,−1],[1,0]]` product would give `K` a determinant/Cassini handle.

## Attempt Counts

- Total attempts: 5
- Current approach attempts: 5
- Approaches tried: 1
