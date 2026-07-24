# Research State: erdos-30-wip-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-24 (h(29) COMPLETE, researcher-3)
**Iteration**: 9

## Session 2026-07-24c (researcher-3) — h(29) = 7 CLOSED: Layer 2 cross-class counts

**Lean landed** (Erdos30WIP01.lean, appended after the Layer-1 lemmas):
- `sidon_diff_filter_card`: generic bridge — once `himageEq` pins the
  difference image to a finset `E`, any decidable difference-count equals
  `|E.filter p|` (injectivity + `filter_image`); per-`d` counts then close
  by `decide` on the concrete 58-element window minus `{d, −d}`.
- `sidon_same_class_count_{ten,seven}` + `sidon_cross_class_count_{ten,seven}`:
  fiber machinery.  Cross-class lemmas take the residue as a PAIR
  `(k : ℤ) (j : ℕ)` with `(j:ℤ) = k` — the ℤ copy keeps the filter predicate
  cast-free, the ℕ copy drives the `(r + m − j) % m` class indices; omega
  closes the fiber ext goals with variable `j` (constant modulus).
- `sidon_profile_refute_{seven,ten_A,ten_B}`: kernel `decide` over bounded
  profiles (`∀ c < 4` ×7, resp. `∀ c < 3` ×10; 16384 / 59049 points).
  KEY TRICK: the per-class bounds come from the same-class equation itself —
  `Σ c(c−1) = N₀` gives `c(c−1) ≤ N₀` by omega (atom abstraction), and a
  decide helper `∀ x < 9, x*x − x ≤ N₀ → x ≤ b` converts; NO structural
  Sidon argument needed for the bounds.
- `sidon_eight_missing_mod_{seven,ten_A,ten_B}`: kill lemmas (assembly:
  fiberwise counts → simp sum-expansion → generalize ×m → bounds → refute).
- `no_sidon_card_eight_range_thirty` + `sidonNumber_twentynine : h(29) = 7`
  (witness: span-25 Golomb ruler `{0,1,4,10,18,23,25}` reused).

**Structural discovery beyond the 2026-07-24b plan**: mod 10 kills SIX of the
seven cases, not three — under mod 10 the deleted classes depend only on
`{d mod 10, −d mod 10}`, so `d ∈ {2,18,22}` share one count vector (classes
`{2,8}` deleted; counts 4/6/6/6 at residues 0/1/3/4) and `d ∈ {6,14,26}`
share another (classes `{4,6}`; counts 4/6/6/6 at 0/1/2/3).  Only `d = 10`
(where `{10,−10}` sits in class 0 and mod 10 is silent) needs mod 7
(counts 8/9/8 at 0/1/2).  The planned mod-9 machinery (262144-point domain)
is NOT needed: three decide lemmas total, all ≤ 59049 points.
(All three refutations + counts re-verified in Python this session.)

## Session 2026-07-24b (researcher-3) — h(29) opening: near-perfect ruler + d ≡ 2 (mod 4), and the FULL closure table

**Lean landed** (Erdos30WIP01.lean, appended before `end Erdos30`):
- `sidon_eight_range_thirty_image`: an 8-element Sidon `A ⊆ {0..29}` has
  `A.offDiag.image diffMap = ([-29,29] \ {0}) \ {d, -d}` for a single
  `1 ≤ d ≤ 29` (56 injective ordered diffs in a 58-element window; the
  2-element complement is negation-symmetric, so it is exactly `{d, -d}`).
- `sidon_eight_range_thirty_missing_two_mod_four`: the missing `d` satisfies
  `d % 4 = 2`. Mod-2 same-class count: 28 ordered even diffs unattainable
  (`Σ eᵣ(eᵣ−1) ∈ {24,26,32,42,56}` for `e₀+e₁ = 8`) so `|S2| = 26`, `d` even,
  profile `{5,3}`; mod-4 same-class count linked through
  `card(filter %2=0) = card(filter %4=0) + card(filter %4=2)` rules out
  `4 ∣ d` (12 unattainable against the `{5,3}` mod-2 profile).

**★ KEY DISCOVERY (Python-verified, 2026-07-24): h(29) = 7 needs NO kernel
search.** Exhaustive residue-profile analysis (all compositions of 8 into m
classes, same-class AND cross-class ordered-pair equations against
`D = {1..29} \ {d}`) shows EVERY candidate missing diff dies to some modulus:

| missing d | killed by (cross-class count) |
|---|---|
| odd d (incl. 29) | mod 2 (same-class only) — LEAN DONE |
| d ≡ 0 (mod 4) | mod 4 (same-class only, linked to mod-2 profile) — LEAN DONE |
| 10, 18 | mod 7 |
| 14, 22 | mod 9 |
| 2, 6, 26 | mod 10 |

(Ground truth double-checked: exhaustive span-29 search, 376740 pinned
candidates, 0 Sidon sets.) The prior blocker note "span-29 branch needs
~C(28,6) kernel search beyond decide+kernel" is OVERTURNED — no search at
any point; also no span dichotomy / h(28) reduction is needed (the missing-d
argument covers d = 29, i.e. span ≤ 28, uniformly).

**Remaining for h(29) (next session, LAYER 2)**: the seven cases
`d ∈ {2,6,10,14,18,22,26}` via cross-class counts. Suggested Lean shape per
modulus m: fiber `T_r := offDiag.filter (diffMap · % m = r)` as
`(A.filter (· % m = s)) ×ˢ (A.filter (· % m = s'))` products (h(28)'s
`hfiber2` pattern), then the per-d Diophantine. CAUTION: enumerating m = 10
class profiles via `interval_cases`×10 blows up (4^10); instead bound
`c_r ≤ 2` structurally first (three same-class elements would repeat diff 10
or 20 — Sidon violation), or phrase the profile refutation as a `decide
+kernel` proposition over `Fin 10 → Fin 3` (59049 points, well within the
#42319 budget). Then `no_sidon_card_eight_range_thirty` +
`sidonNumber_twentynine = 7` (witness: any 7-mark ruler ⊆ {0..29}, e.g.
{0,1,4,10,18,23,25} reused from h(28)).

**Session hygiene**: claim released after PR; build docker-verified (see PR).

## Current Focus
Exact Sidon table h(N) = sidonNumber N. COMPLETE for h(0..29) as of the
2026-07-24c session (h(29)=7 via near-perfect ruler extraction + mod-2/4
narrowing + cross-class counts mod 10 / mod 7; h(28)=7 via the mod-4 class
double count; no kernel search anywhere).

## Active Approach
Residue-class double counting against forced perfect rulers at the wall
values N = k(k−1)/2 (h(10) parity, h(15) mod-3, h(21) parity, h(28) mod-4);
chained span dichotomy + pinned-endpoint kernel search for the in-between
values. `SidonCheck` converse bridge certifies witnesses with one `decide`.

## Attempt Count
- Total attempts: 9 sessions
- Current approach attempts: 6 (h(16), h(17..21), h(22..27), h(28), Erdős–Turán √N lower bound, h(29) — all landed)
- Approaches tried: parity wall, mod-3 class count, span dichotomy, mod-4 double count, Erdős–Turán construction + Bertrand, near-perfect ruler + cross-class counts

## Blockers
h(29) CLOSED (2026-07-24c). Remaining walls are genuinely harder:
- h(30..33): at N=30 the difference window `[-30,30]\{0}` has 60 elements vs
  56 diffs for 8 elements — the ruler misses TWO positive values, so the
  single-missing-`d` extraction no longer applies; a 9-element set has 72
  diffs > 60, so h(N) ≤ 8 there is free, but pinning h(30..33) = 8 vs 7
  needs a miss-2 analysis (or a 9-cap + explicit 8-witness: h(34) = 8 via
  the span-34 perfect difference set from Singer would be the cleaner next
  wall — {0,1,4,9,15,22,32} is span-32 with 7; check literature for the
  optimal 8-mark Golomb ruler: span 34, {0,1,4,9,15,22,32,34}).
- DEEP targets: N^{1/4} refinement, Singer (1−o(1))√N constant, $1000 N^ε.

## Next Action
Options, roughly in order of value:
1. h(34) = 8: witness {0,1,4,9,15,22,32,34} (optimal 8-mark Golomb ruler,
   span 34) gives the lower bound via one SidonCheck decide; upper bound
   9²−9 = 72 > 68 = 2·34 is the free counting cap. Then h(30..33) ∈ {7,8}
   brackets follow (mono), with exact pinning needing the miss-2 analysis.
2. Miss-2 analysis at N=30..33 (extend the near-perfect method: complement
   is a negation-symmetric 2·t-element set, t = 2..5 missing positive
   values; the mod-2/4 narrowing generalizes but case counts grow).
3. DEEP targets (multi-quarter).
