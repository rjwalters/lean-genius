# Research State: erdos-30-wip-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-24 (h(29) opening, researcher-3)
**Iteration**: 8

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
Exact Sidon table h(N) = sidonNumber N. COMPLETE for h(0..28) as of the
2026-07-23b session (h(28)=7 via a mod-4 class double count — the perfect
8-mark ruler is forced at N=28 and the residue-class counts
Σcᵣ(cᵣ−1)=14, Σcᵣ·c_{r+2}=14, Σcᵣ=8 are jointly unsatisfiable; no kernel
search needed).

## Active Approach
Residue-class double counting against forced perfect rulers at the wall
values N = k(k−1)/2 (h(10) parity, h(15) mod-3, h(21) parity, h(28) mod-4);
chained span dichotomy + pinned-endpoint kernel search for the in-between
values. `SidonCheck` converse bridge certifies witnesses with one `decide`.

## Attempt Count
- Total attempts: 8 sessions
- Current approach attempts: 5 (h(16), h(17..21), h(22..27), h(28), Erdős–Turán √N lower bound — all landed)
- Approaches tried: parity wall, mod-3 class count, span dichotomy, mod-4 double count, Erdős–Turán construction + Bertrand

## Blockers
NONE for h(29) — the 2026-07-24b analysis shows pure modular counting closes
it (see the closure table above); the "~376k kernel search" blocker is
OVERTURNED. Genuine remaining walls: h(30..33) (same near-perfect analysis
re-run per N — miss-2-values structure at N=30 needs checking) and the DEEP
targets.

## Next Action
LAYER 2 of h(29): kill `d ∈ {2,6,10,14,18,22,26}` via cross-class counts
(mod 7 for {10,18}, mod 9 for {14,22}, mod 10 for {2,6,26}) following the
recipe in the 2026-07-24b session note, then assemble
`no_sidon_card_eight_range_thirty` and `sidonNumber_twentynine = 7`.
After that: DEEP targets (N^{1/4} refinement, Singer (1−o(1))√N constant,
$1000 N^ε conjecture) or h(30..33) by the same near-perfect method.
