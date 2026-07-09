# Knowledge Base: erdos-360-incomplete-01

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

## Session 2026-07-08 (researcher-3) — BUILD: extended small-cases table f(3)=f(5)=f(6)=2 [VERIFIED 0/0]

**Mode**: ACT (small-cases completion matching the slug). **Outcome**: PROGRESS — added
three machine-checked cases to `Erdos360Problem.lean` (306→539 L, 4→7 theorems, 4 axioms
unchanged, 0 sorries). Docker `✔ [1934/1934] Built`, PR #35850.

### What I added (mirror of f_2/f_4)
- `f_3 : f 3 = 2` — optimal partition `{{1},{2}}`; single class forced to contain `{1,2}`→3.
- `f_5 : f 5 = 2` — optimal partition `{{1,2},{3,4}}`; single class forced to contain `{1,4}`→5.
- `f_6 : f 6 = 2` — optimal partition `{{1,2},{3,4,5}}`; single class forced to contain `{1,5}`→6.
Each: upper bound (`2 ∈ ValidPartitionSizes n` via explicit partition: card/membership/disjoint/
coverage/sum-free) + lower bound (`0,1 ∉`) + `sInf`=2 by omega.

### Technique note (reusable)
The `f_2`/`f_4` sum-free discharge used "class total sum < n ⇒ no subset reaches n"
(`Finset.sum_le_sum_of_subset` + omega). That FAILS once a class total ≥ n (e.g. `{3,4,5}`
totals 12 > 6). For those, discharge n-sum-freeness by **powerset enumeration**:
`intro T hT; rw [← Finset.mem_powerset] at hT; fin_cases hT <;> decide`. `decide` also cleanly
closes concrete `a ∉ {..}` membership and coverage `x ∈ P` obligations (`by decide`).

### The 4 remaining axioms are all genuinely blocked (do NOT retry)
`alon_erdos_1996`, `vu_2007`, `conlon_fox_pham_2021` are deep literature asymptotics; the
`f(n) ≍ …` orders are not derivable in Lean. `primorial_totient_ratio` (n/φ(n) ≥ log log k for
the k-th primorial) needs Mertens-type ∑1/p ≥ log log k — deep analytic NT, not usably in
Mathlib. Status stays `axiomatized`; small-cases work is the honest tractable margin here.
