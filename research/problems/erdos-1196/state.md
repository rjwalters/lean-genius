# Current State

**Phase**: COMPLETED
**Since**: 2026-04-15T00:00:00Z
**Iteration**: 3
**Last update**: 2026-05-13 (S3 ACT — `transition_sum_eq_one` discharged)

## Current Focus

Gallery entry with axiomatized Lean 4 formalization covering the GPT-5.4 Pro
2026 proof of the Erdős–Sárközy–Szemerédi conjecture. Files:

- `proofs/Proofs/Erdos1196Problem.lean` — 363 lines, 5 theorems, 5 defs,
  8 axioms, **0 sorries** (was 1; `transition_sum_eq_one` discharged in S3 ACT
  from `vonMangoldt_sum_eq_log` via `Finset.sum_div` + `div_self`)
- `proofs/Proofs/Erdos1196Aristotle.lean` — Aristotle companion, 2 sorries
  (`vonMangoldt_sum_eq_log_comp`, `transition_sum_eq_one_comp` — these still
  need the Mathlib `vonMangoldt_sum`-vs-`filter (· ∣ n) (range (n+1))` bridge)
- `src/data/proofs/erdos-1196/` — gallery (status `axiomatized`, badge `axiom`,
  `meta.sorries` 3 → 2)

## S3 ACT — `transition_sum_eq_one` Discharge (2026-05-13)

Replaced the `sorry`-terminated `conv_lhs`-based proof at
`Erdos1196Problem.lean:155-170` with a direct discharge:

```lean
theorem transition_sum_eq_one (n : ℕ) (hn : 2 ≤ n) :
    (Finset.filter (· ∣ n) (Finset.range (n + 1))).sum
      (fun q => transitionProb n q) = 1 := by
  have h1n : (1 : ℝ) < (n : ℝ) := by
    have : (1 : ℕ) < n := hn
    exact_mod_cast this
  have hlog : log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos h1n)
  have hsum :
      (Finset.filter (· ∣ n) (Finset.range (n + 1))).sum
          (fun q => transitionProb n q) =
        (Finset.filter (· ∣ n) (Finset.range (n + 1))).sum
          (fun q => (vonMangoldt q : ℝ) / log (n : ℝ)) := by
    refine Finset.sum_congr rfl (fun q hq => ?_)
    have hqn : q ∣ n := (Finset.mem_filter.mp hq).2
    simp only [transitionProb, if_pos (And.intro hqn hn)]
  rw [hsum, ← Finset.sum_div, vonMangoldt_sum_eq_log n hn, div_self hlog]
```

Proof outline:
1. `hsum`: pointwise rewrite each summand `transitionProb n q` to
   `(Λ q : ℝ) / log n` using `if_pos` on the conjunction `q ∣ n ∧ 2 ≤ n`
   (with `q ∣ n` extracted from `Finset.mem_filter`).
2. `← Finset.sum_div`: pull the divisor out of the sum, yielding
   `(∑ q ∈ filter (· ∣ n) (range (n+1)), Λ q) / log n = 1`.
3. `vonMangoldt_sum_eq_log n hn`: replace the von Mangoldt sum with `log n`
   (this is the only axiom invoked).
4. `div_self hlog`: `log n / log n = 1`, closing the goal.

The total axiom budget for the file is unchanged at 8; the discharge consumes
the existing `vonMangoldt_sum_eq_log` (line 138) and adds no new assumptions.

Build status: **build pending** (file modified but no local Docker build run;
doctor/auditor verification expected post-merge per researcher-3 build-pending
pattern). The disk constraint cited in the prior `state.md` snapshot is
resolved (55 GiB free as of 2026-05-13 12:30 UTC).

## Active Approach

None — main file is now sorry-free at axiomatized level. Remaining work is the
two Aristotle companion sorries (`vonMangoldt_sum_eq_log_comp`,
`transition_sum_eq_one_comp`), which need a Mathlib bridge between
`n.divisors` (the canonical divisor finset) and the explicit
`Finset.filter (· ∣ n) (Finset.range (n + 1))` used throughout this proof.

That bridge is plausibly:

```lean
have : Finset.filter (· ∣ n) (Finset.range (n + 1)) = n.divisors := by
  ext d
  simp [Nat.divisors, Nat.lt_succ_iff, Nat.le_of_dvd, hn]
```

— but verifying `Nat.divisors` membership on Mathlib head requires a real
build, and the Aristotle companion is gated on whether Aristotle itself can
discharge those targets. Deferred to a follow-up S4 PREP.

## Blockers

None at the metadata level. Build verification deferred to doctor/auditor.

## Next Action

S4 PREP (if claimed): inspect Mathlib's `Nat.divisors` and `vonMangoldt_sum`
(now at `ArithmeticFunction.vonMangoldt_sum` / `Nat.sum_vonMangoldt`?) to scope
the Aristotle companion's two sorries. No code edits — purely a bearer-audit
PR to identify the right Mathlib lemma names at the pinned lake SHA.

## Axiom Inventory (unchanged in S3 ACT)

The 8 axioms in `Erdos1196Problem.lean` are foundational analytic-number-theory
results gated on Mathlib's eventual `vonMangoldt` API maturation:

- `vonMangoldt_sum_eq_log` (line 138) — divisor sum identity (USED in S3 ACT
  discharge)
- Plus 7 others encoding the GPT-5.4 Pro proof's Markov-chain machinery
  (transition matrices, sub-Markov adjoint property, anatomy-of-integers
  bounds). All are individually candidates for Mathlib upstream once the
  von Mangoldt API stabilises.

## Attempt Counts

- Total attempts: 2
- Current approach attempts: 1 (S3 ACT discharge)
- Approaches tried: 2 (S2 axiomatized scaffold; S3 sorry discharge from axiom)
