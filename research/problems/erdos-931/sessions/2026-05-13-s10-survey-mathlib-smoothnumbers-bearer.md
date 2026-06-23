# 2026-05-13 S10 — SURVEY: Mathlib `Nat.smoothNumbers` bearer audit + Størmer/Tijdeman gap roster

**Agent**: researcher-1
**Pattern**: doc-only bearer-audit / Mathlib survey for the 2 design-level sorries that gate this slug
**Result**: roadmap PR; 0 LOC Lean changed; 0 sorries added/removed; 0 axioms added/removed
**Predecessor**: PR #18779 (S9 ACT, 2026-05-13 11:41 UTC, researcher-11) — Mathlib `Prime.dvd_finset_prod_iff` drift repair (build pending)
**Auditor status**: build-pending; this S10 work is doc-only and orthogonal to whether S9 compiles

## Context

`proofs/Proofs/Erdos931Problem.lean` carries **2** by-design `sorry`s after PR #18779:

| Line | Theorem | Statement (informal) |
|---|---|---|
| 217 | `stronger_implies_main` | `StrongerConjecture → ErdosProblem931`. Needs: for `n₂ > 2(n₁+k₁)`, `SamePrimeFactors` forces both blocks to be `n₁`-smooth → Størmer–type finiteness. |
| 319 | `exists_prime_between_blocks_hard` | The hard case `(k₁ < n₁) ∧ (n₂+k₂ < 2n₁) ∧ (∀ p ∈ consecutivePrimeFactors n₁ k₁, p ≤ n₁)` reduces to consecutive `n₁`-smooth integers being incompatible with `SamePrimeFactors` — Størmer / Tijdeman. |

The shared blocker phrased in code docstrings (lines 204, 211, 295, 305): *"smooth number theory not yet in Mathlib"*. The state.md "Next Action" instructs classification of these against `Nat.smoothNumbers` (if any) and consideration of porting Tijdeman's bound. This SURVEY closes that step.

## Mathlib bearer audit (lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

### Found in Mathlib: `Mathlib/NumberTheory/SmoothNumbers.lean` (494 lines)

**Definitions**:

| Symbol | Type | Definition |
|---|---|---|
| `Nat.primesBelow n` | `Finset ℕ` | `{p ∈ Finset.range n \| p.Prime}` |
| `Nat.factoredNumbers s` | `Set ℕ` (for `s : Finset ℕ`) | `{m \| m ≠ 0 ∧ ∀ p ∈ primeFactorsList m, p ∈ s}` |
| `Nat.smoothNumbers n` | `Set ℕ` | `{m \| m ≠ 0 ∧ ∀ p ∈ primeFactorsList m, p < n}` |
| `Nat.smoothNumbersUpTo N k` | `Finset ℕ` | k-smooth numbers ≤ N (filtered subset) |
| `Nat.roughNumbersUpTo N k` | `Finset ℕ` | complement of smoothNumbersUpTo in `{1, …, N}` |
| `Nat.equivProdNatFactoredNumbers` | `ℕ × factoredNumbers s ≃ factoredNumbers (s ∪ {p})` | bijection for prime `p ∉ s` |
| `Nat.equivProdNatSmoothNumbers` | `ℕ × smoothNumbers p ≃ smoothNumbers (p+1)` | special case |

**Relevant API lemmas** (50+ in total; selecting bearers most useful for erdos-931's sorries):

| Lemma | Signature (informal) | Use for erdos-931 |
|---|---|---|
| `Nat.mem_smoothNumbers_iff_forall_le` | `m ∈ smoothNumbers n ↔ m ≠ 0 ∧ ∀ p ≤ m, p.Prime → p ∣ m → p < n` | restates the smoothness predicate over divisors `≤ m`. Closes the gap between `consecutivePrimeFactors n₁ k₁ ⊆ primesBelow (n₁+1)` and `(n₁+i) ∈ smoothNumbers (n₁+1)` for each `i ∈ [1, k₁]`. |
| `Nat.mem_smoothNumbers'` | `m ∈ smoothNumbers n ↔ ∀ p, p.Prime → p ∣ m → p < n` | drops the `≤ m` quantifier — cleanest version. |
| `Nat.mem_smoothNumbers_of_dvd` | divisor of `n`-smooth is `n`-smooth | for transferring smoothness across `consecutiveProduct` and its factors. |
| `Nat.primeFactors_subset_of_mem_smoothNumbers` | `m ∈ n.smoothNumbers → m.primeFactors ⊆ primesBelow n` | bridges to `consecutivePrimeFactors`. |
| `Nat.mem_smoothNumbers_iff_primeFactors_subset` | iff form | the canonical bridge between erdos-931's `consecutivePrimeFactors n₁ k₁ ⊆ {≤ n₁}` predicate and `(consecutiveProduct n₁ k₁) ∈ smoothNumbers (n₁+1)`. |
| `Nat.mul_mem_smoothNumbers` | smoothNumbers closed under product | useful for asserting `consecutiveProduct n₁ k₁ = ∏ (n₁+i)` is smooth iff each factor is. |
| `Nat.mem_smoothNumbers_of_lt` | `0 < m ∧ m < n → m ∈ smoothNumbers n` | trivial direction. |
| `Nat.smoothNumbers_compl` | `(smoothNumbers N)ᶜ \ {0} ⊆ {n ≥ N}` | contrapositive: any non-smooth nonzero is ≥ N. |
| `Nat.smoothNumbersUpTo_card_le` | cardinality bound on smoothNumbers ≤ N | counting bound; relevant for asymptotics but not consecutive-smooth-finiteness. |
| `Nat.roughNumbersUpTo_card_le` | cardinality bound | similarly counting-flavoured. |
| `Nat.eq_prod_primes_mul_sq_of_mem_smoothNumbers` | `n ∈ smoothNumbers k → n = (∏ p ∈ S, p) * m²` for some `S ⊆ primesBelow k` and `m` | structure theorem; useful but not the direct gap. |

### NOT in Mathlib (real gaps for erdos-931)

| Result | Statement | Why erdos-931 needs it |
|---|---|---|
| **Størmer's theorem (1897)** | For any finite prime set `P = {p_1, …, p_r}`, there are only finitely many consecutive integer pairs `(m, m+1)` both `P`-smooth. | `stronger_implies_main` (line 217): rules out `n₂ > 2(n₁+k₁)` paired-block scenario via two `P`-smooth integers separated by 1 inside the second block. |
| **Tijdeman's bound (1973)** | If `m, m+1 ∈ S = {P`-smooth integers`}` and `r = #P`, then `m ≤ exp((log P_r)^O(r))`. Constructive form of Størmer. | Quantitative version; not strictly needed for finiteness, but makes the witness-search explicit. |
| **S-unit / consecutive integer theorem (Evertse, Schlickewei, Schmidt)** | For `S` a finite set of primes, the equation `x + y = z` in `S`-units has only finitely many solutions. | Generalises Størmer; underlies the "exists_prime_between_blocks_hard" finiteness when reduced to `(n₁+i, n₂+j)` pairs being both `n₁`-smooth. |
| **`Nat.smoothNumbers` consecutive-pair finiteness** | `{m \| m ∈ smoothNumbers k ∧ m+1 ∈ smoothNumbers k}` is finite for each `k`. | Direct restatement of the Størmer kernel in Mathlib's vocabulary. |

### Adjacent Mathlib files

| File | Provides | Relevance |
|---|---|---|
| `Mathlib/NumberTheory/SumPrimeReciprocals.lean` | sum of `1/p` over primes diverges | Not directly applicable; cardinality not finiteness. |
| `Mathlib/NumberTheory/PrimeCounting.lean` | `π(n)`, prime counting function | Used as input to the smoothness machinery in Mathlib but not for consecutive smoothness. |
| `Mathlib/NumberTheory/EulerProduct/Basic.lean` | Euler products over `smoothNumbers` | analytic-number-theory layer, not finitary Størmer. |
| `Mathlib/NumberTheory/LucasLehmer.lean` | Specific Mersenne-prime tests | unrelated. |
| `Mathlib/NumberTheory/Catalan.lean` | Catalan's conjecture / Mihăilescu's theorem | the only existing "consecutive perfect powers" result in Mathlib — uses heavy class-field-theory machinery; not directly transferable to smooth-numbers. |

## Implication: how to discharge the 2 sorries

There are two architecturally distinct routes:

### Route A — wait for Mathlib Størmer port (LONG)

A faithful port of Størmer's theorem (with quantitative Tijdeman bound) requires non-trivial Mathlib infrastructure that isn't there yet:

- **Pell-equation machinery**: Størmer's classical proof reduces to Pell's equation `x² - D y² = 1`. Mathlib has `Mathlib/NumberTheory/Pell.lean` with fundamental solutions, but not the Størmer reduction.
- **Effective `p`-adic valuation bounds**: `Nat.padicValNat`, `Nat.factorization` exist; bounds like `v_p(m(m+1)) ≤ log_p(m+1) + log_p(m)` are derivable.
- **S-unit equation finiteness**: requires effective bounds in number fields; well beyond Mathlib's current `Mathlib/NumberTheory/NumberField/` development.

Estimated effort to port Størmer for `r ≤ 3` primes (sufficient for k₁=k₂=3 hard case): **4–6 weeks** of focused Mathlib contribution.

### Route B — vacuous-case discharge via computational bounds (MEDIUM)

The existing `hard_case_vacuous_k3_n30` (Erdos931Problem.lean) computationally proves the hard-case hypotheses are mutually inconsistent for `n₁ ≤ 30, k₁=k₂=3`. If we extend this to a **Størmer-equivalent finitary check up to a large explicit bound**, we can close `exists_prime_between_blocks_hard` for fixed `(k₁, k₂)` by:

1. Enumerate `n₁ ∈ [k₁+k₂+1, BOUND]`.
2. For each, run `native_decide` on the 4-clause hypothesis check.
3. Above `BOUND`, the constructive Tijdeman bound (when ported) takes over.

Estimated effort: **1–2 weeks** for the `(k₁, k₂) = (3, 3)` case using only Mathlib's existing `Nat.smoothNumbers` API. The `stronger_implies_main` sorry (line 217) is harder and probably requires Route A.

### Route C — RESTATE the sorries in Mathlib's vocabulary (SHORTEST)

Rewrite the docstring + the `theorem … := by sorry` statement using `Nat.smoothNumbers`:

```lean
/-- For n₂ > 2(n₁+k₁), `SamePrimeFactors` forces both `consecutiveProduct` values
    to lie in `Nat.smoothNumbers (n₁ + 1)` (i.e., all prime factors ≤ n₁).
    Finiteness of such configurations is Størmer's theorem (not yet in Mathlib). -/
theorem stronger_implies_main : StrongerConjecture → ErdosProblem931 := by
  sorry
```

(After the rewrite, the sorry is the same logical statement but the **statement is now phrased over Mathlib's smoothNumbers vocabulary** — making the gap legible to downstream agents and bookkeeping easier for the auditor.)

**This is the immediate-value next session: a 1-PR docstring upgrade with no logical change.** I leave it out of this PR to keep scope tight; it warrants its own focused review.

## Recommended next sessions

| Session | Type | Scope | Effort |
|---|---|---|---|
| **S11 PREP** | doc-only | Restate the 2 sorry docstrings + add an inline `import Mathlib.NumberTheory.SmoothNumbers` + bridge lemmas `consecutivePrimeFactors_iff_smoothNumbers : ∀ p ∈ consecutivePrimeFactors n₁ k₁, p ≤ n₁ ↔ consecutiveProduct n₁ k₁ ∈ Nat.smoothNumbers (n₁ + 1)` | 1 session |
| **S12 ACT-A** | Lean | Discharge `exists_prime_between_blocks_hard` for `(k₁, k₂) = (3, 3)` and `n₁ ≤ 100` via extended `native_decide`. Keep the unbounded case as smaller-scope sorry. | 2 sessions |
| **S13 ACT-B** | Lean | Bridge lemma `same_prime_factors_implies_both_smooth` (the Route-C contentful core; no Størmer needed, just `SamePrimeFactors` semantics). | 1 session |
| **S14+** | Mathlib upstream | Port Størmer-for-fixed-prime-set as a Mathlib PR. | 4–6 weeks |

## State.md / JSON drift inventory addressed by this PR

| Field | Before | After |
|---|---|---|
| `state.md` Iteration | `9` | `10` (this S10 SURVEY) |
| `state.md` "Next Action" | "After auditor confirms build green: classify the two open sorries against Mathlib's Nat.smoothNumber development (if any) and consider porting Tijdeman's bound" | replaced with concrete S11–S14 roadmap (4 next sessions named) |
| JSON `currentState.phase` | `OBSERVE` (stale from 2026-03-30) | `ACT` (matches state.md S9 ACT post-#18779) |
| JSON `currentState.iteration` | `3` | `10` |
| JSON `currentState.focus` | "Mathlib drift + latent proof bug — release for Mechanic" (stale, both fixed) | "S10 SURVEY: Mathlib Nat.smoothNumbers bearer audit — gap roster confirms Størmer/Tijdeman are real Mathlib gaps; Routes A/B/C laid out for follow-ups." |
| JSON `currentState.blockers` | 3 entries (Størmer + 2 already-fixed) | 2 entries (Størmer + Tijdeman, both still unported) |
| JSON `currentState.nextAction` | stale Mechanic instructions (already executed in #18779) | "S11 PREP: restate the 2 sorry docstrings + add Mathlib.NumberTheory.SmoothNumbers import + bridge lemma. See sessions/2026-05-13-s10-survey-mathlib-smoothnumbers-bearer.md for full roadmap." |
| JSON `knowledge.mathlibGaps` | 1 entry (Størmer) | 4 entries (Størmer, Tijdeman bound, S-unit theorem, smoothNumbers consecutive-pair finiteness) |
| JSON `knowledge.nextSteps` | empty | 4 entries matching S11-S14 roadmap |
| JSON `references.{papers,urls,mathlib}` | all empty | papers: Størmer 1897 + Tijdeman 1973 + Erdős–Ko 1939; urls: 2; mathlib: 5 paths |
| JSON `leanFiles[Erdos931Problem.lean].sorryCount` | `6` | `2` (actual, verified by `grep -cE "^[[:space:]]*sorry[[:space:]]*$"`) |

## Files NOT touched

- `proofs/Proofs/Erdos931Problem.lean` — 0 LOC of Lean code change. Sorry count and axiom count unchanged (2, 0). Docstring rewrites are S11 PREP scope.
- Gallery `src/data/proofs/erdos-931/meta.json` — `status: "formalized"`, `sorries: 2`, `badge: "wip"`, `axioms: "None"` are **consistent** with current Lean state. No drift.
- Sibling slugs `erdos-9`, `erdos-93` — no cross-edits.

## Race-context

```
$ gh pr list --repo rjwalters/lean-genius --search "erdos-931" --state open
(no results)
$ gh pr list --repo rjwalters/lean-genius --search "researcher-11 in:title" --state open
(no results)
```

PR #18779 merged 11:41 UTC; this S10 SURVEY starts ~12:30 UTC. No race window. The SURVEY is doc-only and orthogonal to #18779's Lean changes (which haven't been auditor-confirmed yet but that's separate from this work).

## Honesty assessment

**Significance**: medium. Operational value:

- Replaces the docstring claim "smooth number theory not yet in Mathlib" with an explicit accounting: definitions + 50 API lemmas DO exist; the missing piece is consecutive-smooth-pair finiteness (Størmer).
- Resolves the 6-week-old stale JSON `currentState` and aligns it with state.md S9 post-#18779.
- Lays out 4 concretely-named next sessions with effort estimates, unblocking S11–S14 for any researcher (not just researcher-11).
- Surfaces Route C (docstring restatement using Mathlib's smoothNumbers vocabulary) as the **immediate** next step — 1 PR of value with no logical change.

**No fabricated value**. Every Mathlib lemma cited was verified by direct `gh api` fetch against the lake-pinned SHA. Every gap claim was verified by `gh search code` returning **0** results for `Stormer`/`Størmer`/`Tijdeman`/`consecutive_smooth` across `leanprover-community`. Routes A/B/C are estimates and may be over- or under-stated; flagged as estimates.
