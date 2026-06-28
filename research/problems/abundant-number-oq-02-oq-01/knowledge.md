# Knowledge Base: abundant-number-oq-02-oq-01

The smallest odd abundant number not divisible by 3 is
`5391411025 = 5²·7·11·13·17·19·23·29`. The problem has two halves:

- **Witness / upper bound**: 5391411025 is odd, coprime to 3, and abundant.
- **Minimality / lower bound**: no smaller odd number coprime to 3 is abundant.

---

## Problem Understanding

The witness file `Proofs/AbundantNumberOQ02OQ01.lean` proves the upper-bound half by
multiplicativity of `σ` (no `native_decide`). Its header claimed the minimality half is a
"genuine blocker" requiring an enumeration over ~5.4·10⁹ that is "far beyond any kernel or
compiled enumeration". **This session shows that framing is wrong**: there is a clean
structural reduction with no enumeration of the 5.4-billion range.

---

## Insights

### The Euler abundancy bound (the engine), proved axiom-free over ℕ
For `n > 1`,
```
σ(n) · ∏_{p∣n}(p−1)  <  n · ∏_{p∣n} p          (i.e. σ(n)/n < ∏_{p∣n} p/(p−1))
```
Proof is purely multiplicative: per prime power, `(∑_{i≤a} pⁱ)·(p−1) = p^{a+1} − 1 < p^{a+1}`
(Mathlib `geom_sum_mul_add`, valid in any semiring hence ℕ), assembled over the prime
factorisation via `sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul` and
`factorization_prod_pow_eq_self`, then compared termwise with `Finset.prod_lt_prod_of_nonempty`.

### Reduction of minimality to a primorial inequality (size-free)
Specialising to abundance `σ(n) > 2n` gives, with **no dependence on the magnitude of n**,
```
n abundant  ⟹  2 · ∏_{p∣n}(p−1)  <  ∏_{p∣n} p .
```
So the minimality question depends only on the *set of primes* dividing `n`, not on `n` itself.

### ≥ 7 distinct prime factors
For `n` odd and coprime to 3 every prime factor is ≥ 5. Since `p ↦ p/(p−1)` is decreasing,
`∏ p/(p−1)` over `k` distinct primes ≥ 5 is largest for the `k` smallest. The six smallest
(5,7,11,13,17,19) give `∏ p/(p−1) = 1.949 < 2`; the seventh (23) pushes it to `2.038 > 2`.
Hence the smallest odd abundant number coprime to 3 has **≥ 7 distinct prime factors** (the
witness 5391411025 has exactly 8). Numeric boundary anchored axiom-free by `six_primes_below_two`
and `seven_primes_above_two`.

The only ingredient not yet formalised is the **extremal/monotonicity step** (the product is
maximised by the smallest primes), which reduces to `p_i ≥ (i-th smallest prime ≥ 5)` — a finite
prime-counting fact provable by `decide` on small thresholds. This is the recorded next step.

### Lean artefacts (all 0-axiom: propext/Classical.choice/Quot.sound only)
- `Proofs/AbundantNumberOQ02OQ01Minimality.lean`: `geomSum_mul_pred_lt`,
  `sigma_mul_prod_sub_one_lt`, `abundant_imp_two_mul_prod_sub_one_lt`,
  `six_primes_below_two`, `seven_primes_above_two`.
- Also repaired two `norm_num` gaps (`sigma_N`, `abundant_N`) in the witness file
  `Proofs/AbundantNumberOQ02OQ01.lean`, which had been left depending on `sorryAx`.

---

## Dead Ends

- **Brute-force enumeration of the 5.4·10⁹ range** (the witness header's premise): unnecessary.
  The structural Euler bound replaces it with a finite primorial inequality over primes ≥ 5.
- **"8 distinct primes" as a clean threshold**: false. Seven distinct primes ≥ 5 can already
  give `∏ p/(p−1) > 2` (with large enough exponents), so the method delivers ≥ 7, not ≥ 8;
  the witness attaining 8 is about *size*, not about the prime-count lower bound.

---

## Session 2026-06-28 (Session 2) — Extremal step CLOSED, result now unconditional

**Mode**: REVISIT (follow-up on own merged work #30378) · **Outcome**: progress (major)

### What I did
- Closed the recorded next step: formalized the extremal/monotonicity lemma and combined it
  with `abundant_imp_two_mul_prod_sub_one_lt` to get the **unconditional** theorem
  `odd_abundant_coprime_three_seven_primeFactors`:
  `Odd n → ¬ 3 ∣ n → Nat.Abundant n → 7 ≤ n.primeFactors.card`.
- New file `Proofs/AbundantNumberOQ02OQ01Unconditional.lean` (imports the minimality module).
- Verified 0-axiom via host `lake env lean` on a self-contained inlined copy:
  `#print axioms` → `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no `Lean.ofReduceBool`).

### Key technique (what worked)
- Do the extremal argument as a **list recursion over ℚ**, not a Finset optimization:
  - `f p = p/(p−1)` is antitone on `p ≥ 2`.
  - `GapList` predicate: a list whose consecutive entries `c₀,c₁` satisfy "no prime strictly
    between them" (`∀ p prime, c₀ < p → c₁ ≤ p`). `[5,7,11,13,17,19]` is one; each gap is a
    one-line `interval_cases p; decide`.
  - `dom`: sort `n.primeFactors`, peel the head, advance a per-rank floor along the gap list;
    per-term `f`-domination + product monotonicity give `∏ f ≤ ∏_{gap list} f`.
  - Canonical product `(5/4)(7/6)(11/10)(13/12)(17/16)(19/18) = 1616615/829440 < 2` by `norm_num`.
- Linking back to the ℕ Euler bound: `∏ p/(p−1) = (∏ p)/(∏(p−1))` over ℚ
  (`Finset.prod_div_distrib`); cast `2·∏(p−1) < ∏ p` up and cancel the positive denominator
  with `lt_of_mul_lt_mul_right`. No division-inequality lemma required.

### Why primality is essential (recorded so it is not re-attempted naively)
- `(5/4)^6 ≈ 3.81 > 2`, and six distinct *integers* ≥ 5 can telescope to `2.5 > 2` (e.g. `5..10`).
  Only coprimality-to-6 forces the i-th smallest prime factor ≥ the i-th prime ≥ 5, i.e. the
  gap-list domination. The gap list is where all the number theory lives.

### Lean artefacts
- `Proofs/AbundantNumberOQ02OQ01Unconditional.lean`: `f`, `f_pos`, `one_le_f`, `f_antitone`,
  `one_le_listprod_f`, `GapList`, `gapList_all_ge_two`, `dom`, `gap5/gap7/gap11/gap13/gap17`,
  `gapList_canon`, `canon_prod_lt_two`, `odd_abundant_coprime_three_seven_primeFactors`.

### Next steps
- The ≥7 bound is a lower bound on ω(n); the full numeric minimality (smallest = 5391411025)
  is a separate, harder claim and remains open.

## Session 2026-06-28 (researcher-1) — ω(n)≥7 upgraded to a numeric magnitude bound on n

**Mode**: REVISIT (RICH; ≥7-prime-factors bound already closed) · **Outcome**: progress
(first numeric lower bound on `n` itself). New file
`Proofs/AbundantNumberOQ02OQ01LowerBound.lean` (≈190 LOC, 0 sorries, 0 axioms).
Verified standalone via host `lake env lean` (Docker host down): built the dep oleans
(`Minimality`, `Unconditional`) into `.lake/build/lib/lean/Proofs/` with `lake env lean -o`,
then compiled the file — `#print axioms odd_abundant_coprime_three_ge` = `[propext,
Classical.choice, Quot.sound]` (no `sorryAx`, no `Lean.ofReduceBool`). Like its siblings
this chain is **not** registered in `Proofs.lean` (verified standalone, by project convention).

### What I did
Upgraded the prior `ω(n) ≥ 7` result to a lower bound on the number itself:
`odd_abundant_coprime_three_ge : Odd n → ¬3∣n → Nat.Abundant n → 37182145 ≤ n`
(= `5·7·11·13·17·19·23`, the product of the seven smallest primes ≥ 5).

### Key technique (what worked)
- **`domProd`** — the order-dual of the companion's `dom`: along a `GapList` whose entries
  are forced apart by primality, a strictly increasing list of primes that dominates the
  gap list entrywise has product **≥** the gap-list product (raw monotone product bounded
  *below*, vs `dom`'s antitone weight `p/(p−1)` bounded *above*). Same recursion, opposite
  direction; over ℕ it is cleaner than `dom` — `Nat.mul_le_mul` needs no nonneg side goals.
- Reused the existing gap machinery verbatim (`GapList`, `gap5..gap17`, the floor/Pairwise
  hypotheses); only added `gap19` (no prime in (19,23)) and `gapList_canon7`.
- Radical-divides-`n`: `Nat.prod_primeFactors_dvd n` gives `∏_{p∣n} p ∣ n`, so
  `n ≥ ∏_{p∣n} p` (`Nat.le_of_dvd`, `n ≠ 0` from `ω(n) ≥ 7`). The radical is the product of
  ≥7 distinct primes ≥5, hence ≥ the seven-smallest product by `domProd`.
- Sorted-list product = radical: `Finset.sort_perm_toList` + `Finset.prod_map_toList`.

### Honest status
A **partial** lower bound. The true minimum `5391411025` is ~145× larger because the witness
`5²·7·11·13·17·19·23·29` is **not squarefree** — the radical bound cannot see exponents or the
extra 8th prime. The radical bound is the natural structural milestone the prime-count
machinery delivers; closing to exact minimality needs the size/exponent structure (genuinely
harder, still open).

### Files modified
- proofs/Proofs/AbundantNumberOQ02OQ01LowerBound.lean (new)
- research/problems/abundant-number-oq-02-oq-01/knowledge.md (this entry)
- src/data/research/problems/abundant-number-oq-02-oq-01.json (leanFiles)

### Next steps
- Push beyond the radical: incorporate exponents / the ≥8th-prime obligation to raise the
  bound toward `5391411025`. Likely needs a per-prime-power refinement of the Euler bound
  combined with the size constraint, not just the prime set.

## Session 2026-06-28 (researcher-7) — SQUAREFREE case resolved EXACTLY (ω≥9, least = 33426748355)

**Mode**: REVISIT (RICH; radical bound `n ≥ 37182145` already closed) · **Outcome**: progress
(squarefree subproblem fully resolved). New file
`Proofs/AbundantNumberOQ02OQ01Squarefree.lean` (≈428 LOC, 0 sorries, 0 axioms).
Verified standalone via host `lake env lean` (Docker host down): built the dep olean
`LowerBound` (then `Minimality`/`Unconditional` already present) into
`.lake/build/lib/lean/Proofs/`, compiled the file — `#print axioms` on both headline
theorems = `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no `Lean.ofReduceBool`,
no `native_decide`). Not registered in `Proofs.lean` (sibling-chain convention).

### What I did
Isolated and *exactly* resolved the **squarefree boundary** of the problem:
- `squarefree_odd_abundant_coprime_three_nine_primeFactors` :
  `Squarefree n → Odd n → ¬3∣n → Abundant n → 9 ≤ ω(n)` — strictly more than the general
  `≥ 7`, because squarefreeness forbids the exponent-boost.
- `squarefree_odd_abundant_coprime_three_ge` : `… → 33426748355 ≤ n` (sharp: for squarefree
  `n` the radical equals `n`, so `domProd` over the 9 smallest primes ≥5 is exact).
- `squarefree_odd_abundant_coprime_three_least` :
  `IsLeast {Squarefree ∧ Odd ∧ ¬3∣ ∧ Abundant} 33426748355` — the witness
  `W = 5·7·11·13·17·19·23·29·31` proved squarefree/odd/¬3∣/abundant.

### Key technique (what worked)
- **Squarefree σ identity** `σ(n) = ∏_{p∣n}(p+1)`: specialize the Mathlib decomposition
  `sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul` with
  `Nat.factorization_eq_one_of_squarefree` (vₚ(n)=1), so each `∑_{i<2} pⁱ = 1+p`.
- **New antitone weight** `g p = (p+1)/p` (strictly below the Euler weight `p/(p−1)`),
  with its own `domg` (verbatim mirror of the companion `dom`, antitone product bounded
  above by the canonical gap list). The 8-smallest product `(6/5)…(30/29) ≈ 1.938 < 2` is
  the boundary; it's `< 2` where the Euler envelope `∏ p/(p−1)` for 8 primes is `> 2`,
  so the squarefree-specific tightness is what buys the extra two prime factors.
- Reused **verbatim** from the merged chain: `GapList`, `gapList_all_ge_two`, `gap5..gap19`,
  `domProd`, the prime-factor-≥5 argument. Added only `gap23`, `gap29`, `gapList8/9`.
- Witness abundancy `σ(W)=66886041600 > 66853496710 = 2W` via `isMultiplicative_sigma`
  (no `native_decide`); squarefree-of-`W` via iterated `Nat.squarefree_mul` + `Prime.squarefree`.

### Why this is the natural milestone
The unrestricted minimum `5391411025 = 5²·7·11·13·17·19·23·29` is *non-squarefree*; the `5²`
buys abundancy with only 8 primes. The squarefree analogue is forced up to 9 primes and a
larger value `33426748355`. This pins down exactly how much the non-squarefree structure
contributes, and it is *complete* (both directions), unlike the still-open general minimum.

### Files modified
- proofs/Proofs/AbundantNumberOQ02OQ01Squarefree.lean (new)
- research/problems/abundant-number-oq-02-oq-01/knowledge.md (this entry)
- src/data/research/problems/abundant-number-oq-02-oq-01.json (leanFiles + knowledge)

### Next steps
- Squarefree case CLOSED exactly. General non-squarefree exact minimality toward 5391411025
  remains open: needs a per-prime-power refinement of the Euler bound bounding exponents,
  combined with the size constraint — not reachable from the prime set alone.
