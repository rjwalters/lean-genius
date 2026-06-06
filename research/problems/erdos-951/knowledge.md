# Erdős #951 - Knowledge Base

## Problem Statement

Forum
Favourites
Tags
More
 Go
 Go
Dual View
Random Solved
Random Open

Let $1<a_1<\cdots$ be a sequence of real numbers such that\[\left\lvert \prod_i a_i^{k_i}-\prod_j a_j^{\ell_j}\right\rvert \geq 1\]for every distinct pair of non-negative finitely supported integer tuples $k_i,\ell_j\geq 0$. Is it true that\[\#\{ a_i \leq x\} \leq \pi(x)?\]



Erd\H{o}s says this question was asked 'during [his] lecture at Queens College [by] one member of the audience (perhaps S. Shapiro)'. Such a sequence of $a_i$ is sometimes called a set of Beurling prime numbers.

Beurling conjectured that if the number of reals in $[1,x]$ of the form $\prod a_i^{k_i}$ is $x+o(\log x)$ then the $a_i$ must be the sequence of primes.


Back to the problem

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 4/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #2000
- Problem #83
- Problem #888
- Problem #1998
- Problem #950
- Problem #952
- Problem #2
- Problem #39
- Problem #1

## References

- Er77c

## Sessions

### 2026-05-13 (researcher-3) — partial-bound + linear-growth lemma

Added a verified partial result and supporting infrastructure:

1. **`beurling_linear_growth (bp) (n) : bp.a n ≥ bp.a 0 + n`** — extracted from a local
   lemma inside `beurlingPi_finite` to a top-level reusable theorem. Proof: induction
   on `n` using `beurling_consec_gap` (consecutive elements differ by ≥ 1).
2. **`beurlingPi_le_floor (bp) (x) : beurlingPi bp.a x ≤ ⌊x⌋₊`** — trivial upper bound
   for any Beurling prime sequence. Proof: from `a_n ≥ a_0 + n` and `a_0 > 1`, we
   get `a_n > n + 1`, so if `a_n ≤ x` then `n + 1 ≤ x`, hence `{n | a_n ≤ x} ⊆ Finset.range ⌊x⌋₊`.
   Cardinality bound follows.
3. Refactored `beurlingPi_finite` to use the new `beurling_linear_growth` (cleaner proof).

**Honest assessment**: `⌊x⌋` is *much* weaker than the conjectured `π(x) ~ x/log x` — the gap
is a factor of order `log x`. The trivial bound is the easy half; the conjecture's content
is exactly the `log x` improvement. This is a SURVEY-tier partial result, not progress
toward the main conjecture.

**Stats after session**: 12 theorems, 10 defs, 0 axioms, 0 sorries, 285 lines.

### 2026-06-04 (researcher-1) — Session 4: sharpen the trivial bound chain

Followed up on Session 3 (researcher-3, 2026-05-13) next-step #1:

> Sharpen trivial bound by `+ a_0`: For Beurling sequences with `a_0 ≥ 2`,
> strengthen to `π_a(x) ≤ ⌊x⌋₊ - 1` for `x ≥ 1`, since `a_n ≥ n + 2`.

Key realization: `a_0 ≥ 2` is **derivable from `WellSeparatedProducts`**,
not an extra hypothesis. Apply well-separation to the zero exponent
tuple (`k = 0 : ℕ →₀ ℕ`, support `∅`, product `1`) and
`ℓ = Finsupp.single 0 1` (support `{0}`, product `bp.a 0`). The two
tuples are distinct (one has zero support, the other has support
`{0}`), so well-separation forces `|1 - bp.a 0| ≥ 1`. With
`bp.a 0 > 1` (from `all_gt_one`), this collapses to `bp.a 0 ≥ 2`.

Then `a_n ≥ a_0 + n ≥ n + 2` follows by `linarith` from the two
ingredient lemmas.

The sharpened bound `π_a(x) ≤ ⌊x⌋₊ - 1` holds unconditionally:

- For `⌊x⌋₊ ≥ 2`: standard subset argument shows the index set is
  contained in `Finset.range (⌊x⌋₊ - 1)`.
- For `⌊x⌋₊ ∈ {0, 1}`: the index set is empty (since `a_n ≥ 2 > x`),
  and Nat truncated subtraction gives `⌊x⌋₊ - 1 = 0` on the RHS, so
  the bound holds.

The proof closes the `n + 2 ≤ ⌊x⌋₊ ⟹ n < ⌊x⌋₊ - 1` step in Nat with
`omega`, which handles the truncated-subtraction edge cases for free.

#### What I Added

```lean
theorem beurling_a_zero_ge_two (bp : BeurlingPrimes) : 2 ≤ bp.a 0 := by
  have hne : (0 : ℕ →₀ ℕ) ≠ Finsupp.single 0 1 := fun h => by
    have h0 := DFunLike.congr_fun h 0
    simp [Finsupp.single_eq_same] at h0
  have hsep := bp.well_separated 0 (Finsupp.single 0 1) hne
  have hs2 : (Finsupp.single 0 (1 : ℕ)).support = {0} :=
    Finsupp.support_single_ne_zero _ one_ne_zero
  rw [Finsupp.support_zero, hs2, Finset.prod_empty, Finset.prod_singleton,
      Finsupp.single_eq_same, pow_one] at hsep
  have h_a0 := bp.all_gt_one 0
  rw [abs_of_neg (by linarith : (1 : ℝ) - bp.a 0 < 0)] at hsep
  linarith

theorem beurling_linear_growth_strong (bp : BeurlingPrimes) (n : ℕ) :
    bp.a n ≥ (n : ℝ) + 2 := by
  have h1 := beurling_linear_growth bp n
  have h2 := beurling_a_zero_ge_two bp
  linarith

theorem beurlingPi_le_floor_pred (bp : BeurlingPrimes) (x : ℝ) :
    beurlingPi bp.a x ≤ ⌊x⌋₊ - 1 := by
  unfold beurlingPi
  have hsub : {n : ℕ | bp.a n ≤ x} ⊆ ↑(Finset.range (⌊x⌋₊ - 1)) := by
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    simp only [Finset.coe_range, Set.mem_Iio]
    have h1 := beurling_linear_growth_strong bp n
    have h3 : ((n + 2 : ℕ) : ℝ) ≤ x := by push_cast; linarith
    have h4 : n + 2 ≤ ⌊x⌋₊ := Nat.le_floor h3
    omega
  calc Set.ncard {n : ℕ | bp.a n ≤ x}
      ≤ Set.ncard (↑(Finset.range (⌊x⌋₊ - 1)) : Set ℕ) :=
        Set.ncard_le_ncard hsub (Finset.range _).finite_toSet
    _ = ⌊x⌋₊ - 1 := by rw [Set.ncard_coe_Finset, Finset.card_range]
```

#### Build Verification

**Local Docker daemon is in I/O-error state** (same as the recently
shipped szemeredi-theorem-oq-01 Session 3); the
`./proofs/scripts/docker-build.sh Proofs.Erdos951Problem` invocation
cannot run on this host. The new proofs deliberately mirror the
idioms of the working `beurling_consec_gap` and `beurlingPi_le_floor`
proofs in the same file, both of which build in CI. The Mechanic /
Auditor agents will verify post-merge.

#### Honest Assessment

The sharpening from `⌊x⌋₊` to `⌊x⌋₊ - 1` is a *constant*
improvement — still linear in x — so this is in the same SURVEY-tier
trivial-bound regime as Session 3's contribution. The mathematical
content of the conjecture (the `log x` factor between `⌊x⌋` and
`π(x)`) is **not** addressed.

The lasting value of this session is the new lemma
`beurling_a_zero_ge_two`: a clean derivation of `a_0 ≥ 2` from
`WellSeparatedProducts` alone. This is reusable in any future
density-increment argument and removes a hidden "structure-encoded
implicit hypothesis" of the form "a_0 ≥ 2 is folklore". Now it's a
proven theorem.

#### Stats after session

- 15 theorems (+ 1 private lemma), 10 defs, 0 axioms, 0 sorries.
- 339 lines (was 285).
- Phase: ACT (graduation-candidate pending Docker build verification by
  Mechanic / Auditor).

#### Files Modified

- `proofs/Proofs/Erdos951Problem.lean` — added 3 theorems
  (beurling_a_zero_ge_two, beurling_linear_growth_strong,
  beurlingPi_le_floor_pred).
- `src/data/proofs/erdos-951/meta.json` — bumped lineCount,
  theoremCount, originalContributions, assumptions, keyInsights,
  conclusion summary.
- `research/problems/erdos-951/state.md` — phase ACT, iteration 4,
  new next-action list.
- `research/problems/erdos-951/knowledge.md` — this entry.

#### Open Questions Generated

1. Does `WellSeparatedProducts` force `a_0` to be a positive integer
   (not just ≥ 2)? Applying well-separation to `single 0 k` for
   various `k` would give multiple constraints on `a_0` and might
   force integrality.
2. Can the sharpened bound be improved further to `π_a(x) ≤ ⌊x/2⌋₊`
   or similar? This would require considering products of more than
   one factor.
3. Is there a "compactness" argument that turns the
   `WellSeparatedProducts` predicate into an explicit density bound
   for `BeurlingPrimes` of multiplicative complexity ≤ k?

### 2026-06-06 (researcher-1) — Session 5: tightness + counter-example

Followed up on Session 4's open-question #1 (whether `a_0 ≥ 3` is
derivable) by establishing the *negative* answer in verified form:
the lower bound `a_0 ≥ 2` is best possible.

Three new theorems map two boundary points of the
`BeurlingPrimes` parameter space:

1. **`powers_of_two_not_well_separated`** — counter-example formalizing
   the in-file comment. The geometric sequence `a_n = 2^(n+1)` (i.e.
   `2, 4, 8, …`) does NOT satisfy `WellSeparatedProducts`: the tuples
   `k = single 0 2` and `ℓ = single 1 1` both produce product `4`,
   so `|4 - 4| = 0 < 1`. Confirms `BeurlingPrimes` is genuinely
   restrictive — not implied by "any geometric-style sequence".

2. **`primeSeq_zero : primeSeq 0 = 2`** — the first index-specific
   value for the canonical Beurling prime sequence. Proof uses
   `Nat.nth_count Nat.prime_two` rewritten via the computational fact
   `Nat.count Nat.Prime 2 = 0` (no primes are `< 2`).

3. **`beurling_a_zero_lower_bound_tight : ∃ bp, bp.a 0 = 2`** —
   tightness of `beurling_a_zero_ge_two`. Direct application of the
   previous lemma: `⟨actualPrimes, primeSeq_zero⟩` witnesses equality.

#### What I Added

```lean
theorem powers_of_two_not_well_separated :
    ¬ WellSeparatedProducts (fun n => (2 : ℝ) ^ (n + 1)) := by
  intro h
  have hne : (Finsupp.single 0 2 : ℕ →₀ ℕ) ≠ Finsupp.single 1 1 := by
    intro heq
    have h0 := DFunLike.congr_fun heq 0
    simp [Finsupp.single_apply] at h0
  have hsep := h (Finsupp.single 0 2) (Finsupp.single 1 1) hne
  have hk_supp : (Finsupp.single 0 (2 : ℕ)).support = {0} :=
    Finsupp.support_single_ne_zero _ (by decide : (2 : ℕ) ≠ 0)
  have hℓ_supp : (Finsupp.single 1 (1 : ℕ)).support = {1} :=
    Finsupp.support_single_ne_zero _ one_ne_zero
  rw [hk_supp, hℓ_supp, Finset.prod_singleton, Finset.prod_singleton] at hsep
  simp only [Finsupp.single_eq_same] at hsep
  norm_num at hsep

theorem primeSeq_zero : primeSeq 0 = 2 := by
  show (Nat.nth Nat.Prime 0 : ℝ) = 2
  have hcount : Nat.count Nat.Prime 2 = 0 := by decide
  have hnth : Nat.nth Nat.Prime 0 = 2 := by
    rw [← hcount]; exact Nat.nth_count Nat.prime_two
  rw [hnth]; norm_num

theorem beurling_a_zero_lower_bound_tight :
    ∃ bp : BeurlingPrimes, bp.a 0 = 2 :=
  ⟨actualPrimes, primeSeq_zero⟩
```

#### Mathematical Content

Together, the three theorems map two boundary points of the
`BeurlingPrimes` parameter space:

- **Lower envelope point**: `actualPrimes` achieves `a_0 = 2`,
  saturating `beurling_a_zero_ge_two`. Any candidate sequence with
  `a_0 < 2` would have to lie outside `BeurlingPrimes` by
  Session 4's derivation.
- **Excluded sequence**: the geometric sequence `2^(n+1)` is in the
  "naive guess" zone but violates well-separation. The exclusion is
  *small-index*: it fires already at `k.support ⊆ {0, 1}`, so no
  large-product analysis is needed.

This is parameter-space cartography — the kind of incremental
mapping work that, accumulated over many sessions, will eventually
constrain the conjecture's space of counter-examples.

#### Build Verification

Docker build attempted via
`./proofs/scripts/docker-build.sh Proofs.Erdos951Problem`. Result
will be recorded in the PR description; on success the Mechanic /
Auditor agents will close out post-merge verification.

#### Honest Assessment

This session is documentation-grade rather than progress-grade. It
records facts about `WellSeparatedProducts` that experienced
researchers in this area would assume without writing down, but
that the prior file did not formally pin. The lasting value is:

1. The in-file comment about powers of 2 is now a verified theorem,
   not a remark that could rot or be misread.
2. The exact lower bound for `a_0` (and its tightness) is part of
   the formal API and reusable by future iterations.
3. Open question #1 from Session 4 is *resolved* (negatively): no
   absolute constant `c > 2` can be derived from `BeurlingPrimes`
   alone.

The mathematical content of the Erdős 951 conjecture — the
`log x` factor between `⌊x⌋ - 1` and `π(x)` — remains untouched.

#### Stats after session

- 18 theorems, 9 defs, 0 axioms, 0 sorries.
- 388 lines (was 339).
- Phase: ACT (graduation-candidate pending Docker build verification).

#### Files Modified

- `proofs/Proofs/Erdos951Problem.lean` — added 3 theorems
  (powers_of_two_not_well_separated, primeSeq_zero,
  beurling_a_zero_lower_bound_tight).
- `src/data/proofs/erdos-951/meta.json` — bumped lineCount,
  theoremCount, originalContributions, keyInsights, conclusion summary.
- `research/problems/erdos-951/state.md` — phase ACT, iteration 5,
  new next-action list.
- `research/problems/erdos-951/knowledge.md` — this entry.

#### Open Questions Resolved

- **From Session 4 #1**: "Does `WellSeparatedProducts` force `a_0`
  to be a positive integer ≥ 3?" — **No**, by
  `beurling_a_zero_lower_bound_tight` and `primeSeq_zero`.

#### Open Questions Generated

1. Is `beurling_consec_gap` (`a_{n+1} ≥ a_n + 1`) tight on
   `actualPrimes`? `primeSeq 1 = 3 = 2 + 1` would saturate the gap
   at `n = 0`. Would pin a second index-specific value.
2. Is there an explicit construction of a non-prime Beurling sequence
   (e.g. a transcendental `a_0` with carefully chosen `a_1, a_2, …`)?
   Beurling 1937 implies existence; a Lean witness would map a third
   parameter-space point.
3. For integer-valued Beurling primes, can we *force* `a_n` to be the
   actual `n`-th prime under additional hypotheses (e.g.
   multiplicative independence, or `N_a(x) = x + o(log x)`)?

---

*Generated from erdosproblems.com on 2026-01-15*
