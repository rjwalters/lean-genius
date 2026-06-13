# Knowledge Base: birthday-problem-oq-01-oq-01-oq-03

Non-uniform generalization of the collision-count analysis.

---

## Problem Understanding

**Open question (from parent `birthday-problem-oq-01-oq-01`):** Does the formal
analysis of the collision count `X` generalize to *non-uniform* birthday
distributions (unequal day probabilities), the relevant setting for hash-collision
analysis in cryptography?

The parent file `proofs/Proofs/BirthdayProblemOQ01OQ01.lean` formalizes the
**uniform** model: assignments `f : Fin n → Fin d` under the counting measure
(every `f` equally likely, `d^n` total). Its headline distributional facts are:

- `collisionCount f = |{(i,j) : i < j, f i = f j}|`
- `X = 0 ↔ Injective` and `#{f | X=0} = descFactorial d n`
- `Pr(X = 0) = descFactorial(d,n) / d^n`
- indicator decomposition `X = Σ_{i<j} I_{ij}`
- `E[X] = C(n,2)/d` (defined as `expectedPairs n d` in `BirthdayProblemOQ01`)
- `Var(X) = C(n,2)(d-1)/d²`, `Var(X) ≤ E[X]`

The per-pair collision probability in the uniform model is `1/d`: for fixed
`i ≠ j`, `Pr(f i = f j) = Σ_v (1/d)(1/d) = d·(1/d²) = 1/d`.

---

## Insights

### The generalization is clean and the answer is YES

Model: independent day choices with a probability vector `p : Fin d → ℝ`,
`0 ≤ p k` and `∑ k, p k = 1`. Each of the `n` items independently lands on day
`k` with probability `p k`.

1. **Per-pair collision probability becomes `∑ k, (p k)²`.** For `i ≠ j`,
   `Pr(item i and item j share a day) = Σ_v Pr(both = v) = Σ_v (p v)²`.
   This replaces the uniform `1/d`.

2. **Expected collision count.** By linearity of expectation over the
   `C(n,2)` pair-indicators (exactly the parent's `collisionCount_eq_sum_indicators`
   structure, now with weighted indicators):
   ```
   E[X] = C(n,2) · ∑ k, (p k)²
   ```
   Recovers the parent: uniform `p ≡ 1/d` gives `∑ (1/d)² = d·(1/d²) = 1/d`,
   hence `E[X] = C(n,2)/d`. ✓

3. **Uniform MINIMIZES collisions (the sharp, cryptographically meaningful
   statement).** By Cauchy–Schwarz applied to `p` and the all-ones vector:
   ```
   1 = (∑ k, p k)²  ≤  d · ∑ k, (p k)²      ⟹   ∑ k, (p k)² ≥ 1/d,
   ```
   with equality iff `p` is uniform. So **any** non-uniformity strictly
   increases the expected number of collisions. This is precisely why uniform
   hashing minimizes expected collisions — the result a cryptographer cares
   about, and it goes *beyond* a mechanical re-derivation of `E[X]`.

So the OQ resolves to a precise, provable triple:
`E[X] = C(n,2)·Σpₖ²`  +  `Σpₖ² ≥ 1/d`  +  `equality ↔ uniform`.

### The hard inequality is already available in-repo

`ProbMethodSecondMoment.lean:78` proves (privately, over ℚ)
```
sq_sum_le_card_mul_sum_sq (s : Finset α) (f : α → ℚ) :
    (s.sum f)^2 ≤ ↑s.card * s.sum (fun a => f a ^ 2)
```
by `Finset.induction_on` + `sub_sq` expansion + sum of squares ≥ 0. The exact
same proof works over ℝ; Mathlib also supplies the general inner-product form
`inner_mul_le_norm_mul_norm`. Setting `s = univ : Finset (Fin d)` and `f = p`
gives `1 ≤ d · Σpₖ²` directly. **No missing Mathlib infrastructure for the
minimization theorem.**

---

## Recommended formal target (ACT plan)

New file `proofs/Proofs/BirthdayProblemOQ01OQ01OQ03.lean`, namespace
`BirthdayDistributionNonUniform`, importing the parent. Mirror the parent's
*definitional* rigor (the parent defines `expectedPairs` as a closed formula
rather than building a measure space, so matching that level is consistent and
honest):

```lean
variable {d : ℕ} (p : Fin d → ℝ)

/-- Per-pair collision probability for a day-distribution p. -/
def collisionProb : ℝ := ∑ k, (p k) ^ 2

/-- Expected collision count among n items: C(n,2) · Σ pₖ². -/
def expectedCollisions (n : ℕ) : ℝ := (n.choose 2 : ℝ) * collisionProb p

-- (T1) Recovery of the parent: uniform p ≡ 1/d gives collisionProb = 1/d,
--      hence expectedCollisions n = C(n,2)/d  = (expectedPairs n d : ℝ).
theorem collisionProb_uniform (hd : 0 < d) :
    collisionProb (fun _ => (1 : ℝ) / d) = 1 / d := by ...

-- (T2) Cauchy–Schwarz lower bound: uniform minimises collisions.
theorem collisionProb_ge (hp : ∀ k, 0 ≤ p k) (hsum : ∑ k, p k = 1) (hd : 0 < d) :
    1 / d ≤ collisionProb p := by
  have hcs : (∑ k, p k) ^ 2 ≤ (d : ℝ) * ∑ k, (p k) ^ 2 := <CS, port of sq_sum_le_card_mul_sum_sq>
  rw [hsum] at hcs; ... -- 1 ≤ d · collisionProb ⟹ 1/d ≤ collisionProb

-- (T3) Equality characterisation: collisionProb p = 1/d ↔ p uniform.
--      From CS equality case (all p k equal) + hsum ⟹ p k = 1/d.

-- (T4) Monotone consequence: expectedCollisions n p ≥ C(n,2)/d, i.e.
--      non-uniformity never decreases expected collisions.
```

Optional stretch (only if a genuine product-PMF expectation is wanted): build
the model on `PMF (Fin d)` and prove `E[X] = C(n,2)·Σpₖ²` via
`PMF`/`Finset.sum` linearity. This is the moderate-infrastructure part
(~independence + product measure bookkeeping) and is **not** required to close
the OQ at the parent's rigor level — T1–T4 already answer it.

---

## Dead Ends / Cautions

- Do **not** attempt a full measure-theoretic product space as the *primary*
  route — it is far heavier than the OQ requires and the parent itself avoids it.
- The equality case (T3) needs the CS equality characterisation; if porting
  that is fiddly, T3 can be stated as `... ↔ ∀ k, p k = 1/d` and proved from the
  `Σ (p a - p b)² = 0` term in the induction, or deferred — T1, T2, T4 alone
  already constitute a defensible closure.

---

## Status / Blocker

- **Phase:** OBSERVE → **ORIENT** (this session: precise statement fixed,
  Mathlib path identified, in-repo CS lemma located, draft skeleton written).
- **Decision:** SURVEY. The math is fully understood and the formalization is
  BUILD-tractable (<300 lines, no missing Mathlib infra).
- **Blocker is infrastructure, not mathematics:** ACT (writing + compiling the
  new file) is gated by the Docker/`lake build` verification outage of
  2026-06-13 — a new proof file cannot be machine-checked right now, and shipping
  unverified Lean as "complete" is against policy. Resume ACT when Docker is back.
