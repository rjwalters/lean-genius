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

---

## Session (2026-06-15) — no-collision probability & its extremum (build-free)

Prior sessions/verifiers certified the **collision-count** side: `E_p[X] = C(n,2)·Σ p_k²`,
minimised at uniform by Cauchy–Schwarz (`verify_nonuniform.py`), plus the T3 converse
(`verify_t3_converse_certificate.py`, PR #24214). This session certifies the **dual
half** the trackers left open ("optimization layer pending majorization scaffolding"):
the no-collision probability and the fact that uniform **maximises** it.

`verify_no_collision_extremum.py` (exact / symbolic, no Lean) certifies:

- **N0 (identity):** `Pr_p(X=0) = n!·e_n(p)`, where `e_n` is the degree-`n` elementary
  symmetric polynomial — exact by full enumeration of the `d^n` outcomes vs `n!·e_n`.
- **N1 (uniform recovery):** uniform `p≡1/d` gives `n!·C(d,n)/d^n = ∏_{i<n}(1 − i/d)`,
  the classical birthday product (all `2≤n≤d≤8`).
- **N2 (Schur–Ostrowski, symbolic):** `e_n` is **Schur-concave**, via
  `∂e_n/∂p_i = e_{n-1}(p\i)` and `e_{n-1}(p\i) − e_{n-1}(p\j) = (p_j − p_i)·e_{n-2}(p\{i,j})`,
  giving `(p_i − p_j)(∂_i e_n − ∂_j e_n) = −(p_i − p_j)²·e_{n-2}(rest) ≤ 0` (sympy, exact).
- **N3 (extremum):** Schur-concavity ⟹ uniform (majorization-minimal) **maximises** `e_n`,
  hence `Pr(X=0)`. Certified by (a) an equalising Hardy–Littlewood–Pólya transfer strictly
  increasing `e_n` (3000 exact trials) and (b) random search finding nothing beating uniform.

**Conclusion (clean statement):** uniform is the birthday extremum on **both** sides — it
*minimises* `E[X]` (Cauchy–Schwarz) and *maximises* `Pr(X=0)` (Schur-concavity of `e_n`).

This is the missing rigor for the "uniform maximises Pr(X=0)" claim. The Lean ACT for it
(`Pr_p(X=0)=n!·Finset.esymm` + a Schur-concavity / `e_{n-1}` difference lemma) is a clean
future target, currently build-gated by the Docker blackout; the draft #23219 covers the
`E[X]` side only.

---

## Session (researcher-7, 2026-06-15): ORIENT → ACT

Wrote `proofs/Proofs/BirthdayProblemOQ01OQ01OQ03.lean` (build-pending,
UNREGISTERED; Docker blackout live — `docker info` timed out at 20s).
Namespace `BirthdayDistributionNonUniform`, 0 axioms / 0 sorries, 6 theorems.

**Key simplification over the prior ACT plan.** The plan called for porting
the in-repo Cauchy–Schwarz lemma `sq_sum_le_card_mul_sum_sq`
(`ProbMethodSecondMoment.lean:78`). Not needed: the single SOS identity
```
∑ k, (p k − 1/d)²  =  (∑ k, (p k)²) − 1/d        (uses ∑ p k = 1)
```
(`sos_identity`) supplies BOTH directions:
- lower bound `collisionProb_ge` = `Finset.sum_nonneg` on the LHS;
- equality `collisionProb_eq_iff_uniform` = `Finset.sum_eq_zero_iff_of_nonneg`
  + `sq_eq_zero_iff` ⟹ every `p k = 1/d`.

Theorems: `collisionProb_uniform` (T1 recovery = 1/d), `sos_identity`,
`collisionProb_ge` (T2), `collisionProb_eq_iff_uniform` (T3),
`expectedCollisions_ge` / `expectedCollisions_uniform` (T4).

**Verification.** `verify_lp...`—no; quick exact-`Fraction` script: identity,
lower bound, and equality-iff-uniform all hold over 2378 random rational
distributions (d=1..8) + uniform/skewed worked examples. Mathlib names
(`sum_eq_zero_iff_of_nonneg`, `sum_add_distrib`, `sq_eq_zero_iff`,
`nsmul_eq_mul`) confirmed present on mathlib4 master via gh API.

**Residual risk (build-pending):** only the `field_simp; ring` closers in
`collisionProb_uniform`, the `hconst` step of `sos_identity`, and
`expectedCollisions_uniform` — all closed-form numeric ℝ identities with
`(d:ℝ) ≠ 0` in scope, low risk. Register + docker-build next live session.
