# Knowledge Base: nth-root-irrational-oq-03

Insights accumulated during research on this problem (Hermite-Lindemann / Lindemann-Weierstrass).

---

## Problem Understanding (Iteration 1, researcher-10, 2026-05-12)

This slug was placed under the `nth-root-irrational` parent during seeker batch initialization (2026-05-12 13:06 UTC, PR #18263), but the Lindemann–Weierstrass / Hermite–Lindemann content it covers is **transcendence theory**, which is orthogonal to the parent's *algebraic irrationality of irreducible polynomial roots* material. The slug's effective home is the existing `e-transcendental-oq-*` family (`oq-01`, `oq-02`, `oq-03`) and `hermite-lindemann` (no slug yet, but `HermiteLindemann.lean` exists).

## Insights

### Insight 1 — The "open question" is mostly already infrastructure

The problem statement (transcendence of $e^\alpha$ for nonzero algebraic $\alpha$, and the algebraic-independence form for $\Q$-linearly-independent $\alpha_1, \dots, \alpha_n$) is **already stated and axiomatized** in `proofs/Proofs/HermiteLindemann.lean:147` via:

```lean
axiom hermite_lindemann :
    ∀ α : ℂ, α ≠ 0 → IsAlgebraic ℚ α → Transcendental ℤ (Complex.exp α)
```

with 390 lines of supporting pedagogical exposition, statement of the LW theorem, and corollary derivations for $e$ (Wiedijk #67) and $\pi$ (Wiedijk #53). The "open question" framing is misleading: the *statement* is closed; what remains is *proof* of the axiomatized statement, plus surrounding bridge work.

### Insight 2 — Two tractable adjacent axioms (in OQ03 sibling)

`ETranscendentalOQ03.lean` contains two axioms feeding the $\mu(e) = 2$ irrationality-measure result:

1. `irrational_liouvilleWith_two : ∀ x, Irrational x → LiouvilleWith 2 x` (Dirichlet's approximation theorem lower bound)
2. `e_not_liouvilleWith_gt_two : ∀ p > 2, ¬LiouvilleWith p (exp 1)` (sharp upper bound from regular CF expansion of $e$)

Axiom (1) is a standard Mathlib-provable result (Dirichlet's theorem on rational approximations: every irrational has at least one infinite sequence of approximants $|x - p/q| < 1/q^2$). It should reduce to existing `Mathlib.NumberTheory.DiophantineApproximation` API.

Axiom (2) is harder but uses the *known* regular continued fraction $e = [2; 1, 2k, 1]_{k=1}^\infty$ (Euler 1737). The proof requires:

- Linking the partial quotients $a_n$ to the convergents $p_n/q_n$
- Bounding $q_{n+1} \leq (2k+1) q_n + q_{n-1}$, hence $q_n$ grows polynomially-in-$\sqrt{n}$ in the relevant subsequence
- Concluding that the approximation quality is at most $1/q^{2+o(1)}$

Mathlib has `Mathlib.NumberTheory.ContinuedFractions.*` API that may cover most of this; the bottleneck is matching the project's `LiouvilleWith` formulation.

### Insight 3 — The full HL axiom is 800-1500 lines of work

`hermite_lindemann` is the deep result. A complete formal proof requires:

1. **Auxiliary polynomial machinery**: $f_p(x) = x^{p-1}(x-\alpha)^p (x - 2\alpha)^p \cdots (x - n\alpha)^p / (p-1)!$ for large prime $p$.
2. **Integral analysis**: Define $F(x) = \sum_{j \geq 0} f^{(j)}(x)$; key identity $\int_0^{k\alpha} f(t) e^t dt = e^{k\alpha} F(0) - F(k\alpha)$.
3. **Prime-selection contradiction**: Show $S = \sum_k \beta_k I_k$ is simultaneously a nonzero integer divisible by $p$ (lower-bound $\geq 1$) and bounded by $C^p / (p-1)!$ in absolute value (upper-bound $\to 0$). Take $p$ larger than $\max(|\alpha|, |\beta_0|)$ to derive a contradiction.

Estimating proof length:

- Polynomial setup + derivatives + factorial accounting: ~200 lines
- Integral identity (integration by parts $p$-many times): ~150 lines
- Integer-and-divisibility argument: ~250 lines
- Bound argument (Stirling + max-modulus): ~150 lines
- Coercion between $\mathbb{Z}[\alpha]$ and $\mathbb{C}$: ~100 lines
- Glue + main theorem statement: ~50 lines

Total: roughly 900 lines, conservatively. Mathlib has had an active Lindemann–Weierstrass formalization PR (search: `mathlib4 lindemann`) — the right move long-term is to **wait for Mathlib upstream** and then bridge, rather than re-formalize.

### Insight 4 — Project status is "axiomatized", not "verified"

For meta.json on this slug's gallery entry (if/when created), the appropriate badge is `axiom` and status is `axiomatized`. The full proof depends on:

- `axiom hermite_lindemann` (HermiteLindemann.lean) — the marquee assumption
- 2 axioms in `ETranscendentalOQ03.lean` — sibling slug, not strictly this one's
- 4 sorries across `eTranscendental.lean`, `ETranscendentalOQ01.lean`, `ETranscendentalOQ02.lean`, `PiTranscendental.lean` — partial-proof in-progress siblings

Per the Axiom Integrity Policy in CLAUDE.md, this slug must NEVER be marked `verified` while these assumptions remain.

## Dead Ends

None recorded for this slug yet — Iteration 1 is the first session.

## Promising Next-Iteration Targets

### Target A (S2): Discharge `irrational_liouvilleWith_two`

**Statement to prove:**

```lean
theorem irrational_liouvilleWith_two (x : ℝ) (hx : Irrational x) : LiouvilleWith 2 x
```

**Proof strategy (Mathlib API):**

The Mathlib definition of `LiouvilleWith` (in `Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith`) requires a constant $C > 0$ and infinitely many rationals $p/q$ with $|x - p/q| < C/q^p$. For $p = 2$, this is exactly Dirichlet's approximation theorem.

Mathlib has (or should have, depending on pin):

- `Irrational.exists_int_nat_lt` or similar
- `Real.exists_rat_btwn` — interval density
- `Nat.exists_pos_of_lt` — bound construction

Candidate sketch:

```lean
theorem irrational_liouvilleWith_two (x : ℝ) (hx : Irrational x) : LiouvilleWith 2 x := by
  -- LiouvilleWith p x ↔ ∃ C, ∀ᶠ q in atTop, ∃ p, |x - p/q| < C/q^p
  -- Dirichlet: ∀ N, ∃ q ∈ [1, N], ∃ p, |x - p/q| < 1/(qN) ≤ 1/q^2
  -- Use C = 1, take q large
  sorry
```

**Risk:** Mathlib v4.26.0 (the pin used here) may have slightly different API names; ~1-2 hours to chase the right lemmas.

### Target B (S3): Lindemann–Weierstrass bridge to Mathlib

**Goal:** Survey current Mathlib state of `Mathlib.NumberTheory.Transcendental` (or wherever the LW formalisation is landing). If a `transcendental_exp_of_isAlgebraic_ne_zero` or similar is upstream, write a bridge lemma; otherwise document the upstream PR status and add a comment to `HermiteLindemann.lean` referencing the upstream effort.

### Target C (S4 or beyond): `e_not_liouvilleWith_gt_two`

Harder — but isolated. The continued-fraction route is the right strategy. If `Mathlib.NumberTheory.ContinuedFractions` has the regular CF of $e$ pre-computed (unlikely on v4.26.0), bridge directly; otherwise this requires standalone CF infrastructure and is multi-session.

## Open Questions for Future Iterations

- What is the current state of `mathlib4` Lindemann–Weierstrass PRs as of 2026-05-12? (Web check needed in S2.)
- Should this slug be **renamed/aliased** to align with the existing `e-transcendental-*` or `hermite-lindemann` family? Or should `nth-root-irrational-oq-03` remain as a curated cross-reference entry pointing to the real work in those slugs?
- Are there any *new* mathematical content gaps (i.e., theorems not in any existing file) that this slug could fill? (Initial scan suggests no — the territory is well-covered.)

## Cross-References

- **Sibling slugs**: `e-transcendental-oq-01`, `e-transcendental-oq-02`, `e-transcendental-oq-03` — directly related
- **Lean files**: `proofs/Proofs/HermiteLindemann.lean`, `eTranscendental.lean`, `ETranscendentalOQ0{1,2,3}.lean`, `PiTranscendental.lean`
- **Parent**: `nth-root-irrational` (algebraic irrationality of irreducible-polynomial roots) — orthogonal in technique despite shared "expanding $\Q$" theme
- **Adjacent transcendence work**: `angle-trisection-cos-20-gal-oq-01-oq-03` (cyclotomic $\Phi_{2p}(-1) = p$, requires algebraic-not-transcendental machinery), `algebraic-numbers-countable-oq-02-oq-04` (countability bounds)
