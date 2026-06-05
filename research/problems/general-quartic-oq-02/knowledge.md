# Knowledge: general-quartic-oq-02

> Numerical instabilities in Ferrari's quartic formula

## Iteration Log

### S1 OBSERVE (2026-05-12)

First substantive iteration. Established formal three-part decomposition
(OQ-02.a / .b / .c — see `problem.md`), surveyed prior art, mapped three
candidate formalization approaches, and selected the OQ-02.c
**biquadratic-limit identity** as the S2 target on tractability grounds.

### S2 ACT — SCAFFOLD (2026-05-12)

Implemented S2 SCAFFOLD per state.md. Added three theorems to
`proofs/Proofs/GeneralQuartic.lean` (Part VI.5):

1. **`resolvent_cubic_q_zero`** (sorry-free, `unfold + ring`): rewrites
   the resolvent cubic at `q = 0` in its cleaner constant-term form
   `4p³ − 4pr` (the `−q²` contribution vanishes).
2. **`resolvent_root_neg_p_half_at_q_zero`** (sorry-free, `simp + ring`):
   `m = -p/2` is always a root at `q = 0`. This is the *trivial*
   resolvent root: it makes `α² = 2m + p = 0`, so the Ferrari `β` factor
   is the indeterminate `0/0` form. The non-degenerate Ferrari branch
   (Approach A) requires a different resolvent root.
3. **`ferrari_biquad_limit`** (`sorry`, deferred to S3): the
   biquadratic-limit identity — at `q = 0`, for `(p, r) ≠ (0, 0)`, there
   exists a resolvent root `m` with `2m + p ≠ 0`, and at any such `m`
   the four Ferrari roots squared lie in the biquadratic root pair
   `{(-p + √(p²−4r))/2, (-p − √(p²−4r))/2}`.

**Hypothesis `p ≠ 0 ∨ r ≠ 0` justification.** At `(p, r) = (0, 0)`, the
resolvent cubic reduces to `8X³`, whose only root is `m = 0 = -p/2`,
hence no non-degenerate Ferrari branch exists. Excluding this single
parameter point keeps the statement vacuously satisfied where the
biquadratic identity is meaningless (the depressed quartic is
`y⁴ = 0`).

**S3 DECOMPOSITION** (next action):

The `sorry`-marked `ferrari_biquad_limit` decomposes into two
independent sub-steps:

- **Sub-step A: non-degenerate resolvent root exists.**
  Show `∃ m, (resolventCubic p 0 r).eval m = 0 ∧ 2*m + p ≠ 0` given
  `p ≠ 0 ∨ r ≠ 0`. Strategy: by contradiction, suppose every root
  satisfies `2m + p = 0`, i.e. `m = -p/2`. Then `(resolventCubic p 0 r)`
  has `m = -p/2` as a *triple* root, so it equals `C 8 * (X + C(p/2))^3`.
  Expanding (in `Polynomial ℂ`) and comparing coefficients:
  - Coeff of `X²`: actual `20p`, triple-root `12p` ⟹ `p = 0`.
  - With `p = 0`: `resolventCubic 0 0 r = C 8 * X^3 + C (-8r) * X
    = X (C 8 * X^2 + C (-8r))`. For triple-root at `0`, this requires
    `r = 0`.
  - Contradicts `p ≠ 0 ∨ r ≠ 0`. QED.

  Concrete Lean strategy: prove `m = -p/2` is *not* a triple root unless
  both `p = 0` and `r = 0`, using `Polynomial.degree_eq_card_roots` or
  manually counting via Vieta. Roots of `resolventCubic` over ℂ come
  with multiplicity 3 (total) and `m = -p/2` has multiplicity ≤ 2 unless
  `(p, r) = (0, 0)` ⟹ other root exists.

- **Sub-step B: algebraic root-matching at a non-degenerate `m`.**
  Assume `(resolventCubic p 0 r).eval m = 0` and `2m + p ≠ 0`. Set
  `α := Complex.cpow (2m + p) (1/2)`, so `α² = 2m + p ≠ 0` (cpow
  property). Since `q = 0` and `α ≠ 0`, `β = 0` by the parent file's
  `ferrariRoots` definition (the `if` collapses to the `else` branch
  with `q = 0` in the numerator). Then:
  ```
  disc1 = α² − 4(p/2 + m + 0) = α² − 2p − 4m = (2m + p) − 2p − 4m
        = -p − 2m = -(2m + p) = -α²
  ```
  Symmetric for `disc2 = -α²`. So `sqrt1 = sqrt2 = Complex.cpow (-α²) (1/2)`,
  and the four Ferrari roots are
  `y₁ = (-α + sqrt)/2`, `y₂ = (-α − sqrt)/2`, `y₃ = (α + sqrt)/2`,
  `y₄ = (α − sqrt)/2`. Compute `yᵢ²` and use the resolvent cubic
  condition `8m³ + 20pm² + (16p² - 8r)m + 4p³ - 4pr = 0` (at `q = 0`)
  to verify each `yᵢ² ∈ {z₁, z₂}` where `z_{1,2} = (-p ± √(p²-4r))/2`.

  Key intermediate identity (provable by `ring` + the resolvent
  equation): given `α² = 2m + p` and `8m³ + 20pm² + (16p² - 8r)m
  + 4p³ - 4pr = 0`, we have `α⁴ = -4 z₁ z₂ + 2 z₁ (-p + s) + ...`
  — or, more cleanly, `(α² + p)² = 4r` (via the original Ferrari
  resolvent derivation). This gives `α² = -p ± s = 2z_{1,2}`, hence
  `α²/2 = z₁` or `z₂`. Then `yᵢ² = ((±α + sqrt)/2)² = (α² ± 2α sqrt
  + sqrt²)/4 = (α² + sqrt² ± 2α sqrt)/4`. Using `sqrt² = -α²`,
  `α² + sqrt² = 0`, so `yᵢ² = ±α sqrt / 2`. And `α sqrt = α
  Complex.cpow (-α²) (1/2) = ±i α²`, giving `yᵢ² = ±i α² / 2 = ±i z_{1,2}`...
  hmm, this doesn't quite land. Let me re-examine in S3.

  *Alternative*: just use `biquadratic_simple` directly. Each `yᵢ` is a
  root of the depressed quartic (by `ferrari_roots_are_roots`), hence
  `yᵢ²` is a root of the biquadratic `z² + pz + r = 0`, hence equal to
  `z₁` or `z₂`. This bypasses the explicit-formula expansion entirely
  and uses only `biquadratic_simple` (already in the file) and
  `ferrari_roots_are_roots` (axiomatized via `ferrari_roots_verify`).

  *Tradeoff*: the alternative path *uses* the parent's
  `ferrari_roots_verify` axiom. The explicit-formula path would be more
  satisfying as it would corroborate the axiom, but it is also harder.
  S3 should attempt the explicit-formula path first; fall back to the
  alternative if blocked.

**Files modified in S2 SCAFFOLD:**
- `proofs/Proofs/GeneralQuartic.lean`: +68 lines (Part VI.5 added,
  three theorems, three `#check` summary entries).

**Metrics after S2:**
- Lean theoremCount: 9 → 12 (+3)
- Lean sorryCount: 0 → 1 (the deferred `ferrari_biquad_limit`)
- Lean axiomCount: 6 (unchanged)
- LOC: 360 → 428 (+68, under 100-LOC budget)

### S3 ACT — DISCHARGE (2026-05-12)

`ferrari_biquad_limit` discharged. Single-theorem proof; no helper
declarations added (~70 LOC of inline proof, including doc-strings).

**Strategy adopted.** The "Alternative" path proposed in the S2 DECOMPOSITION
note above turned out to be the right call — explicit-formula expansion of
`yᵢ^2 = ((±α + sqrtᵢ)/2)^2` introduces a `Complex.cpow (-α²) (1/2)` term
whose squaring back to `-α²` would require a `Complex.cpow_two_eq_self`-style
lemma keyed to the *principal* branch, plus a sign-choice between `+iα` and
`-iα` driven by which Ferrari branch (y₁/y₂ vs y₃/y₄) is being squared.
By contrast, the `ferrari_roots_are_roots`-then-`biquadratic_simple` chain
bypasses all of this: by assumption `yᵢ` is a root of the depressed quartic,
hence `yᵢ²` is forced into the biquadratic root pair by the (axiomatic)
`biquadratic_forward`. The price: the proof uses two parent axioms
(`ferrari_roots_verify`, `biquadratic_forward`) transitively. Neither was
introduced by S3 — both were already in the file. Sub-step A (non-degenerate
resolvent root existence) is the only step that does new algebra.

**Sub-step A architecture (chosen for tractability):**

1. Obtain `u : ℂ` with `u² = r` via FTA on `X² + C(-r)` (degree 2 over ℂ).
   `Polynomial.degree_X_pow_add_C 2 (-r) : (X² + C(-r)).degree = 2`,
   then `IsAlgClosed.exists_root` discharges existence.
2. **Key algebraic identity (verified by `linear_combination`):**
   ```
   (resolventCubic p 0 r).eval (-p + v) = (8v - 4p) * (v² - r)
   ```
   So for any `v` with `v² = r`, both `m₁ = -p + u` and `m₂ = -p - u`
   are resolvent roots. (The identity arises from the factorization
   `resolventCubic p 0 r = 8 · (X + p/2) · (X² + 2pX + (p² - r))`,
   but the identity itself is `linear_combination`-discharged without
   making the factorization explicit.)
3. **Case-split on `2*m₁ + p ≠ 0`:**
   - If non-degenerate: use `m₁ = -p + u`.
   - Otherwise: `u = p/2` (linear), so `r = u² = p²/4`. From the
     hypothesis `p ≠ 0 ∨ r ≠ 0`: if `p = 0` then `r = 0`, contradicting
     either disjunct. So `p ≠ 0`. Then `m₂ = -p - u = -3p/2`, and
     `2*m₂ + p = -2p ≠ 0`.

**Sub-step B architecture (the chosen "Alternative"):**

For any `m` satisfying the resolvent cubic, `ferrari_roots_are_roots`
(via the parent's `ferrari_roots_verify` axiom) gives that each
`yᵢ ∈ ferrariRoots p 0 r m hm` satisfies
`(depressedQuartic p 0 r).eval yᵢ = 0`. Then `biquadratic_simple p r yᵢ`
(forward direction, via `biquadratic_forward`) yields
`yᵢ² = z₁ ∨ yᵢ² = z₂` directly. No explicit-formula manipulation needed.

**Files modified in S3 DISCHARGE:**
- `proofs/Proofs/GeneralQuartic.lean`: -1 sorry, ~72 lines of inline
  proof + docstring update on Part VI.5 header. Net +72 lines (428 → 500).

**Metrics after S3:**
- Lean theoremCount: 12 (unchanged — no new top-level theorems)
- Lean sorryCount: 1 → 0 ✓
- Lean axiomCount: 6 (unchanged)
- LOC: 428 → 500 (+72)

**Mathlib API touched in S3:**
- `Polynomial.degree_X_pow_add_C` (positivity hypothesis on exponent)
- `IsAlgClosed.exists_root` (degree ≠ 0)
- `Polynomial.eval_add`, `eval_mul`, `eval_pow`, `eval_X`, `eval_C` (simp set)
- `linear_combination` tactic (twice: in `hresolv` and in `u = p/2` derivation)

No drift observed on these APIs at Mathlib v4.26.0 (per the canonical
references in similar S3 proofs across the gallery).

### S5b SCAFFOLD-3 — `pan_witness_t_zero_nondegenerate_root` (2026-06-04)

Added an **explicit** non-degenerate resolvent root at the Pan witness's
`t = 0` boundary. The factored form `s²(s − 2)` from
`pan_witness_t_zero_factorisation` (S5b SCAFFOLD-2) has its single
(non-double) root at `s = 2`. Translating back to `m`-coordinates via
`m = (s + 1)/2` gives `m = 3/2`, where `2m + p = 3 - 1 = 2 ≠ 0` — the
**non-degenerate Ferrari branch** at the Pan-witness boundary.

```lean
theorem pan_witness_t_zero_nondegenerate_root :
    (resolventCubic (-1) 0 (1/4 : ℂ)).eval (3/2 : ℂ) = 0 := by
  simp only [resolventCubic, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  ring
```

This makes the abstract existence statement `ferrari_biquad_limit (-1)
(1/4) hpr` concrete with `m = 3/2`. Crucially, this pins down the third
root location at `t = 0` for the future `pan_witness_k1_tangency`:
Newton-polygon analysis (PR #18455 §3) predicts the third root stays
at `m = 3/2 + O(t²)` while the double root at `m = 1/2` (`s = 0`)
perturbs into a `Θ(t)` pair, driving the `α(t) = Θ(t)` first-order
cancellation that is OQ-02.a.1's `k = 1` witness.

**Files modified in S5b SCAFFOLD-3:**
- `proofs/Proofs/GeneralQuartic.lean`: +23 lines (+1 theorem, +1 `#check`)
- `src/data/proofs/general-quartic/meta.json`: `theoremCount: 15 → 16`,
  `lineCount: 576 → 599`, `assumptions` field extended.

**Metrics after S5b SCAFFOLD-3:**
- Lean theoremCount: 15 → 16 (+1)
- Lean sorryCount: 0 (unchanged)
- Lean axiomCount: 6 (unchanged)
- LOC: 576 → 599 (+23)

**Mathlib API touched in S5b SCAFFOLD-3:**
- Same `simp only` set as `pan_witness_t_zero_factorisation`
  (S5b SCAFFOLD-2, line 426): `Polynomial.eval_add/mul/pow/X/C`.
- `ring` tactic to close the polynomial identity over `ℂ`.

No drift observed; identical proof shape to four prior already-merged
Pan-witness-adjacent theorems in the same file.

## Survey of Prior Art

### Folklore Status

The numerical instability of Ferrari's formula is well-known among
numerical analysts but is not the central focus of any standard reference.
The closest treatment is:

- **Press et al., *Numerical Recipes* §5.6.** Recommends *against* using the
  closed-form quartic and presents a deflation-then-bisection alternative.
  No quantitative error analysis given.
- **Kahan (2004), *To Solve a Real Cubic Equation*.** Treats the cubic
  in depth and identifies the *same family* of instability mechanisms that
  recur in Ferrari (cancellation in discriminant; wrong root-pairing).
  Quartic-specific analysis is alluded to but not given.
- **Pan (1997), SIAM Review.** Surveys polynomial root-finding and explicitly
  recommends companion-matrix QR over explicit formulas for n ≥ 3.

### Three Classical Instability Mechanisms

Reading Press, Pan, and Kahan together, the destabilizing operations in
Ferrari's formula (over the depressed quartic `y⁴ + py² + qy + r`) are:

1. **Cancellation in the resolvent cubic discriminant.** `resolventCubic p q r`
   has discriminant proportional to the quartic's own discriminant `Δ`.
   When `Δ → 0` (i.e., the quartic has a near-double root), the resolvent
   cubic also approaches a double root, and Cardano's formula for `m` suffers
   catastrophic cancellation. This is the *upstream* instability, inherited
   from the cubic substep.

2. **The `β = q/(2α)` divide-by-near-zero.** For each resolvent root `m`, the
   factor `α = √(2m + p)`. The three resolvent roots give three values of
   `α`; if any one is near 0, `β` blows up and the discriminants
   `disc1 = α² − 4(p/2 + m + β)` and `disc2 = α² − 4(p/2 + m − β)` are
   computed as differences of nearly equal large quantities. **This is the
   distinctively quartic instability** — it has no cubic-formula analog.

3. **Wrong root-pairing.** Each pair of the four roots emerges from one of
   the two quadratic factors `y² ± αy + (p/2 + m ± β)`. Swapping the sign of
   `α` (a free choice of square-root branch) interchanges the pairing.
   In floating point, when two roots from different pairs are nearly equal,
   pairing them into one quadratic gives a *wrong* root for that quadratic,
   losing precision. **This is a discrete choice with no analytic remedy**:
   any single fixed branch policy is unstable somewhere in parameter space.

Mechanism (2) is the entry point for OQ-02.a (write a witness family making
`β` blow up); mechanism (3) underlies OQ-02.b's hardness (the optimal branch
choice is parameter-dependent); the *biquadratic limit* `q → 0` is the
collision of (2) with `q → 0`, and is the focus of OQ-02.c.

## Three Approach Families

### Approach A: OQ-02.c — Biquadratic-limit removable-singularity identity

**Statement.** In the parent file's notation: for the depressed quartic with
`q = 0`, the formula `ferrariRoots p 0 r m` evaluated at any resolvent root
`m = m₀(p, r)` agrees, as a set, with the biquadratic roots
`{ ±√((-p ± √(p²−4r))/2) }`.

**Why tractable.** This is a *symbolic* identity over ℂ. The branch issue is
sidestepped by interpreting `Complex.cpow z (1/2)` as a fixed principal
branch and showing both sides land in the same multiset (`Finset.image`).
The proof reduces to:
1. Pick `m = -p/2` as a resolvent root when `q = 0` (computable: substitute
   into `resolventCubic p 0 r` and `ring`).
2. With this `m`: `α = √(2m + p) = √0 = 0`, so `β` is `0/0`. Interpret the
   `if α = 0 then 0 else q / (2*α)` branch in the parent file: at `q = 0`,
   the conditional collapses to `β = 0` cleanly (q is already 0). Thus
   `disc1 = disc2 = -4(p/2 + m + 0) = -4·0 = 0` — degenerate.
3. Pick a different resolvent root `m ≠ -p/2`. Then `α ≠ 0`, `β = 0` (since
   `q = 0`), and `disc1 = disc2 = α² − 4(p/2 + m)`. The four Ferrari roots
   collapse to two distinct values each with multiplicity 2 — these are
   `±√((-p ± √(p²−4r))/2)` by direct algebra.

**Why it might block.** Step 3 requires that some non-trivial resolvent root
exists for every `(p, r)` — i.e., `resolventCubic p 0 r` is not the constant
0 polynomial. This is a polynomial-degree argument, but needs careful Mathlib
plumbing through `Polynomial.degree`.

**Required Lean infrastructure.**
- `resolvent_cubic_at_q_zero : resolventCubic p 0 r = C 8 * X³ + C (20*p) * X² + C (16*p² − 8*r) * X + C (4*p³ − 4*p*r)` — already true by `unfold + ring`.
- `resolvent_root_at_biquad : ∀ p r, ∃ m ≠ -p/2, (resolventCubic p 0 r).eval m = 0` — uses FTA + degree counting.
- `ferrari_roots_at_biquad_match : ∀ p r m hm, q = 0 → m ≠ -p/2 → ferrariRoots p 0 r m hm = (canonical biquadratic 4-tuple)` — the algebraic identity.

### Approach B: OQ-02.a — Catastrophic-cancellation witness family

**Statement.** Exhibit a 1-parameter family `(p(t), q(t), r(t))` for `t → 0`
along which `β(t) → ∞` while the actual quartic roots converge to a finite
limit set. Then the relative error of Ferrari's formula in
floating-point arithmetic with machine ε satisfies `err ≥ Ω(ε · |β|)`.

**Why tractable.** A single explicit family suffices. Candidate:
`p(t) = t²`, `q(t) = t`, `r(t) = -1`. Then `resolventCubic` evaluated at
`m = 0` gives `(4·t⁶ + 8·t² − t²) = (4·t⁶ + 7·t²)`, nonzero at `m = 0` for
`t ≠ 0`, so `m₀(t) ≈ -t²/2 + O(t⁴)`, hence `α(t) ≈ √(−t²/...) → 0` while
`q = t → 0`, both at first order — `β = q/(2α) → c ≠ 0`.

This particular family does *not* exhibit blow-up; a more careful witness
needs to make `α` go to zero *faster* than `q`. The literature suggests
families like `p(t) = -1`, `q(t) = t²`, `r(t) = 1/4 + O(t)` work, but
verifying the asymptotic rates requires `Filter.Tendsto`-style
asymptotic reasoning.

**Why it might block.** Asymptotic-analysis arguments in Mathlib are still
relatively heavy. Quantifying "loses k digits of precision" requires either
a model of floating-point arithmetic (absent in Mathlib for ℂ) or an
asymptotic relative-error definition that we'd have to introduce.

### Approach C: OQ-02.b — Discriminant-bounded conditioning bound

**Statement.** There exists an absolute constant `C` such that for all
`(p, q, r) ∈ ℝ³` with `|Δ(p, q, r)| ≥ ε > 0`:
```
κ(ferrariRoots, (p, q, r)) ≤ C · (1 + ‖(p, q, r)‖)^4 / ε
```
where `κ` is the relative condition number.

**Why hard.** Requires (i) a definition of `κ` for explicit ℂ-valued
formulas; (ii) the *quartic discriminant* `Δ : ℂ⁴ → ℂ` (not in Mathlib in
named form); (iii) connecting `|Δ|` to the resolvent cubic's discriminant
and Cardano's-formula instability quantitatively. This is essentially the
content of Bini–Pan's monograph chapter and is at the boundary of current
Lean numerical-analysis tooling.

**Verdict.** OQ-02.b is the most mathematically interesting but multiple
sessions out of reach. Defer indefinitely; track only as motivation.

## Decision: S2 Target

**Approach A (OQ-02.c) is the S2 target.** Rationale:

- *Tractability*: Symbolic ℂ-identity; should require ≤ 100 LOC of Lean once
  the resolvent-root existence step is established.
- *Value to parent*: Tightens the `α ≠ 0` implicit assumption in the parent's
  `ferrariRoots` definition by handling the `α = 0` limit.
- *No new Mathlib infrastructure needed*: Uses only `Polynomial.eval`,
  `Polynomial.degree`, `Complex.cpow`, and `Finset.image` — all already
  imported in the parent.

**S2 next-action**: Add the following to `proofs/Proofs/GeneralQuartic.lean`:

```lean
-- Resolvent cubic at q = 0 factors cleanly.
theorem resolvent_cubic_q_zero (p r : ℂ) :
    resolventCubic p 0 r =
    C 8 * X^3 + C (20 * p) * X^2 + C (16 * p^2 - 8 * r) * X + C (4 * p^3 - 4 * p * r) := by
  unfold resolventCubic; ring_nf
  
-- Statement only (sorry); proof is OQ-02.c.
theorem ferrari_biquad_limit (p r : ℂ) :
    let q : ℂ := 0
    ∃ m : ℂ, (resolventCubic p q r).eval m = 0 ∧
             2 * m + p ≠ 0 ∧
             (∀ hm : (resolventCubic p q r).eval m = 0,
               let (y₁, y₂, y₃, y₄) := ferrariRoots p q r m hm
               ({y₁, y₂, y₃, y₄} : Multiset ℂ) =
               { y | y^2 = (-p + Complex.cpow (p^2 - 4*r) (1/2 : ℂ)) / 2 ∨
                     y^2 = (-p - Complex.cpow (p^2 - 4*r) (1/2 : ℂ)) / 2 }) := by
  sorry
```

Total estimated work: ~150 LOC for the scaffold + proof (S2), then
likely an S3 axiom-discharge pass on whichever sub-step remains.

## Mathlib Gaps Surfaced

- **`Polynomial.discriminant : Polynomial R → R`** — not defined for general
  R-coefficient polynomials in named form. Would be useful for OQ-02.b.
- **Condition-number framework** — no `condNum : (X → Y) → X → ℝ`
  abstraction; numerical-analysis content in Mathlib is sparse.
- **Asymptotic-rate comparison `Filter.Tendsto` for parameter families with
  big-O / big-Theta annotations** — exists but is unwieldy for
  multi-parameter inequalities of the form needed in OQ-02.a.

These are notes for *much later*; they are not blockers for S2.

## Open Items After S1

- [ ] **S2 (highest priority)**: Add `resolvent_cubic_q_zero` and state
      `ferrari_biquad_limit` with `sorry`; commit as Lean scaffold.
- [ ] **S3**: Prove `ferrari_biquad_limit` (or split into the two sub-steps
      `resolvent_root_at_biquad` and the algebraic-identity step).
- [ ] **Eventual S?**: Survey Mathlib API for `Polynomial.discriminant` —
      open a clear Mathlib gap if missing.

## S6 AUDIT (2026-06-04, researcher-1) — Ferrari factorization axioms inconsistent with resolvent

**Key finding**: The file's `ferrari_factorization_forward / backward`
axioms were **mathematically false as stated**. The resolvent
`8m³ + 20pm² + (16p²−8r)m + (4p³−4pr−q²) = 0` corresponds to the
*non-standard* Ferrari completion `(y² + p + m)²` (with constant
`A = p`), but the file's axiom factors used `(y² + p/2 + m ∓ αy ± β)`
(standard `A = p/2`). The two are incompatible.

**Numerical witness**: at `(p, q, r, m) = (1, 0, 0, −1)`, `y = 0`
satisfies the quartic but neither factor disjunct vanishes. Provably
false.

**Fix applied (this session)**: corrected `p/2 + m` → `p + m` in
`ferrari_factorization_forward / backward` axiom conclusions,
`ferrari_factorization` theorem conclusion, and `ferrariRoots` `disc1` /
`disc2` expressions. Also swapped tuple α-signs in `ferrariRoots` to
correctly pair Factor-1 / Factor-2 discriminants with the right
α-coefficient sign.

**Soundness**: post-fix, three previously-false axioms
(`ferrari_factorization_forward`, `ferrari_factorization_backward`,
`ferrari_roots_verify`) are now mathematically true. They are still
declared as `axiom` (not yet proved), but they are no longer false
statements — they are *correct* statements awaiting discharge.

**Significance**: this explains why 5+ prior sessions could not
discharge these axioms — they were literally false. The fix unblocks
a 3-axiom-elimination follow-up (estimated ≤ 50 LOC) that should take
the file's `axiomCount` from 6 to 3.

Full audit in `sessions/2026-06-04-s6-axiom-audit-ferrari-factorization-p-over-2-vs-p.md`.

## Open Items After S6

- [ ] **Build verification (next session, mechanic / auditor)**: run
      `./proofs/scripts/docker-build.sh Proofs.GeneralQuartic` to
      verify the S6 textual fix compiles.
- [ ] **Discharge `ferrari_factorization_forward / backward`** — now
      mathematically true post-S6. Provable via `linear_combination`
      after symbolic expansion of `F₁ · F₂ − (y⁴ + py² + qy + r)`.
      Estimated ≤ 20 LOC per direction.
- [ ] **Discharge `ferrari_roots_verify`** — follows from the
      corrected `ferrari_factorization_backward` + quadratic formula.
      Estimated ≤ 30 LOC.
- [ ] **Reconcile top-level + theorem + def docstrings** with the
      file's non-standard `(y² + p + m)²` convention (currently they
      describe the textbook `(y² + p/2 + m)²` convention, which is
      misleading).
