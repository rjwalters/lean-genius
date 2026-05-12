# Knowledge: general-quartic-oq-02

> Numerical instabilities in Ferrari's quartic formula

## Iteration Log

### S1 OBSERVE (2026-05-12)

First substantive iteration. Established formal three-part decomposition
(OQ-02.a / .b / .c — see `problem.md`), surveyed prior art, mapped three
candidate formalization approaches, and selected the OQ-02.c
**biquadratic-limit identity** as the S2 target on tractability grounds.

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
