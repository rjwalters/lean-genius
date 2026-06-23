# Knowledge — birthday-problem-oq-01-oq-02

## S1 (researcher-12, 2026-05-11) — OBSERVE survey

### Problem snapshot

The OQ asks: can the **coupling between expected shared-birthday pairs and
the collision probability** be formalised? Two existing gallery proofs
treat the birthday problem from complementary angles:

| Source | Quantity | Type | Approach |
|--------|----------|------|----------|
| `BirthdayProblemOQ01.lean` | `expectedPairs n d = C(n,2)/d` | `ℚ` | linearity of expectation over pair indicators |
| `BirthdayProblemOQ02.lean` | `probCollision k d = 1 - ∏(1 - i/d)` | `ℝ` | finite-product collision probability |
| `BirthdayProblemOQ01OQ01.lean` | `collisionCount f : ℕ` | random variable | finite sample space `(Fin n → Fin d)` |

There is **no current formal proof** that these viewpoints sandwich
the same collision probability. The two natural couplings are:

```
(MARKOV)         probCollision n d ≤ ↑(expectedPairs n d)
(PALEY-ZYGMUND)  probCollision n d ≥ (expectedPairs n d)² / E[X²]
```

### Markov bound — the one-line proof

```
1 - ∏_{i<n} (1 - i/d)  ≤  ∑_{i<n} i/d  =  n(n-1)/(2d)  =  C(n,2)/d
```

The middle equality is `gauss_sum_div` (`BirthdayProblemOQ02.lean:145`).
The first inequality is the **union bound for products**, provable by
induction on the index set:

| Step | Identity | Comment |
|------|----------|---------|
| Base | `1 - ∏ ∅ = 0 ≤ 0` | `Finset.prod_empty`, `Finset.sum_empty`. |
| Step | `1 - (1-a)·P = a + (1-a)·(1-P) ≤ a + (1-P) ≤ a + ∑ rest` | `(1-a) ≤ 1` since `a ≥ 0`; `(1-P) ≥ 0` by inductive nonnegativity. |

Critical micro-fact: `(1-a)·(1-P) ≤ 1-P` when `0 ≤ 1-a ≤ 1` and
`0 ≤ 1-P`. Direct `nlinarith` or `mul_le_one_of_nonneg`.

### Paley–Zygmund bound

The discrete form: for a nonneg random variable `X` with `E[X²] > 0`,
```
P(X > 0) ≥ E[X]² / E[X²]
```
Proof: Cauchy-Schwarz, `E[X · 1_{X>0}]² ≤ E[X²] · P(X > 0)`,
and `E[X · 1_{X>0}] = E[X]` when `X ≥ 0`.

Substituting `X = collisionCount f` and using `E[X] = expectedPairs n d`
(`OQ01OQ01:?`) and `E[X²] ≤ E[X] + E[X]²` (from `Var(X) ≤ E[X]` which
is `variancePairs_le_expected`, `OQ01:164`) gives an explicit lower
bound:
```
probCollision n d ≥ (C(n,2)/d)² / (C(n,2)/d + (C(n,2)/d)²)
                  = (C(n,2)/d) / (1 + C(n,2)/d)
```

For `C(n,2)/d ≥ 1` (i.e. `n ≥ 28` when `d = 365`) this gives
`probCollision ≥ 1/2`, matching the classical threshold.

### Worked numerics (for sanity)

`d = 365`, `n = 23`: `C(23,2) = 253`, `expectedPairs = 253/365 ≈ 0.6932`.
`probAllDistinct 23 365 ≈ 0.4927`, `probCollision ≈ 0.5073`.

Check Markov: `0.5073 ≤ 0.6932` ✓ (gap ≈ 0.186).
Check Paley-Zygmund: `≥ 0.6932/(1 + 0.6932) = 0.4097` ✓ (gap ≈ 0.097).
Check exponential (`OQ02.probCollision_ge`): `≥ 1 - exp(-253/365) ≈
0.5000`. Gap ≈ 0.007 — the exponential bound is sharper here than
Paley-Zygmund.

`n = 50`: `C(50,2)/365 ≈ 3.36`, `probCollision ≈ 0.9704`.
- Markov: `0.9704 ≤ 3.36` ✓ (vacuous when E[X] > 1).
- Paley-Zygmund: `≥ 3.36/4.36 ≈ 0.7706` ✓.
- Exponential: `≥ 1 - exp(-3.36) ≈ 0.9653`. Again sharper.

**Conclusion**: the exponential bound (OQ02) is tighter than
Paley-Zygmund for moderate `n`, but Markov has the **strictly simpler
proof** and gives a sharp **upper** bound that the exponential argument
does not provide. The two couplings are complementary, not redundant.

### Bridge between OQ02 product formula and OQ01OQ01 counting

`OQ02.probAllDistinct n d = ∏_{i=0}^{n-1} (1 - i/d)` is a real product.

`OQ01OQ01` characterises injective `f : Fin n → Fin d` and proves
`#injective = Nat.descFactorial d n` (`Fintype.card_embedding_eq`,
`OQ01OQ01:?`). The probability `P(X = 0) = P(f injective) =
descFactorial(d,n) / d^n`.

These two real numbers are **equal** by the identity
```
∏_{i=0}^{n-1} (1 - i/d)  =  ∏_{i=0}^{n-1} (d - i) / d  =  descFactorial(d,n) / d^n
```
(provided `n ≤ d`; for `n > d`, both equal 0). Direct telescoping
proof, ~30 lines.

**Without this bridge** the Markov bound (states a real ≤ real) and the
Paley-Zygmund bound (needs the finite-sample-space `X`) are speaking
to slightly different `probCollision`s. The bridge unifies them.

### Insights

1. **Markov coupling is one-line**: just `one_sub_prod_le_sum` + `gauss_sum_div`.
   Likely a 50–60 line single-PR S2/S3 deliverable.
2. **Paley-Zygmund is heavier** (~80 lines) because it needs the
   bridge S6 between OQ02's product and OQ01OQ01's counting. Best done
   in two sessions: S5 (Paley-Zygmund proof skeleton) after S6 (bridge).
3. **The exponential bound (OQ02) is generally sharper than Paley-Zygmund**
   for the birthday parameter range, but Markov gives an **upper** bound
   that complements OQ02's lower bound exclusively.
4. **`variancePairs_le_expected` (OQ01:164) gets a downstream client** as
   soon as Paley-Zygmund lands. Currently it sits unused.
5. **No new axioms needed.** The file stays `verified` once all sorries
   close (target: 0 sorries after S2/S3/S5/S6).
6. **`field_simp` does NOT discharge algebraic residues** (S4 ACT iter 1 → iter 2 trap,
   surfaced at PR #19422). After clearing denominators on the bridge identity
   `1 - 1/(1+x) = x/(1+x)`, `field_simp` left `1 + x - 1 = x` as a residual goal
   (build error L159:51 `unsolved goals`). Fix: append `ring` (or
   `linarith`/`nlinarith` if inequality-typed). The mental model "field_simp
   closes the goal" applies ONLY when the cleared form is `0 = 0` or
   typeclass-decidable. NOT anticipated by S4c §4 (F1–F6), S5 §4 (F7),
   or S5b §3a/§4a (F8/F9) registers — "F-extra" in S6 STATE-SYNC §7.
   Carries forward to future `field_simp` on equalities (vs disequations or `≤`).

### Mathlib gaps (at the pinned revision)

1. **No `Finset.one_sub_prod_le_sum` lemma** that fires directly on the
   product/sum form `1 - ∏(1 - f i) ≤ ∑ f i`. Provable in ~25 lines as
   `one_sub_prod_le_sum` in this file's S2.
2. **No discrete-sample-space `Markov` / `Paley-Zygmund`** that mirrors
   the measure-theoretic `MeasureTheory.measure_*_inv_le_*` family.
   Mathlib's measure-theoretic versions require setting up a
   `MeasureSpace` / probability measure on `Fin n → Fin d`, which is
   non-trivial in `decide`-style proofs. A direct combinatorial statement
   sidesteps this entirely.
3. **No worked `descFactorial`-to-`probAllDistinct` bridge** in Mathlib;
   `Fintype.card_embedding_eq` exists but the explicit product-to-counting
   identity for the birthday problem is not in the Probability namespace.

### Mathlib API names

- `Finset.prod_range_succ`, `Finset.prod_range_succ_comm` — induction step API
- `Finset.sum_range_succ` — sum induction step
- `Finset.prod_empty`, `Finset.sum_empty` — base cases
- `mul_le_one`, `mul_le_one_of_nonneg` — `(1-a)·(1-P) ≤ 1-P` step
- `nlinarith` / `linarith` for `0 ≤ (1-a)·(something nonneg)`
- `pushCast`, `norm_cast`, `Rat.cast_div` — ℚ → ℝ bridging
- `gauss_sum_div` (in-gallery, `OQ02:145`)
- `two_mul_choose_two` (in-gallery, `OQ01:109`)
- `Nat.descFactorial` (Mathlib `Combinatorics.Choose.Factorial`)
- `Fintype.card_embedding_eq` (Mathlib `Data.Fintype.Pi`)

### Risk Notes

- The `proofs/.lake` symlink is broken (`feedback_researcher_lake_symlink_broken`),
  costing ~25–45 minutes per Docker build. S2 is short enough to finish
  with one end-of-S2 build; S5 likely needs two sessions.
- `Rat.cast` elaboration can be slow on long chains; pre-emptively
  `push_cast` between steps.
- Aristotle is a good target for the `one_sub_prod_le_sum` helper
  (`S2`) once the inductive proof skeleton is committed.

### Next-Action priority list

| Session | Target | Est. lines | Build |
|---------|--------|-----------:|-------|
| S2 | `one_sub_prod_le_sum` helper | ~25 | yes |
| S3 | `probCollision_le_expectedPairs` (Markov) | ~40 | yes |
| S6 | `probAllDistinct_eq_descFactorial_div` (bridge) | ~30 | yes |
| S4 | second moment `E[X²]` formula | ~50 | yes |
| S5 | `probCollision_ge_paley_zygmund` | ~80 | maybe split |
