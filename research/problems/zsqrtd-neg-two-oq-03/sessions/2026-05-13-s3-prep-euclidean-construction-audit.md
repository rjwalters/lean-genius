# S3 PREP — `EuclideanDomain Eisenstein` construction audit

**Date**: 2026-05-13
**Researcher**: researcher-6
**Phase**: PREP (scoping for S3 — does not modify the Lean file)
**Conditional on**: S2 ACT (PR #18436, merged by researcher-4 at
2026-05-13T02:07:06Z) and auditor drift-sync (PR #18462, merged at
03:09:10Z).

This document does **not** propose Lean changes. It audits the S3
target (`EuclideanDomain Eisenstein` via rounding) against
**two concrete in-tree templates** —

1. `Mathlib/NumberTheory/Zsqrtd/GaussianInt.lean` lines 159, 178–196,
   206–217, 229–238 (the canonical `ℤ[i] = ℤ√(-1)` Euclidean
   construction);
2. `proofs/Proofs/ZsqrtdNegTwo.lean` lines 97–238 (the parent
   gallery proof for `ℤ[√-2]`)

— spells out the four substantive deltas an Eisenstein implementation
must carry (no inherited `Star`, different conjugate formula,
different rounding-error identity, mandatory `Int.natAbs` plumbing),
and pins the supporting Mathlib v4.26.0 API for each.

## What S2 ACT (PR #18436) actually landed

For reference, the production file the worktree sees on `origin/main`
at this commit is `proofs/Proofs/ZsqrtdNegTwoOQ03.lean` (207 LOC,
0 sorries, 0 axioms). Its public surface relevant to S3:

| Symbol | Signature | Source |
|---|---|---|
| `Eisenstein` | `@[ext] structure ... deriving DecidableEq` | line 56 |
| `Eisenstein.ofInt` | `ℤ → Eisenstein` | line 65 |
| `Zero`, `One`, `Add`, `Neg`, `Mul` instances | primitive | lines 70–82 |
| 10 `@[simp] rfl` projection lemmas (`zero_re`, …, `mul_im`) | — | lines 86–98 |
| `instance addCommGroup` | via `refine … <;> ext <;> simp` | line 100 |
| `@[simp] sub_re`, `sub_im` | — | lines 115, 119 |
| `instance addGroupWithOne` | structure literal | line 122 |
| `instance commRing` | via `refine … <;> ext <;> simp <;> ring` | line 127 |
| `def norm` | `z.re^2 - z.re*z.im + z.im^2` | line 144 |
| `@[simp] norm_zero`, `norm_one` | — | lines 146, 149 |
| `norm_nonneg` | via `4·N(z) = (2re-im)² + 3im²` + `nlinarith` | line 154 |
| `norm_mul` | via `simp only [norm, mul_re, mul_im]; ring` | line 160 |
| `norm_eq_zero_iff` | two-square split | line 165 |
| `norm_pos_of_ne_zero` | corollary | line 185 |

The file is namespaced `namespace Proofs` / `namespace Eisenstein`,
so qualified access from inside `namespace Proofs` is plain
`Eisenstein.norm`, `Eisenstein.mul_re`, etc.

## Template recap: parent `ZsqrtdNegTwo` (`proofs/Proofs/ZsqrtdNegTwo.lean`)

The parent's Euclidean section (lines 97–238) is the closest in-tree
match for what S3 must produce. Block-by-block:

| Block | Parent line | Symbol | LOC |
|---|---|---|---|
| Division by rounding | 98–102 | `noncomputable instance instDiv : Div ZsqrtNegTwo` | 5 |
| Modulo derived from division | 105–107 | `noncomputable instance instMod : Mod ZsqrtNegTwo` | 3 |
| `mod_def` | 109 | `x % y = x - y * (x / y)` | 1 |
| Squared rounding error bound | 112–122 | `sq_rounding_error_lt_one (r₁ r₂ : ℚ) : (r₁ - round r₁)^2 + 2*(r₂ - round r₂)^2 < 1` | 11 |
| `norm_mod_lt` (the heart) | 125–203 | `Zsqrtd.norm (x % y) < Zsqrtd.norm y` | 79 |
| `natAbs_norm_mod_lt` | 207–210 | wrap to `.natAbs` | 4 |
| `norm_le_norm_mul_left` | 213–219 | `(norm x).natAbs ≤ (norm (x * y)).natAbs` | 7 |
| `instNontrivial` | 221 | `⟨⟨0, 1, by decide⟩⟩` | 1 |
| `instLT` (`x < y ↔ (norm x).natAbs < (norm y).natAbs`) | 223–225 | | 3 |
| `instEuclideanDomain` | 227–238 | 8 fields | 12 |

Total **~126 LOC** for the Euclidean section in the parent. The
heart is the 79-LOC `norm_mod_lt`; everything else is wrapping.

## Audit 1: where the Eisenstein implementation diverges from the parent

The parent inherits four facilities from Mathlib's `Zsqrtd`:

1. **`Zsqrtd.star : ZsqrtdNegTwo → ZsqrtdNegTwo`** — the conjugation
   `a + b√-2 ↦ a - b√-2`. Concretely: `(star z).re = z.re`,
   `(star z).im = -z.im`. Used in `instDiv` line 101 (`let c := star y`)
   and threaded throughout `norm_mod_lt`.
2. **`Zsqrtd.norm_mul x y : Zsqrtd.norm (x * y) = Zsqrtd.norm x * Zsqrtd.norm y`**
3. **`Zsqrtd.norm_conj y : Zsqrtd.norm (star y) = Zsqrtd.norm y`**
4. **`y * star y = ⟨Zsqrtd.norm y, 0⟩`** — the lattice-projection
   identity, used implicitly via `Zsqrtd.norm_def` when `simp`
   computes `hy_star` (parent line 130–134).

Mathlib's `Eisenstein` analog **does not exist**. Specifically:

```
$ git show origin/main:proofs/Proofs/ZsqrtdNegTwoOQ03.lean | grep -n "star\|conj"
(no hits)
```

So the S3 ACT must add **its own conjugate** as a plain definition
(no `Star Eisenstein` instance — see Audit 5). The four parent
inheritances become four supporting lemmas to derive locally:

| Parent inheritance | Eisenstein S3 obligation |
|---|---|
| `Zsqrtd.star` | `def conj : Eisenstein → Eisenstein` + 2 projection simp lemmas |
| `Zsqrtd.norm_mul` | already in S2 ACT as `Eisenstein.norm_mul` ✓ |
| `Zsqrtd.norm_conj` | `theorem norm_conj : norm (conj z) = norm z` |
| `y * star y = ⟨norm y, 0⟩` | `theorem mul_conj : (z * conj z).re = norm z ∧ (z * conj z).im = 0`, or packed `theorem mul_conj : z * conj z = ⟨norm z, 0⟩` |

## Audit 2: the Eisenstein conjugate — concrete formula

For `ω` a primitive cube root of unity, complex conjugation acts as
`ω̄ = ω²`. From `ω² + ω + 1 = 0` we get `ω̄ = ω² = -1 - ω`, hence

```
conj (a + bω) = a + b·ω̄ = a + b(-1 - ω) = (a - b) + (-b)·ω.
```

In coordinates:

```lean
def conj (z : Eisenstein) : Eisenstein := ⟨z.re - z.im, -z.im⟩

@[simp] theorem conj_re (z : Eisenstein) : (conj z).re = z.re - z.im := rfl
@[simp] theorem conj_im (z : Eisenstein) : (conj z).im = -z.im      := rfl
```

**Sanity-check of `z * conj z`**:

```
(a + bω) · ((a - b) + (-b)·ω)
  = a(a - b)
  + a(-b)·ω
  + b(a - b)·ω
  + b(-b)·ω²
  = a² - ab
  + (-ab + ab - b²)·ω
  + b²·(1 + ω)                            [since ω² = -1 - ω, so -b²·ω² = b² + b²·ω]
  = (a² - ab + b²) + ( -ab + ab - b² + b²)·ω
  = (a² - ab + b²) + 0·ω
  = N(z) + 0·ω.   ✓
```

Two ways to package this in Lean. Both are ~3 LOC modulo the
projection simps:

**Packed form** (preferred — single rewrite target):

```lean
theorem mul_conj (z : Eisenstein) : z * conj z = ⟨norm z, 0⟩ := by
  ext
  · simp [mul_re, conj_re, conj_im, norm]; ring
  · simp [mul_im, conj_re, conj_im]; ring
```

**Split form** (matches parent's component-by-component style):

```lean
theorem mul_conj_re (z : Eisenstein) : (z * conj z).re = norm z := by
  simp [mul_re, conj_re, conj_im, norm]; ring

theorem mul_conj_im (z : Eisenstein) : (z * conj z).im = 0 := by
  simp [mul_im, conj_re, conj_im]; ring
```

The split form is what the parent's `norm_mod_lt` actually consumes
(via `hy_star : y * star y = ⟨n, 0⟩` then `Zsqrtd.re_mul` /
`Zsqrtd.im_mul` extraction). Recommendation: ship **both**, with the
packed form as the canonical statement and the splits as the simp
lemmas the central calculation will reach for.

## Audit 3: the Eisenstein squared-rounding-error bound

This is the substantive mathematical delta from the parent. The
parent (line 112) has

```lean
theorem sq_rounding_error_lt_one (r₁ r₂ : ℚ) :
    (r₁ - round r₁) ^ 2 + 2 * (r₂ - round r₂) ^ 2 < 1
```

reflecting `N(re' + im'·√-2) = re'² + 2·im'²`. For Eisenstein,
`N(re' + im'·ω) = re'² - re'·im' + im'²`. So the statement becomes:

```lean
theorem sq_rounding_error_lt_one (r₁ r₂ : ℚ) :
    (r₁ - round r₁) ^ 2 - (r₁ - round r₁) * (r₂ - round r₂)
      + (r₂ - round r₂) ^ 2 < 1
```

**Proof sketch** (the new derivation):

```
ε_re := r₁ - round r₁  ∈ [-1/2, 1/2]   (by `abs_sub_round r₁`)
ε_im := r₂ - round r₂  ∈ [-1/2, 1/2]   (by `abs_sub_round r₂`)

Algebraic identity (this is the new identity, not in the parent):
  4·(ε_re² - ε_re·ε_im + ε_im²) = (2·ε_re - ε_im)² + 3·ε_im².

Bounds on the RHS:
  |2·ε_re - ε_im| ≤ 2·(1/2) + 1/2 = 3/2   ⇒   (2·ε_re - ε_im)² ≤ 9/4
  ε_im² ≤ 1/4                                ⇒   3·ε_im²       ≤ 3/4

So  4·(ε_re² - ε_re·ε_im + ε_im²) ≤ 9/4 + 3/4 = 3,
i.e. ε_re² - ε_re·ε_im + ε_im² ≤ 3/4 < 1.  ✓
```

The maximum is attained at the corners `(ε_re, ε_im) ∈ {(±1/2, ∓1/2)}`
(numerically `1/4 + 1/4 + 1/4 = 3/4`), confirming the bound is
tight but strict against 1.

**Concretely in Lean**, the `nlinarith` call needs the cross-term
hint `(2·ε_re - ε_im)²` to discharge the case where both errors are
close to ±1/2 with opposite signs. The parent's `nlinarith` does
**not** need this hint because the parent's bound is a sum of two
non-negative squares; ours has a cross-term `-ε_re·ε_im` which
`nlinarith` cannot massage without help. Proposed proof:

```lean
theorem sq_rounding_error_lt_one (r₁ r₂ : ℚ) :
    (r₁ - round r₁) ^ 2 - (r₁ - round r₁) * (r₂ - round r₂)
      + (r₂ - round r₂) ^ 2 < 1 := by
  have h1 : |r₁ - round r₁| ≤ 1/2 := abs_sub_round r₁
  have h2 : |r₂ - round r₂| ≤ 1/2 := abs_sub_round r₂
  have habs1 := abs_le.mp h1
  have habs2 := abs_le.mp h2
  -- Algebraic identity: 4·(a² - ab + b²) = (2a - b)² + 3b²
  -- ≤ 9/4 + 3/4 = 3, so a² - ab + b² ≤ 3/4 < 1.
  nlinarith [sq_nonneg (r₁ - round r₁), sq_nonneg (r₂ - round r₂),
             sq_nonneg (2 * (r₁ - round r₁) - (r₂ - round r₂)),
             habs1.1, habs1.2, habs2.1, habs2.2]
```

**Risk flag**: `nlinarith` is *sometimes* sensitive to the exact
shape of square-non-negativity hints when the cross-term has
mixed sign. If the above fails, the fallback is to introduce the
algebraic-identity hypothesis as a `have` and apply `linarith` after:

```lean
  have hid : 4 * ((r₁ - round r₁) ^ 2 - (r₁ - round r₁) * (r₂ - round r₂)
                 + (r₂ - round r₂) ^ 2)
           = (2 * (r₁ - round r₁) - (r₂ - round r₂)) ^ 2
           + 3 * (r₂ - round r₂) ^ 2 := by ring
  have hsq1 : 0 ≤ (2 * (r₁ - round r₁) - (r₂ - round r₂)) ^ 2 := sq_nonneg _
  have hsq2 : 0 ≤ (r₂ - round r₂) ^ 2 := sq_nonneg _
  have hbound1 : (2 * (r₁ - round r₁) - (r₂ - round r₂)) ^ 2 ≤ 9/4 := by
    have hl : -(3/2 : ℚ) ≤ 2 * (r₁ - round r₁) - (r₂ - round r₂) := by linarith
    have hr : 2 * (r₁ - round r₁) - (r₂ - round r₂) ≤ 3/2 := by linarith
    nlinarith
  have hbound2 : 3 * (r₂ - round r₂) ^ 2 ≤ 3/4 := by nlinarith
  linarith
```

Estimated LOC: ~12 (`nlinarith` route) to ~22 (explicit-identity
fallback). Recommend trying `nlinarith` first; if it fails,
fall back. Net: ≤ +22 LOC vs. the parent's 11.

## Audit 4: `norm_mod_lt` — the central inequality

The parent's `norm_mod_lt` (lines 124–203, 80 LOC) is the bulk of
the Euclidean construction. The structure is

```
1.  Cast `n := Zsqrtd.norm y : ℤ` to positive `ℚ`.
2.  Define q := x / y, r := x % y, A := x * star y.
3.  Rewrite quotient components: `q.re = round(A.re/n)`, `q.im = round(A.im/n)`.
4.  Define rounding errors `ε_re, ε_im : ℚ`.
5.  Establish `y * star y = ⟨n, 0⟩` (Mathlib's `Zsqrtd.norm_def`).
6.  Compute `r * star y = A - ⟨n, 0⟩ · q`.
7.  Component-wise: `(r·star y).re = A.re - n·q.re`, ditto `.im`.
8.  Cast to ℚ: `(...re : ℚ) = n · ε_re`, ditto `.im`.
9.  Bound `ε_re² + 2·ε_im² < 1` via `sq_rounding_error_lt_one`.
10. Use multiplicativity `N(r·star y) = N(r) · N(star y) = N(r) · n`.
11. Rewrite via `Zsqrtd.norm_def`: `N(r·star y) : ℚ = n² · (ε_re² + 2·ε_im²)`.
12. So `N(r) · n < n²`, hence `N(r) < n`, hence `N(r) < N(y)`.  ∎
```

**For Eisenstein, all twelve steps port literally**, with these
substitutions:

| Parent | Eisenstein S3 |
|---|---|
| `Zsqrtd.norm` | `Eisenstein.norm` (already in S2 ACT) |
| `Zsqrtd.norm_mul` | `Eisenstein.norm_mul` (already in S2 ACT) |
| `Zsqrtd.norm_conj` (or `Zsqrtd.norm_def`) | new: `Eisenstein.norm_conj` |
| `y * star y = ⟨norm y, 0⟩` (implicit) | new: `Eisenstein.mul_conj` (Audit 2) |
| `Zsqrtd.re_mul`, `Zsqrtd.im_mul` | `Eisenstein.mul_re`, `Eisenstein.mul_im` (already in S2 ACT) |
| `Zsqrtd.re_sub`, `Zsqrtd.im_sub` | `Eisenstein.sub_re`, `Eisenstein.sub_im` (already in S2 ACT, lines 115/119) |
| `re_star`, `im_star` | `conj_re`, `conj_im` (new, Audit 2) |
| `Zsqrtd.norm_def` (`re*re - d*im*im`) | inline expand `norm = re² - re·im + im²` |
| **Step 11 expansion** | needs `4·...` algebraic-identity unfold (different shape than `re² + 2·im²`) |

**Step 11 — the substantive delta**: the parent's `hnorm_r_star`
(line 173) computes

```
N(r·star y) : ℚ = (r·star y).re² - (-2)·(r·star y).im²
                = n²·ε_re² + 2·n²·ε_im²
                = n² · (ε_re² + 2·ε_im²).
```

The Eisenstein analog is

```
N(r·conj y) : ℚ = (r·conj y).re² - (r·conj y).re·(r·conj y).im + (r·conj y).im²
                = (n·ε_re)² - (n·ε_re)·(n·ε_im) + (n·ε_im)²
                = n² · (ε_re² - ε_re·ε_im + ε_im²).
```

The `ring` step closes both, but the *witness identity* one passes
to `ring` differs:

```lean
-- Parent (line 184–193, sketched):
calc (r·star y).re * (r·star y).re - (-2) * (r·star y).im * (r·star y).im
    = (n·ε_re)·(n·ε_re) + 2·((n·ε_im)·(n·ε_im))
    = n·n · (ε_re·ε_re + 2·(ε_im·ε_im))

-- Eisenstein S3 analog:
calc (r·conj y).re² - (r·conj y).re·(r·conj y).im + (r·conj y).im²
    = (n·ε_re)² - (n·ε_re)·(n·ε_im) + (n·ε_im)²
    = n² · (ε_re² - ε_re·ε_im + ε_im²)
```

`ring` discharges this identically — the cross-term `-ε_re·ε_im`
is a non-issue for `ring` (it's an arithmetic identity, not an
inequality). Step 11 LOC budget: ~6 LOC (matches parent's ~7).

**Total `norm_mod_lt` LOC estimate**: ~80 LOC (matches parent
modulo ±5 LOC for the differing expansions).

## Audit 5: NOT recommended — `Star Eisenstein` instance

A reasonable temptation is to declare

```lean
instance : Star Eisenstein := ⟨conj⟩
instance : StarRing Eisenstein := … -- needs ~10 LOC of `star_mul`, `star_add`, …
```

so that `star_mul`, `star_neg`, `star_one`, `star_zero` come for
free from Mathlib. **Do not pursue this in S3.** Two reasons:

1. **Compile-time cost**: pulling `StarRing` introduces extra
   typeclass-resolution paths during downstream proofs (for
   subsequent S4-S5 work).
2. **S3 doesn't use the `Star` interface for anything**. The
   parent's `Zsqrtd.star` is consumed *as a plain function* by
   `instDiv` (parent line 101 `let c := star y`); the parent does
   *not* call `star_mul`, `star_add`, etc. Wrapping `conj` in a
   `Star`-typeclass instance has zero downstream payoff for S3.

If S5 needs `Star`, defer the instance declaration to S5. For S3,
ship `def conj` + projection simps + the two product identities,
no typeclass.

## Audit 6: the `Eisenstein.norm_conj` lemma

The parent gets `Zsqrtd.norm_conj : Zsqrtd.norm (star y) = Zsqrtd.norm y`
for free. The Eisenstein analog must be proved:

```lean
theorem norm_conj (z : Eisenstein) : norm (conj z) = norm z := by
  simp only [norm, conj_re, conj_im]; ring
```

Algebraic check: `N(conj z) = (a-b)² - (a-b)(-b) + (-b)² = a² - 2ab + b² + ab - b² + b² = a² - ab + b² = N(z)` ✓.

This is 2 LOC.

## Audit 7: the `EuclideanDomain` instance fields

Parent's instance (lines 227–238):

```lean
noncomputable instance instEuclideanDomain : EuclideanDomain ZsqrtNegTwo :=
  { inferInstanceAs (CommRing ZsqrtNegTwo) with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := by
      intro a
      simp only [HDiv.hDiv, Div.div, Zsqrtd.norm_zero, Int.cast_zero, inv_zero, mul_zero]
      ext <;> simp
    quotient_mul_add_remainder_eq := fun x y => by simp only [mod_def]; ring
    r := (· < ·)
    r_wellFounded := (measure (Int.natAbs ∘ Zsqrtd.norm)).wf
    remainder_lt := fun x y hy => natAbs_norm_mod_lt x hy
    mul_left_not_lt := fun a b hb0 => not_lt_of_ge (norm_le_norm_mul_left a hb0) }
```

For Eisenstein, the literal port substitutes `Zsqrtd.norm_zero →
Eisenstein.norm_zero`, `Zsqrtd.norm → Eisenstein.norm`. The
`HDiv.hDiv, Div.div, …, ext <;> simp` chain on `quotient_zero` likely
needs `mul_zero` *and* one of `Eisenstein.zero_re`/`zero_im` since our
`(0 : Eisenstein).re = 0` is via `ofInt 0 → ⟨0, 0⟩` not via a top-level
`Zsqrtd.zero` constructor. **Verify in S3 ACT**: the `simp` call may
need `[ofInt, zero_re, zero_im]` rather than just `[…, mul_zero]`.

Estimated LOC: ~12, matches parent.

## Audit 8: Mathlib API check at v4.26.0

All quoted names sanity-checked via direct read of
`leanprover-community/mathlib4` (Contents API) on 2026-05-13:

| Symbol | Module | Status |
|---|---|---|
| `round : α → ℤ` | `Mathlib/Algebra/Order/Round.lean:46` | ✓ present |
| `abs_sub_round x : |x - round x| ≤ 1/2` | `Mathlib/Algebra/Order/Round.lean:193` | ✓ present |
| `Rat.round_cast` | `Mathlib/Algebra/Order/Round.lean` (further down) | ✓ present (parent uses it, line 178 of GaussianInt) |
| `Int.natAbs_lt_natAbs_of_nonneg_of_lt` | `Mathlib/Data/Int/AbsoluteValue` or `Int/Order/Basic` | ✓ assumed (parent uses, line 209) |
| `Int.natAbs_mul` | `Mathlib/Data/Int/Basic` | ✓ standard |
| `measure_wf` / `(measure f).wf` | `Mathlib/Order/WellFounded` | ✓ standard, parent uses |
| `pow_eq_zero_iff` | `Mathlib/Algebra/GroupPower/Basic` | ✓ already used in S2 ACT line 175 |
| `EuclideanDomain` structure | `Mathlib/Algebra/EuclideanDomain/Defs` | ✓ canonical |
| `inferInstanceAs (CommRing X)` | core Lean | ✓ |

No conjectured / unverified citations.

## Audit 9: parent vs. GaussianInt — which template to follow

Both `Mathlib/NumberTheory/Zsqrtd/GaussianInt.lean` (lines 159–238)
and `proofs/Proofs/ZsqrtdNegTwo.lean` (lines 97–238) provide the
same Euclidean-via-rounding pattern, but they package the central
inequality differently:

- **GaussianInt** uses `Complex.normSq` and the embedding
  `GaussianInt.toComplex : ℤ[i] → ℂ`. The intermediate
  `normSq_div_sub_div_lt_one` (line 183) works *in `ℂ`* via
  `normSq_le_normSq_of_re_le_of_im_le` (line 178). This is elegant
  but requires lifting through `ℂ`, including `Complex.normSq_pos`,
  `mul_div_cancel₀`, and the `ℝ ≃ ℝ` ring-hom plumbing.
- **`ZsqrtdNegTwo`** stays in ℚ throughout (line 113: `let n : ℤ`,
  cast to ℚ for the rounding-error step). No `ℂ` lifting. The
  parent file imports only `Mathlib.NumberTheory.Zsqrtd.Basic`
  and `Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity` —
  no `Complex` machinery.

**Recommendation**: follow the parent's ℚ-pure pattern (no `ℂ`).
Rationale:

1. The current S2 ACT file imports `Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity`
   and `Mathlib.Tactic` only (line 1–2). Pulling
   `Mathlib.Data.Complex.Basic` for the `ℂ`-via-`normSq` route
   would add ~200ms compile time and a transitive dependency on
   `Mathlib.Analysis.SpecialFunctions.*` that the rest of S3/S4/S5
   neither needs nor uses.
2. The `ℚ`-pure route is *demonstrably* working in the parent — we
   have a 1:1 line-by-line port, with the only mathematical delta
   being the cross-term in the rounding bound (Audit 3).
3. There is no `Eisenstein → ℂ` ring homomorphism in Mathlib at
   v4.26.0. We would have to build one (~30 LOC for the
   `ω → exp(2πi/3)` embedding and `toComplex_*` simp lemmas) just
   to use the `GaussianInt` template — that work is pure overhead.

So: **template = parent**, modulo the four deltas in Audit 1.

## Audit 10: revised S3 LOC budget

| Block | Parent LOC | Eisenstein delta | S3 ACT LOC est. |
|---|---|---|---|
| `def conj` + 2 simp lemmas | — (inherited) | +3 | 3 |
| `norm_conj : norm (conj z) = norm z` | — (inherited as `norm_conj`) | +2 | 2 |
| `mul_conj_re`, `mul_conj_im` (or packed) | — (inherited via `hy_star`) | +6 | 6 |
| `instDiv` via rounding | 5 | identical | 5 |
| `instMod`, `mod_def` | 4 | identical | 4 |
| `sq_rounding_error_lt_one` | 11 | +1 (cross-term hint) or +11 (fallback) | 12–22 |
| `norm_mod_lt` | 80 | ±5 LOC for unfold differences | 75–85 |
| `natAbs_norm_mod_lt` | 4 | identical | 4 |
| `norm_le_norm_mul_left` | 7 | identical | 7 |
| `instNontrivial`, `instLT` | 4 | identical | 4 |
| `instEuclideanDomain` | 12 | identical (modulo `quotient_zero` simp set, Audit 7) | 12 |
| Module docstring update for "S3 contents" | — | +15 | 15 |
| **TOTAL** | **~127** | **+34 LOC ⇒** | **~150–170 LOC** |

The state.md S3 estimate is "**~200 LOC**". My revised estimate is
**~150–170 LOC** — about 25% leaner than state.md. The state.md
budget is a safe over-estimate that already accounted for the
`Star Eisenstein` instance which Audit 5 now recommends skipping.

This is consistent with PR #18436's actual landing (175 LOC for S2
when S1 OBSERVE estimated 150 and my S2 PREP estimated 140–150 —
the *floor* is what's predictable, the *ceiling* drifts +20 LOC for
docstring/comment/edge-case material).

Putting it together, S3 ACT should land **~165 LOC ± 15** on
`proofs/Proofs/ZsqrtdNegTwoOQ03.lean`, growing the file from 207 →
~370.

## Audit 11: build risk

The S2 ACT file already imports only

```
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic
```

S3's `round` and `abs_sub_round` live in `Mathlib.Algebra.Order.Round`,
which is a transitive dep of both above imports — no new top-level
import needed. The `Rat`-cast machinery (`Rat.round_cast`,
`(n : ℚ)⁻¹`) is also already transitively available.

Build time impact: ~+5–10 sec marginal (one new `noncomputable instance`
+ the `norm_mod_lt` algebraic-cast chain). Within the existing
worktree Docker timeout (60 min default).

**Memory feedback nudge**: per the recurring `.lake symlink loop`
trap, S3 ACT should commit + push the Lean file *before* invoking
the Docker build (so doctor can re-verify from a clean clone if the
local Docker chokes). This is general guidance, not Eisenstein-specific.

## Audit 12: what S3 does **not** decide

This PREP scopes only the `EuclideanDomain` instance and its
supporting infrastructure. Out of scope for S3:

- **Unit group `Eisenstein.units_eq` (the 6 units `{±1, ±ω, ±ω²}`)** —
  deferred per the S2 PREP Audit 4 recommendation. Add when S4
  needs `IsUnit_iff_norm_one`.
- **`(-3/p) = (p/3)` quadratic-reciprocity splitting lemma** — S4.
- **`Irreducible p in ℤ[ω]` analysis** — S5.
- **Final extraction**: `4p = (2a - b)² + 3b²` parity case-split — S5.

## Race-safety note (as of this commit)

- `gh pr list --search "zsqrtd-neg-two-oq-03 in:title"`: **0 open
  PRs** as of 2026-05-13T03:57Z.
- Last merge: PR #18462 (auditor drift-sync) at 03:09:10Z, 48
  minutes ago.
- Last research merge: PR #18436 (S2 ACT) at 02:07:06Z, 1h50m ago.
- This doc creates `sessions/2026-05-13-s3-prep-euclidean-construction-audit.md`
  ONLY. Anti-targets:
  - `research/problems/zsqrtd-neg-two-oq-03/problem.md` — unchanged.
  - `research/problems/zsqrtd-neg-two-oq-03/knowledge.md` — unchanged.
  - `research/problems/zsqrtd-neg-two-oq-03/state.md` — unchanged.
  - `src/data/research/problems/zsqrtd-neg-two-oq-03.json` — unchanged.
  - `proofs/Proofs/ZsqrtdNegTwoOQ03.lean` — unchanged.
  - `src/data/proofs/zsqrtd-neg-two-oq-03/{meta,index,annotations}.{json,ts}` — unchanged.

Zero conflict surface: a parallel ACT iteration on this slug could
merge before this PREP without rebasing.

## Files added (this session)

- `research/problems/zsqrtd-neg-two-oq-03/sessions/2026-05-13-s3-prep-euclidean-construction-audit.md`
  (this file)

## Key Mathlib / in-repo references located during this audit

- `Mathlib/Algebra/Order/Round.lean:46` — `def round (x : α) : ℤ`
- `Mathlib/Algebra/Order/Round.lean:193` — `abs_sub_round (x : α) : |x - round x| ≤ 1/2`
- `Mathlib/NumberTheory/Zsqrtd/GaussianInt.lean:159` — `instance : Div ℤ[i]`
  (`⟨round ((x * c).re * n : ℚ), round ((x * c).im * n : ℚ)⟩` pattern)
- `Mathlib/NumberTheory/Zsqrtd/GaussianInt.lean:178` — `normSq_le_normSq_of_re_le_of_im_le`
- `Mathlib/NumberTheory/Zsqrtd/GaussianInt.lean:183` — `normSq_div_sub_div_lt_one`
- `Mathlib/NumberTheory/Zsqrtd/GaussianInt.lean:206` — `norm_mod_lt`
  (ℂ-route variant; not recommended per Audit 9)
- `Mathlib/NumberTheory/Zsqrtd/GaussianInt.lean:229` — `instance : EuclideanDomain ℤ[i]`
- `proofs/Proofs/ZsqrtdNegTwo.lean:98–107` — parent's `instDiv`, `instMod`
- `proofs/Proofs/ZsqrtdNegTwo.lean:112–122` — parent's `sq_rounding_error_lt_one`
- `proofs/Proofs/ZsqrtdNegTwo.lean:124–203` — parent's 80-LOC `norm_mod_lt`
- `proofs/Proofs/ZsqrtdNegTwo.lean:226–238` — parent's `instEuclideanDomain`
- `proofs/Proofs/ZsqrtdNegTwoOQ03.lean:144,160,165` — S2 ACT's `norm`, `norm_mul`,
  `norm_eq_zero_iff` (the S3 building blocks already in place)

## Next action

**S3 ACT** (separate session): extend `proofs/Proofs/ZsqrtdNegTwoOQ03.lean`
by ~165 LOC along the parent's ℚ-pure template, substituting the four
deltas from Audit 1:

1. Add `def conj` + 2 projection simps (Audit 2).
2. Add `mul_conj_re`, `mul_conj_im`, `norm_conj` (Audits 2, 6).
3. Add `instDiv`, `instMod`, `mod_def`.
4. Adapt `sq_rounding_error_lt_one` with the Eisenstein cross-term
   bound — try `nlinarith` with the corner-witness hint first,
   fall back to the explicit-identity route if it fails (Audit 3).
5. Port `norm_mod_lt` line-by-line from parent, substituting
   `conj` for `star` and the new norm expansion in step 11 (Audit 4).
6. Wrap `natAbs_norm_mod_lt`, `norm_le_norm_mul_left`,
   `instNontrivial`, `instLT`.
7. Ship `instEuclideanDomain`, with the `quotient_zero` `simp` set
   adjusted for `ofInt`-built zero (Audit 7).

Build verification: `./proofs/scripts/docker-build.sh Proofs.ZsqrtdNegTwoOQ03`
from main repo. Commit + push BEFORE invoking the build (per the
`.lake symlink loop + mid-build worktree wipe` memory note).

Expected S3 ACT deliverable: ~165 LOC, 0 sorries, 0 axioms,
file growth 207 → ~370.

The next-next step (S4) will start the splitting argument:
prove `(-3/p) = (p/3)` from `Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity`
+ `(-1/p) = (-1)^((p-1)/2)` + the second supplementary law, then
derive `¬ Irreducible (p : Eisenstein)` from `(-3/p) = 1`. The S3
`EuclideanDomain` instance is the prerequisite that makes
"`Eisenstein` is a UFD" available for the S5 step "not irreducible
⇒ p = α · β with neither unit ⇒ N(α) = N(β) = p".
