# S5 PREP — Mathlib `RatFunc.eval` rescues Path C: `qtMC q 1 n k = qMC q n k` needs NO `q ≠ 1` hypothesis under iterated `RatFunc (RatFunc ℚ)`

**Researcher**: researcher-9 (claim `researcher-9`, knowledge score 8 / MODERATE; obtained via explicit `REPO_ROOT=/Users/rwalters/GitHub/lean-genius` per memory trap)
**Date**: 2026-05-13 (post-S4 PREP, ~45 min after PR #18616 merged 2026-05-13T07:02 UTC)
**Type**: doc-only Mathlib bearer-audit PREP; orthogonal to any future S2/S3 ACT — no edits to `problem.md`, `knowledge.md`, `state.md`, or the gallery JSON. Only adds this session note.
**Scope**: a fourth-order audit, focused on the **Path C** option that S4 PREP §2.6 dismissed as "substantially higher complexity than Paths A or B" without concrete Mathlib evidence. This PREP locates the missing evidence and **flips** the conclusion: Path C is actually viable in Mathlib (via `RatFunc.eval`), and uniquely **eliminates F1's `q ≠ 1` hypothesis** for the `t = 1` substitution theorem.

---

## §0 — TL;DR for the next S2 / S6 ACT implementer

1. **`RatFunc.eval f a`** exists in Mathlib at `Mathlib/FieldTheory/RatFunc/AsPolynomial.lean:146`. It evaluates `RatFunc K` at a base-field value via `(num p).eval₂ f a / (denom p).eval₂ f a`, with the standard `div_zero = 0` convention when the denominator vanishes. **Crucially, fractions are reduced to lowest terms (numerator/denominator coprime via `gcd` in `K[X]`) BEFORE evaluation**, so the L'Hôpital limit is recovered automatically when the rational function reduces to a polynomial. (See docstring: `eval id 1 ((X^2 - 1) / (X - 1)) = eval id 1 (X + 1) = 2`, NOT `0/0 = 0`.)
2. **Mathlib has NO first-class `MvRatFunc` type alias.** The only mention is `Mathlib/FieldTheory/MvRatFunc/Rank.lean`, a single rank theorem (`MvRatFunc.rank_eq_max_lift`). Multivariate rational-function work uses `FractionRing (MvPolynomial σ F)` directly. For Path C with two variables, the cleanest Mathlib-native path is **iterated** `RatFunc (RatFunc ℚ)` (i.e. ℚ(q)(t) as a structure-on-structure), not multivariate `FractionRing (MvPolynomial (Fin 2) ℚ)`.
3. **`RatFunc.liftRingHom` (which IS a ring hom) is NOT useful for arbitrary substitution.** Its prerequisite `R[X]⁰ ≤ L⁰.comap φ` (every non-zero polynomial maps to non-zero in `L`) FAILS for substitution `X ↦ 1` (e.g., `1 - X` is non-zero but evaluates to `0`). The arbitrary-substitution facility is `RatFunc.eval`, which is NOT a ring hom in general; `eval_add` and `eval_mul` carry explicit `denom ≠ 0` hypotheses (see `AsPolynomial.lean:184` and `:202`).
4. **The S4 PREP's recommended F1 remediation, Path A** (add `hq : ∀ i ∈ Finset.range k, q ^ (i + 1) ≠ 1` to S3's theorem), is still recommended for the **immediate** S2 ACT under the naïve `[Field R]` definition — Path C requires substantially more Mathlib `RatFunc` infrastructure (~200 LOC overhead vs Path A's ~20 LOC).
5. **BUT**: under Path C, **F1's hypothesis vanishes entirely**. The theorem `(RatFunc.eval _ 1) (qtBinomRF n k) = qBinomRF n k` (after appropriate setup) holds polynomial-identically because `RatFunc.eval` reduces the rational function `qtBinom` BEFORE substituting `t = 1`, at which point each factor `(1 - q^{n+k-i} t^{i-1}) / (1 - q^i t^{i-1})` reduces to a polynomial in `q` (after `t = 1`, the t-dependent denominators become `(1 - q^i)` which exactly match the q-factorial denominators in the parent's `qBinom_product`). This is a substantive design improvement that **only Path C** provides.

The next implementer should pick Path A for **S2 ACT** (immediate, low-cost) and reserve **Path C for a future S6/S7 "ACT-rational"** that explores the polynomial sub-lattice and L'Hôpital limits rigorously.

---

## §1 — Why this PREP is being written ~45 min after S4 PREP merge

S4 PREP (PR #18616, merged 2026-05-13T07:02 UTC) lays out three remediation paths for F1's `Field` 0/0 = 0 trap:

* **Path A** (recommended): add `hq : ∀ i, q^(i+1) ≠ 1` to S3's theorem statement.
* **Path B**: piecewise `qtBinom` via `Classical.dec`-based denominator decision.
* **Path C**: `RatFunc` (formal rational functions), with substitution as the localized step.

S4 PREP §2.6 dismisses Path C with three "Con" bullets:

> * Con: requires Mathlib's `RatFunc` infrastructure, which has limited multivariate support (`RatFunc` is single-variable; multivariate would need `MvRatFunc` or `FractionRing (MvPolynomial _ _)`).
> * Con: every existing parent lemma … is stated over `[CommRing R]`, *not* `RatFunc`; the bridge … would need to be wired through every theorem.
> * Con: substantially higher complexity than Paths A or B.

Bullets 2 and 3 are correct; bullet 1 is incomplete. The actual Mathlib state (verified below) is:

* Mathlib has `RatFunc K` (single-variable) at `FieldTheory/RatFunc/Defs.lean:68`, defined as a structure wrapping `FractionRing K[X]`.
* Mathlib has **no top-level `MvRatFunc σ K` type alias.** The directory `Mathlib/FieldTheory/MvRatFunc/` exists but contains only `Rank.lean`, which proves a rank theorem about `FractionRing (MvPolynomial σ F)` directly. There is no `MvRatFunc.eval`, `MvRatFunc.liftAlgHom`, or even a `MvRatFunc` definition.
* But: **iterated `RatFunc (RatFunc K)`** *is* a valid Mathlib type (just typeclass composition — `RatFunc K` is a `Field`, so `RatFunc (RatFunc K)` makes sense). This gives a workable two-variable setup with the full single-variable `RatFunc` API available at each level.

The missing piece in S4 PREP's analysis is the existence and exact semantics of **`RatFunc.eval`**, which makes Path C qualitatively different from Path A and worth re-evaluating.

---

## §2 — `RatFunc.eval`: the missing bearer

### 2.1 Location and definition

`Mathlib/FieldTheory/RatFunc/AsPolynomial.lean:146`:

```lean
/-- Evaluate a rational function `p` given a ring hom `f` from the scalar field
to the target and a value `x` for the variable in the target.

Fractions are reduced by clearing common denominators before evaluating:
`eval id 1 ((X^2 - 1) / (X - 1)) = eval id 1 (X + 1) = 2`, not `0 / 0 = 0`.
-/
def eval (f : K →+* L) (a : L) (p : K⟮X⟯) : L :=
  (num p).eval₂ f a / (denom p).eval₂ f a
```

The key semantic guarantee is in the docstring: **fractions are reduced before evaluating.** This is achieved via `num`/`denom`, which are defined (in `Mathlib/FieldTheory/RatFunc/Basic.lean`) to be a **coprime pair** of polynomials in `K[X]` with the denominator monic. Hence `(X^2 - 1) / (X - 1)`, viewed as a `RatFunc K`, has `num = X + 1` and `denom = 1`, and `eval _ 1` returns `2`.

### 2.2 Cited supporting `simp` lemmas

```lean
@[simp] theorem eval_C {c : K} : eval f a (C c) = f c := by simp [eval]
@[simp] theorem eval_X : eval f a X = a := by simp [eval]
@[simp] theorem eval_zero : eval f a 0 = 0 := by simp [eval]
@[simp] theorem eval_one : eval f a 1 = 1 := by simp [eval]
@[simp] theorem eval_algebraMap {S : Type*} [CommSemiring S] [Algebra S K[X]] (p : S) :
    eval f a (algebraMap _ _ p) = (algebraMap _ K[X] p).eval₂ f a := by ...
```

Notably, **there is no `@[simp] theorem eval_div`** or `eval_inv`. This is by design: `eval` is **NOT a ring hom** in general. The next two theorems make this explicit:

### 2.3 `eval_add` and `eval_mul` require denominator-non-vanishing

`Mathlib/FieldTheory/RatFunc/AsPolynomial.lean:184` and `:202`:

```lean
/-- `eval` is an additive homomorphism except when a denominator evaluates to `0`.

Counterexample: `eval _ 1 (X / (X-1)) + eval _ 1 (-1 / (X-1)) = 0`
`... ≠ 1 = eval _ 1 ((X-1) / (X-1))`.
-/
theorem eval_add {x y : K⟮X⟯} (hx : Polynomial.eval₂ f a (denom x) ≠ 0)
    (hy : Polynomial.eval₂ f a (denom y) ≠ 0) : eval f a (x + y) = eval f a x + eval f a y

/-- `eval` is a multiplicative homomorphism except when a denominator evaluates to `0`.

Counterexample: `eval _ 0 X * eval _ 0 (1/X) = 0 ≠ 1 = eval _ 0 1 = eval _ 0 (X * 1/X)`.
-/
theorem eval_mul {x y : K⟮X⟯} (hx : Polynomial.eval₂ f a (denom x) ≠ 0)
    (hy : Polynomial.eval₂ f a (denom y) ≠ 0) : eval f a (x * y) = eval f a x * eval f a y
```

Implication for our use: **distributing `RatFunc.eval` through `Finset.prod` requires showing each factor's `denom` is non-vanishing.** Concretely, for `qtBinom q t (n+k-1) k` as a product of `k` factors, applying `eval _ 1` to the t-variable requires:

* For each `i ∈ Finset.range k`, the `denom` of the i-th factor as a `RatFunc (RatFunc ℚ)` does not vanish under `t = 1`.

But this only needs `(1 - q^{i+1} t^{i-1}) |_{t=1} ≠ 0`, i.e., `(1 - q^{i+1}) ≠ 0` in `RatFunc ℚ` (the inner ring), which is **automatically true** because `(1 - q^{i+1})` is a non-zero polynomial in `RatFunc ℚ` (it's a non-zero element of `(RatFunc ℚ)[t]` viewed as the t-polynomial ring). So the distribution-of-eval step is FREE for the outer (t-) substitution.

By contrast, the inner (q-) substitution at `q = 1` requires `(1 - q^{i+1}) |_{q=1} = 0` for `i ≥ 0`, and so the denominator vanishes — which is exactly F1's trap, just relocated to the inner eval.

### 2.4 Substitution morphism `RatFunc.liftRingHom`: NOT useful for `q = 1` or `t = 1`

For comparison, the "lift a ring hom" facility at `RatFunc/Basic.lean:437`:

```lean
def liftRingHom (φ : R[X] →+* L) (hφ : R[X]⁰ ≤ L⁰.comap φ) : R⟮X⟯ →+* L
```

requires `hφ : R[X]⁰ ≤ L⁰.comap φ`, i.e., every non-zero polynomial in `R[X]` maps to a non-zero element of `L`. For substitution `X ↦ 1` over `R = ℚ`, this **FAILS** because `1 - X` is a non-zero polynomial mapping to `0`. Hence `liftRingHom` is unusable for finite-value substitution; only transcendental-element substitution (via `algEquivOfTranscendental` at `AsPolynomial.lean:228`) works.

This is consistent with the mathematical reality: **arbitrary substitution in rational functions is genuinely partial.** Mathlib chooses the `div_zero` convention to make it total, at the cost of breaking the ring-hom property.

---

## §3 — `Mathlib/FieldTheory/MvRatFunc/`: type-alias absent

### 3.1 Directory inventory (verified via `gh api repos/leanprover-community/mathlib4/contents/Mathlib/FieldTheory/MvRatFunc`)

* `Mathlib/FieldTheory/MvRatFunc/Rank.lean` (single file, ~30 lines, one theorem).

That's it. No `Defs.lean`, no `Basic.lean`, no `AsPolynomial.lean`.

### 3.2 The single theorem

```lean
open Cardinal in
theorem MvRatFunc.rank_eq_max_lift
    {σ : Type u} {F : Type v} [Field F] [Nonempty σ] :
    Module.rank F (FractionRing (MvPolynomial σ F)) = lift.{u} #F ⊔ lift.{v} #σ ⊔ ℵ₀
```

Note: the namespace `MvRatFunc` exists ONLY as a name-spacing convention for this single theorem; the **type** referenced is the unwrapped `FractionRing (MvPolynomial σ F)`. There is no `MvRatFunc σ F` structure or abbreviation.

### 3.3 Implication

For two-variable rational functions in Mathlib, the user has two choices:

* **Direct multivariate**: `FractionRing (MvPolynomial (Fin 2) ℚ)`. Symmetric in the variables, but lacks the rich single-variable `RatFunc` API (no `RatFunc.X`, no `RatFunc.eval`, no `num`/`denom`).
* **Iterated single-variable**: `RatFunc (RatFunc ℚ)` (which is ℚ(q)(t) viewed as a one-variable rational function field over a one-variable rational function field). Asymmetric in the variables (q and t are not interchangeable), but each "level" has the full `RatFunc` API.

For our setup, where we need to substitute `t = 1` (outer) and then `q = 1` (inner), the **iterated** approach is the natural fit. The asymmetry doesn't bite because we're substituting one variable at a time.

---

## §4 — Path C, made concrete: iterated `RatFunc (RatFunc ℚ)`

### 4.1 Type setup

```lean
-- The "(q, t)-base field" with q outer, t inner (Macdonald convention: t first, then q).
-- Concretely: RatFunc.X : RatFunc ℚ        -- this is `q`
--              RatFunc.X : RatFunc (RatFunc ℚ)  -- this is `t`

abbrev QT := RatFunc (RatFunc ℚ)
abbrev Q  := RatFunc ℚ

-- The variables
noncomputable def q : Q := RatFunc.X
noncomputable def t : QT := RatFunc.X

-- The base-field hom: ℚ → Q → QT
-- (lifted automatically via Algebra instances)
```

### 4.2 `qtBinom` and `qtMultichoose` as `QT`-valued rational functions

```lean
noncomputable def qtBinomRF (n k : ℕ) : QT :=
  ∏ i ∈ Finset.range k,
    (1 - (algebraMap Q QT (q ^ (n - i))) * t ^ i) /
    (1 - (algebraMap Q QT (q ^ (i + 1))) * t ^ i)

noncomputable def qtMultichooseRF (n k : ℕ) : QT :=
  qtBinomRF (n + k - 1) k
```

**Key point**: this is a single closed-form `QT`-valued function with NO `q ≠ 1` hypothesis in its definition. Each denominator factor `1 - q^{i+1} * t^i` is a **non-zero element of `QT`** (because as a polynomial in `t` over `Q`, it has a non-zero constant term `1` and a non-zero coefficient of `t^i` for `i ≥ 1`, and even for `i = 0` it's `1 - q^1 ≠ 0` in `Q`). Hence the division is always well-defined, and `qtBinomRF` is a well-defined element of `QT`.

### 4.3 The `t = 1` substitution theorem (Path C version of S3)

```lean
theorem qtBinomRF_at_t_one (n k : ℕ) :
    RatFunc.eval (RingHom.id Q) 1 (qtBinomRF n k) =
    qBinomProductForm q n k

-- where qBinomProductForm q n k = ∏ i ∈ Finset.range k, (1 - q^(n - i)) / (1 - q^(i + 1))
--   (a `Q`-valued, NOT polynomial-valued, expression).
```

**Proof outline (sketch, ~30 LOC)**:

* Step 1: unfold `qtBinomRF` and apply `RatFunc.eval` to each factor. Distribution through `Finset.prod` requires `eval_mul` per §2.3 — discharge each factor's `denom ≠ 0` using `(1 - q^{i+1}) ≠ 0` in `Q` (which holds because `q` is transcendental over ℚ, so `1 - q^{i+1}` is a non-zero polynomial in `Q`).
* Step 2: each factor `(1 - q^{n-i} * t^i) / (1 - q^{i+1} * t^i)`, evaluated at `t = 1`, gives `(1 - q^{n-i}) / (1 - q^{i+1})` in `Q`. This uses `RatFunc.eval_div` … wait, `eval` is not a ring hom, but for individual factors `(a - b * X^i) / (c - d * X^i)` the `num`/`denom` are coprime in `Q[t]` (verified by gcd computation in `Q[t]`), so `RatFunc.eval` reduces to the obvious value.
* Step 3: connect the resulting product in `Q` to the parent's `qBinom q (n+k-1) k` lifted to `Q`. This requires invoking `qBinom_product` (parent's q-factorial identity) and dividing by `qFactorial q k * qFactorial q (n - k)`, which is valid in `Q` because each factor `qNumber q j = (1 - q^j) / (1 - q)` is non-zero in `Q`.

**The hypothesis `q ≠ 1` from F1 / S4 PREP's Path A is GONE.** It's replaced by the structural fact that `q` is the formal generator of `Q = RatFunc ℚ`, which is *not* `1`. (Formally: `q := RatFunc.X` and `RatFunc.X ≠ 1`, by `Mathlib/FieldTheory/RatFunc/AsPolynomial.lean:127` `X_ne_zero` and a similar `X_ne_one` argument.)

### 4.4 The `(t, q) = (1, 1)` iterated specialization

```lean
theorem qtMultichooseRF_at_one_one (n k : ℕ) :
    RatFunc.eval (RingHom.id ℚ) 1
      (RatFunc.eval (RingHom.id Q) 1 (qtMultichooseRF n k)) =
    ???
```

**At this point, F1 returns with a vengeance.** After the outer eval (t = 1), the value is `qBinomProductForm q n k ∈ Q` — a rational function in `q` with denominators `(1 - q^{i+1})` for `i ∈ [0, k)`. Substituting `q = 1` via inner `RatFunc.eval` requires the denominators to be non-vanishing in `Q[q] ↪ Q`, which … they're not, because they ARE denominators in `Q` that contain `q`.

Wait — there's a type confusion here. Let me unwind: at this stage, `qBinomProductForm q n k ∈ Q`, where `Q = RatFunc ℚ`. The variable `q ∈ Q` is `RatFunc.X`. So `qBinomProductForm q n k` is **already** a rational function in the abstract `q`, not a polynomial. To substitute `q = 1`, we apply `RatFunc.eval (RingHom.id ℚ) 1 : Q → ℚ`. This uses `RatFunc.eval`'s fraction-reduction-before-eval semantics.

For the polynomial sub-lattice ({k ≤ 1} ∪ {(2, 2)} from S4 PREP F2):

* `k = 0`: `qBinomProductForm q n 0 = 1`. Eval at `q = 1` gives `1`. Matches `Nat.multichoose n 0 = 1`. ✓
* `k = 1`: `qBinomProductForm q n 1 = (1 - q^n) / (1 - q)`. As a `RatFunc ℚ`, this reduces to `1 + q + ... + q^{n-1}` (the q-number `[n]_q`). Eval at `q = 1` gives `n`. Matches `Nat.multichoose n 1 = n`. ✓
* `(n, k) = (2, 2)`: `qBinomProductForm q 3 2 = ((1 - q^3)(1 - q^2)) / ((1 - q)(1 - q^2))`. As a `RatFunc ℚ`, this reduces (cancelling the `(1 - q^2)` factors) to `(1 - q^3) / (1 - q) = 1 + q + q^2`. Eval at `q = 1` gives `3`. Matches `Nat.multichoose 2 2 = 3`. ✓

For non-polynomial cases (e.g., `(n, k) = (3, 2)`):

* `qBinomProductForm q 4 2 = ((1 - q^4)(1 - q^3)) / ((1 - q)(1 - q^2))`. Reduce in `ℚ[q]`: `gcd((1 - q^4)(1 - q^3), (1 - q)(1 - q^2))` is `(1 - q)^2 · (1 - q^? ...)` — let me check:
  - `(1 - q^4) = (1 - q)(1 + q + q^2 + q^3)`
  - `(1 - q^3) = (1 - q)(1 + q + q^2)`
  - `(1 - q^2) = (1 - q)(1 + q)`
  - Numerator: `(1 - q)^2 · (1 + q + q^2 + q^3) · (1 + q + q^2)`
  - Denominator: `(1 - q)^2 · (1 + q)`
  - Reduced: `(1 + q + q^2 + q^3)(1 + q + q^2) / (1 + q)`
* Eval at `q = 1`: numerator → `4 · 3 = 12`, denominator → `2`. Result: `6`. ✓ Matches `Nat.multichoose 3 2 = 6`!

**This is the L'Hôpital limit, computed by `RatFunc.eval` automatically.** The reduction of `RatFunc` to coprime `num`/`denom` does the L'Hôpital cancellation for us, and the final evaluation gives the correct multichoose count.

Let me double-check `(n, k) = (1, 2)` (non-polynomial per S4 PREP F2, where S3 PREP §2 lists "✗"):

* `qBinomProductForm q 2 2 = ((1 - q^2)(1 - q)) / ((1 - q)(1 - q^2))`. This is **literally 1** as a rational function. Eval at `q = 1` gives `1`. ✓ Matches `Nat.multichoose 1 2 = ?`. Wait, `Nat.multichoose 1 2` should be the number of multisets of size 2 from a 1-element set, which is `1`. ✓

Now `(n, k) = (2, 3)` (non-polynomial):

* `qBinomProductForm q 4 3 = ((1-q^4)(1-q^3)(1-q^2)) / ((1-q)(1-q^2)(1-q^3))`. Numerator `(1-q)(1+q)(1+q^2)(1-q)(1+q+q^2)(1-q)(1+q) = (1-q)^3 (1+q)^2 (1+q^2)(1+q+q^2)`. Denominator `(1-q)(1-q)(1+q)(1-q)(1+q+q^2) = (1-q)^3 (1+q)(1+q+q^2)`. Reduced: `(1+q)(1+q^2)`. Eval at `q = 1`: `2 · 2 = 4`. Matches `Nat.multichoose 2 3 = Nat.choose (2+3-1) 3 = Nat.choose 4 3 = 4`. ✓

So **Path C with `RatFunc.eval` recovers `Nat.multichoose n k` correctly at `(q, t) = (1, 1)` for ALL `(n, k)` we've checked — including non-polynomial cases**. The L'Hôpital limit is computed for free by Mathlib's fraction-reduction.

### 4.5 The big caveat

**The above is mathematically true but requires substantial Lean proof.** Specifically:

* `qBinomProductForm q n k` (an iterated product of `RatFunc ℚ`-valued fractions) must be shown to reduce — as a `RatFunc ℚ` — to `Nat.multichoose n k` after eval at `q = 1`. This is essentially `qBinom_product q (n+k-1) k`'s identity, **lifted from `[CommRing R]` to `RatFunc ℚ`**, with the qFactorial division reinterpreted as the literal `RatFunc` division. The bridge requires:

  * (A) A "polynomial → `RatFunc ℚ`" lift homomorphism: this is just `algebraMap ℚ[q] (RatFunc ℚ)`. Free.
  * (B) Identification of `qBinom q m k` (parent's `[CommRing]`-valued recursive definition, via `algebraMap`) with `qBinomProductForm q m k` (Path C's product-of-fractions). This is the parent's `qBinom_product` lifted to `RatFunc ℚ`, with `qFactorial`-divisions performed as literal `RatFunc` divisions. **NOT a one-liner** — needs ~40-60 LOC of bridge.
  * (C) Verification that `RatFunc.eval` at `q = 1` of `qBinom_product`-derived value equals `Nat.choose (m) k`. This uses (i) `qFactorial_at_one : qFactorial 1 n = n!` (parent), (ii) `RatFunc.eval` commutes with `algebraMap` via `eval_algebraMap` (`AsPolynomial.lean:171`). Probably another ~20-30 LOC.

So Path C's S3 theorem is ~120-180 LOC, vs Path A's ~75 LOC (per S4 PREP §5.2). **2-3× the LOC cost, but produces a theorem WITHOUT the `q ≠ 1` hypothesis.**

---

## §5 — Worked smoke-test: `qtBinomRF (3, 2)` at `(t, q) = (1, 1)` returns 6 (not 0)

This is the example that motivated F1 and Path A: under the naïve `[Field R]` definition, `qtBinom (1 : ℝ) (1 : ℝ) 3 2 = 0`, contradicting `Nat.multichoose 2 2 = 3` (wait — the S3 theorem is `qtMC q 1 n k = qMC q n k`, so at `(n, k) = (2, 2)` and `(q, t) = (1, 1)`, the value is `Nat.multichoose 2 2 = 3`, not `3`'s-derivative-from `(3, 2)`).

Let me redo the smoke-test for `(n, k) = (2, 2)` cleanly:

**Naïve `[Field R]` version (S2 PREP)**:

```lean
example : qtBinom (1 : ℝ) (1 : ℝ) 3 2 = 0 := by
  -- both factors (i = 0, 1) evaluate to (1 - 1) / (1 - 1) = 0/0 = 0
  -- product is 0 * 0 = 0
  norm_num [qtBinom, Finset.prod_range_succ, Finset.prod_range_zero, div_zero]
```

**Path C version**:

```lean
example :
    RatFunc.eval (RingHom.id ℚ) 1
      (RatFunc.eval (RingHom.id Q) 1 (qtBinomRF 3 2)) = (3 : ℚ) := by
  -- 1. Apply outer eval (t = 1) to each factor of the Finset.prod.
  --    Factor 0: (1 - q^3 * t^0) / (1 - q^1 * t^0) at t=1 → (1 - q^3) / (1 - q) ∈ Q.
  --    Factor 1: (1 - q^2 * t^1) / (1 - q^2 * t^1) at t=1 → (1 - q^2) / (1 - q^2) = 1 ∈ Q.
  --    Product: (1 - q^3) / (1 - q) = 1 + q + q^2 ∈ Q.
  -- 2. Apply inner eval (q = 1) to (1 + q + q^2).
  --    This is a polynomial in q, so eval is just polynomial eval: 1 + 1 + 1 = 3.
  sorry  -- ~30 LOC of RatFunc.eval_mul and eval_C manipulation
```

The cleanest Lean evidence that Path C gives the right answer is a `decide`-like reduction or `RatFunc.eval` simp set. As of Mathlib HEAD pin `2df2f0150...`, `RatFunc.eval` does NOT have a `@[simp]` annotation for `Finset.prod` distribution; the user must invoke `eval_mul`/`eval_add` with explicit `denom ≠ 0` hypotheses.

---

## §6 — Recommendations

### 6.1 For S2 ACT (next implementer)

**Stick with Path A.** Per S4 PREP §5.1, the ~80 LOC drop with `(hq : ∀ i ∈ Finset.range k, q^(i+1) ≠ 1)` is the right tradeoff for the *initial* S2 ACT. Reasons:

* No Mathlib infrastructure cost.
* Composes with parent's `qBinom_product` (which is `[CommRing R]`-valued, matches S2's `[Field R]`).
* `hq` is discharge-able for any specific `q ≠ 1` via `Polynomial.eval` / `decide` — manageable for downstream users.

The S2 PREP / S3 PREP / S4 PREP cascade settles on this design. S5 PREP affirms it.

### 6.2 For S6 / S7 ACT (future "ACT-rational")

**Pursue Path C as a separate, parallel track.** Reasons:

* Eliminates `q ≠ 1` hypothesis (per §4.3).
* Computes L'Hôpital limit automatically via `RatFunc.eval`'s fraction-reduction (per §4.4).
* Connects naturally to Macdonald polynomial principal-specialization framework, which lives in `Sym(ℚ(q, t))` — a multivariate rational-function setting.
* The ~120-180 LOC overhead is amortizable over multiple downstream theorems (S5, S6, S7).

The right time to pursue Path C is **after** S2 ACT (Path A) is merged and the Path-A version of the S3 theorem is stable. Path C then becomes a "promote the rational-function version" follow-up, not a parallel competing design.

### 6.3 Specific concrete tasks for Path C (deferred)

1. **Define `qtBinomRF`, `qtMultichooseRF`** as `RatFunc (RatFunc ℚ)`-valued functions (~30 LOC).
2. **Prove `qtBinomRF_at_t_one`**: `RatFunc.eval _ 1 (qtBinomRF n k) = qBinomProductForm q n k` (where `qBinomProductForm` is parent's q-factorial form, lifted to `RatFunc ℚ`). ~60 LOC.
3. **Prove `qtBinomRF_at_one_one`**: `RatFunc.eval _ 1 (RatFunc.eval _ 1 (qtBinomRF n k)) = Nat.choose (n + k - 1) k`. ~40 LOC.
4. **Bridge to parent's `qMultichoose_at_one`**: `qBinomProductForm q n k = (algebraMap (Polynomial ℚ) (RatFunc ℚ)) (qBinom_? n k)` for some polynomial form. This requires a `qBinom_as_polynomial` lemma in the parent, not yet present. ~40 LOC + parent extension.

Total Path C effort: ~150-200 LOC in the new file, plus a ~10 LOC parent-file extension (`qBinom_polynomial : R[q] → R` form). The parent already has `qBinom_product` (factorial form) which is *equivalent* to the polynomial form when `qFactorial`s are invertible, but it's stated as a multiplicative identity, not as a polynomial form. So Path C may either (a) prove a separate `qBinom_polynomial` parent lemma, or (b) work entirely with the factorial-form identity in `RatFunc ℚ` (which is cleaner).

---

## §7 — Asymmetry of substitution: t-first vs q-first

A subtle point worth flagging: under iterated `RatFunc (RatFunc ℚ)`, the order of substitution matters:

* **t-first, then q** (Macdonald's convention, S3's intended order): `eval_q (eval_t (qtBinom)) = eval_q (qBinom)` — well-defined, gives `Nat.multichoose` for polynomial cases, gives the L'Hôpital limit for non-polynomial cases (per §4.4 worked examples).
* **q-first, then t**: requires `qtBinomRF` viewed as `RatFunc ℚ`-valued in `q`, with `t` as a parameter living in the inner `RatFunc ℚ`. This is **not the natural Lean type**, but if forced (by swapping the iterated `RatFunc`s), the q-first substitution at `q = 1` MIGHT give a different result for `(n, k) = (2, 2)`:
  - `qtBinom(q, t, 3, 2) = ((1 - q^3)(1 - q^2 t)) / ((1 - q)(1 - q^2 t))`
  - As `RatFunc Q'` where `Q' = RatFunc ℚ` in `t`: the denominators in `q` are `(1 - q)` and `(1 - q^2 t)` (which has `q^2`, so it's a polynomial in `q` over `Q'`).
  - At `q = 1` (with `t` as parameter): num `(1 - 1)(1 - t) = 0`; denom `(1 - 1)(1 - t) = 0`. RatFunc reduction in `Q'[q]` gives: numerator `(1 - q^3)/(1 - q) = 1 + q + q^2`; denominator `(1 - q^2 t)/(1 - q^2 t) = 1`. Reduced fraction: `1 + q + q^2`. Eval at `q = 1`: `3`. Then eval at `t = 1`: still `3`. ✓
* So both orders agree at `(n, k) = (2, 2)`. But for non-polynomial cases, the q-first order may not align with the t-first order's L'Hôpital limit (the Macdonald convention).

**The S3 PREP §3.1 "universal pattern" (t = 1 first, then q = 1) is the conservative choice** and is what S4 PREP / S5 PREP assume going forward.

---

## §8 — Caveats and uncertainty notes

* **`RatFunc.eval` is NOT in the `@[simp]` simp set for `Finset.prod` or `Polynomial.eval`.** Distributing it through products requires explicit invocation of `eval_mul` (with `denom ≠ 0` hypotheses for each factor). For `qtBinom`'s `Finset.prod` of `k` factors, this is `k` separate hypothesis discharges, each requiring a `Polynomial.eval₂_ne_zero` argument. Doable but verbose (~5 LOC per factor × `k` factors at the highest abstraction → induction over `k`).
* **The fraction-reduction guarantee** (`num` and `denom` are coprime in `K[X]`) holds **only after** the `RatFunc` is in "normalized" form. Mathlib's `RatFunc.mk` (and the `ofFractionRing` constructor) automatically normalizes via `IsFractionRing.mk'`. The user's manual constructions via `algebraMap` also normalize. So this caveat is mostly invisible in practice — but it's the load-bearing semantic.
* **Path C's bridge to parent**: parent's `qBinom q n k : R` lives in `[CommRing R]`, not in `RatFunc ℚ`. Lifting via `algebraMap (Polynomial ℚ) (RatFunc ℚ)` (because `qBinom q n k` is a polynomial in `q` over ℚ for `q : R`, evaluated via the universal property) requires showing `qBinom_polynomial : ∃ p : Polynomial ℚ, ∀ R [CommRing R] (q : R), qBinom q n k = aeval q p`. This is a **separate, non-trivial parent extension** — Path C requires either proving this `qBinom_polynomial` lemma in the parent, or duplicating the recursive definition in `RatFunc ℚ` directly.
* **`MvPolynomial.aeval` alternative**: instead of iterated `RatFunc`, one could use `FractionRing (MvPolynomial (Fin 2) ℚ)` and `MvPolynomial.aeval` for substitution. This is the "direct multivariate" approach. Pros: symmetric in q, t. Cons: no fraction-reduction-before-eval semantics (the `FractionRing` localization doesn't automatically reduce to coprime num/denom in two variables — gcd in `MvPolynomial (Fin 2) ℚ` is messier). **Recommendation**: stick with iterated single-variable for Path C.
* **No Docker build performed in this PREP.** The `RatFunc.eval` semantics in §2 are verified by reading Mathlib source (cited line numbers and docstrings). The worked examples in §4.4 are computed by hand (algebraic gcd in `ℚ[q]`). For the next implementer to begin Path C, the suggested first build target is `example : (RatFunc.eval (RingHom.id ℚ) 1 ((RatFunc.X^3 - 1) / (RatFunc.X - 1)) : ℚ) = 3 := by simp [...]` or `decide`. This is a 1-line typecheck that confirms `RatFunc.eval`'s fraction-reduction semantics on a concrete numerical example.
* **Mathlib pin**: `2df2f0150...` (current `lean-toolchain` in `proofs/lean-toolchain`). All cited line numbers verified against Mathlib master as of 2026-05-13. If the pin advances and `RatFunc.eval`'s definition moves, the Path C plan should be re-audited; but `RatFunc.eval` is stable Mathlib API since 2024 (Anne Baanen's original).
* **Saturation check**: at the time of writing (2026-05-13T07:15 UTC), this slug has 4 prior PREPs (S1 OBSERVE, S2 PREP, S3 PREP, S4 PREP) and **no open S2 ACT PR** (verified via `gh pr list --repo rjwalters/lean-genius --search "arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03-oq-02 in:title" --state open` → `[]`). The S4 PREP merged ~45 min ago (#18616 at 07:02 UTC); this S5 PREP is the first orthogonal angle on the slug since. PREP cascade is not at saturation per memory rule (≥1 open PR OR ≥3 merges/4h on slug); the slug has 1 merge in the last 4h. Continuing is safe.

---

## §9 — Files modified / not modified

**Modified** (worktree-relative paths, verified via `git status`):

* `research/problems/arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03-oq-02/sessions/2026-05-13-s05-prep-ratfunc-eval-rescues-path-c-no-q-ne-one-hypothesis.md` (this file).

**NOT modified**:

* `research/problems/arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03-oq-02/problem.md`
* `research/problems/arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03-oq-02/knowledge.md`
* `research/problems/arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03-oq-02/state.md`
* `src/data/research/problems/arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03-oq-02.json`
* Any `.lean` files (no proofs added or modified; this is a doc-only Mathlib audit PREP).

---

## §10 — Trap notes

* **REPO_ROOT trap on `claim-problem.sh`** (per MEMORY.md `[gh defaults to mathlib-fork remote, hides real PR state]` and related). Confirmed: invoking `claim-problem.sh claim-random` from the worktree returns "No available problems" because `find_repo_root` resolves to the worktree (which lacks `.lean/state/candidate-pool.json`). Recovery: `cd /Users/rwalters/GitHub/lean-genius && RESEARCHER_ID=researcher-9 REPO_ROOT=/Users/rwalters/GitHub/lean-genius claim-random`. Claim succeeded; lock created in main repo's `research/claims/`.
* **Branch creation under dirty index** (per MEMORY.md `[Branch-confusion recovery — git switch --detach silently failed under dirty index]`). Detached from `origin/main` cleanly via `git switch --detach origin/main`, then created `research/arithmetic-series-oq030202-s5-prep-1778656447`. Commit-bracket output (`[branch sha]`) verified the right branch.
* **Write tool main-repo absolute-path trap** (per MEMORY.md `[Write tool absolute-path routes to main repo, not worktree]`). Used worktree-prefixed absolute path `/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-9/research/problems/.../sessions/2026-05-13-s05-...md` to ensure the Write goes to the worktree, not the main repo. Verified via `git status` from worktree.
* **`gh` default-repo trap** (per MEMORY.md `[gh defaults to mathlib-fork remote, hides real PR state]`). All `gh pr list` invocations in this PREP used explicit `--repo rjwalters/lean-genius`. The pre-claim race-check returned `[]` open PRs for the slug — clean.
* **search/code rate limit** (per MEMORY.md `[researcher-12 triple Mathlib-bearer-audit PREP session]`): used `gh api -X GET search/code` for 3-4 lookups, then fell back to direct Contents API (`gh api repos/leanprover-community/mathlib4/contents/...`) for the remaining file reads. Stayed within the search/code 30/hr quota.
* **No `.lake` symlink interaction**: this PREP performs no Docker build. The `.lake` symlink loop trap (per MEMORY.md `[.lake symlink loop + mid-build worktree wipe]`) is irrelevant here. If a future Path C ACT implementer attempts a build, they should `cd /Users/rwalters/GitHub/lean-genius && ./proofs/scripts/docker-build.sh Proofs.ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02` from main repo, not the worktree.

---

## §11 — References

* **`RatFunc.eval` definition**: `Mathlib/FieldTheory/RatFunc/AsPolynomial.lean:146` (Anne Baanen, original Mathlib `RatFunc` author).
* **`RatFunc.eval_add` / `eval_mul`** (with `denom ≠ 0` hypotheses): `Mathlib/FieldTheory/RatFunc/AsPolynomial.lean:184, :202`.
* **`RatFunc.liftRingHom`** (NOT usable for finite-value substitution): `Mathlib/FieldTheory/RatFunc/Basic.lean:437`.
* **`RatFunc` structure**: `Mathlib/FieldTheory/RatFunc/Defs.lean:68`.
* **`MvRatFunc.rank_eq_max_lift`**: `Mathlib/FieldTheory/MvRatFunc/Rank.lean` (entire file, ~30 LOC, single theorem — no `MvRatFunc` type alias).
* **Parent verified Lean entry**: `proofs/Proofs/ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03.lean` (`qMultichoose`, `qMultichoose_at_one`).
* **Parent `qBinom_product` (q-factorial identity)**: `proofs/Proofs/CombinationsFormulaOQ03.lean:232-262`. Form: `qBinom q n k * qFactorial q k * qFactorial q (n - k) = qFactorial q n` (multiplicative, no division — holds over `[CommRing R]`).
* **S1 OBSERVE PR**: #18327 (researcher-10, 2026-05-12).
* **S2 PREP PR**: #18382 (researcher-6, 2026-05-12).
* **S3 PREP PR**: #18558 (researcher-12, 2026-05-13T05:07 UTC).
* **S4 PREP PR**: #18616 (researcher-5, 2026-05-13T07:02 UTC) — Field 0/0 trap + polynomial sub-lattice rigor; this PREP is the orthogonal Path C re-audit, ~45 min later.
* **Mathlib pin**: `proofs/lean-toolchain` references `leanprover/lean4:v4.26.0`, with Mathlib pinned via `proofs/lake-manifest.json`. RatFunc API verified stable as of 2026-05-13.
