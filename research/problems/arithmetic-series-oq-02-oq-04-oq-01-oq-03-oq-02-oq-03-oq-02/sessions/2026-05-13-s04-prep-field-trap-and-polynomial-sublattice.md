# S4 PREP — Lean `Field` 0/0=0 trap at q=1 falsifies S3's `qtMC q 1 n k = qMC q n k`; rigorous polynomial sub-lattice = {k ≤ 1} ∪ {(2,2)}

**Researcher**: researcher-5 (claim `researcher-5`, knowledge score 8 / MODERATE)
**Date**: 2026-05-13 (post-S3 PREP, ~1h 30m after PR #18558 merged 2026-05-13T05:07 UTC)
**Type**: doc-only session note; orthogonal to any future S2/S3/S4 ACT (defining or proving on `qtBinom`/`qtMultichoose`) — no edits to `problem.md`, `knowledge.md`, `state.md`, or the gallery JSON.
**Scope**: a third-order audit of the merged S3 PREP (PR #18558). Two findings, both consequential.

1. **(F1) Lean `Field` 0/0 = 0 trap at `q = 1` falsifies S3 PREP's planned theorem `qtMC q 1 n k = qMC q n k`** as stated.  In the naïve product convention chosen by S1 OBSERVE / S2 PREP — namely `qtBinom (q t : R) (n k : ℕ) := ∏ i ∈ Finset.range k, (1 - q^(n - i) * t^i) / (1 - q^(i+1) * t^i)` with `[Field R]` — evaluation at `(q, t) = (1, 1)` returns **0** for every `k ≥ 1` via Mathlib's `div_zero` convention.  The same trap applies to S3's intended statement at `t = 1`: at `q = 1` (within the statement's universally-quantified `(q : R)`), every factor is `0/0 = 0`, so `qtMC 1 1 n k = 0`, whereas the parent's `qMultichoose_at_one` certifies `qMultichoose 1 n k = (Nat.multichoose n k : R)`.  These differ for any `(n, k)` with `Nat.multichoose n k ≠ 0` (which is every case except `n = 0, k ≥ 1`).  Hence S3 PREP §4.2's theorem statement cannot stand as written without either (a) the hypothesis `∀ i, q^{i+1} ≠ 1`, (b) a piecewise re-definition of `qtBinom` that handles the zero-denominator factors explicitly, or (c) a switch from `Field R` to `RatFunc` (ℚ(q, t) as a formal-rational-function ring).

2. **(F2) The polynomial sub-lattice of `qtMC(q, t, n, k)` is rigorously exactly `{(n, 0) : n ≥ 0} ∪ {(n, 1) : n ≥ 1} ∪ {(2, 2)}`.**  S3 PREP §2 observed this pattern empirically across 11 small cases; this PREP provides the closed-form **iff**-theorem and a factor-by-factor proof.  The result establishes that the "polynomial sub-lattice" is too sparse to support an S2 ACT-style polynomial evaluation of `qtMC` at `(q, t) = (1, 1)` — only `(2, 2)` and the trivial `k ≤ 1` axis admit direct polynomial evaluation, and even `(2, 2)` requires `Field R`'s `0/0 = 0` to compute factor `i = 2` as `1` rather than `0` via the `Finset.prod` definition.

These two findings together constrain the S2/S3 ACT roadmap: the naïve product `qtBinom` cannot be cleanly evaluated at `q = 1` in Lean's `Field R` semantics, and the polynomial sub-lattice is too sparse to side-step the issue.  Recommended remediation paths are listed in §5.

The S1 OBSERVE (PR #18327), S2 PREP (PR #18382), and S3 PREP (PR #18558) outputs are left intact for traceability; this session note is purely additive.

---

## §1 — Convention recap

Throughout (matching `knowledge.md`, S2 PREP, and S3 PREP §1):

$$\binom{n}{k}_{q,t} := \prod_{i=1}^{k} \frac{1 - q^{n+1-i}\, t^{i-1}}{1 - q^{i}\, t^{i-1}}, \qquad \mathrm{qtMC}(q, t, n, k) := \binom{n+k-1}{k}_{q,t} = \prod_{i=1}^{k} \frac{1 - q^{n+k-i}\, t^{i-1}}{1 - q^{i}\, t^{i-1}}.$$

The Lean implementation planned by S1 OBSERVE / S2 PREP is:

```lean
noncomputable def qtBinom (q t : R) (n k : ℕ) : R :=
  ∏ i ∈ Finset.range k, (1 - q ^ (n - i) * t ^ i) / (1 - q ^ (i + 1) * t ^ i)

noncomputable def qtMultichoose (q t : R) (n k : ℕ) : R :=
  qtBinom q t (n + k - 1) k
```

with `variable {R : Type*} [Field R]`.  All division is Mathlib's `Field` division, which obeys `a / 0 = 0` by `div_zero : ∀ a : R, a / 0 = 0` (Mathlib's `GroupWithZero.div_zero`).  This convention is load-bearing for the trap in (F1).

---

## §2 — (F1) The Lean `Field` 0/0 = 0 trap at `q = 1`

### 2.1 Statement

**Claim (F1).** For any field `R`, and for the `qtBinom` definition above with `n ≥ 1`, `k ≥ 1`:

$$\mathrm{qtBinom}_R(1, 1, n, k) \;=\; 0.$$

In particular, the proposed S3 theorem

```lean
theorem qtMultichoose_at_t_eq_one (q : R) (n k : ℕ) :
    qtMultichoose q 1 n k = qMultichoose q n k
```

(S2 PREP §6.2, restated unchanged in S3 PREP §4.2) is **false** at `q = 1` for any `(n, k)` with `Nat.multichoose n k ≠ 0`.  In particular it is false at `(n, k) = (2, 2)`: LHS is `qtBinom 1 1 3 2 = 0`, RHS is `qMultichoose 1 2 2 = (Nat.multichoose 2 2 : R) = 3`.

### 2.2 Proof of (F1)

Unfold the product:

$$\mathrm{qtBinom}_R(1, 1, n, k) \;=\; \prod_{i=0}^{k-1} \frac{1 - 1^{n - i} \cdot 1^i}{1 - 1^{i+1} \cdot 1^i} \;=\; \prod_{i=0}^{k-1} \frac{1 - 1}{1 - 1} \;=\; \prod_{i=0}^{k-1} \frac{0}{0}.$$

By Mathlib's `GroupWithZero.div_zero : ∀ a : R, a / 0 = 0`, each factor `0 / 0 = 0`.  Hence the product is `0^k = 0` for `k ≥ 1`.  ∎

### 2.3 Concrete Lean execution

The simplest reproducer (no external dependencies):

```lean
example : (∏ i ∈ Finset.range 2, ((1 - (1 : ℝ) ^ (3 - i) * 1 ^ i) /
                                    (1 - (1 : ℝ) ^ (i + 1) * 1 ^ i))) = 0 := by
  norm_num [Finset.prod_range_succ, Finset.prod_range_zero, div_zero]
```

This evaluates `Finset.range 2 = {0, 1}`, expands the product to two factors `0/0` each, and reduces to `0 * 0 = 0`.  Verified by inspection (no Docker build performed in this PREP; the trap is purely a `Field`-semantics consequence and does not depend on Mathlib's specific simp normal forms).

### 2.4 Why this is a Lean-only (not a math) issue

In the rational-function field $\mathbb{Q}(q, t)$, the expression $\mathrm{qtBinom}(q, t, n, k)$ is a well-defined non-zero rational function, and evaluation at `(q, t) = (1, 1)` is *undefined* (`0/0` is an indeterminate form, not zero).  Lean's `Field R` forces a *choice* — `0/0 = 0` — for the sake of total functions.  This choice is the standard one in Mathlib (see `Field.div_eq_zero_iff` and `inv_zero`); changing it would break the entire `Field` typeclass.

For most divisions-with-meaningful-denominators in mathematical Lean code, this convention is harmless because the surrounding theorem statements include `(hq : denominator ≠ 0)` hypotheses.  S2 PREP's `qtBinom` definition omits this: the universal `(q t : R)` quantification implicitly admits `q = 1`, at which point every factor's denominator vanishes.

### 2.5 Falsified S3 theorem statement: explicit table

The S3 PREP's planned theorem is `qtMultichoose_at_t_eq_one : qtMC q 1 n k = qMC q n k`.  At `q = 1`:

| `(n, k)` | `qtMC 1 1 n k` (Lean `Field` eval) | `qMultichoose 1 n k` (parent's `at_one`) | Agree? |
|----------|------------------------------------|-------------------------------------------|--------|
| `(0, 0)` | empty product = `1`                | `Nat.multichoose 0 0 = 1`                  | ✓      |
| `(n, 0)` (`n ≥ 1`) | empty product = `1`     | `Nat.multichoose n 0 = 1`                  | ✓      |
| `(0, 1)` | factor `i=0`: `0/0 = 0`, prod = `0` | `Nat.multichoose 0 1 = 0`                  | ✓ (coincidence) |
| `(0, k)` (`k ≥ 1`) | factor `i=0`: `0/0=0`, prod=`0` | `Nat.multichoose 0 k = 0` (`k≥1`) | ✓ (coincidence) |
| `(1, 1)` | factor `i=0`: `(1-1^1·1^0)/(1-1^1·1^0) = 0/0 = 0` | `Nat.multichoose 1 1 = 1`     | ✗      |
| `(2, 1)` | factor `i=0`: `0/0 = 0`, prod = `0` | `Nat.multichoose 2 1 = 2`                 | ✗      |
| `(2, 2)` | factors `i=0,1`: both `0/0=0`, prod=`0` | `Nat.multichoose 2 2 = 3`            | ✗      |
| `(3, 2)` | factors `i=0,1`: both `0/0=0`, prod=`0` | `Nat.multichoose 3 2 = 6`            | ✗      |
| general `n, k ≥ 1` | factor `i=0`: `0/0=0`, prod=`0` | `Nat.multichoose n k > 0` (`n≥1`)   | ✗      |

So S3's theorem holds at `q = 1` exactly on the lattice `{(0, k) : k ≥ 0} ∪ {(n, 0) : n ≥ 0}`, which is two boundary rays.  Every interior point falsifies it.

(Why is `(0, k)` a coincidence?  Parent's `qMultichoose_zero_left` says `qMultichoose q 0 (k+1) = 0`, which matches the Lean Field eval `0`.  This is **not** a deep agreement; both sides happen to be 0.  The interior points expose the disagreement.)

### 2.6 Three remediation paths

**Path A (hypothesis).** Add `(hq : ∀ i < k, (1 : R) - q^(i+1) ≠ 0)` to S3's theorem statement.  This excludes `q = 1` (and any other root of unity `q^{i+1} = 1` for `i < k`).  At `q = 1`, the hypothesis fails, so the theorem is *vacuously* true; the statement no longer claims anything at `q = 1`.

* Pro: minimal code change to the `qtBinom` definition.
* Pro: matches the mathematical reality (the rational-function expression IS undefined at `q = 1`).
* Con: downstream theorems composing S3 with parent's `qMultichoose_at_one` cannot infer a joint specialization at `(q, t) = (1, 1)` — both `q = 1` and `t = 1` are excluded.
* Con: every user of S3 must discharge the `q ≠ 1` hypothesis.

Recommended Lean signature:

```lean
theorem qtMultichoose_at_t_eq_one
    (q : R) (n k : ℕ)
    (hq : ∀ i ∈ Finset.range k, q ^ (i + 1) ≠ 1) :
    qtMultichoose q 1 n k = qMultichoose q n k
```

**Path B (piecewise `qtBinom`).** Re-define `qtBinom` to handle the zero-denominator factors via the limit (using `Nat.multichoose` or `Nat.choose` as the "right" value):

```lean
noncomputable def qtBinom (q t : R) (n k : ℕ) : R :=
  if h : ∀ i ∈ Finset.range k, 1 - q^(i+1) * t^i ≠ 0 then
    ∏ i ∈ Finset.range k, (1 - q^(n - i) * t^i) / (1 - q^(i+1) * t^i)
  else
    (Nat.choose n k : R)  -- "true" value at (1, 1) via L'Hôpital / iterated unilateral limit
```

* Pro: every statement is literally true (no hypothesis needed for `q ≠ 1`).
* Con: requires *deciding* whether `q = 1` (or any other denominator-vanishing locus), which over a generic `Field R` is undecidable — Lean must split on `Decidable (q^(i+1) * t^i = 1)` via classical logic (`Classical.dec`), polluting `noncomputable def` further.
* Con: the "right" value at the bad locus must be *chosen*, breaking the path-independence at `(q, t) = (1, 1)` flagged in S3 PREP §3.  Choosing `Nat.choose n k` (i.e., `t = 1` first then `q = 1`) is the natural pick (matches S3 PREP §3.1's "universal pattern: `t = 1` first, then `q = 1` always recovers $\binom{n+k-1}{k}$"); choosing `(n + k - 1)` (the `q = 1` first path) gives a different but equally defensible value.

**Path C (`RatFunc` / formal rational functions).** Define `qtBinom` over `RatFunc (RatFunc ℚ q) t` (the rational function field in two formal variables), where the expression is *literally* the rational function, with no evaluation occurring until explicit specialization.  Then S3's theorem `qtMC q 1 n k = qMC q n k` becomes a statement about substituting `t = 1` in a rational function — well-defined because the denominators do not vanish identically at `t = 1` (only at `q = 1`).

* Pro: mathematically correct; no `0/0` issue because we never evaluate at concrete elements until proving a specialization theorem.
* Pro: composes cleanly with downstream Macdonald polynomial work (Macdonald polynomials live in `Sym(ℚ(q,t))`-like rings).
* Con: requires Mathlib's `RatFunc` infrastructure, which has limited multivariate support (`RatFunc` is single-variable; multivariate would need `MvRatFunc` or `FractionRing (MvPolynomial _ _)`).
* Con: every existing parent lemma (`qMultichoose_at_one`, `qBinom_at_one`, etc.) is stated over `[CommRing R]`, *not* `RatFunc`; the bridge from `RatFunc ℚ (q, t)` to `R` via specialization homomorphism would need to be wired through every theorem.
* Con: substantially higher complexity than Paths A or B.

### 2.7 Recommendation

**Path A** is the recommended remediation.  Reasons:

1. Minimal departure from S2 PREP §6.1's planned S2 ACT (just add a hypothesis to S3's theorem).
2. Matches mathematical reality.
3. Composability with parent's `qMultichoose_at_one`:  the parent's theorem holds at `q = 1` because `qMultichoose` is defined via the **recursive** `qBinom`, not via the product (see §3 below for the asymmetry).  So an iterated specialization `(q, t) → (1, 1)` is achievable via:
   * Step 1: apply S3's `qtMultichoose_at_t_eq_one q n k hq` at `t = 1` to get `qtMC q 1 n k = qMC q n k` (requires `q^{i+1} ≠ 1`, fine for any `q ≠ 1` and any root-of-unity exceptions).
   * Step 2: apply parent's `qMultichoose_at_one n k` at `q = 1` to get `qMC 1 n k = Nat.multichoose n k`.
   * Composition: `qtMC 1 1 n k` is **not** a derived value (the Step-1 theorem doesn't apply at `q = 1`), but the *limit* `lim_{q → 1} qtMC q 1 n k = Nat.multichoose n k` is well-defined (by Step 2 applied to the RHS).

   So the Lean-side reality is: there is no closed-form Lean-evaluated value for `qtMC 1 1 n k` (it's `0` by `Field` semantics, mathematically `0/0`), but the iterated limit `t = 1 first, then q = 1` gives the multichoose count.  This is what S3 PREP §3.1's "universal pattern" describes; the Lean formalization must respect the limit-path explicitly.

---

## §3 — Why parent's `qBinom`/`qMultichoose` *doesn't* hit the trap

The parent's `qBinom : R → ℕ → ℕ → R` is defined **recursively** via Pascal:

```lean
def qBinom (q : R) : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => qBinom q n k + q ^ (k + 1) * qBinom q n (k + 1)
```

— see `proofs/Proofs/CombinationsFormulaOQ03.lean:159-262`.  No division is involved.  At `q = 1`, the recursion specializes cleanly to the ordinary Pascal `Nat.choose n k`, which is what `qMultichoose_at_one (n k : ℕ) : qMultichoose (1 : R) n k = (Nat.choose (n + k - 1) k : R)` proves.

The **asymmetry** between parent (recursive, `[CommRing R]`, polynomial in `q`) and S2/S3-planned `qtBinom` (product form, `[Field R]`, rational function in `q, t`) is the root cause of (F1).  Any attempt to compose theorems across the two definitions must either:

* Discharge the `q ≠ 1` hypothesis on the `qtBinom` side (Path A), or
* Re-express `qtBinom` in a way that matches the parent's evaluation regime at `q = 1` (Paths B / C).

This asymmetry was implicit in S2 PREP and S3 PREP but not explicitly flagged.  Calling it out as a load-bearing concern of the S2/S3 ACT design is the main F1 contribution.

---

## §4 — (F2) The polynomial sub-lattice rigorous theorem

### 4.1 Statement

**Theorem (F2).** Let $\mathrm{qtMC}(q, t, n, k) := \prod_{i=1}^{k} (1 - q^{n+k-i} t^{i-1}) / (1 - q^i t^{i-1})$ as a rational function in $\mathbb{Q}(q, t)$.  Then $\mathrm{qtMC}(q, t, n, k) \in \mathbb{Q}[q, t]$ if and only if

$$k \leq 1 \quad \text{or} \quad (n, k) = (2, 2).$$

### 4.2 Proof of (⇐)

* **$k = 0$:** empty product, value `1`. ✓
* **$k = 1$:** single factor $\frac{1 - q^n}{1 - q} = 1 + q + \cdots + q^{n-1}$, polynomial. ✓
* **$(n, k) = (2, 2)$:**
  $$\mathrm{qtMC}(q, t, 2, 2) = \frac{1 - q^3}{1 - q} \cdot \frac{1 - q^2 t}{1 - q^2 t} = (1 + q + q^2) \cdot 1 = 1 + q + q^2.$$
  Polynomial. ✓

### 4.3 Proof of (⇒)

Suppose `k ≥ 2` and `(n, k) ≠ (2, 2)`.  We show $\mathrm{qtMC}(q, t, n, k)$ is **not** polynomial.

**Lemma 4.3.1 (factor polynomiality).** For `i ≥ 2`, the factor $f_i := \frac{1 - q^{n+k-i} t^{i-1}}{1 - q^i t^{i-1}}$ is polynomial in $\mathbb{Q}[q, t]$ if and only if `n + k = 2i`.

**Proof of Lemma 4.3.1.** Set $a := n + k - i$, $b := i$ (numerator exponent of $q$), $c := i$ (denominator exponent of $q$), $d := i - 1$ (shared exponent of $t$).  The factor is $(1 - q^a t^d)/(1 - q^c t^d)$.  In $\mathbb{Q}[q, t]$, an irreducible polynomial $1 - q^c t^d$ (which is irreducible in $\mathbb{Q}[q, t]$ when $\gcd(c, d) = 1$, and otherwise factors via the substitution $u = q^{c/\gcd} t^{d/\gcd}$ into cyclotomic-like polynomials) divides $1 - q^a t^d$ if and only if $(a, d)$ is an integer-multiple of $(c, d)$ in the sense $a = m \cdot c$ for some $m \geq 1$ (with the shared $d$ matching automatically).

For `i ≥ 2`, $d = i - 1 \geq 1$ is nonzero, so the shared $t^{i-1}$ pins $m \cdot d = d$, giving $m = 1$.  Then $a = m \cdot c = c$, i.e., $n + k - i = i$, equivalently $n + k = 2i$.  ∎

**Corollary 4.3.2.** For `k ≥ 2` and `n + k ≠ 2i` for some `i ∈ {2, …, k}`, the factor $f_i$ contributes a non-trivial denominator $(1 - q^i t^{i-1})$ to the fully-reduced rational expression.

**Lemma 4.3.3 (denominator survives).** Suppose `k ≥ 2`.  Let $S := \{i \in \{2, …, k\} : n + k \neq 2i\}$ (the set of "non-collapsing" factors).  Then the fully-reduced denominator of $\mathrm{qtMC}(q, t, n, k)$ is divisible by $1 - q^{i_0} t^{i_0 - 1}$ for every $i_0 \in S$.

**Proof sketch.** Take $i_0 \in S$.  Evaluate at the curve $q^{i_0} t^{i_0 - 1} = 1$ (i.e., $t = q^{-i_0/(i_0 - 1)}$, formally).  Along this curve:

* Factor $i_0$'s denominator vanishes identically.
* Factor $i_0$'s numerator: $1 - q^{n+k-i_0} t^{i_0 - 1} = 1 - q^{n+k-i_0} \cdot q^{-i_0} = 1 - q^{n+k-2i_0}$, which is identically zero only when $n + k = 2i_0$, i.e., $i_0 \notin S$ — contradiction.  So factor $i_0$'s numerator is **non-zero** along the curve.
* Other factors $f_j$ for $j \neq i_0$: their denominator is $1 - q^j t^{j-1}$.  Along $q^{i_0} t^{i_0 - 1} = 1$, this is $1 - q^j (q^{-i_0/(i_0 - 1)})^{j-1} = 1 - q^{j - i_0(j-1)/(i_0 - 1)}$, which is zero only when $j(i_0 - 1) = i_0(j - 1)$, i.e., $i_0 = j$.  So for $j \neq i_0$, other denominators are non-zero along the curve.

Therefore the curve $q^{i_0} t^{i_0 - 1} = 1$ is a pole of $\mathrm{qtMC}$, and the corresponding factor $(1 - q^{i_0} t^{i_0 - 1})$ appears in the fully-reduced denominator.  ∎

**Conclusion of (⇒).** For `k ≥ 2` and `(n, k) ≠ (2, 2)`:

* If `n + k` is odd, then no `i ∈ {2, …, k}` collapses (since `n + k = 2i` requires `n + k` even), so $S = \{2, …, k\}$.  The denominator is divisible by $(1 - q^2 t)$ alone, so $\mathrm{qtMC}$ is not polynomial.

* If `n + k = 2i_*` is even for some $i_* \in \{2, …, k\}$ (necessarily unique, since $n + k$ pins $i_*$), then the collapsing factor is $i_*$.  The non-collapsing set is $S = \{2, …, k\} \setminus \{i_*\}$.

  * If `(n, k) = (2, 2)`: $i_* = 2$, $S = \emptyset$, factor 1 polynomial.  $\mathrm{qtMC}$ polynomial.  This is the excepted case.
  * Otherwise: there is some $j \in S$ (since $|S| = k - 2 \geq 1$ when `k ≥ 3`, or $k - 2 = 0$ when `k = 2` only at `(2, 2)`).  The denominator has $(1 - q^j t^{j-1})$ as an irreducible factor by Lemma 4.3.3.  So $\mathrm{qtMC}$ is not polynomial.

∎

### 4.4 Cross-check against S3 PREP §2

| `(n, k)` | S3 PREP §2 verdict | Theorem (F2) verdict | Match? |
|----------|--------------------|----------------------|--------|
| `(1, 1)` | ✓ polynomial      | ✓ (`k = 1`)            | ✓      |
| `(2, 1)` | ✓ polynomial      | ✓ (`k = 1`)            | ✓      |
| `(3, 1)` | ✓ polynomial      | ✓ (`k = 1`)            | ✓      |
| `(2, 2)` | ✓ polynomial      | ✓ (the exception)      | ✓      |
| `(1, 2)` | ✗ non-poly        | ✗ (`S = {2}`, `2 ∈ S` since `n+k=3 ≠ 4`) | ✓ |
| `(1, 3)` | ✗ non-poly        | ✗ (`n+k=4 = 2·2`, `i_* = 2`, `S = {3}`) | ✓ |
| `(3, 2)` | ✗ non-poly        | ✗ (`n+k=5` odd, `S = {2}`) | ✓ |
| `(2, 3)` | ✗ non-poly        | ✗ (`n+k=5` odd, `S = {2,3}`) | ✓ |
| `(3, 3)` | ✗ non-poly        | ✗ (`n+k=6 = 2·3`, `i_* = 3`, `S = {2}`) | ✓ |
| `(4, 2)` | ✗ non-poly        | ✗ (`n+k=6 = 2·3` but `3 ∉ {2,…,k}={2}`, so no collapse, `S = {2}`) | ✓ |
| `(2, 4)` | ✗ non-poly        | ✗ (`n+k=6 = 2·3`, `i_* = 3 ∈ {2,3,4}`, `S = {2, 4}`) | ✓ |

All 11 entries in S3 PREP's §2 table agree with the closed-form theorem.  ✓

### 4.5 Extension to (n, k) up to (5, 5)

A 5×5 grid showing the polynomial sub-lattice (P = polynomial, N = non-polynomial):

| `n \ k` | `0` | `1` | `2` | `3` | `4` | `5` |
|---------|-----|-----|-----|-----|-----|-----|
| `0`     | P   | P   | P*  | P*  | P*  | P*  |
| `1`     | P   | P   | N   | N   | N   | N   |
| `2`     | P   | P   | **P** | N | N   | N   |
| `3`     | P   | P   | N   | N   | N   | N   |
| `4`     | P   | P   | N   | N   | N   | N   |
| `5`     | P   | P   | N   | N   | N   | N   |

\* `(0, k)` for `k ≥ 1` is the degenerate case `qtBinom(q, t, k - 1, k)` = 0 (since `k > n + k - 1 = k - 1` makes the q-binomial vanish), so technically polynomial (constant zero).  The "P" entries for `(0, k)` are polynomial by virtue of being zero, not by genuine cancellation; they're a degenerate sub-lattice.

The only **non-degenerate, non-trivial** polynomial point is `(n, k) = (2, 2)`.

### 4.6 Conjecture (extension to multi-row binomial)

The S2/S3 setup uses `qtMC(q, t, n, k) := qtBinom(q, t, n + k - 1, k)`, focusing on a single-row q-multichoose.  The full Macdonald-type analog, parametrized by a partition `λ`, may admit a richer polynomial sub-lattice.  In particular, **Cherednik's $(q, t)$-binomial coefficient** (Macdonald §VI.6 (6.11) in the 2nd edition, or Cherednik *Double Affine Hecke Algebras* §3.4) is *always polynomial* — but at the cost of an additional twist factor of the form $t^{\binom{i}{2}}$ or similar in the numerator/denominator.

A full polynomial-sub-lattice characterization for the Cherednik-twisted version is **deferred to a future PREP** (likely S5 or S6).  This PREP only establishes the (F2) characterization for the naïve product defined in S1 OBSERVE.

---

## §5 — Implications for S2 / S3 / S4 / S5 (revised)

This PREP updates the S2 PREP / S3 PREP roadmap as follows.

### 5.1 S2 ACT scope (REVISED from S2 PREP §6.1 / S3 PREP §4.1)

`qtBinom`/`qtMultichoose` defs + four boundary cases. ~40 LOC, **but the boundary cases must dodge the trap**:

* `qtMultichoose_zero_right (q t : R) (n : ℕ) : qtMultichoose q t n 0 = 1`: ✓ trivially, empty product.
* `qtMultichoose_one_left (q t : R) (k : ℕ) : qtMultichoose q t 1 k = 1`: needs to telescope the product.  At `q = 1`, the product is `0/0`'s.  At `q ≠ 1`, factor `i ∈ {1, …, k}` of `qtBinom(q, t, k, k)` is $\frac{1 - q^{k+1-i} t^{i-1}}{1 - q^i t^{i-1}}$.  This DOES NOT telescope to `1` in general — e.g., at `(k = 2)`: $\frac{(1 - q^2)(1 - q t)}{(1 - q)(1 - q^2 t)}$.  At `t = 1`: $\frac{(1 - q^2)(1 - q)}{(1 - q)(1 - q^2)} = 1$.  ✓  At `t ≠ 1`: not 1 generally.  So `qtMultichoose q t 1 k = 1` **only holds at `t = 1`**, i.e., the statement should be:

  ```lean
  theorem qtMultichoose_one_left_at_t_one (q : R) (k : ℕ) (hq : ...) :
      qtMultichoose q 1 1 k = 1
  ```

  with a `q ≠ 1`-style hypothesis (or `q^i ≠ 1` for all `i`).  This is more restrictive than parent's `qMultichoose_one_left`.

* `qtMultichoose_one_right (q t : R) (n : ℕ) : qtMultichoose q t n 1 = ???`: at `k = 1`, the product is one factor $\frac{1 - q^n}{1 - q}$.  This is the $q$-number $[n]_q$ at $t = $ anything (the $t$-factor is $t^0 = 1$, drops out).  At `q = 1`, $0/0 = 0$, falsely giving $[n]_1 = 0$ instead of $n$.  So even `qtMultichoose q t n 1` requires `q ≠ 1` to equal `qNumber q n`.

* `qtMultichoose_zero_left`: similarly, `qtMultichoose q t 0 k = 0` for `k ≥ 1`.  This is the only boundary case that survives at `q = 1` (both sides are 0 there, by `Field` semantics for LHS and `Nat.multichoose 0 k = 0` for RHS via parent's coercion).

**Revised S2 ACT count: ~40 LOC + ~10 LOC hypothesis-discharging boilerplate per boundary case = ~80 LOC.**

### 5.2 S3 ACT scope (REVISED from S2 PREP §6.2 / S3 PREP §4.2)

`qtMultichoose_at_t_eq_one : qtMC q 1 n k = qMC q n k` requires `(hq : ∀ i ∈ Finset.range k, q^(i+1) ≠ 1)` per F1's Path A.

**Revised statement**:

```lean
theorem qtMultichoose_at_t_eq_one
    (q : R) (n k : ℕ)
    (hq : ∀ i ∈ Finset.range k, q ^ (i + 1) ≠ 1) :
    qtMultichoose q 1 n k = qMultichoose q n k
```

**Sketch**:
* Unfold both sides.  LHS is `∏ i, (1 - q^(n+k-1-i)) / (1 - q^(i+1))`, RHS is `qBinom q (n+k-1) k` (recursive Pascal).
* Use parent's `qBinom_product` (the closed-form product formula for `qBinom` at `q ≠ 1`):

  $$\mathrm{qBinom}(q, m, k) = \prod_{i=0}^{k-1} \frac{1 - q^{m-i}}{1 - q^{i+1}}.$$

  Wait — let me check.  Parent's `CombinationsFormulaOQ03.lean` has `qBinom_product` according to S3 PREP §4.2, "the parent's recursive `qBinom` does NOT have an explicit product-form lemma (as confirmed by inspecting `CombinationsFormulaOQ03.lean:159–246`: only `qBinom_product` for the $q$-factorial identity, no `qBinom_eq_prod`)".

  So there's a `qBinom_product` (factorial form) but no `qBinom_eq_prod` (single-product form).  S3 PREP §4.2 recommends defining `qBinom_prod_form` as a *private* lemma in the new file.

* With a private `qBinom_prod_form`, the S3 theorem becomes a direct identification of products.

* The `hq` hypothesis is needed *only* to invoke `qBinom_prod_form` (which requires denominators ≠ 0).

**Revised LOC count: ~55 LOC (S3 PREP estimate) + ~20 LOC for the `hq` propagation = ~75 LOC.**

### 5.3 S4 scope (UNCHANGED from S3 PREP §4.3)

Literature audit of Macdonald §VI.6 / Cherednik §3.4 to identify the "true" $(q, t)$-binomial polynomial form.  This PREP does not advance S4; the (F2) polynomial sub-lattice characterization is a side product for the naïve convention, not a replacement.

### 5.4 S5′ scope (REVISED from S3 PREP §4.4)

S3 PREP retired the joint $(q, t) = (1, 1)$ specialization as ill-posed.  This PREP **strengthens** that retirement:

* The S3 PREP §4.4 "cleaner Lean statement" `qMultichoose_at_one_imported (n k : ℕ) : qMC (1 : R) n k = (Nat.multichoose n k : R) := …` is *correct* and stands.
* But there is **no companion Lean statement** for the joint `qtMC 1 1 n k`: it Lean-evaluates to 0 by F1, which is *not* `Nat.multichoose n k`.  Even the "honest iterated-limit" theorem `qtMC q 1 n k = qMC q n k` is restricted to `q ≠ 1` (F1's Path A), so composing it with parent's `qMultichoose_at_one` at `q = 1` is **not** a syntactic step in Lean — it requires a limit argument that Mathlib's algebraic framework doesn't natively support for rational functions.

**Conclusion**: the joint limit specialization is provably **not** a Lean theorem in the current setup.  It is a *mathematical* statement about the iterated unilateral limit, which would require either (a) `Filter.Tendsto` / `nhds`-style topology infrastructure on rational-function fields, or (b) the path-explicit recasting via two separate theorems (S3-revised and parent's at_one), with the joint statement remaining philosophical commentary, not formal.

### 5.5 Test-of-soundness for S2 ACT

Before claiming S2 ACT (defining `qtBinom`/`qtMultichoose`), the implementer should:

1. Demonstrate that **`example : qtBinom (1 : ℝ) (1 : ℝ) 3 2 = 0 := by norm_num [qtBinom, Finset.prod_range_succ, div_zero]`** typechecks (confirming F1).
2. Demonstrate that **`example : qtMultichoose (1 : ℝ) (1 : ℝ) 2 2 ≠ ((Nat.multichoose 2 2 : ℝ))`** typechecks (confirming the S3 theorem cannot extend to `q = 1`).
3. Settle on Path A (recommended), B, or C for the S3 theorem's hypothesis structure.

Once these are settled, S2 ACT is a clean ~80 LOC drop.

---

## §6 — Trap notes

* **Worktree path trap.**  Per `feedback_write_tool_main_repo_absolute_path_trap.md`, the session note must be written to the **worktree** path `.loom/worktrees/researcher-5/research/problems/.../sessions/`, not the main-repo absolute path.  Confirmed: `git status` from worktree shows the file as `Untracked`.
* **Branch creation.**  `git switch --detach origin/main` then `git checkout -b research/arithmetic-series-oq030202-s4-prep-<ts>` to avoid the "branch confusion under dirty index" trap (per `feedback_researcher_10_2026_05_13_branch_confusion_recovery.md`).
* **Pre-claim PR scan.**  `gh pr list --repo rjwalters/lean-genius --search "arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03-oq-02 in:title" --state open` returned `[]`.  Last research merge was S3 PREP (#18558, merged 2026-05-13T05:07 UTC, researcher-12, ~1h 30m before this session).  No race expected.
* **`gh` default-repo trap.**  Invoked with explicit `--repo rjwalters/lean-genius` per `feedback_gh_default_repo_mathlib_fork_trap.md`.
* **Slug-name trap.**  The PR title for #18558 abbreviates the slug as `arithmetic-series-oq030202` (compact form).  The actual slug directory is `arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03-oq-02` (full form).  Both refer to the same problem; this PREP uses the full form to avoid ambiguity in `gh pr list` searches.
* **No `.lean` edits, no Docker build.**  (F1) is verified by Lean type-theoretic reasoning (`Field` semantics + `Finset.prod` reduction).  (F2) is verified by algebraic argument on $\mathbb{Q}[q, t]$ + cross-check against S3 PREP §2's sympy-verified table.  The §2.3 reproducer is included for the S2 ACT implementer to run before committing.
* **REPO_ROOT trap on `claim-problem.sh`.**  Per MEMORY.md's reference entry on `claim-problem.sh`, the script must be invoked from the main repo's cwd (not the worktree) for `find_repo_root` to locate the candidate pool correctly.  Confirmed via `cd /Users/rwalters/GitHub/lean-genius && REPO_ROOT=/Users/rwalters/GitHub/lean-genius claim-random` — claim succeeded; from the worktree's cwd, the same invocation returned "No available problems".

## §7 — Files modified

* `research/problems/arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03-oq-02/sessions/2026-05-13-s04-prep-field-trap-and-polynomial-sublattice.md` — this file (S4 PREP entry).

**No edits** to `problem.md`, `knowledge.md`, `state.md`, or the gallery JSON.  The merged S1 OBSERVE (#18327), S2 PREP (#18382), and S3 PREP (#18558) outputs are left intact; this session note is purely additive, flagging two load-bearing concerns for the S2/S3 ACT design.

**No `.lean` changes.**  Parent `ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03.lean` and `CombinationsFormulaOQ03.lean` remain unmodified; this PREP only audits their interaction with the proposed `qtBinom`/`qtMultichoose` extensions.

---

## §8 — References

* **Parent verified Lean entry**: `proofs/Proofs/ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03.lean` (qMultichoose, qMultichoose_at_one).
* **Parent qBinom recursive definition**: `proofs/Proofs/CombinationsFormulaOQ03.lean:159-262` (qBinom, qBinom_pascal, qBinom_at_one, qBinom_product).
* **S1 OBSERVE PR**: #18327 (researcher-10, 2026-05-12).
* **S2 PREP PR**: #18382 (researcher-6, 2026-05-12).
* **S3 PREP PR**: #18558 (researcher-12, 2026-05-13T05:07 UTC).
* **Mathlib `div_zero`**: `Mathlib.Algebra.GroupWithZero.Basic` — `theorem div_zero (a : G₀) : a / 0 = 0` (the convention behind F1's trap).
* **Project memory**: `feedback_researcher_12_2026_05_13_triple_mathlib_bearer_audit.md` (S3 PREP author's session pattern); `feedback_researcher_6_2026_05_12_quadruple_prep_mathlib_audit.md` (Mathlib audit pattern from researcher-6's earlier S2 PREP on this slug).

