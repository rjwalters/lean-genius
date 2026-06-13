# Knowledge Base: derangements-convergence-oq-01-oq-02

Insights accumulated during research on this problem.

ORIENT survey by researcher-10 on 2026-06-13 (Docker verification blackout — no
Lean build available; this is a math + infrastructure survey, not an ACT).

---

## Problem Understanding

**Parent** (`derangements-convergence-oq-01`, file `DerangementsConvergenceOQ01.lean`,
namespace `KFixedConvergence`): for a uniform random permutation of `Fin n`, with
`X_n` = number of **fixed points** (= 1-cycles), proves

  P(X_{n+k} = k) = (1/k!)·D(n)/n! → e⁻¹/k!  as n → ∞,

which is the **Poisson(1)** mass function. Here `D` = `numDerangements`
(permutations with no fixed point) and the analytic engine is Mathlib's
`numDerangements_tendsto_inv_e`.

**This open question** (`-oq-02`): replace 1-cycles (fixed points) by **k-cycles**.
For a uniform random permutation `σ` of `[n]`, let `C_{n,k}` = number of k-cycles
of `σ`. Prove

  P(C_{n,k} = m) → e^{−1/k}·(1/k)^m / m!   as n → ∞,

i.e. `C_{n,k}` converges in distribution to **Poisson(1/k)** (Goncharov 1944).

> **Statement correction.** The seeker's one-line phrasing
> "`P(σ has exactly m k-cycles) → Pois(1/k)^m`" is imprecise. The correct limit is
> the Poisson(1/k) *pmf* evaluated at `m`: `e^{−1/k}·(1/k)^m/m!`. The "`^m`" in the
> seeker text should be read as "the pmf at the point m", not a literal m-th power
> of a probability. The ACT theorem must target `e^{−1/k}·(1/k)^m/m!`.

---

## Insights

### 1. The exact closed form (the key reduction — fully worked out)

Define `a_{j,k}` = (number of permutations of `[j]` with **no k-cycle**) / `j!`.
Note `a_{j,1} = D(j)/j!` is exactly the derangement fraction (no 1-cycle = no fixed
point). Then for `mk ≤ n`:

  **P(C_{n,k} = m) = (1/(k^m · m!)) · a_{n−mk, k}.**     (★)

*Derivation.* A permutation with exactly `m` k-cycles is built by (i) choosing the
`mk` elements that lie on the k-cycles and arranging them into `m` unordered
k-cycles, then (ii) permuting the remaining `n−mk` elements with **no** k-cycle.
The number of ways to arrange `mk` labelled elements into `m` k-cycles is
`(mk)!/(k^m · m!)`, and `C(n,mk)·(mk)! = n!/(n−mk)!`. Hence

  #{exactly m k-cycles} = [n!/((n−mk)!·k^m·m!)] · A_{n−mk,k},

and dividing by `n!` gives (★), with `A_{j,k} = j!·a_{j,k}`.

**Sanity check vs parent (k = 1).** (★) gives
`P(C_{n,1}=m) = (1/(1^m·m!))·a_{n−m,1} = (1/m!)·D(n−m)/(n−m)!` — this is *exactly*
the parent's `probKFixed_eq` (with `m` the number of fixed points). The
generalization is therefore the faithful one and is consistent at k = 1. ✓

### 2. Inclusion–exclusion sum for `a_{j,k}` (the analogue of `numDerangements_sum`)

Via the exponential generating function for permutations with no k-cycle,
`(1/(1−z))·exp(−z^k/k)`, extracting `[z^j]` gives the partial sum

  **a_{j,k} = Σ_{i=0}^{⌊j/k⌋} (−1)^i / (k^i · i!).**     (†)

For `k = 1` this is `Σ_{i=0}^{j} (−1)^i/i! = D(j)/j!`, matching
`numDerangements_sum`. ✓

### 3. The limit (analogue of `numDerangements_tendsto_inv_e`)

`e^{−1/k} = Σ_{i≥0} (−1)^i/(k^i·i!)`, so (†) is its partial sum truncated at
`i = ⌊j/k⌋`. The terms `(1/k)^i/i!` are strictly decreasing in `i` (ratio
`(1/k)/(i+1) < 1`), so the alternating-series estimate gives the **rate bound**

  |a_{j,k} − e^{−1/k}| ≤ (1/k)^{⌊j/k⌋+1} / (⌊j/k⌋+1)!  →  0.

Therefore `a_{j,k} → e^{−1/k}` as `j → ∞`, and combining with (★):

  P(C_{n+mk,k} = m) = (1/(k^m·m!))·a_{n,k} → e^{−1/k}·(1/k)^m/m!.   ∎

This mirrors the parent line-for-line: (★)↔`probKFixed_succ_eq`, the rate
bound↔`derangements_rate`/`kFixed_convergence_rate`, the limit↔`kFixed_tendsto`.

---

## Lean / Mathlib infrastructure assessment

**Available (k = 1 only):** `Mathlib.Combinatorics.Derangements.{Basic,Finite,Exponential}`
provides `numDerangements`, `numDerangements_sum`, and
`numDerangements_tendsto_inv_e`. These cover *only* the fixed-point (1-cycle) case
the parent already used. There is **no** general "permutations with no k-cycle"
count or its limit in Mathlib.

**Needed but NOT in Mathlib (k ≥ 2):**
- A definition `numNoKCycle k j` := `(Finset.univ.filter (fun σ : Equiv.Perm (Fin j) =>
  k ∉ σ.cycleType)).card`, built on `Equiv.Perm.cycleType` (which *is* in Mathlib).
- The counting identity (★): requires the "number of ways to form m disjoint
  k-cycles = (mk)!/(k^m·m!)" lemma. Mathlib has `Equiv.Perm.cycleType` and some
  cardinality-by-cycle-type results, but the disjoint-k-cycle count and the
  product decomposition (★) are not packaged; this is the heaviest new lemma.
- The inclusion–exclusion identity (†). Mathlib's derangement EGF argument lives in
  `Derangements.Exponential` but is specialized to fixed points; generalizing it to
  k-cycles is non-trivial new combinatorics.

**Conclusion:** ACT is gated by (a) the Docker build outage [[project-verification-blackout-20260613-allroutes]],
and (b) substantial new Mathlib-level combinatorics (≈ several hundred lines for the
fully-verified route). The mathematics, however, is **settled and exact** above.

---

## Recommended ACT skeleton (once Docker returns)

Two routes, mirroring how the parent handled its hard analytic input (it left
`derangements_rate` as an imported sorry):

**Route B — tractable first ACT (`axiomatized`), recommended.**
File `DerangementsConvergenceOQ01OQ02.lean`, namespace `KCycleConvergence`:
1. `def probMKCycle (n k m : ℕ) : ℝ` — fraction of `Equiv.Perm (Fin n)` with exactly
   `m` k-cycles (`filter` on `cycleType.count k = m`).
2. `def noKCycleFrac (j k : ℕ) : ℝ := numNoKCycle k j / j!` (the `a_{j,k}`).
3. **axiom / hypothesis** `noKCycleFrac_tendsto : k ≥ 1 → Tendsto (noKCycleFrac · k) atTop (𝓝 (rexp (−1/k)))`
   — the analytic limit (analogue of `numDerangements_tendsto_inv_e`), stated as an
   assumption so the entry is `axiomatized`/badge `axiom` per the Axiom Integrity Policy.
4. `lemma probMKCycle_eq` — the closed form (★) (pure counting; provable but heavy).
5. `theorem kcycle_tendsto (k m : ℕ) (hk : 1 ≤ k) : Tendsto (fun n => probMKCycle (n+m*k) k m) atTop (𝓝 (rexp (−1/k)·(1/k)^m / m!))`
   — assembled from (★) + the axiom, exactly as `kFixed_tendsto` is assembled.

**Route A — fully `verified` goal (no axioms).** Replace step 3's axiom by proving
(†) via a k-cycle inclusion–exclusion (generalize `Derangements.Exponential`) and
deriving the limit from the alternating-series tail bound. Largest effort; the
right long-term target but not a single-session ACT.

Either route reduces to the parent at k = 1, so cross-checking against
`KFixedConvergence` lemmas is a free correctness oracle.

---

## Dead Ends

- **Reading "Pois(1/k)^m" literally** (an m-th power of a probability) — wrong; the
  intended object is the Poisson(1/k) pmf at `m`, `e^{−1/k}(1/k)^m/m!`. See the
  statement-correction note above.
- **Hoping Mathlib already has the k-cycle count** — it does not; only the k = 1
  (`numDerangements`) specialization exists. Do not plan an ACT that `exact?`-wires
  a nonexistent general lemma.
