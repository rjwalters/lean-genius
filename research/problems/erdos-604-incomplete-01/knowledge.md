# Knowledge Base: erdos-604-incomplete-01

Insights accumulated during research on this problem.

---

## Problem Understanding

**Target sorry** (`Erdos604Problem.lean:179–182`):

```lean
theorem integerLattice_pinnedDistances (n : ℕ) (hn : n ≥ 2) :
    ∃ A : Finset (ℝ × ℝ), A.card = n ∧
      ∀ x ∈ A, (pinnedDistanceCount x A : ℝ) ≤ (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) := by
  sorry
```

This is the **upper-bound (construction) half** of the pinned distinct-distance problem:
exhibit an `n`-point set in which *every* point sees at most `n/√(log n)` distinct
distances. The integer lattice is the conjectured extremal example. Note this is the
construction that Erdős used to argue `n/√(log n)` is the *right* order — it is not the
open hard direction (the lower bound / Katz–Tardos side), but its rigorous proof still
requires deep analytic number theory (below).

The rest of the file is sorry-free: `katzTardos_bound` (lower bound, exponent ≈0.864),
`pinnedDistance_pos`, `pinnedDistance_le` (trivial `≤ n−1`), `pinnedDistances_subset_all`.

---

## Insights

### The reduction: lattice pinned distances ARE sums of two squares

Take the axis-aligned grid `G_m = {0,…,m−1} × {0,…,m−1} ⊂ ℝ²` (so `|G_m| = m²`). Fix any
lattice point `x = (a,b) ∈ G_m`. For `y = (c,d) ∈ G_m`,

```
euclideanDist x y = √((a−c)² + (b−d)²),   with (a−c), (b−d) ∈ ℤ, |a−c|,|b−d| ≤ m−1.
```

Since `√· ` is injective on `[0,∞)`, the number of **distinct distances** from `x` equals
the number of **distinct values** of the integer `(a−c)² + (b−d)²`. Hence

```
pinnedDistanceCount x G_m  ≤  #{ k ∈ ℕ : 0 < k ≤ 2(m−1)² and k is a sum of two squares }.
```

This bound is **uniform over `x`** (every grid point, corner or interior, only ever produces
squared-distances that are sums of two squares in `[0, 2(m−1)²]`), which is exactly what the
`∀ x ∈ A` quantifier in the sorry needs. So the geometric problem collapses to a **counting
problem about sums of two squares** — this is the crux and is elementary to formalize.

### Why the trivial upper bound is not enough

`pinnedDistance_le` already gives `pinnedDistanceCount x A ≤ |A| − 1 = n − 1`. But the target
is `n/√(log n)`, and `n/√(log n) < n − 1` for all large `n` (the ratio `→ 0` relative to `n`).
So the trivial bound is *asymptotically too weak* — the whole content is the `1/√(log n)`
savings, which is precisely the Landau–Ramanujan phenomenon.

### The missing analytic input: Landau–Ramanujan density

Let `B(N) = #{k ≤ N : k is a sum of two squares}`. Landau (1908) / Ramanujan:

```
B(N) ~ K · N / √(log N),   K = Landau–Ramanujan constant ≈ 0.7642.
```

Applying this with `N = 2(m−1)² = Θ(m²) = Θ(n)` (so `log N = Θ(log n)`) gives

```
pinnedDistanceCount x G_m ≤ B(2(m−1)²) = Θ(n/√(log n)),
```

which, with the correct constant handling, yields the sorry's bound. **This density theorem
is the entire remaining difficulty.**

### Small-n regime (where the sorry is trivially true)

For `n = 2, 3, 4`: `n/√(log n)` evaluates to ≈ `2.40, 2.86, 3.40`, while `pinnedDistanceCount
≤ n − 1 = 1, 2, 3`. Since `n − 1 ≤ n/√(log n)` here, *any* `n`-point set works and the bound
follows from `pinnedDistance_le` alone. The inequality `n − 1 ≤ n/√(log n)` fails once
`√(log n) > n/(n−1)`, i.e. roughly `n ≥ 5` (`log 5 ≈ 1.609 > (5/4)² = 1.5625`). So the trivial
argument covers only `n ≤ 4`; every larger `n` genuinely needs the density input.

---

## Mathlib gap (verified 2026-07-02)

- **Present**: `Mathlib.NumberTheory.SumTwoSquares` — the *characterization* of which integers
  are sums of two squares (Fermat: `n` is a sum of two squares iff every prime `≡ 3 (mod 4)`
  divides `n` to an even power). `Nat.Prime.sq_add_sq`, `ZMod` machinery, etc.
- **Absent**: any *asymptotic density / counting function* for sums of two squares. `grep` for
  `landau|ramanujan` over Mathlib finds only the big-O `Landau` notation and the Chudnovsky
  π-formula "Ramanujan" — **the Landau–Ramanujan density theorem and constant are not in
  Mathlib**.

Consequently the sorry **cannot** be discharged at `0` axioms with the current library. The
honest options are:

1. **Conditional formalization** (recommended, tractable): prove, sorry-free, the geometric
   reduction
   `pinnedDistanceCount x G_m ≤ #{sums of two squares ≤ 2(m−1)²}` uniformly in `x`, and state
   `integerLattice_pinnedDistances` as a theorem taking a **Landau–Ramanujan hypothesis**
   (`B(N) ≤ K·N/√(log N)`) as an explicit argument. This isolates the open/deep input as a
   clearly-labelled assumption and makes the geometric half fully verified. Entry would be
   `status: axiomatized` with the density bound disclosed in `assumptions`.
2. **Formalize Landau–Ramanujan** in Mathlib — a major analytic-number-theory undertaking
   (Dirichlet series / Selberg–Delange method); out of scope for a single research iteration.
3. **Leave the sorry** and only ship the reduction lemma as sorry-free infrastructure.

---

## Dead Ends

- **Discharging the sorry directly at 0 axioms**: impossible with current Mathlib — the bound
  is exactly Landau–Ramanujan, which is not formalized. Do not attempt to `sorry`-fill it or to
  bury the difficulty in a `native_decide`/false-`decide`; the statement is asymptotic, not
  decidable.
- **Using only `pinnedDistance_le` (`≤ n−1`)**: works only for `n ≤ 4`; asymptotically too weak.
- **Perfect-square subtlety**: `G_m` has `m²` points. For general `n` (not a perfect square),
  the usual fix is to take `n = m²` and absorb the gap into the `o(1)`; but the sorry demands an
  *exact* `n`-point set for *every* `n ≥ 2`. A clean formalization should take the first `n`
  points of a large enough grid — each still only produces sum-of-two-squares distances, so the
  uniform reduction bound survives; only the counting constant needs a little slack.
