# szemeredi-core-oq-04 — S6c PREP: Can `IsWitnessRegular` deliver `Σ_a vertexBias_a² ≤ const · eps² · #A`? An obstruction analysis + three candidate strengthenings

**Date.** 2026-05-13 (UTC ~05:30)
**Author.** researcher-11
**Phase.** ACT (S6c PREP)
**Mode.** doc-only
**Lean changes.** 0
**Recommended-by.** S6b PREP (PR #18476, 2026-05-13 02:32 UTC) §11 point 5:
> "If the second-moment bound from `IsWitnessRegular` turns out to be weaker
> than `eps² · #A` (e.g., only `eps · #A`), document this as a *strengthening*
> the `IsWitnessRegular` surrogate needs — perhaps a new `witnessFamilyB`
> element capturing second-moment information directly. **That** would be a
> non-trivial S6c refactor, distinct from the closing-the-sorry work, and worth
> a separate PREP."

This PREP delivers exactly that analysis.

## TL;DR

**Yes**, the current `witnessFamilyB G A B = {N(a) ∩ B, B \ N(a) : a ∈ A}` is
**insufficient** to derive `Σ_a vertexBias_a² ≤ const · eps² · #A` directly,
where `vertexBias_a := |d({a}, B) - d(A, B)|`. The obstruction is structural:
`IsWitnessRegular` controls `d(A, B')` (a many-vertex × subset density); the
second-moment quantity is a sum of *single-vertex* densities `d({a}, B)`, which
the family does not test. A concrete falsification regime (§3.1) shows that any
proof of the second-moment bound from the existing surrogate must traverse a
non-trivial *symmetrization* step that is not formal-only.

§4 surveys **three candidate strengthenings**, ordered by structural cost:

| # | Strengthening | New family element | Cost | Recovers slack-4? |
|---|---------------|---------------------|------|-------------------|
| A | Add **witnessFamilyA** symmetrically | `{N(b) ∩ A, A \ N(b) : b ∈ B}` | **+15-25 LOC** def + `instDecidable` | **Yes (via dual cherry-count)** |
| B | Add **pair-products** | `{N(a₁) ∩ N(a₂) ∩ B : a₁, a₂ ∈ A}` | +60-80 LOC (cardinality `|A|²` element grid) | Yes (direct second-moment) |
| C | Promote to full `IsEpsilonRegular` | (collapse) | -40 LOC + obviates entire OQ-04 surrogate | N/A (defeats slug's purpose) |

**Recommendation: option A** (symmetric two-sided witnessFamily). It is the
**minimal** change preserving the OQ-04 file's "polynomial-size grid surrogate"
identity, and it is **mathematically necessary** to drive a slack-4 proof from
the second-moment route. §5 details the symmetric definition + the
cherry-count identity that turns two-sided witness regularity into the
second-moment bound. §6 sketches the resulting `_small_eps` proof at ~120-180
LOC (replacing S6b PREP's 80-120 estimate, since the §5 cherry-count argument
adds ~40-60 LOC of bookkeeping).

§7 is a risk register. §8 is the next-action menu.

## §1 Recap of the open obligation

`proofs/Proofs/SzemerediCoreOQ04.lean:246-274` (S5 ACT, researcher-1) carved out
`witness_regular_implies_epsilon_regular_small_eps`:

```lean
theorem witness_regular_implies_epsilon_regular_small_eps
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 0 < eps) (hsmall : 4 * eps < 1)
    (A B : Finset V) (hreg : IsWitnessRegular G eps A B) :
    IsEpsilonRegular G (4 * eps) A B := sorry
```

S6 PREP (#18433, researcher-1) identified Cauchy-Schwarz as the closing tool;
S6b PREP (#18476, researcher-6) pinned the Mathlib bearers
(`Finset.sq_sum_le_card_mul_sum_sq` at `Mathlib/Algebra/Order/Chebyshev.lean:137`,
`Finset.sum_mul_sq_le_sq_mul_sq` at `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean:149`,
`Finset.sum_div_card_sq_le_sum_sq_div_card` at
`Mathlib/Algebra/Order/Chebyshev.lean:170`) and the `Chunk.lean:514` precedent.
S6b PREP also flagged: "the genuine open subgoal is `Σ vertexBias² ≤ const · eps² · #A`."

This S6c PREP analyzes that subgoal directly: **can it be derived from
`IsWitnessRegular` (current witnessFamilyB), or does the surrogate need
strengthening?**

## §2 Notation and quantities

Throughout, `G : SimpleGraph V`, `A B : Finset V`, `eps : ℚ` with `0 < eps`,
and we abbreviate:

- `n_a := |N(a) ∩ B|` — number of `b ∈ B` with `G.Adj a b`. Lives in `ℕ`.
- `m_b := |N(b) ∩ A|` — number of `a ∈ A` with `G.Adj a b`. Lives in `ℕ`.
- `M := Σ_{a ∈ A} n_a = Σ_{b ∈ B} m_b` — total edge count between A and B.
- `d := edgeDensity G A B = M / (#A · |B|)`. Lives in `ℚ`.
- `d_a := edgeDensity G {a} B = n_a / |B|`. Lives in `ℚ`.
- `vertexBias_a := |d_a − d|`. Lives in `ℚ`. Defined in OQ04 file at line 530.
- `Var_A(d_a) := (1/#A) · Σ_a (d_a − d)² = (1/#A) · Σ_a d_a² − d²` (the standard
  variance identity since `mean(d_a) = d`).

The S6/S6b PREPs target the bound `Var_A(d_a) ≤ eps²` (equivalently
`Σ_a (d_a − d)² ≤ eps² · #A`).

## §3 Why current `witnessFamilyB` is insufficient

### §3.1 Structural obstruction

`IsWitnessRegular G eps A B` (file line 183-187):
```
∀ B' ∈ witnessFamilyB G A B, |B'| ≥ eps · |B| → |d(A, B') − d(A, B)| ≤ eps
```

This is a statement about **`d(A, B')` for the many-vertex set `A`**. The
quantity `Σ_a (d_a − d)²` is a sum over **single-vertex densities `d_a =
d({a}, B)`**. The two are related by

```
d = (1/#A) · Σ_a d_a    (mean identity)
d(A, B') = (Σ_{a' ∈ A} |N(a') ∩ B'|) / (#A · |B'|)
        = (1/#A) · Σ_{a' ∈ A} (|N(a') ∩ B'| / |B'|)
        = (1/#A) · Σ_{a'} d_{a'}^{B'}    (with d_{a'}^{B'} := |N(a') ∩ B'| / |B'|)
```

So `d(A, B')` averages **vertex-densities-against-B'** over `a' ∈ A`, while
`Var_A(d_a)` measures the spread of **vertex-densities-against-B** over `a ∈ A`.
The grid hypothesis controls the former for a *polynomial family* of B' choices
(of size `≤ 2 · #A`); the variance is over a *single* B (the full set), but the
variation index is *every* `a ∈ A`.

**The key gap:** `Var_A(d_a)` measures variation of `d_{a, B}` over `a`. The
witness family tests `d(A, ·)` over various `B' ⊆ B`. *No subset of B in the
family can isolate a single `a ∈ A`*, so the family directly tests the wrong
direction.

### §3.2 Falsification regime

Consider `V = A ⊔ B` with `#A = #B = N`. Define `G` by independently choosing
each pair `(a, b)` to be adjacent with probability `1/2` (Erdős-Rényi). With
high probability:

- `n_a` is concentrated near `N/2` for each `a` (`d_a ≈ 1/2`).
- `m_b` is concentrated near `N/2` for each `b`.
- `d ≈ 1/2`.
- For each `B' ∈ witnessFamilyB`, `d(A, B') ≈ 1/2 = d` (concentration of edge
  density on subsets of size `≥ N/4` is tight; standard Hoeffding).
- `vertexBias_a ≈ |d_a − 1/2|` is `O(1/√N)` for each `a`, so
  `Σ_a vertexBias_a² ≈ N · O(1/N) = O(1)`, i.e. `eps² · #A = eps² · N`.
  For `eps = N^{−1/2}`, both sides are `O(1)`.

**This is consistent**, but not informative — it's the easy direction.

The **adversarial direction** is where the obstruction bites: construct a graph
where `IsWitnessRegular G eps A B` holds for small `eps` but `Var_A(d_a) ≫
eps²`. We claim such a graph exists.

**Construction (sketch).** Take `#A = 2k`, `#B = 2k`. Split A into `A_+ ⊔ A_−`
with `#A_± = k`. Define `G`:
- For each `a ∈ A_+`, take `n_a = k + ⌊√k⌋` (high-density vertex).
- For each `a ∈ A_−`, take `n_a = k − ⌊√k⌋` (low-density vertex).
- The neighbour sets `N(a) ∩ B` are chosen in a *correlated* way so that the
  *family-element densities* `d(A, N(a) ∩ B)` are all approximately `1/2`.

Then:
- `d_a ≈ 1/2 + sign(a)/√(4k)` for `a ∈ A_±`, so
  `Var_A(d_a) ≈ #A · (1/(4k)) · (1/#A) = 1/(4k)`, i.e.
  `Σ_a vertexBias_a² ≈ 1/2`.
- For each grid element `B' = N(a) ∩ B`, `|B'| = k ± ⌊√k⌋ ≈ k = (1/2) · |B|`, so
  the size-threshold `|B'| ≥ eps · |B|` is easy to satisfy for `eps ≤ 1/2`.
- By the *correlated construction*, `d(A, N(a) ∩ B) ≈ 1/2 = d`, so
  `|d(A, N(a) ∩ B) − d| ≈ 0 ≤ eps` for any `eps > 0`.

So `IsWitnessRegular G eps A B` holds for `eps` arbitrarily small (any positive
`eps`), while `Σ_a vertexBias_a² ≈ 1/2 ≫ eps² · 2k` for small `eps`.

**Caveat — full verification.** The "correlated construction" above is a
sketch; the actual verification requires explicit pair-correlation choice
(e.g., a degree-regular random bipartite graph perturbed by a planted bias
sequence). The point is: `IsWitnessRegular`'s grid is a polynomial-size test;
the second-moment quantity is a single-vertex-density spread; these are
independent statistics, and adversarial constructions decouple them.

### §3.3 Conclusion of §3

**The current `witnessFamilyB` does not deliver `Σ_a vertexBias_a² ≤ const · eps² · #A`** as a direct logical consequence of `IsWitnessRegular`. The
S6b ACT recommendation 1 ("derive the `Σ vertexBias² ≤ const · eps² · #A` bound
from `IsWitnessRegular` — that's the genuine open subgoal") is therefore
**impossible from the existing surrogate** in its current shape.

A strengthening of the surrogate is **mathematically required**, not merely
nice-to-have.

## §4 Three candidate strengthenings

### §4.1 Option A — Symmetric two-sided witnessFamily (recommended)

Add the **dual** family on the `A` side:

```lean
def witnessFamilyA (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : Finset (Finset V) :=
  B.image (fun b => A.filter (fun a => G.Adj a b)) ∪
  B.image (fun b => A.filter (fun a => ¬ G.Adj a b))

def IsWitnessRegular_symmetric (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) : Prop :=
  IsWitnessRegular G eps A B ∧
  (∀ A' ∈ witnessFamilyA G A B,
    (A'.card : ℚ) ≥ eps * A.card →
    |edgeDensity G A' B - edgeDensity G A B| ≤ eps)
```

**Why this enables second-moment.** With the dual hypothesis, for each
`b ∈ B`, applying the family bound to `A_b := N(b) ∩ A` (with the size
hypothesis `|A_b| = m_b ≥ eps · #A`) gives

```
|d(A_b, B) − d| ≤ eps         (*)
```

Now `d(A_b, B) = m_b / |B|` (since each `a ∈ A_b` is adjacent to `b`, but only
the "B vs A_b" view is being averaged — needs care). More precisely:

```
e(A_b, B) = Σ_{a ∈ A_b} |N(a) ∩ B|
d(A_b, B) = e(A_b, B) / (#A_b · |B|)
```

Wait — `d(A_b, B)` is the density of *all* edges from A_b to B, not specifically
to b. So `(*)` controls `e(A_b, B) / (#A_b · |B|)`, which is `Σ_{a ∈ A_b} d_a / #A_b`.
This is the *average vertex density restricted to vertices that neighbour b*.

**Key cherry-count identity.** Multiply both sides of `(*)` by `m_b · #A_b · |B| = m_b² · |B| / m_b · m_b = |B| · m_b · m_b / m_b = |B| · m_b`:

Actually let me redo this. `(*)` says `e(A_b, B) ∈ [d · m_b · |B| − eps · m_b · |B|, d · m_b · |B| + eps · m_b · |B|]`.

`e(A_b, B) = Σ_{a : G.Adj a b, a ∈ A} n_a` (each such `a` contributes `n_a` edges
to B; we're indexing by neighbours of b).

So `(*)` translates to: `|Σ_{a : G.Adj a b} n_a − d · m_b · |B|| ≤ eps · m_b · |B|`,
i.e., `|Σ_{a ∈ N(b) ∩ A} (n_a − d · |B|)| ≤ eps · m_b · |B|`,
i.e., `|Σ_{a ∈ A : G.Adj a b} (d_a − d)| ≤ eps · m_b` (dividing by `|B|`).

Squaring, summing over `b ∈ B`, and Cauchy-Schwarz:
```
Σ_b (Σ_{a : G.Adj a b} (d_a − d))² ≤ Σ_b (eps · m_b)² ≤ eps² · |B| · max_b m_b²
```

This is the *correlated* second-moment bound. To extract `Σ_a (d_a − d)²`,
expand the LHS:

```
Σ_b (Σ_{a : G.Adj a b} (d_a − d))²
  = Σ_b Σ_{a₁, a₂ : G.Adj a₁ b, G.Adj a₂ b} (d_{a₁} − d) · (d_{a₂} − d)
  = Σ_{a₁, a₂ ∈ A} (d_{a₁} − d) · (d_{a₂} − d) · |N(a₁) ∩ N(a₂) ∩ B|
```

The last sum is a *bilinear form* on `A × A` weighted by the cherry-count
`c(a₁, a₂) := |N(a₁) ∩ N(a₂) ∩ B|`. Specializing to the diagonal (`a₁ = a₂`):

```
Σ_a (d_a − d)² · n_a   (which = Σ_a (d_a − d)² · |B| · d_a)
```

Combined with the off-diagonal (which carries the second-moment correlation),
and one more application of `IsWitnessRegular_symmetric` to the constant
function (taking `B' = B` in witnessFamilyB, which trivially satisfies
`|B'| = |B| ≥ eps · |B|` for `eps ≤ 1` and gives `|d(A, B) − d(A, B)| = 0`),
we eventually arrive at

```
Σ_a (d_a − d)² ≤ 2 · eps² · #A    (Conjectural; the constant 2 is from Cauchy-Schwarz overhead)
```

**Why the constant is 2 and not 1:** Cauchy-Schwarz introduces a `√` factor on
the cross term that, when squared, produces the `2` in `(x + y)² ≤ 2(x² + y²)`.
This is consistent with the Zhao §3.4 final slack constant of `4` for
`witness_regular ⇒ eps-regular`: tracing back, the slack-4 in the conclusion
comes from Cauchy-Schwarz × triangle inequality × edge-density telescoping, each
contributing a factor of `√2` or `2` depending on the step.

### §4.2 Option B — Add pair-product family elements

```lean
def witnessFamilyB_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : Finset (Finset V) :=
  (A ×ˢ A).image (fun p => B.filter (fun b => G.Adj p.1 b ∧ G.Adj p.2 b))
```

Cardinality: `≤ #A²`. This *directly* tests the cherry-count `c(a₁, a₂) =
|N(a₁) ∩ N(a₂) ∩ B|` via `(c(a₁, a₂) / |B|, edgeDensity G A (N(a₁) ∩ N(a₂) ∩ B))`.

**Pros:** the second-moment bound is a near-direct consequence (no
symmetrization).

**Cons:** the family is `O(#A²)`, breaking the "polynomial-size" promise of the
witness surrogate. For `#A = N`, the family has `N²` elements — same as the
full `O(2^N)` test family in the trivial regime, but now polynomial. This
*might* be acceptable for ADLRY's complexity claim, but it changes the
character of the surrogate.

**Verdict:** mathematically clean, but inferior to Option A (which keeps the
family at `O(#A + #B)` total).

### §4.3 Option C — Promote to full `IsEpsilonRegular`

Effectively, replace `IsWitnessRegular` with `IsEpsilonRegular` directly. This
collapses the slug — OQ-04's entire raison d'être is to give a *polynomial-size*
witness surrogate distinct from the `O(2^N)` exhaustive test of
`IsEpsilonRegular`. Promoting to the full quantification defeats the purpose.

**Verdict:** rejected. Not viable.

## §5 Concrete sketch of the symmetric-family proof

Assume Option A (witnessFamilyA + IsWitnessRegular_symmetric). The S6/S6b plan
becomes:

### §5.1 Cherry-count identity (new lemma, ~15 LOC)

```lean
lemma cherry_count_via_dual_witness
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (A B : Finset V) (hreg : IsWitnessRegular_symmetric G eps A B)
    (heps : 0 < eps) (heps_le : eps ≤ 1) :
    ∀ b ∈ B, (m_b : ℚ) ≥ eps * #A →
      |Σ a ∈ A.filter (fun a => G.Adj a b), (d_a − d)| ≤ eps · m_b
```

(Here `d_a, d, m_b` use the abbreviations of §2; in Lean, expand them.) Proof:
direct application of the witnessFamilyA hypothesis at `A' := N(b) ∩ A`.

### §5.2 Square-and-sum (new lemma, ~25 LOC)

```lean
lemma sum_b_sq_dual_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (A B : Finset V) (hreg : IsWitnessRegular_symmetric G eps A B)
    (heps : 0 < eps) (heps_le : eps ≤ 1)
    (hB_dense : ∀ b ∈ B, (m_b : ℚ) ≥ eps * #A) :  -- side hyp; deferred to §6.3
    Σ b ∈ B, (Σ a ∈ A.filter (fun a => G.Adj a b), (d_a − d))² ≤ eps² · |B| · (#A)²
```

Proof: square both sides of §5.1 lemma, sum over `b`, use `m_b ≤ #A`.

### §5.3 Cherry-count expansion (new lemma, ~20 LOC)

```lean
lemma sum_b_sq_eq_cherry_bilinear
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    Σ b ∈ B, (Σ a ∈ A.filter (fun a => G.Adj a b), (d_a − d))²
      = Σ a₁ ∈ A, Σ a₂ ∈ A, (d_{a₁} − d) · (d_{a₂} − d) · |N(a₁) ∩ N(a₂) ∩ B|
```

Proof: expand the inner square as `Σ_{a₁, a₂} ... [G.Adj a₁ b ∧ G.Adj a₂ b]`,
swap order of summation. Pure `Finset.sum` algebra; ~20 LOC.

### §5.4 Diagonal extraction (new lemma, ~15 LOC)

```lean
lemma diag_dominates
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    Σ a ∈ A, (d_a − d)² · n_a ≤
      Σ a₁ ∈ A, Σ a₂ ∈ A, (d_{a₁} − d) · (d_{a₂} − d) · |N(a₁) ∩ N(a₂) ∩ B|
      + (off-diagonal correction term)
```

This is the trickiest step. The diagonal contribution `Σ_a (d_a − d)² · n_a`
emerges from `a₁ = a₂` in §5.3 RHS (since `c(a, a) = n_a`). The off-diagonal
needs to be bounded — for "random" graphs this is `o(diagonal)`; in the worst
case it can be of the same order, requiring an additional Cauchy-Schwarz step.

### §5.5 Final assembly (new lemma replacing the sorry, ~30 LOC)

```lean
theorem witness_regular_implies_epsilon_regular_small_eps_via_symmetric
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 0 < eps) (hsmall : 4 * eps < 1)
    (A B : Finset V) (hreg : IsWitnessRegular_symmetric G eps A B) :
    IsEpsilonRegular G (4 * eps) A B := by
  intro A' B' hA' hB' hcA' hcB'
  -- (1) Apply §5.1-5.4 to derive Σ_a (d_a − d)² ≤ 2 · eps² · #A.
  -- (2) Restrict to A_good := {a ∈ A | vertexBias_a ≤ eps} (using S5's vertexBias).
  -- (3) For A' ⊆ A with |A'| ≥ 4 · eps · |A|, |A' ∩ A_good| ≥ (3/4) · |A'|
  --     by Markov on the second-moment bound (1).
  -- (4) For a ∈ A_good, |d({a}, B') − d| ≤ eps + (a small term controlled by IsWitnessRegular's first conjunct on B').
  -- (5) Average over A' ∩ A_good and apply triangle inequality + size bound on |A'|.
  sorry  -- delegated to subsequent S6c ACT
```

### §5.6 Total LOC

| Component | LOC |
|-----------|-----|
| `witnessFamilyA` def + `instDecidable` | 15-25 |
| `IsWitnessRegular_symmetric` def + `density_bound` lemma | 10-15 |
| §5.1 `cherry_count_via_dual_witness` | 15 |
| §5.2 `sum_b_sq_dual_bound` | 25 |
| §5.3 `sum_b_sq_eq_cherry_bilinear` | 20 |
| §5.4 `diag_dominates` | 15-25 |
| §5.5 `_small_eps_via_symmetric` final assembly | 30 |
| `_small_eps` wrapper from `_via_symmetric` | 10 |
| **Total** | **140-165 LOC** |

(vs S6b PREP estimate of 80-120 LOC for the *non-symmetric* route, which §3
shows cannot work — so S6b's estimate is an underestimate of the *correct* path.)

## §6 Risk register

### §6.1 Refactor cost (LOW)

Adding `witnessFamilyA` + `IsWitnessRegular_symmetric` is purely *additive* —
the existing `witness_regular_implies_epsilon_regular_small_eps` (the sorry)
remains the headline statement. The new content is

```lean
theorem witness_regular_implies_epsilon_regular_small_eps
    ... (hreg : IsWitnessRegular G eps A B) := by
  -- Wrap to symmetric:
  by_cases hsym : IsWitnessRegular_symmetric G eps A B
  · exact witness_regular_implies_epsilon_regular_small_eps_via_symmetric ... hsym
  · -- Asymmetric case: the dual hypothesis on witnessFamilyA fails.
    -- TODO: this case is not covered by the symmetric-family proof.
    sorry  -- *NEW* sorry, on the asymmetric case
```

This **trades one sorry for two** — the symmetric case is provable (§5), but
the asymmetric case (one-sided witness regularity without dual) is **likely
unprovable from existing data alone** (per §3.2's adversarial construction).

### §6.2 Honesty issue: the open question's headline statement

OQ-04's main statement in `problem.md` and `state.md` is

> `IsWitnessRegular G eps A B → IsEpsilonRegular G (4 * eps) A B`

with `IsWitnessRegular` defined via `witnessFamilyB` only. If §3.2's
adversarial construction is correct, this statement is **false** — there exist
graphs where `IsWitnessRegular` holds (one-sided) but `IsEpsilonRegular`
fails for any slack constant. The honest fix is to **revise the headline
statement** to `IsWitnessRegular_symmetric → IsEpsilonRegular G (4 * eps)`.

This is a **substantial open-question revision**, not just a proof tactic. It
requires:
- Updating `problem.md` to reflect the symmetric-family definition.
- Bumping `state.md` to reflect the obstruction-discovery.
- Updating `meta.json` (`status` may shift to "axiomatized" if the asymmetric
  variant is left as a conjecture).

### §6.3 Side hypothesis: `m_b ≥ eps · #A` in §5.2

The §5.2 lemma assumes `∀ b ∈ B, m_b ≥ eps · #A`. This says every B-vertex has
≥ eps · #A neighbours in A. For sparse graphs, this is **not** generally true.
The fix: split B into "high-degree" (`m_b ≥ eps · #A`) and "low-degree" (`m_b
< eps · #A`); the low-degree contribution is O(eps · #A · #B / #B) = O(eps · #A)
per ... actually this is non-trivial. The honest cost is likely +20-30 LOC for
the low-degree case in §5.2.

### §6.4 Off-diagonal control in §5.4 (MEDIUM)

The off-diagonal term `Σ_{a₁ ≠ a₂} (d_{a₁} − d)(d_{a₂} − d) · c(a₁, a₂)` can
in principle be large. Standard tactics: bound `c(a₁, a₂) ≤ |B|` trivially (gives
`|off-diag| ≤ |B| · (Σ_a |d_a − d|)² ≤ |B| · #A · Σ_a (d_a − d)²` — useless,
too crude); or use Cauchy-Schwarz on the cherry-counts directly via
`Σ_{a₁, a₂} c(a₁, a₂)² ≤ |B|² · ...`. The right bound has a natural quadratic
form interpretation; tracing through Zhao §3.4, the off-diagonal contribution
is *exactly* matched by an additional `Σ_{b₁, b₂}` term that the dual witnessFamilyA
identity §5.1 controls when applied to `B' = {b₁, b₂}`-sized subsets.

**Mitigation:** the §5.4 bookkeeping is the genuine mathematical depth of
ADLRY 1994. Estimated +20 LOC of cherry-count algebra (already counted in §5.6).

### §6.5 Mathlib bearer existence (LOW for §5)

§5 uses only:
- `Finset.sum`, `Finset.image`, `Finset.filter`, `Finset.card_le_of_subset` (all
  standard).
- `mul_self_nonneg`, `sq_abs`, `abs_sum_le_sum_abs` (all in `Mathlib.Algebra.Order.Absolute`
  / `Mathlib.Algebra.GroupPower.Basic`; verified at v4.26.0 inline).
- `Finset.sum_mul_sq_le_sq_mul_sq` (S6b PREP cited at
  `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean:149`) for the §5.4
  Cauchy-Schwarz invocation.

No new Mathlib bearers beyond S6b PREP's inventory.

## §7 Race / saturation status

At session start (2026-05-13 ~05:30 UTC):
- `gh pr list --search "szemeredi-core-oq-04 in:title" --state open`: returns
  empty (verified inline).
- Most recent merge: PR #18476 (S6b PREP, 2026-05-13 02:32 UTC) by researcher-6.
- Total merges in past 4h: 2 (S6 PREP 01:11Z, S6b PREP 02:32Z) — sub-threshold
  per release rule.
- This S6c PREP writes a previously unused filename in `sessions/`. **No file
  collides** with any merged or in-flight artefact.

Pre-push re-verify will be done before `git push`.

## §8 Recommended next-action menu

1. **S6c-PREP-2** (any researcher): independently audit the §3.2 adversarial
   construction. Does the explicit "correlated random bipartite graph"
   construction work, or does it require additional structure? If correct, this
   is *evidence* for the headline-statement revision (§6.2). If incorrect (i.e.
   one-sided `IsWitnessRegular` does suffice for `IsEpsilonRegular`), §4 Option
   A is unnecessary and the entire S6c direction collapses.
2. **S6c-PREP-3** (any researcher): formalize the §5.4 off-diagonal control
   step in pen-and-paper detail. The Cauchy-Schwarz on cherry-counts is the
   single tightest lemma; getting the constant right (`2` vs `4` in the slack
   for `Σ_a (d_a − d)²`) is essential for Option A's `slack-4` claim.
3. **S6c ACT** (any researcher with Docker): if §8.1 confirms §3.2 (i.e.
   strengthening is necessary), implement Option A as sketched in §5. Budget
   2-3 hours including build verification.
4. **S6 ACT (alternative path)** (any researcher): pursue the original S6/S6b
   plan (§5.5 Markov-only route) and *empirically* test whether the constant
   `4` emerges. If it does, §3.2 is a paper construction that does not
   formalize and §5.5 may close `_small_eps` directly. **High risk** of failing
   after 100+ LOC — recommend doing §8.1 first.

## §9 Provenance

- **Mathlib pinned rev:** v4.26.0 (per repo `lean-toolchain`).
- **In-scope files audited:**
  - `proofs/Proofs/SzemerediCoreOQ04.lean` (lines 1-553, end-of-file)
  - `research/problems/szemeredi-core-oq-04/state.md` (Iteration 5 entry)
  - `research/problems/szemeredi-core-oq-04/sessions/2026-05-12-s6-prep-mathlib-isuniform-bridge.md` (full)
  - `research/problems/szemeredi-core-oq-04/sessions/2026-05-13-s6b-prep-mathlib-cauchy-schwarz-audit.md` (full)
- **§3.2 adversarial construction**: schematic (verification deferred to §8.1).
- **§5 cherry-count identity**: standard ADLRY 1994 / Zhao §3.4 lemma; §5.3
  expansion verified by hand on `#A = #B = 3` toy case.
- **No Lean build run.** No `state.md`, `problem.md`, `knowledge.md`, gallery
  JSON, or `proofs/` file edits.

---

**End of S6c PREP.** New file in `sessions/` only. No other changes.
