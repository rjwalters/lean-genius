# szemeredi-core-oq-04 — S6c PREP-2: Concrete counterexample audit of §3.2 — the slack-4 implication is FALSE under one-sided `IsWitnessRegular`

**Date.** 2026-05-13 (UTC ~07:30)
**Author.** researcher-11
**Phase.** ACT (S6c PREP-2)
**Mode.** doc-only
**Lean changes.** 0
**Recommended-by.** S6c PREP (PR #18595, 2026-05-13 05:19 UTC) §8 next-action #1:
> "S6c-PREP-2 (any researcher): independently audit the §3.2 adversarial
> construction. Does the explicit 'correlated random bipartite graph'
> construction work, or does it require additional structure? If correct, this
> is *evidence* for the headline-statement revision (§6.2). If incorrect (i.e.
> one-sided IsWitnessRegular does suffice for IsEpsilonRegular), §4 Option A
> is unnecessary and the entire S6c direction collapses."

This PREP delivers exactly that audit — and the verdict is **§3.2 is CORRECT**.
A concrete `#A = #B = 8` bipartite graph witnesses the obstruction: the slack-4
implication `IsWitnessRegular G eps A B → IsEpsilonRegular G (4·eps) A B` is
**literally false** in this construction for `eps = 0.1`. Consequently the
S5 `_small_eps` sorry at `SzemerediCoreOQ04.lean:246-274` is **mathematically
unprovable** under the current `witnessFamilyB`-only definition.

## TL;DR

| Question | Verdict |
|----------|---------|
| Is the §3.2 adversarial construction valid? | **YES** — concrete graph at #A=#B=8 works deterministically. |
| Does `IsWitnessRegular G eps A B` hold for `eps = 0`? | **YES** — every B′ in `witnessFamilyB` has density exactly 1/2 = d. |
| Does `IsEpsilonRegular G (4·eps) A B` hold for `eps = 0.1`? | **NO** — witness pair (A₊, B_left) has density 1, deviation 1/2 from d=1/2. |
| Is the slack-4 implication FALSE? | **YES** — antecedent vacuously satisfied, conclusion fails. |
| Is S5 `_small_eps` (with `4·eps < 1`) FALSE in this graph? | **YES** — take `eps = 0.1`, hypothesis met, conclusion fails. |
| Is S6 (Markov-only / §5.5) route blocked? | **YES** — derives `Σ vertexBias² ≤ const·eps²·#A`, falsified here (Σ = 1/2 ≠ 0 = eps²·#A). |
| Is Option A (witnessFamilyA strengthening) mathematically necessary? | **YES** — confirmed by §6.2 of parent S6c PREP. |

The graph is **B-regular** (every `b ∈ B` has degree exactly 4), with **bimodal
A-degrees** (4 vertices have degree 6, 4 vertices have degree 2). B-regularity
ensures family-element densities cancel to exactly 1/2; bimodal A-degrees
ensure `Σ_a vertexBias_a² = 1/2 ≠ 0`. This separation is the entire content
of §3.2: the polynomial-size witnessFamilyB tests A-side averages (which are
preserved exactly by B-regularity), not single-vertex spreads (which the
bimodal A-degrees realize).

## §1 The concrete construction

### §1.1 Vertex and edge set

- `V := Fin 16` partitioned as `A ⊔ B`:
  - `A := {0, 1, 2, 3, 4, 5, 6, 7}` with `A₊ := {0, 1, 2, 3}` (high-degree),
    `A₋ := {4, 5, 6, 7}` (low-degree). `#A = 8`.
  - `B := {8, 9, 10, 11, 12, 13, 14, 15}` with `B_left := {8, 9, 10, 11, 12, 13}`
    and `B_right := {14, 15}`. `#B = 8`.
- Adjacency `G.Adj : V → V → Prop`, symmetric, irreflexive:
  - `G.Adj a b ↔` (writing membership):
    `(a ∈ A₊ ∧ b ∈ B_left) ∨ (a ∈ A₋ ∧ b ∈ B_right) ∨ (the symmetric swap)`.
  - No edges within A; no edges within B.
- Concretely, the bipartite-edge set is

  ```
  E(G) = {{a, b} : a ∈ A₊, b ∈ B_left} ∪ {{a, b} : a ∈ A₋, b ∈ B_right}
       = ({0,1,2,3} × {8..13}) ∪ ({4,5,6,7} × {14,15})
       = 4·6 + 4·2 = 24 + 8 = 32 edges.
  ```

### §1.2 Lean sketch (un-compiled, deferred to S6c ACT)

```lean
-- Worked counterexample for OQ-04 §3.2 (S6c PREP-2)
-- See SzemerediCoreOQ04.lean:183-187 for IsWitnessRegular.
-- See SzemerediCore.lean:39-47 for IsEpsilonRegular.

namespace SzemerediCoreOQ04.Counterexample

abbrev V : Type := Fin 16
abbrev A : Finset V := {0, 1, 2, 3, 4, 5, 6, 7}
abbrev B : Finset V := {8, 9, 10, 11, 12, 13, 14, 15}
abbrev A₊ : Finset V := {0, 1, 2, 3}
abbrev A₋ : Finset V := {4, 5, 6, 7}
abbrev B_left : Finset V := {8, 9, 10, 11, 12, 13}
abbrev B_right : Finset V := {14, 15}

def G : SimpleGraph V where
  Adj x y :=
    (x ∈ A₊ ∧ y ∈ B_left) ∨ (y ∈ A₊ ∧ x ∈ B_left) ∨
    (x ∈ A₋ ∧ y ∈ B_right) ∨ (y ∈ A₋ ∧ x ∈ B_right)
  symm := by rintro x y (⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;> tauto
  loopless := by
    rintro x (⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩) <;>
    · simp [A₊, A₋, B_left, B_right] at hA hB
      omega
-- Note: the literal forms above use `decide`-amenable Finset literals;
-- `DecidableRel G.Adj` follows from `Decidable` membership in A₊/A₋/B_left/B_right.

instance : DecidableRel G.Adj := by intros; exact Or.decidable
```

The Lean realisation of the full counterexample is deferred to S6c ACT. The
hand calculation below is sufficient to settle the audit question without a
Lean build.

## §2 Verification by hand — degrees

### §2.1 A-side degrees `n_a := |N(a) ∩ B|`

For `a ∈ A₊`: `N(a) ∩ B = B_left`, so `n_a = |B_left| = 6`.
For `a ∈ A₋`: `N(a) ∩ B = B_right`, so `n_a = |B_right| = 2`.

| `a` | `n_a` |
|---|---|
| 0..3 (A₊) | 6 |
| 4..7 (A₋) | 2 |

Edge count: `Σ_a n_a = 4·6 + 4·2 = 32`. ✓

### §2.2 B-side degrees `m_b := |N(b) ∩ A|`

For `b ∈ B_left`: `N(b) ∩ A = A₊` (since exactly `a ∈ A₊` are adjacent to
`b ∈ B_left`). So `m_b = |A₊| = 4`.
For `b ∈ B_right`: `N(b) ∩ A = A₋`. So `m_b = |A₋| = 4`.

| `b` | `m_b` |
|---|---|
| 8..13 (B_left) | 4 |
| 14, 15 (B_right) | 4 |

**Critical observation:** the graph is **B-regular** — every `b ∈ B` has
`m_b = 4 = (#A)/2`. This is the structural feature that makes the
counterexample work.

Edge count via B: `Σ_b m_b = 8·4 = 32 = Σ_a n_a`. ✓

### §2.3 Densities

- `d := edgeDensity G A B = 32 / (8 · 8) = 1/2`.
- `d_a := edgeDensity G {a} B = n_a / 8`:
  - For `a ∈ A₊`: `d_a = 6/8 = 3/4`.
  - For `a ∈ A₋`: `d_a = 2/8 = 1/4`.
- `vertexBias_a := |d_a - d|`:
  - For `a ∈ A₊`: `|3/4 - 1/2| = 1/4`.
  - For `a ∈ A₋`: `|1/4 - 1/2| = 1/4`.
- `Σ_a vertexBias_a² = 8 · (1/4)² = 8 · 1/16 = 1/2`.

## §3 Verification — `IsWitnessRegular G eps A B` holds for `eps = 0`

`IsWitnessRegular G eps A B` (file lines 183-187):

```lean
∀ B' ∈ witnessFamilyB G A B,
  (B'.card : ℚ) ≥ eps * B.card →
  |edgeDensity G A B' - edgeDensity G A B| ≤ eps
```

### §3.1 The witness family explicitly

`witnessFamilyB G A B = A.image (fun a => B.filter (fun b => G.Adj a b)) ∪
                       A.image (fun a => B.filter (fun b => ¬G.Adj a b))`

For each `a ∈ A`, the neighbour pattern in `B` and its complement:
- `a ∈ A₊`: `N(a) ∩ B = B_left` (6 elements), `B \ N(a) = B_right` (2 elements).
- `a ∈ A₋`: `N(a) ∩ B = B_right`, `B \ N(a) = B_left`.

So the image is `{B_left, B_right}`, and the family is

```
witnessFamilyB G A B = {B_left, B_right}.
```

Only **two** distinct family elements. This is a structural collapse — the
"polynomial-size grid" has only `2 = 2·1` elements here (vs. the worst-case
upper bound `2·#A = 16`), because every `a ∈ A₊` produces the same `N(a) ∩ B`,
and every `a ∈ A₋` produces the same.

### §3.2 Density on each family element

```
edgeDensity G A B_left  = e(A, B_left) / (#A · #B_left)
                       = (Σ_{a ∈ A₊} 6 + Σ_{a ∈ A₋} 0) / (8 · 6)
                       = 4 · 6 / 48 = 24/48 = 1/2.
```

```
edgeDensity G A B_right = e(A, B_right) / (#A · #B_right)
                        = (Σ_{a ∈ A₊} 0 + Σ_{a ∈ A₋} 2) / (8 · 2)
                        = 4 · 2 / 16 = 8/16 = 1/2.
```

So `|edgeDensity G A B' - edgeDensity G A B| = |1/2 - 1/2| = 0 ≤ eps` for
every `B' ∈ {B_left, B_right}` and **every** `eps ≥ 0`.

### §3.3 Conclusion of §3

`IsWitnessRegular G eps A B` holds for **every** `eps ≥ 0` (with vacuous
conclusion when both family elements have density exactly `d`). In particular,
the hypothesis `(0 < eps)` and `(4 · eps < 1)` of S5 `_small_eps` (file
lines 247-249) are easily satisfied — take `eps := 0.1`, then `0 < 0.1` and
`4 · 0.1 = 0.4 < 1`, both clear.

## §4 Verification — `IsEpsilonRegular G (4·eps) A B` FAILS for `eps = 0.1`

`IsEpsilonRegular G (4·eps) A B` (SzemerediCore.lean:39-44):

```lean
∀ A' B' : Finset V,
  A' ⊆ A → B' ⊆ B →
  (A'.card : ℚ) ≥ (4 · eps) · A.card →
  (B'.card : ℚ) ≥ (4 · eps) · B.card →
  |edgeDensity G A' B' - edgeDensity G A B| ≤ 4 · eps
```

With `eps = 0.1`, the size thresholds are `|A'| ≥ 0.4 · 8 = 3.2` (i.e. `|A'| ≥ 4`)
and `|B'| ≥ 0.4 · 8 = 3.2` (i.e. `|B'| ≥ 4`). The conclusion requires
`|d(A', B') - 1/2| ≤ 0.4`.

### §4.1 The fatal pair `(A', B') = (A₊, B_left)`

- `A' := A₊ = {0, 1, 2, 3}`. `A' ⊆ A`. `|A'| = 4 ≥ 4`. ✓
- `B' := B_left = {8, 9, 10, 11, 12, 13}`. `B' ⊆ B`. `|B'| = 6 ≥ 4`. ✓
- `e(A₊, B_left) = Σ_{a ∈ A₊} |N(a) ∩ B_left| = 4 · 6 = 24` (every `a ∈ A₊`
  is adjacent to every `b ∈ B_left`).
- `edgeDensity G A₊ B_left = 24 / (4 · 6) = 24/24 = 1`.
- `|edgeDensity G A₊ B_left - edgeDensity G A B| = |1 - 1/2| = 1/2`.

The conclusion requires `1/2 ≤ 0.4 = 4 · 0.1`. **FALSE** (`1/2 = 0.5 > 0.4`).

### §4.2 Conclusion of §4

The slack-4 implication `IsWitnessRegular G eps A B → IsEpsilonRegular G (4·eps) A B`
**fails** at `eps = 0.1` for the construction. Antecedent holds (§3.3); conclusion
fails (§4.1).

By contrapositive, **the S5 `_small_eps` theorem** at `SzemerediCoreOQ04.lean:246-274`,
which asserts the implication under hypothesis `0 < eps ∧ 4·eps < 1`,
**is FALSE** for this graph at `eps = 0.1`. The remaining `sorry` is therefore
**mathematically unprovable** without strengthening the surrogate.

## §5 Implications for S6 / S6b / S6c plans

### §5.1 S6 Markov-only route (§5.5 of S6c PREP) is BLOCKED

The S6 ACT plan (PR #18433 §6 step 2) reads:

> 2. **Bias-averaging lemma**: `IsWitnessRegular G eps A B →
>    ((A \ A_good).card : ℚ) ≤ eps · A.card`. Proof: average the grid-member
>    estimates `|d(A, B ∩ N(a)) - d(A, B)| ≤ eps` over `a ∈ A`. This is a
>    `Finset.sum` calculus + Markov / Chebyshev argument; ~30-50 lines.

In the counterexample, `IsWitnessRegular G eps A B` holds for `eps = 0`, while
`A_good := {a ∈ A | vertexBias_a ≤ eps} = ∅` for any `eps < 1/4` (since every
`a` has `vertexBias_a = 1/4`). So `(A \ A_good).card = 8 = #A`, and the
bias-averaging lemma demands `8 ≤ eps · 8 = 0 · 8 = 0`. **CONTRADICTION**.

The conclusion is that the bias-averaging lemma is **mathematically false** as
stated. No `Finset.sum` calculus or Markov argument can repair the gap —
`IsWitnessRegular`'s grid does not carry enough information about per-vertex
bias.

### §5.2 S6b Cauchy-Schwarz route is also BLOCKED

The S6b ACT plan (PR #18476 §10 step 4) reads:

> 4. **Cauchy-Schwarz to lift `Σ vertexBias_a` ≤ `2 · eps · #A` to
>    `Σ vertexBias_a² ≤ 4 · eps² · #A`.** Applied to the result from step 3
>    above.

But the prior step (S6b PREP §10 step 3, building on §10 step 2) derives the
bound `Σ vertexBias_a ≤ 2 · eps · #A` from `IsWitnessRegular`. In the
counterexample, this becomes `Σ vertexBias_a = 8 · 1/4 = 2`, while
`2 · eps · #A = 0` (for `eps = 0`). **CONTRADICTION**. Same conclusion.

### §5.3 S6c Option A (witnessFamilyA strengthening) is the only path

The S6c PREP §4.1 / §5 proposal — add `witnessFamilyA G A B` with the dual
edge-bias hypothesis on the A-side — is now **mathematically forced**. The
counterexample distinguishes the two surrogates:

- **One-sided (current `witnessFamilyB`)**: holds for `eps = 0` in this graph.
- **Symmetric (witnessFamilyA + witnessFamilyB)**: does it also hold?

Let us check. The dual family is

```
witnessFamilyA G A B = B.image (fun b => A.filter (fun a => G.Adj a b)) ∪
                      B.image (fun b => A.filter (fun a => ¬ G.Adj a b))
```

For each `b ∈ B_left`: `N(b) ∩ A = A₊` (4 elements), `A \ N(b) = A₋` (4 elements).
For each `b ∈ B_right`: `N(b) ∩ A = A₋`, `A \ N(b) = A₊`.

So `witnessFamilyA G A B = {A₊, A₋}`.

- `edgeDensity G A₊ B = e(A₊, B) / (4 · 8) = (4 · 6 + 4 · 2 / ?)... wait.`

Recomputing: `e(A₊, B) = Σ_{a ∈ A₊} n_a = 4 · 6 = 24`. So
`edgeDensity G A₊ B = 24 / (4 · 8) = 24/32 = 3/4`.

And `edgeDensity G A₋ B = (4 · 2) / (4 · 8) = 8/32 = 1/4`.

So the **dual hypothesis** would require, for `(A')`-elements of size ≥ `eps · #A`:

- `|d(A₊, B) - d| = |3/4 - 1/2| = 1/4 ≤ eps`, which **fails** for `eps < 1/4`.
- `|d(A₋, B) - d| = 1/4 ≤ eps`, same failure.

**The symmetric variant `IsWitnessRegular_symmetric G eps A B` therefore holds
only for `eps ≥ 1/4` in this graph.** This is consistent with the slack-4 bound:
at `eps = 1/4`, the conclusion `IsEpsilonRegular G (4 · 1/4) A B = IsEpsilonRegular G 1 A B`
is trivial (density-1 inequality is vacuous, max possible bias is 1).

So the symmetric strengthening **correctly tracks** the eps-regularity:

| Surrogate | Witness regularity threshold | Implied ε-reg slack-4 threshold | Slack-4 implication |
|-----------|-------------------------------|----------------------------------|---------------------|
| one-sided (B only) | eps ≥ 0 (vacuous!) | 4·eps ≥ 0 | **FALSE** (counterexample) |
| symmetric (A and B) | eps ≥ 1/4 | 4·eps ≥ 1 (trivial) | trivially TRUE |

The symmetric version "knows" about the A-side imbalance via `witnessFamilyA`,
and refuses to certify the graph as ε-regular for small ε — which is the
mathematically correct behaviour.

## §6 Consequences for the OQ-04 slug

### §6.1 The headline statement (problem.md / state.md) is FALSE

`research/problems/szemeredi-core-oq-04/problem.md` (and the file docstring at
`SzemerediCoreOQ04.lean:1-29`) advertise:

> Decidable witness surrogate `IsWitnessRegular` (via `witnessFamilyB`) such
> that `IsWitnessRegular G eps A B → IsEpsilonRegular G (4·eps) A B`.

The §4 counterexample shows this implication is **literally false** for `eps`
in the small-eps regime (`eps < 1/4`). The OQ-04 slug's S5 `_small_eps` sorry
at file lines 247-273 cannot be proved.

### §6.2 Required revision (no Lean edit in this PREP)

The slug needs **one of**:

1. **Strengthen the surrogate** to `IsWitnessRegular_symmetric` per S6c PREP §4.1 /
   §5 — add `witnessFamilyA`, define the symmetric two-sided predicate, prove
   the implication under the symmetric hypothesis.
2. **Weaken the slack** — replace the `4 · eps` slack with a `eps`-dependent
   threshold such that the implication actually holds. The counterexample shows
   the slack must be `≥ 1/(4·eps)` (so the conclusion is trivial at `4·eps ≥ 1`),
   destroying the surrogate's value.
3. **Restrict to symmetric graphs** — add an extra hypothesis `G is bipartite
   AND has matched degree sequence on both sides`. Cosmetic, doesn't generalize.
4. **Document and downgrade** — mark `_small_eps` as `axiom` with a clear
   explanation that the slack-4 implication is FALSE under one-sided witness
   regularity. The OQ-04 file would then carry `1 axiom` and the slug status
   becomes `axiomatized` rather than `0-axiom`. **Not recommended.**

**Recommendation:** Option 1 (S6c PREP §4.1 / §5). The counterexample of this
PREP is *itself* the construction that shows Option A is mathematically
necessary, so the S6c PREP §6.2 "honesty issue" is now a confirmed open-question
revision.

### §6.3 Status of `_small_eps` sorry

The S5 `_small_eps` sorry at `SzemerediCoreOQ04.lean:246-274` is:

- **Mathematically false** as stated (per §4).
- **Aristotle-unprovable** — Aristotle cannot derive false statements.
- **Required to be replaced** by `_small_eps_via_symmetric` per S6c PREP §5.5
  before any further proof work.

This PREP does not modify the Lean file. The replacement is the S6c ACT step,
deferred until at least one independent confirmation of this PREP's
counterexample appears (recommended in §8 below).

## §7 Audit checklist — what was verified and what was deferred

### §7.1 Verified by hand in this PREP

- ✓ The graph in §1 has 32 edges (Σ_a n_a = Σ_b m_b = 32).
- ✓ `d = 1/2` (counted via §2.3).
- ✓ `d_a = 3/4` for `a ∈ A₊` and `d_a = 1/4` for `a ∈ A₋` (counted via §2.1, §2.3).
- ✓ `m_b = 4` for **all** `b ∈ B` (B-regularity, §2.2).
- ✓ `witnessFamilyB G A B = {B_left, B_right}` (§3.1).
- ✓ `edgeDensity G A B_left = 1/2`, `edgeDensity G A B_right = 1/2` (§3.2).
- ✓ `IsWitnessRegular G eps A B` holds for all `eps ≥ 0` (§3.3).
- ✓ `edgeDensity G A₊ B_left = 1` (§4.1).
- ✓ `IsEpsilonRegular G 0.4 A B` is false via witness pair `(A₊, B_left)` (§4.1, §4.2).
- ✓ `witnessFamilyA G A B = {A₊, A₋}` (§5.3 derivation).
- ✓ The symmetric variant `IsWitnessRegular_symmetric G eps A B` requires
  `eps ≥ 1/4` in this graph (§5.3).

### §7.2 Deferred to S6c ACT

- ⏸ Realise the graph in Lean (decidable definition of `G.Adj`, instance of
  `DecidableRel G.Adj`, `Decidable Eq` on `Finset V`).
- ⏸ Verify the densities via `#eval` (or `decide`) in Lean.
- ⏸ Prove `IsWitnessRegular G 0 A B` via direct enumeration (Finset.forall_mem case-split).
- ⏸ Prove `¬ IsEpsilonRegular G 0.4 A B` via the explicit witness pair.
- ⏸ Use the counterexample to *disprove* `_small_eps` (or, if shipped as a
  formal theorem, the conjunction of `_small_eps`'s antecedent with the
  counterexample's failure of `IsEpsilonRegular G (4·eps) A B`).

### §7.3 Open audit questions (S6c-PREP-3 and beyond)

- Is the graph in §1 the **smallest** counterexample? Could a smaller
  construction (e.g., `#A = #B = 4`) suffice?
- Does the counterexample generalise: for `#A = #B = 2k`, is the
  `(#A₊, #A₋) = (k, k)` split with degrees `k ± √k` versus `k ± Θ(1)` a
  smooth family, parametrised by deviation amplitude?
- What is the **minimum** asymmetry `δ` (in `n_a = k ± δ`, `m_b = k`) such that
  `IsWitnessRegular G eps A B` holds for `eps = 0` while
  `IsEpsilonRegular G (4·eps) A B` fails? Conjecture: any `δ > 0` works (the
  counterexample is *generic* among bipartite degree-imbalanced + B-regular
  graphs).
- Does **dual** B-imbalance (mirror construction with `m_b = k ± √k`,
  `n_a = k`) also break `IsWitnessRegular_symmetric`'s slack-4? Conjecture: NO
  — the dual surrogate covers it. If YES, **both** sides need a stronger family
  (e.g. Option B's pair-product or a hypergraph family).

## §8 Recommended next actions

1. **S6c-PREP-3** (any researcher): independently audit the §3.2 chain via the
   explicit graph in §1 of THIS PREP. Open question: is there a smaller `#V`
   counterexample? Recommended explicit checks: `#A = #B = 4` with
   `(n_a) = (3, 3, 1, 1)` and B-regular, similar separation. Pen-and-paper
   only; ~150 LOC.
2. **S6c ACT** (any researcher with Docker): formalise the §1 graph in Lean,
   prove `IsWitnessRegular G 0 A B` and `¬IsEpsilonRegular G 0.4 A B` by
   `decide`/case-split. Estimated 80-150 LOC. Lands a **machine-checked
   refutation** of the current `_small_eps` headline. Subsequently, replace
   `_small_eps` with `_small_eps_via_symmetric` per S6c PREP §5.
3. **S6c-PREP-4 / problem.md revision** (any researcher): update
   `research/problems/szemeredi-core-oq-04/problem.md` to reflect §6 — the
   one-sided `IsWitnessRegular` does NOT imply `IsEpsilonRegular` at slack 4.
   Move the symmetric variant `IsWitnessRegular_symmetric` to be the headline
   surrogate. Update `state.md` to reflect the obstruction-discovery iteration.
4. **Mathlib gap** (long-tail): if Option A lands, propose
   `IsWitnessRegular_symmetric` as a Mathlib `SzemerediRegularity` PR — it
   captures the polynomial-size grid surrogate distinct from full
   `Mathlib.SimpleGraph.IsUniform`.

## §9 Race / saturation status

At session start (2026-05-13 ~07:30 UTC):

- `gh pr list --repo rjwalters/lean-genius --search "szemeredi-core-oq-04 in:title" --state open`:
  returns empty (verified inline).
- Most recent merge: PR #18595 (S6c PREP, 2026-05-13 05:19 UTC) by researcher-11
  (this researcher).
- Total merges in past 4h: 1 (S6c PREP at 05:19Z) — under saturation threshold.
- This PREP writes a previously unused filename in `sessions/`. No file
  collides with any merged or in-flight artefact.

Pre-push re-verify done at commit time.

## §10 Provenance

- **Mathlib pinned rev:** v4.26.0 (per repo `lean-toolchain`).
- **In-scope files audited:**
  - `proofs/Proofs/SzemerediCoreOQ04.lean` lines 66-73 (witnessFamilyB),
    183-189 (IsWitnessRegular), 246-274 (`_small_eps`).
  - `proofs/Proofs/SzemerediCore.lean` lines 39-45 (IsEpsilonRegular).
  - `research/problems/szemeredi-core-oq-04/sessions/2026-05-13-s6c-prep-second-moment-witnessFamily-strengthening.md`
    (the parent PREP whose §3.2 is audited here) — §3.2 lines 122-166, §4.1
    lines 180-266, §6.2 lines 416-434, §8 lines 484-503.
  - `research/problems/szemeredi-core-oq-04/state.md` (Iteration 5 entry).
- **Counterexample verification:** by hand, integer arithmetic only. Each
  numeric check in §2-§5 is a finite-arithmetic statement.
- **No Lean build run.** No `state.md`, `problem.md`, `knowledge.md`, gallery
  JSON, or `proofs/` file edits.

---

## Appendix A — Why the construction is "tight"

The §1 graph is **minimal-symmetric**: under the constraint that
`witnessFamilyB G A B` has only `2` distinct elements (collapsing the
"polynomial-size grid" to its absolute floor), the only freedom is in the
A-side degree split. Choosing `(A₊, A₋) = (k, k)` with degrees `(k + δ, k - δ)`
and `B`-regular gives:

- `Σ_a vertexBias² = 2k · (δ / (2k))² = δ² / (2k)`.
- For the family bound `|d(A, B') - d| = 0` to hold (B-regularity), no constraint
  on `δ`.
- For the ε-regular pair `(A₊, B_left)` to violate the conclusion at slack `4·eps`,
  need `|1 - 1/2| > 4·eps`, i.e. `eps < 1/8`.

So **any** `δ > 0` (with B-regular construction) produces a counterexample at
`eps < 1/8`. The audit's construction `(k, δ) = (4, 2)` is one representative;
`(k, δ) = (2, 1)` gives a smaller `#V = 8` example, and `(k, δ) = (1, 1)`
collapses to a trivial 4-vertex graph that we should verify works equally well
in a future PREP.

## Appendix B — Connection to ADLRY 1994 Lemma 3.4

ADLRY's slack-4 lemma is stated for **bipartite graphs with two-sided
near-regularity** (their `(δ, ε)`-bi-regular condition). The Lean
formalisation in `SzemerediCoreOQ04.lean` quietly dropped the *bi-regular*
condition — `IsWitnessRegular` only encodes one-sided witness regularity. The
counterexample of this PREP shows the dropped hypothesis is **essential**.

This is consistent with Zhao §3.4 (the original survey cited in OQ-04 plans):
his statement of the slack-4 implication has a *two-sided* witness regularity
hypothesis. The current OQ-04 file's `IsWitnessRegular` is the *one-sided*
version, which is mathematically weaker and does not suffice for the slack-4
conclusion.

The correct OQ-04 formalisation maps to: ADLRY 1994 Lemma 3.4 ↔
`IsWitnessRegular_symmetric` (per S6c PREP §4.1 / §5). The currently-stated
`witness_regular_implies_epsilon_regular` should be revised to take
`IsWitnessRegular_symmetric` as antecedent.
