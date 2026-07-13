# Problem: Countability of Computable Real Numbers

## Statement

### Plain Language

Prove that the set of computable real numbers is countable. A real number is
*computable* if there exists a Turing machine that, given `n : ℕ`, outputs a
rational approximation `q_n : ℚ` with the sequence `q_0, q_1, q_2, ...`
converging to it. Turing-machine descriptions are finite strings (over a
finite alphabet), hence countable — and the map "TM → real it converges to"
factors the computable reals through a countable set.

This completes the cardinality hierarchy of "describable" subfamilies of ℝ:

    ℚ  ⊊  algebraic  ⊊  computable  ⊊  ℝ
    ↑          ↑              ↑       ↑
    ℵ₀         ℵ₀             ℵ₀      𝔠

All three nested inclusions are *qualitatively* strict (different sets) but
*cardinally* the same — ℵ₀. The final inclusion is strict by cardinality
(ℵ₀ < 𝔠), so uncountably many non-computable reals exist (e.g., Chaitin's Ω).

**Note**: the original statement said "computable ⊂ algebraic" — this is
**mathematically incorrect**. The correct inclusion is `algebraic ⊊ computable`,
since `e` and `π` are computable yet transcendental.

### Formal Statement

In Lean 4 (Mathlib):

```lean
def IsComputable (r : ℝ) : Prop :=
  ∃ f : ℕ → ℚ, Computable f ∧ Tendsto (fun n => (f n : ℝ)) atTop (nhds r)

theorem computable_reals_countable :
    Set.Countable {r : ℝ | IsComputable r}
```

The `Computable` predicate is from `Mathlib.Computability.Partrec`; `Tendsto`
is from `Filter`.

### Cardinal Form

$$
\#\{r : \mathbb{R} \mid \text{IsComputable } r\} \leq \aleph_0
$$

Combined with the rational embedding `ℚ ↪ {r | IsComputable r}` (constant
sequences), this becomes:

$$
\#\{r : \mathbb{R} \mid \text{IsComputable } r\} = \aleph_0
$$

## Classification

```yaml
tier: B
significance: 6
tractability: 6
tags:
  - set-theory
  - real-analysis
  - cardinality
  - computability
  - computable-analysis
  - turing
  - cantor
  - research
  - seeker-selected
  - gallery-extracted
```

**Significance**: 6/10 — completes a well-motivated cardinality hierarchy and
provides foundation for computable analysis in Lean.

**Tractability**: 6/10 — the proof uses standard Mathlib computability
infrastructure (`Computable`, `Nat.Partrec.Code`). The challenge is API
identification, not mathematical depth.

## Why This Matters

1. **Completes Turing's 1936 observation**: Turing's original paper noted
   the countability of computable reals as the basis for proving the
   existence of non-computable reals (uncountably many of them). Formalizing
   this in Lean grounds computable analysis in Mathlib.

2. **Cardinality hierarchy refinement**: the existing entry
   `algebraic-numbers-countable-oq-02-oq-03` proved `#transcendentals = 𝔠`.
   This entry refines that picture by showing the *computable* subset of ℝ
   (which strictly contains the algebraic reals) is still only ℵ₀.

3. **Bridge to computable analysis**: subsequent results (computable
   arithmetic on reals, computable Cauchy completion, computable real
   closed fields) rest on basic countability of the underlying set.

## Related Gallery Proofs

| Proof                                                  | Relevance                                                                 |
| ------------------------------------------------------ | ------------------------------------------------------------------------- |
| `algebraic-numbers-countable`                          | Parent: algebraic reals are countable. Algebraic ⊊ computable.            |
| `algebraic-numbers-countable-oq-02`                    | Ancestor: ℝ is uncountable. Combined gives strict inclusion computable ⊊ ℝ. |
| `algebraic-numbers-countable-oq-02-oq-03`              | Sibling: exact cardinality of transcendentals = 𝔠. Refines this picture.   |
| `e-transcendental`                                     | Related: `e` is transcendental — and computable, hence witness of strictness. |
| `cantor-diagonalization`                               | Foundational: ℵ₀ < 𝔠 used to conclude computable ⊊ ℝ.                       |
| `schroeder-bernstein-oq-03`                            | Related: Myhill's theorem on computable injections, computability infrastructure. |
