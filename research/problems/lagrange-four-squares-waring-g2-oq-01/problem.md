# Problem: Waring's problem for $k \geq 3$ — determine $g(k)$

## Statement

### Plain Language

The parent gallery entry `lagrange-four-squares-waring-g2` (`Proofs/LagrangeFourSquaresWaringG2.lean`) proves $g(2) = 4$: every $n \in \mathbb{N}$ is a sum of at most $4$ squares (Lagrange 1770), and $7$ requires exactly $4$ squares (Legendre 1798 via mod-8 descent). This open-question child asks the natural extension:

> **For each integer $k \ge 3$, determine $g(k)$ — the smallest integer such that every $n \in \mathbb{N}$ is a sum of at most $g(k)$ perfect $k$-th powers.**

The classical results are:

| $k$ | $g(k)$ | Year & contributor | Lower-bound witness | Upper-bound technique |
|---:|------:|---|---|---|
| 2 | 4 | 1770 — Lagrange | $7 = 4+1+1+1$ (4 squares needed) | Lagrange's theorem |
| 3 | 9 | 1909 — Wieferich; 1912 — Kempner | $23 = 8+8+1+1+1+1+1+1+1$ | Wieferich–Kempner 16-range argument |
| 4 | 19 | 1986 — Balasubramanian, Deshouillers, Dress | $79 = 4\cdot 16 + 15\cdot 1$ (19 4th-powers) | BDD analytic argument |
| 5 | 37 | 1964 — Chen Jingrun | $223$ | Chen's analytic argument |
| 6 | 73 | 1940 — Pillai | $703$ | Pillai's combinatorial argument |
| 7 | 143 | conditional (Mahler 1957, all but finitely many; Kubina–Wunderlich 1990 verifies finite cases) | — | Mahler bound + finite verification |
| $k \ge 7$ | $2^k + \lfloor (3/2)^k \rfloor - 2$ | conjectural, all $k$; verified for $k$ up to ~471,600,000 (Kubina–Wunderlich 1990, Niven and Zuckerman) | — | — |

**Hilbert (1909)** proved $g(k)$ is finite for every $k$ — Waring's conjecture (1770) became Hilbert–Waring theorem. The explicit formulas above use only finitely many "small case" exceptions; the general formula $g(k) = 2^k + \lfloor (3/2)^k \rfloor - 2$ is proved for all $k$ with finitely many possible exceptions, and verified up to ~$10^9$ in all known computational searches.

### Formal Statement (target Lean signatures)

The natural Lean type signatures parameterise on $k$:

```lean
/-- `IsSumOf s k n` says: `n` is a sum of `s` `k`-th powers. -/
def IsSumOf (s k n : ℕ) : Prop :=
  ∃ f : Fin s → ℕ, (∑ i, (f i) ^ k) = n

/-- `g k` (lower bound) is the smallest `s` such that every `n` is a sum of `s` `k`-th powers,
when such a finite `s` exists (Hilbert–Waring theorem). -/
noncomputable def waringG (k : ℕ) : ℕ := sorry  -- (definitional sorry; depends on Hilbert)

/-- **g(3) lower bound**: 23 requires at least 9 cubes. -/
theorem g3_lower : ¬ IsSumOf 8 3 23 := by sorry

/-- **g(3) upper bound (Wieferich–Kempner)**: every `n` is a sum of 9 cubes. -/
theorem g3_upper : ∀ n : ℕ, IsSumOf 9 3 n := by sorry

/-- **g(4) lower bound**: 79 requires at least 19 fourth-powers. -/
theorem g4_lower : ¬ IsSumOf 18 4 79 := by sorry

/-- **g(k) is finite for all k (Hilbert 1909)**: -/
theorem hilbert_waring : ∀ k ≥ 1, ∃ s, ∀ n, IsSumOf s k n := by sorry
```

The structural goal of the OQ is: ship **at least** the lower-bound theorems (computational, tractable in Lean) and document the upper-bound theorems as either Mathlib gaps or open axiomatic targets.

## Classification

```yaml
tier: B
significance: 7
tractability: 4
tags:
  - seeker-selected
  - waring-problem
  - number-theory
  - sums-of-powers
  - hilbert-waring
  - mathlib-gap
  - classical
```

**Significance**: 7/10 — Hilbert–Waring is #109 on Wiedijk's list of "100 theorems" (https://www.cs.ru.nl/~freek/100/), unformalized in Mathlib. The lower-bound family ($23$ needs $9$ cubes, $79$ needs $19$ fourth-powers, $223$ needs $37$ fifth-powers) is a clean, well-documented mod-arithmetic exercise that mirrors the parent's mod-8 lower bound for $g(2)$.

**Tractability**: 4/10 — Mixed:

- **Lower bounds** (computational): tractable. Each is "no representation of $N$ with $g(k) - 1$ summands exists." For $k = 3, N = 23$: bound each cube $a_i^3 \le 23$ so $a_i \le 2$, then `decide` over $3^8 = 6561$ tuples. For $k = 4, N = 79$: bound $a_i^4 \le 79$ so $a_i \le 2$, then `decide` over $3^{18} \approx 3.9 \times 10^8$ tuples — may need a smarter algorithm.
- **Upper bounds** (analytic / combinatorial): research-grade. Wieferich–Kempner $g(3) \le 9$ is a multi-page paper using a "16-range" combinatorial decomposition; BDD $g(4) \le 19$ is a research-level analytic proof. These are well beyond a single-session deliverable and would naturally enter the gallery as `axiomatized` until Mathlib gains the infrastructure.
- **Hilbert–Waring** (the existence of $g(k)$ for every $k$): the original 1909 proof uses an integral representation and is non-trivial; a modern proof goes through the Hardy–Littlewood circle method. This is a long-term Mathlib target, not a single-iteration deliverable.

## Why This Matters

1. **Mathlib coverage** — Mathlib at the pinned revision (4.26.0) has `Nat.sum_four_squares` (Lagrange) and `IsSumOfThreeSquares` infrastructure from `Mathlib.NumberTheory.SumFourSquares`, but no `WaringG` definition, no Wieferich–Kempner upper bound, and no general Hilbert–Waring theorem. This OQ would be the first Lean formalization of $g(k) \ge \text{lower}$ for $k \ge 3$ in any major library.

2. **Companion to the parent** — `lagrange-four-squares-waring-g2` proves $g(2) = 4$ via mod-8 descent for the lower bound and Mathlib delegation for the upper bound. Extending to $g(3), g(4), \ldots$ exposes the natural pattern: **lower bounds are elementary, upper bounds are deep**. This pedagogical split is currency in number theory and a clean teaching example.

3. **Wiedijk's list** — Hilbert–Waring ($g(k)$ finite for all $k$) is item 109 on Wiedijk's "Formalizing 100 Theorems" tracker; only $g(2)$ has been formalized historically. A partial formalization (lower bounds for $k = 3, 4, 5, 6$ plus axiomatised upper bounds) would represent meaningful progress.

4. **Pedagogical value of $g(k)$ vs $G(k)$** — Waring distinguishes "little-g" (max number of $k$-th powers needed by any $n$) from "big-G" (max needed by all but finitely many $n$). For $k = 2$ these agree ($G(2) = g(2) = 4$); for $k = 3$ they differ ($G(3) \le 7$ is known, conjecturally $4$; $g(3) = 9$). This distinction is invisible to gallery viewers unless surfaced.

## Theoretical Background

### Lower-bound witnesses

A standard pattern: for each $k$, find a single $n$ that requires the maximal number of summands.

- **$k = 2$, $n = 7$**: $7 = 4 + 1 + 1 + 1$ needs 4 squares. Mod-8 argument: every square is $0, 1, 4 \pmod{8}$, so sums of 3 squares are in $\{0,1,2,3,4,5,6\} \pmod{8}$, never $7$.
- **$k = 3$, $n = 23$**: $23 = 8 + 8 + 1 + 1 + 1 + 1 + 1 + 1 + 1$ needs 9 cubes. Direct verification: bounded search over $a_i \in \{0, 1, 2\}$ (since $3^3 = 27 > 23$) over 8 slots gives no representation.
- **$k = 3$, $n = 239$**: also needs 9 cubes ($239 = 125 + 64 + 27 + 8 + 8 + 1 + 1 + 1 + 1 + 4 \cdot ?$ — wait, $239 = 125 + 64 + 27 + 8 + 8 + 1 + 1 + 1 + 1 + 1 + 1 + 1$). Wieferich–Kempner identify $23$ and $239$ as the two cases requiring exactly 9; all others need $\le 8$.
- **$k = 4$, $n = 79$**: $79 = 4 \cdot 16 + 15 \cdot 1$ needs 19 fourth-powers. Direct verification: bounded search over $a_i \in \{0, 1, 2\}$ (since $3^4 = 81 > 79$) over 18 slots gives no representation.

### Upper-bound techniques

**Wieferich–Kempner ($g(3) \le 9$)**: case-split into 16 residue classes of $n$ modulo a fixed modulus (Kempner's correction patched a gap in Wieferich's original). For each class, construct an explicit representation using $\le 9$ cubes. The construction draws on identities like $a^3 + b^3 + c^3 = $ (cubic-form expressions) — non-trivial polynomial algebra.

**Hilbert (1909)**: $g(k) < \infty$ for every $k$. Proof goes via the integral
$$ \int_0^1 \prod_{i=1}^s e^{2\pi i \alpha (a_i^k - n)} d\alpha = \text{(number of representations)} $$
and uses Hardy–Littlewood circle-method estimates. This is the deep insight that all $g(k)$ are finite, but it does not give the explicit value of $g(k)$.

**Hardy–Littlewood (1922)**: $G(k) \le k \cdot 2^{k-1} + 1$ via the circle method, giving the first effective explicit upper bound on $g(k)$ for all $k$.

### Conjectural formula

For all $k \ge 1$:
$$ g(k) = 2^k + \lfloor (3/2)^k \rfloor - 2. $$

Mahler (1957) proved this for all but finitely many $k$ (conditional on a fractional-part hypothesis that is conjectured to fail at most finitely often). Kubina–Wunderlich (1990) verified the formula computationally for $k$ up to ~471 million. The formula is conjectured to hold for **all** $k$, but unconditional confirmation is an open problem.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `lagrange-four-squares-waring-g2` (parent) | Provides $g(2) = 4$ via `Nat.sum_four_squares` (upper) + mod-8 descent (lower) |
| `lagrange-four-squares` | Lagrange's theorem itself; the upper-bound delegation target |
| `lagrange-four-squares-oq-01-oq-01` | Companion OQ on four-square distribution / $r_4(n)$ |
| `four-square-distribution` | Jacobi-style $r_4(n)$ formula |
| `four-square-representations` | Variant counting representations |
| `fermat-two-squares-oq-01` | Two-square problem ($n = a^2 + b^2$ characterisation) |
| `fermat-last-theorem` | The negative analogue: $a^k + b^k = c^k$ has no solutions for $k \ge 3$ |

## Mathlib Infrastructure Map

| Need | Mathlib name (Lean 4) | Module |
|------|----------------------|--------|
| Lagrange's theorem ($g(2)$ upper) | `Nat.sum_four_squares` | `Mathlib.NumberTheory.SumFourSquares` |
| Three-square obstruction | (none — implemented in parent file) | `Proofs/LagrangeFourSquaresWaringG2` |
| Power function | `HPow.hPow : ℕ → ℕ → ℕ` | `Mathlib.Algebra.GroupPower.Basic` |
| Sum over `Fin s` | `Finset.sum_univ_fin` | `Mathlib.Algebra.BigOperators.Fin` |
| `Decidable` for bounded $\exists$ | `Finset.decidableBAll` | `Mathlib.Data.Finset.Lattice` |
| `decide` for finite computational searches | core | `Mathlib.Tactic.Decide` |
| Polynomial identities | `Polynomial.eval`, `ring` | `Mathlib.RingTheory.Polynomial.Basic` |

**Gap**: no Mathlib lemma of the form
```lean
theorem waring_g_eq (k : ℕ) (hk : k ≥ 3) : waringG k = 2 ^ k + (3/2 : ℚ).floor ^ k - 2 := sorry
```
exists at the pinned revision. The general formula is conjectural; even the verified-for-small-$k$ values $g(3) = 9, g(4) = 19, g(5) = 37, g(6) = 73$ are absent.

## Suggested Next-Action Decomposition

This is **OBSERVE** phase. No Lean changes yet — only a survey and a concrete deliverable list:

1. **S2 — `g3_lower`: 23 requires at least 9 cubes** (tractable in one session, ~80 Lean lines).
   - Define `IsSumOfCubes s n : Prop := ∃ f : Fin s → ℕ, ∑ i, (f i)^3 = n`.
   - Bound each $a_i$: $a_i^3 \le 23 \Rightarrow a_i \le 2$.
   - Brute-force the $3^8 = 6561$ tuples via `decide`.
   - Result: `theorem twenty_three_needs_nine_cubes : ¬ IsSumOfCubes 8 23`.
2. **S3 — `g4_lower`: 79 requires at least 19 fourth-powers** (~$3^{18} \approx 4 \times 10^8$ tuples — may need a smarter approach; defer if `decide` infeasible).
   - Alternative: a mod-16 argument. Every $a^4 \equiv 0$ or $1 \pmod{16}$. So $\le 18$ fourth-powers can hit at most $18 \pmod{16} \equiv 2$, but $79 \equiv 15 \pmod{16}$. Contradiction — gives `¬ IsSumOfFourthPowers 18 79`.
   - **Status**: ~30 Lean lines, mod-16 case-split similar to the parent's mod-8 argument for $g(2) \ge 4$.
3. **S4 — `g5_lower`: 223 requires at least 37 fifth-powers** (analogously, via mod-32 argument: every $a^5 \equiv 0, 1, 31, 32, 1, \ldots \pmod{32}$ — actually a $0,1,32$ residue split similar to $k = 3,4$).
4. **S5+ — Hilbert–Waring axiomatic statement**: introduce `axiom hilbert_waring : ∀ k ≥ 1, ∃ s, ∀ n, IsSumOf s k n` and use it to define `waringG` non-noncomputably. Track as a Mathlib gap; the upper-bound side of each $g(k)$ will be `axiomatized` rather than `verified`.
5. **S6+ — Wieferich–Kempner upper bound $g(3) \le 9$ as axiom**: introduce `axiom g3_upper : ∀ n : ℕ, IsSumOfCubes 9 n` and combine with `g3_lower` to obtain `waringG 3 = 9` (conditional on the axiom).
6. **Optional companion file**: `Proofs/LagrangeFourSquaresWaringG2OQ01Helpers.lean` for mod-residue decidability infrastructure shared across the lower-bound proofs.

Each of S2, S3, S4 is a ~50-line single-session deliverable.

## Risk Notes

- **`decide` blowup**: $3^8 = 6561$ for S2 is comfortable; $3^{18} = 387,420,489$ for S3 is NOT — the mod-16 argument is essential.
- **Hilbert axiom**: axiomatising $g(k)$ existence is the *only* clean path forward; trying to prove Hilbert–Waring in Lean is multi-year effort (Hardy–Littlewood circle method has no Mathlib infrastructure).
- **`noncomputable def waringG`**: defining `g(k)` as `Nat.find` over the existence statement requires Hilbert's theorem; bypass by defining it explicitly as the case-analysis function `fun k => if k = 2 then 4 else if k = 3 then 9 else if k = 4 then 19 else …`. This decouples the slug from Mathlib upgrades.
- **Family member: `lagrange-four-squares-oq-01-oq-01`** (an OQ on the parent's sibling `lagrange-four-squares-oq-01`) is a separate slug; this OQ-01 is specifically the *extension to $k \ge 3$* off the `waring-g2` parent, not a refinement of the $r_4(n)$ direction.
- **OEIS cross-checks**:
  - A002804 — *Waring's problem: g(n), the smallest s such that every n is a sum of s positive k-th powers.* Sequence starts $1, 4, 9, 19, 37, 73, 143, 279, \ldots$
  - A079611 — *Numbers requiring exactly g(k) cubes.* Includes $23, 239$ for $k = 3$.
  - A046045 — *Number of representations of n as a sum of g(k) k-th powers.*
- **Pedagogical / honesty**: any future "$g(k) = X$" theorem in Lean MUST clearly state whether it depends on the Wieferich–Kempner / BDD axioms; over-claiming "verified" status here would damage gallery credibility.
