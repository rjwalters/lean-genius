# Erdős #827 - Knowledge Base

## Problem Statement

Let $n_k$ be minimal such that any $n_k$ points in $\mathbb{R}^2$ in general
position contain a $k$-subset where all $\binom{k}{3}$ triples determine
circles of distinct radii. **Determine $n_k$.**

- Erdős (1975) asked whether $n_k$ exists.
- Erdős (1978) gave $n_k \leq k + 2\binom{k-1}{2}\binom{k-1}{3}$ — argument
  later shown incorrect by Martinez & Roldán-Pensado.
- Martinez & Roldán-Pensado (2015) proved $n_k \ll k^9$.

The exact value of $n_k$ remains **open** for $k \geq 4$.

## Status

- **Erdős database**: OPEN
- **Lean formalization**: 4 axioms, 14 theorems, 0 sorries
- **Tractability**: 4/10 (full solution requires the published MRP proof)
- **Aristotle suitable**: No (the open conjecture is the value of n_k itself)

## Lean Formalization Architecture

**Geometry primitives:**
- `Point := ℝ × ℝ`
- `distSq p q : ℝ` — squared Euclidean distance
- `GeneralPosition S` — no three collinear, via cross-product determinant
- `circumRadiusSq p q r` — formula `a²·b²·c² / (4·Area²)`
- `AllDistinctCircumradii T` — every two distinct triples in T have ≠ radii

**Threshold function:**
- `NkExists k : Prop` — ∃ n forces a good k-subset in any GP set of size ≥ n
- `minimalNk : ℕ → ℕ` — axiomatized as the minimal such threshold
- `ErdosProblem827 : Prop := ∀ k ≥ 3, NkExists k`
- `MartinezBound : Prop` — ∃ C > 0, ∀ k ≥ 3, minimalNk k ≤ C·k⁹

**Construction:**
- `parabolaPoint i := (i, i²)` — parabolic embedding
- `parabolaSet n` — the first n parabola points
- `parabolaSet_gp` — parabola points are in GP (collinearity determinant
  factors as $(a-c)(b-c)(b-a) \neq 0$)

## Insights

### 1. Opaque function design forces axiom triple

`minimalNk` is declared as `axiom minimalNk : ℕ → ℕ`. This *forces*
`minimalNk_valid` (validity) and `minimalNk_sharp` (sharpness) to also be
axioms — Lean has no way to derive properties of an opaque function.

### 2. `Nat.find` refactor consolidates axioms

A `noncomputable def` using `Nat.find` over a witness existence axiom
collapses three axioms (function + valid + sharp) into one (witness
existence) plus zero (def is a definition, not an axiom).

```lean
def NkProperty (k n : ℕ) : Prop :=
  ∀ S : Finset Point, GeneralPosition S → n ≤ S.card →
    ∃ T : Finset Point, T ⊆ S ∧ T.card = k ∧ AllDistinctCircumradii T

axiom nk_property_witness (k : ℕ) (hk : 3 ≤ k) : ∃ n, NkProperty k n

noncomputable def minimalNk (k : ℕ) : ℕ :=
  if h : ∃ n, NkProperty k n then Nat.find h else 0
```

Then `minimalNk_valid` follows from `Nat.find_spec`, and `minimalNk_sharp`
follows from `Nat.find_min`. This reduces 4 → 2 axioms.

### 3. Parabola GP via determinant factoring

The collinearity test for $(a,a^2), (b,b^2), (c,c^2)$ reduces to:
$$
(a-c)(b^2-c^2) - (b-c)(a^2-c^2) = (a-c)(b-c)(b-a)
$$
which is non-zero iff a, b, c are pairwise distinct.

### 4. n_3 = 3 via vacuous AllDistinctCircumradii

For 3-element sets, there is only one unordered triple, so the "every two
*distinct* triples have different radii" hypothesis has empty conclusion
domain. This forces `nk_three` even though `minimalNk` is opaque.

### 5. Monotonicity is automatic from validity + sharpness

`nk_monotone` follows by contradiction: if $n_{k_2} < n_{k_1}$, then the
sharp witness for $k_1$ is a GP set of size $\geq n_{k_2}$, hence has a
good $k_2$-subset $T$. Subset $T' \subseteq T$ of size $k_1$ inherits
`AllDistinctCircumradii` (the property is hereditary), contradicting
sharpness.

### 6. Vacuous-ness is geometry-blind

`nk_three = 3` is a *combinatorial* truth, not a geometric one — it follows
from the structure of "all distinct triples" being empty for 3-sets. This is
why it can be proved without touching circumRadiusSq computations.

### 7. Further axiom reduction needs published proof formalization

The deepest remaining axiom is `martinez_roldan_pensado` (the polynomial
bound). Eliminating it would require formalizing the Martinez & Roldán-Pensado
2015 paper (Acta Math. Hungar.) — a multi-month effort involving incidence
geometry and polynomial method techniques.

## Mathlib Gaps

(None identified during this audit. The proofs use only `Real`, `Finset`,
`Tactic` — basic Mathlib infrastructure.)

## Sessions

### Session 1 (pre-2026-04, recorded retroactively)
- Reduced axiom count 6 → 5 → 4
- Proved nk_ge_k, nk_three, nk_monotone (all promoted from axioms)
- Built parabola GP infrastructure
- Added structural lemmas (distSq, hereditary properties)
- See git log: PRs #7696, #7239, #7324, #8301

### Session 2 (2026-04-27, this session — researcher-7)
- Audit: confirmed file state matches metadata (4 axioms, 14 theorems, 0 sorries)
- Identified Nat.find refactor as concrete next step (4 → 2 axioms)
- Refactor deferred to next session: disk at 89%, Docker build unsafe;
  per CLAUDE.md never run lake build directly
- No Lean code changes this session; pure metadata + planning

## References

- [Er75h] Erdős, P. *Some problems on elementary geometry.* Austral. Math.
  Soc. Gaz. (1975), 2-3.
- [Er78c] Erdős, P. *Some more problems on elementary geometry.* Austral.
  Math. Soc. Gaz. (1978), 52-54.
- [MaRo15] Martínez, L. and Roldán-Pensado, E. *Points defining triangles
  with distinct circumradii.* Acta Math. Hungar. (2015), 136–141.

## Tags

- erdos
- geometry
- discrete-geometry
- circumradii
- ramsey-type

## Related Problems

- #826, #828 (neighbors in Erdős's geometry sequence)
- #2000, #1998 (other Ramsey-type combinatorial geometry)
- #83, #888 (related distinct-distance / distinct-radius problems)

---

*Last updated: 2026-04-27 by researcher-7 (audit/refactor-planning session)*
