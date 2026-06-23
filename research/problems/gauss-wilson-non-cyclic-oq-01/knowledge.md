# Knowledge — gauss-wilson-non-cyclic-oq-01

## Numerical sanity table

Let $P(n) := \prod_{x \in (\mathbb{Z}/n\mathbb{Z})^\times} x \pmod n$.

| $n$ | $(\mathbb{Z}/n)^\times$ order | cyclic? | $P(n)$ | match |
|----:|---:|---|----:|---|
| 1 | 1 | trivially cyclic | 0 (≡ −1 mod 1) | ✓ |
| 2 | 1 | cyclic | 1 (≡ −1 mod 2) | ✓ |
| 3 | 2 | cyclic | 2 (≡ −1 mod 3) | ✓ |
| 4 | 2 | cyclic | 3 (≡ −1 mod 4) | ✓ |
| 5 | 4 | cyclic | 4 (≡ −1 mod 5) | ✓ |
| 6 | 2 | cyclic ($2 \cdot 3$) | 5 (≡ −1 mod 6) | ✓ |
| 7 | 6 | cyclic | 6 (≡ −1 mod 7) | ✓ |
| 8 | 4 | **non-cyclic** ($\mathbb{Z}/2 \times \mathbb{Z}/2$) | 1 | ✓ |
| 9 | 6 | cyclic ($3^2$) | 8 (≡ −1 mod 9) | ✓ |
| 10 | 4 | cyclic ($2 \cdot 5$) | 9 (≡ −1 mod 10) | ✓ |
| 12 | 4 | **non-cyclic** ($\mathbb{Z}/2 \times \mathbb{Z}/2$) | 1 | ✓ |
| 15 | 8 | **non-cyclic** ($\mathbb{Z}/2 \times \mathbb{Z}/4$) | 1 | ✓ |
| 16 | 8 | **non-cyclic** ($\mathbb{Z}/2 \times \mathbb{Z}/4$) | 1 | ✓ |
| 24 | 8 | **non-cyclic** ($(\mathbb{Z}/2)^3$) | 1 | ✓ |
| 25 | 20 | cyclic ($5^2$) | 24 (≡ −1 mod 25) | ✓ |

All hand-checked against the seeker's reference: OEIS A001783 lists $(n-1)!$ mod $n$ but $P(n) \bmod n \in \{1, n-1\}$ matches the dichotomy above for $n \geq 2$.

## Proof strategy (three-phase)

### Phase A — Generic finite commutative group: reduce to 2-torsion

**Statement.** Let $G$ be a finite commutative group and $H = \{x \in G : x^2 = 1\}$. Then
$$
\prod_{x \in G} x \;=\; \prod_{x \in H} x.
$$

**Proof sketch.** Apply `Finset.prod_involution` to $G \setminus H$ with involution $g \mapsto g^{-1}$:
- $g \cdot g^{-1} = 1$ (the multiplicative analogue of `hg₁`),
- $g \neq g^{-1}$ for $g \notin H$ (the involution is fixed-point-free outside $H$),
- the involution is its own inverse.

So $\prod_{g \in G \setminus H} g = 1$ and the total product equals $\prod_{x \in H} x$.

**Lean sketch.**
```lean
theorem prod_univ_eq_prod_two_torsion (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G] :
    ∏ x : G, x = ∏ x ∈ (Finset.univ : Finset G).filter (fun x => x ^ 2 = 1), x := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ) (fun x : G => x ^ 2 = 1)]
  conv_rhs => rw [← mul_one (∏ x ∈ _, x)]
  congr 1
  -- The "x^2 ≠ 1" half multiplies to 1 via the inverse involution
  refine Finset.prod_involution (fun g _ => g⁻¹) ?_ ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hg
    field_simp
  · intro g hg hg1
    intro heq
    -- g = g⁻¹ ⇒ g² = 1, but g is in the "x² ≠ 1" filter
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    exact hg (by rw [← heq, ← sq]; group)
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    refine ⟨trivial, ?_⟩
    intro h
    apply hg
    have : (g⁻¹) ^ 2 = 1 := h
    calc g ^ 2 = (g ^ 2)⁻¹⁻¹ := by group
      _ = ((g⁻¹) ^ 2)⁻¹ := by group
      _ = 1⁻¹ := by rw [this]
      _ = 1 := inv_one
  · intro g hg; group
```

(The above is an outline; the proof above doesn't quite typecheck as written and will need adjustments. The crucial idea is mechanical.)

**Tighter alternative.** Mimic Mathlib's `prod_univ_units_id_eq_neg_one`: instead of splitting, work directly on the full `Finset.univ`, with the involution $g \mapsto g^{-1}$ extended trivially to identity on 2-torsion (and then erase 2-torsion).

### Phase B — Product over an elementary abelian 2-group of order ≥ 4

**Statement.** Let $H$ be a finite commutative group with $h^2 = 1$ for all $h \in H$, and $|H| \geq 4$. Then $\prod_{x \in H} x = 1$.

**Proof sketch.** Pick any $h \in H$ with $h \neq 1$. Define the involution $\phi(x) = h \cdot x$. Then $\phi(\phi(x)) = h \cdot h \cdot x = x$, $\phi$ is fixed-point-free (since $hx = x \Rightarrow h = 1$, contradiction). Pair $x$ with $\phi(x)$: each pair multiplies to $x \cdot hx = h x^2 = h \cdot 1 = h$. There are $|H|/2$ pairs, so the product equals $h^{|H|/2}$. Since $H$ has exponent dividing 2, $|H|$ is a power of 2 (Lagrange + Sylow), so $|H| \geq 4 \Rightarrow |H|/2 \geq 2 \Rightarrow$ $h^{|H|/2} = 1$ (since $h^2 = 1$ and exponent of 2 in $|H|/2$ is $\geq 1$).

**Lean sketch.**
```lean
theorem prod_univ_of_elementary_abelian_two
    {H : Type*} [CommGroup H] [Fintype H] [DecidableEq H]
    (h_exp : ∀ x : H, x ^ 2 = 1) (h_card : 4 ≤ Fintype.card H) :
    ∏ x : H, x = 1 := by
  -- Pick any non-identity element h₀
  obtain ⟨h₀, h₀_ne⟩ : ∃ h : H, h ≠ 1 := by
    by_contra hall; push_neg at hall
    have : Fintype.card H ≤ 1 := by
      rw [Fintype.card_le_one_iff_subsingleton]
      exact ⟨fun a b => by rw [hall a, hall b]⟩
    omega
  -- Use prod_ninvolution with the translation x ↦ h₀ * x
  -- Each pair contributes h₀; the number of pairs is |H|/2 which is even since |H| is 2^k, k ≥ 2
  sorry
```

The "card is a power of 2" step uses Mathlib's `Monoid.exponent` and finite-abelian-group structure theory, or alternatively a direct Sylow argument. Mathlib's `card_eq_pow_card_iff_isPGroup` or similar may apply.

**Alternative**: cleaner phrasing via additive notation, using $H$ as an $\mathbb{F}_2$-vector space. The sum over $\mathbb{F}_2^k$ is $0$ when $k \geq 2$ (each coordinate sums to $2^{k-1} \cdot 1 = 0$ in $\mathbb{F}_2$ for $k \geq 1$, but the whole sum is 0 iff $k \geq 2$). Bridging from `CommGroup` with exponent 2 to `Module F₂` requires a small lemma.

### Phase C — Specialize to $(\mathbb{Z}/n\mathbb{Z})^\times$

**Statement.**
$$
\prod_{x \in (\mathbb{Z}/n\mathbb{Z})^\times} x \;=\;
\begin{cases} -1 & \text{if IsCyclic } (\mathbb{Z}/n\mathbb{Z})^\times\\ \phantom{-}1 & \text{otherwise.}\end{cases}
$$

**Proof sketch.** Combine Phase A + Phase B + the parent's `card_sq_eq_one_ge_three`:

- Cyclic case ($n \in \{0,1,2,4,p^m,2p^m\}$): the 2-torsion of a finite cyclic group has cardinality $\gcd(|G|, 2) \in \{1, 2\}$. For $n \geq 3$, $-1 \neq 1$, so 2-torsion = $\{1, -1\}$ and the product over 2-torsion is $-1$. For $n \in \{0, 1, 2\}$: handle each small case directly.

- Non-cyclic case: by parent's `card_sq_eq_one_ge_three`, the 2-torsion has at least 3 elements. Since it is a 2-elementary abelian group (elementary because $x^2 = 1$ for all 2-torsion $x$), its order is a power of 2. So $|H| \geq 4$, and Phase B gives $\prod = 1$.

**Lean sketch.**
```lean
theorem prod_univ_units_zmod_eq_neg_one_iff_isCyclic (n : ℕ) [NeZero n] :
    ∏ x : (ZMod n)ˣ, x = -1 ↔ IsCyclic (ZMod n)ˣ := by
  -- Forward: contrapositive. If non-cyclic, Phase A + parent + Phase B → product = 1 ≠ -1.
  -- Backward: cyclic → 2-torsion ⊆ {1, -1} → Phase A reduces to {1, -1} product = -1.
  sorry
```

## Mathlib API summary

Key invocations we expect:

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic   -- Finset.prod_involution
import Mathlib.RingTheory.ZMod.UnitsCyclic               -- ZMod.isCyclic_units_iff
import Mathlib.GroupTheory.SpecificGroups.Cyclic         -- IsCyclic, orderOf
import Mathlib.FieldTheory.Finite.Basic                  -- prod_univ_units_id_eq_neg_one (reference)
```

Critical lemmas to compose:
- `Finset.prod_involution` (pair-up by inverse)
- `IsCyclic.card_orderOf_eq_totient` (for the cyclic side's 2-torsion count)
- `ZMod.isCyclic_units_iff` (boundary characterization)
- Parent file's `card_sq_eq_one_ge_three` (non-cyclic side's lower bound)

## Mathlib gaps

| Gap | Workaround |
|---|---|
| No `Finset.prod_univ_eq_prod_two_torsion` for general finite abelian groups | Provide in Phase A as a gallery-local lemma; potential Mathlib PR |
| No `prod_univ_eq_one_of_two_torsion_card_ge_four` lemma | Provide in Phase B as a gallery-local lemma; potential Mathlib PR |
| Bridging "exponent 2 + finite + |H| = power of 2" requires assembly | Use `Monoid.exponent_dvd_iff` + `Fintype.card_eq_pow_card_orderOf` route, or hand-roll with Sylow |

## S2 next-action skeleton

The first ACT iteration should ship **Phase A in isolation** as `proofs/Proofs/GaussWilsonNonCyclicOQ01A.lean`:

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Algebra.Group.Basic

namespace GaussWilsonNonCyclicOQ01

open Finset

/-- For any finite commutative group, the product of all elements equals the product of the 2-torsion.

    Proof: pair each non-self-inverse element with its inverse via `Finset.prod_involution`. -/
theorem prod_univ_eq_prod_two_torsion (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G] :
    ∏ x : G, x = ∏ x ∈ (univ : Finset G).filter (fun x => x ^ 2 = 1), x := by
  classical
  -- Split univ = (2-torsion) ⊎ (non-2-torsion); show product over non-2-torsion = 1
  sorry

end GaussWilsonNonCyclicOQ01
```

~30 lines including the proof. Self-contained. No dependency on the parent file. Ships with 1 sorry to be closed in S3.

## References

- Gauss, *Disquisitiones Arithmeticae* (1801), §78.
- Hardy & Wright, *An Introduction to the Theory of Numbers* (1979), §6.3.
- Mathlib4 `Mathlib/FieldTheory/Finite/Basic.lean` — `prod_univ_units_id_eq_neg_one`.
- Mathlib4 `Mathlib/RingTheory/ZMod/UnitsCyclic.lean` — `ZMod.isCyclic_units_iff`.
- OEIS A001783 — $\prod_{1 \leq k < n, \gcd(k,n) = 1} k \bmod n$.
