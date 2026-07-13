# Problem: Sharpening the van der Waerden First-Moment Family Bound to n²/(k-1)

**Slug**: van-der-waerden-first-moment-oq-01
**Created**: 2026-06-27T11:33:01-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\left| \mathrm{vdwFamily}(n, k) \right| \;\le\; n \cdot \left\lfloor \frac{n-1}{k-1} \right\rfloor \;\le\; \frac{n^2}{k-1}, \qquad k \ge 2,
$$

where $\mathrm{vdwFamily}(n,k)$ is the set of length-$k$ arithmetic progressions $\{a, a+d, \dots, a+(k-1)d\}$ with positive step $d \ge 1$ that fit inside $[0,n)$, i.e. satisfy $a + (k-1)d < n$. The current gallery lemma `card_vdwFamily_le` proves only the loose bound $|\mathrm{vdwFamily}(n,k)| \le n^2$.

### Plain Language

How many arithmetic progressions of length $k$ fit inside the interval $\{0, 1, \dots, n-1\}$? Each such progression is fixed by its starting point $a$ and its common difference (step) $d \ge 1$. There are $n$ choices for $a$, and the existing proof crudely bounds the number of steps by $n$ as well, giving $n^2$. But the fitting constraint $a + (k-1)d < n$ forces $(k-1)d < n$, so the step can be at most $\lfloor (n-1)/(k-1) \rfloor$ — there are roughly $n/(k-1)$ admissible steps, not $n$. Counting the $(a,d)$ pairs with this tighter step range gives $n \cdot \lfloor (n-1)/(k-1) \rfloor \approx n^2/(k-1)$ progressions, an improvement by a factor of $k-1$.

### Why This Matters

The family bound feeds directly into the first-moment (union-bound) lower bound for van der Waerden numbers $W(k)$: if the number of length-$k$ APs in $[0,n)$ is below $2^{k-1}$, then $[0,n)$ admits a 2-colouring with no monochromatic length-$k$ AP, so $W(k) > n$. With the loose count $n^2 < 2^{k-1}$ the gallery proves $W(k) \gtrsim 2^{(k-1)/2}$. Replacing $n^2$ by $n^2/(k-1)$ improves the threshold to $n^2 < (k-1)\,2^{k-1}$, i.e. $W(k) \gtrsim \sqrt{k-1}\cdot 2^{(k-1)/2}$ — a polynomial-in-$k$ sharpening of the constant in front of the exponential. It does not change the exponential rate (that needs the Lovász Local Lemma), but it tightens the elementary bound at essentially no proof cost, and it is a self-contained combinatorial counting exercise.

## Known Results

### What's Already Proven

- `card_vdwFamily_le` (gallery `van-der-waerden-first-moment`, `Proofs/VanDerWaerdenFirstMoment.lean`) — the loose bound $|\mathrm{vdwFamily}(n,k)| \le n^2$, via `Finset.card_image_le`, `Finset.card_filter_le`, and `Finset.card_product` over the $(a,d)$ index set $\mathrm{range}(n) \times \mathrm{Icc}(1,n)$.
- `card_vdwAP` (same file) — a fitting positive-step AP has exactly $k$ elements (injectivity / no-wraparound argument); confirms the $(a,d)$-parameterization is the correct object to count.

### What's Still Open

- Prove the sharpened bound $|\mathrm{vdwFamily}(n,k)| \le n \cdot \lfloor (n-1)/(k-1) \rfloor$ by restricting the step index set from $\mathrm{Icc}(1,n)$ to $\mathrm{Icc}(1, \lfloor (n-1)/(k-1) \rfloor)$ before applying the filter/image monotonicity chain.
- Propagate the improved count into `vdw_lower_bound` to obtain the strengthened threshold $W(k) \gtrsim \sqrt{k-1}\cdot 2^{(k-1)/2}$.

### Our Goal

Add a new lemma `card_vdwFamily_le'` (or strengthen `card_vdwFamily_le`) establishing $|\mathrm{vdwFamily}(n,k)| \le n \cdot \lfloor (n-1)/(k-1) \rfloor$, and wire it into a sharpened corollary of `vdw_lower_bound`. This is purely a refinement of the AP count; the probabilistic core (the Property B first-moment engine) is untouched.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| van-der-waerden-first-moment | Parent entry; contains `card_vdwFamily_le` to be sharpened and `vdw_lower_bound` to be re-threaded | Finset cardinality bounds, AP-as-`Finset (Fin n)`, Property B instantiation |
| property-b-first-moment | The verified first-moment / union-bound engine consumed as a black box by the parent | Probabilistic method, hypergraph 2-colouring, expectation/counting |

## Initial Thoughts

### Potential Approaches

1. **Approach A — restrict the step index set**: Replace the index family $\mathrm{range}(n) \times \mathrm{Icc}(1,n)$ by $\mathrm{range}(n) \times \mathrm{Icc}(1, \lfloor (n-1)/(k-1) \rfloor)$. Every fitting $(a,d)$ satisfies $(k-1)d \le a + (k-1)d < n$, so $d \le (n-1)/(k-1)$, hence $d$ lies in the smaller `Icc`; the filtered set is therefore contained in the smaller product, and `Finset.card_image_le` + `Finset.card_filter_le` + `Nat.card_Icc` give $n \cdot \lfloor (n-1)/(k-1) \rfloor$.
   - Why it might work: it reuses the exact monotonicity chain already in `card_vdwFamily_le`, only swapping the step range and adding one `Nat.le_div_iff_mul_le` step.
   - Risk: off-by-one handling of `Nat.div` and `Icc` cardinality; the floor must be stated so the $k=1$ degenerate case (division by zero) is excluded by the $k \ge 2$ hypothesis.

2. **Approach B — sum over starts**: Bound $|\mathrm{vdwFamily}(n,k)| \le \sum_{a<n} \#\{d \ge 1 : a+(k-1)d < n\}$ and evaluate each inner count as $\lfloor (n-1-a)/(k-1) \rfloor \le \lfloor (n-1)/(k-1) \rfloor$.
   - Why it might work: gives the tightest possible $\sum_a \lfloor (n-1-a)/(k-1) \rfloor \approx n^2/(2(k-1))$ bound, an extra factor of 2.
   - Risk: more Finset-summation bookkeeping than Approach A; better saved as a follow-up once the simpler product bound lands.

### Key Difficulties

- Natural-number division and floor arithmetic in Lean: deriving $d \le \lfloor (n-1)/(k-1) \rfloor$ from $(k-1)d < n$ needs `Nat.le_div_iff_mul_le` (or `Nat.lt_succ`/`Nat.div` lemmas) with care at the $k-1 = 0$ boundary, which the $k \ge 2$ hypothesis must rule out.
- Keeping the change additive: the parent entry is `verified`/`original`, so the sharpened lemma should be a new statement that does not weaken or break the existing `card_vdwFamily_le` consumers.

### What Would a Proof Need?

- Key lemma 1: every fitting $(a,d)$ has $1 \le d \le \lfloor (n-1)/(k-1) \rfloor$ — from $(k-1)d < n$ via `Nat.le_div_iff_mul_le`.
- Key lemma 2: `Nat.card_Icc 1 m = m`, so the restricted step `Icc` has cardinality $\lfloor (n-1)/(k-1) \rfloor$; combine with `Finset.card_product`/`card_filter_le`/`card_image_le` exactly as in `card_vdwFamily_le`.
- Technical requirements: the $k \ge 2$ hypothesis (so $k-1 \ge 1$ and division is well-defined); `[NeZero n]` instance already present in the file.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- This is a self-contained counting refinement, not a new theorem: the proof skeleton (`card_image_le` → `card_filter_le` → `card_product`) already exists in `card_vdwFamily_le` and only the step-range index set and one division inequality change.
- Similar already-solved work: `card_vdwAP` and `card_vdwFamily_le` in the same file demonstrate the exact Finset-cardinality toolkit; the only new ingredient is `Nat`-division reasoning, which Mathlib supports well (`Nat.le_div_iff_mul_le`, `Nat.div_lt_iff_lt_mul`).
- Mathlib provides `Nat.card_Icc`, `Finset.card_product`, `Finset.card_filter_le`, `Finset.card_image_le`, and the `Nat.div` lemma family — everything the argument needs.

**Estimated Effort**:
- Exploration: 1–2 hours (locate the right `Nat.div` lemma, settle the floor/`Icc` formulation).
- If tractable: 1–2 days (write `card_vdwFamily_le'`, Docker-build green, thread it into a sharpened `vdw_lower_bound` corollary, update gallery meta).
- If hard: unlikely; the main risk is fiddly `Nat.div` off-by-ones rather than any genuine mathematical obstruction.

## References

### Papers
- B. L. van der Waerden, "Beweis einer Baudetschen Vermutung," 1927 — original van der Waerden theorem establishing the numbers $W(k)$.
- P. Erdős, "On a combinatorial problem," 1963 — Property B / first-moment 2-colourability, the engine the parent entry instantiates.
- W. T. Gowers, "A new proof of Szemerédi's theorem," 2001 — modern context and the best known bounds on van der Waerden / Szemerédi growth.

### Online Resources
- https://en.wikipedia.org/wiki/Van_der_Waerden_number — survey of known bounds on $W(k)$, including the probabilistic lower bounds and the Lovász Local Lemma improvement.

### Mathlib
- `Mathlib.Order.Interval.Finset.Nat` — `Nat.card_Icc` (cardinality of the restricted step interval).
- `Mathlib.Data.Finset.Card` — `Finset.card_image_le`, `Finset.card_filter_le`, `Finset.card_product` (the monotonicity/product chain reused from `card_vdwFamily_le`).
- `Mathlib.Algebra.Order.Group.Nat` / `Mathlib.Data.Nat.Defs` — `Nat.le_div_iff_mul_le` and the `Nat.div` lemma family for the step-bound inequality.

## Metadata

```yaml
tags:
  - combinatorics
  - probabilistic-method
  - van-der-waerden
  - arithmetic-progressions
related_proofs:
  - van-der-waerden-first-moment
  - property-b-first-moment
difficulty: medium
source: proof-suggestion
created: 2026-06-27T11:33:01-07:00
```
</content>
</invoke>
