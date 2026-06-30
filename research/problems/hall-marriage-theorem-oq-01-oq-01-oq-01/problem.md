# Problem: Closed-Form Maximum Partial Transversal Size via Hall Deficiency

**Slug**: hall-marriage-theorem-oq-01-oq-01-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For a finite family $t : \iota \to \text{Finset}\,\alpha$, define the **deficiency**

$$
\delta \;=\; \max_{s \subseteq \iota} \bigl( |s| - |\textstyle\bigcup_{i \in s} t(i)| \bigr) .
$$

Then the maximum size of a partial transversal (a partial system of distinct representatives, i.e. an injective partial choice function) equals

$$
\max\text{-partial-transversal size} \;=\; |\iota| - \delta .
$$

Equivalently, packaging the deficiency as an explicit `Finset.sup` over the powerset turns Mathlib's `Finset.all_card_le_biUnion_card_iff_exists_injective` / deficiency form of Hall's theorem into a closed-form cardinality statement.

### Plain Language

Hall's marriage theorem says a perfect matching (a full system of distinct representatives) exists exactly when **no** subset $s$ of the index set has its combined neighbourhood smaller than $s$ itself. The *deficiency* version refines this: even when a perfect matching fails, the largest partial matching you can achieve falls short of the ideal $|\iota|$ by exactly the worst-case shortfall $\delta = \max_s(|s| - |\bigcup_{i\in s} t(i)|)$. This problem asks to formalize that closed form — that the maximum number of indices you can simultaneously and distinctly represent is precisely $|\iota| - \delta$ — with $\delta$ written as a concrete `Finset.sup` so the bound is computable.

### Why This Matters

The deficiency formula is the quantitative heart of matching theory (König–Egerváry, defect Hall) and underlies flow/assignment bounds throughout combinatorial optimization. The qualitative Hall criterion is already in Mathlib; turning it into the explicit "$|\iota| - \delta$" maximum gives an immediately reusable, decidable bound and makes the parent entry's `deficiency_matching_iff` into a self-contained extremal statement rather than a conditional one.

## Known Results

### What's Already Proven

- Parent `hall-marriage-theorem-oq-01-oq-01` (verified): a `deficiency_matching_iff`-style characterization of when a full matching exists.
- Mathlib: `Finset.all_card_le_biUnion_card_iff_exists_injective` (Hall's theorem), `Finset.biUnion`, `Finset.sup`, and powerset machinery.
- Classical: the defect form of Hall's theorem (maximum matching $= |\iota| - \max_s(|s| - |N(s)|)$).

### What's Still Open

- A Lean definition of $\delta$ as `Finset.sup (Finset.powerset Finset.univ) (fun s => |s| - |s.biUnion t|)` (over $\mathbb{Z}$ to avoid truncated subtraction), and the theorem `maxPartialTransversal t = Fintype.card ι - δ`.
- Connecting the closed form back to the parent's `deficiency_matching_iff` ($\delta = 0 \iff$ full matching).

### Our Goal

Define the deficiency as an explicit `Finset.sup` over the powerset of $\iota$ (in $\mathbb{Z}$), then prove the maximum partial-transversal cardinality equals $|\iota| - \delta$, recovering the parent's matching criterion as the special case $\delta = 0$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| hall-marriage-theorem-oq-01-oq-01 | Direct parent; deficiency matching criterion | Hall's theorem, biUnion bounds |
| hall-marriage-theorem-oq-01 | Root entry; Hall's marriage theorem | systems of distinct representatives |

## Initial Thoughts

### Potential Approaches

1. **Reduce to an augmented Hall instance.** Add $\delta$ "universal" dummy targets so that the augmented family satisfies Hall's condition exactly; a full matching of the augmented family restricts to a maximum partial transversal of size $|\iota| - \delta$.
   - Why it might work: this is the standard defect-Hall reduction and lets us reuse Mathlib's existing existence theorem as a black box.
   - Risk: constructing the augmented target family in `Finset` form and tracking cardinalities through the reduction.

2. **Direct `Finset.sup` bookkeeping.** Define $\delta$ over $\mathbb{Z}$ (signed, to dodge `Nat` subtraction), prove the upper bound $\text{size} \le |\iota| - \delta$ from the witnessing worst-case $s$, and the matching lower bound by induction mirroring the parent's proof.
   - Why it might work: keeps everything in one file and aligned with the parent's induction.
   - Risk: the lower bound essentially re-runs the Hall induction; may duplicate the parent's effort.
