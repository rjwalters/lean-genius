# Problem: Finite Finset formulation of Hall's theorem connecting to Hall.Basic and König

**Slug**: halls-theorem-oq-01-oq-02
**Created**: 2026-07-02
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

**Hall's marriage theorem (finite Finset form).** Let $S : \iota \to \text{Finset } \alpha$ be a finite family of finite sets. A system of distinct representatives (an injective $f : \iota \to \alpha$ with $f(i) \in S(i)$) exists iff Hall's condition holds:

$$
\forall\, T \subseteq \iota,\quad |T| \le \Big|\bigcup_{i \in T} S(i)\Big|.
$$

Connect this to Mathlib's combinatorial `Finset.all_card_le_biUnion_card_iff_exists_injective` (the `Hall.Basic` statement) and to König's theorem on bipartite matchings.

### Plain Language

Hall's theorem characterizes when a family of finite sets admits a "matching" (a distinct representative from each set): exactly when no collection of $k$ sets is confined to fewer than $k$ total elements. This problem specializes any more abstract in-repo Hall statement to the concrete finite `Finset` version and links it to Mathlib's packaged combinatorial form and to König's theorem.

### Why This Matters

The finite `Finset` form is the version practitioners use for bipartite matching and it is the bridge to König's min–max theorem. Making the connection explicit turns the gallery's Hall entry into a directly reusable combinatorial tool.

## Known Results

### What's Already Proven

- Hall's theorem (parent) — proof `halls-theorem-oq-01` (verified).
- Mathlib `Finset.all_card_le_biUnion_card_iff_exists_injective` (`Hall.Basic`) — the finite Finset Hall statement.
- König's theorem for bipartite graphs is derivable from Hall / available in Mathlib's combinatorics.

### What's Still Open

- An explicit in-repo lemma specializing the parent to the `Finset` family form and citing `Hall.Basic`.
- The stated equivalence/derivation linking Hall's condition to König's max-matching = min-vertex-cover.

### Our Goal

State and prove the finite `Finset` version of Hall's theorem in-repo (or exhibit it as a specialization of the parent), align it with Mathlib's `Hall.Basic`, and record the derivation of König's theorem (bipartite) from it.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| halls-theorem-oq-01 | Parent: Hall's marriage theorem (verified) | Hall condition, SDR |
| halls-theorem-oq-01-oq-01 | Related Hall follow-ups / infrastructure | matchings |

## Initial Thoughts

### Potential Approaches

1. **Specialize to `Finset` families**: Instantiate the parent's abstract statement with `S : ι → Finset α` and prove it is defeq/equivalent to `Finset.all_card_le_biUnion_card_iff_exists_injective`.
   - Why it might work: Mathlib already has the exact target lemma; the work is matching hypotheses (`Fintype ι`, decidable eq).
   - Risk: reconciling the parent's phrasing (relations vs Finset-valued maps) with Mathlib's `biUnion` form.

2. **König bridge**: Model the family as a bipartite graph and derive König (max matching = min cover) from the Finset Hall statement.
   - Why it might work: standard textbook derivation; Mathlib has bipartite/`SimpleGraph` matching support.
   - Risk: graph encoding overhead; may be scoped as a follow-up if time is short.

### Key Difficulties

- Bookkeeping between "injective SDR" and "matching saturating one side."
- Ensuring finiteness/decidability instances line up with `Hall.Basic`.

### What Would a Proof Need?

- Key lemma 1: the equivalence of the parent statement with the `Finset` biUnion-cardinality condition.
- Key lemma 2: `Finset.all_card_le_biUnion_card_iff_exists_injective` invocation.
- Technical requirements: `Fintype ι`, `DecidableEq α`, Mathlib `Hall.Basic`.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- Mathlib already proves the finite Hall statement, so the "hard" theorem exists; this is a connection/specialization task.
- The König derivation is standard once Hall is in Finset form.
- Main cost is instance/hypothesis alignment, not new mathematics.

**Estimated Effort**:
- Exploration: hours–1 day
- If tractable: 2–4 days

## References

### Papers
- Hall, P. (1935), "On representatives of subsets", *J. London Math. Soc.*
- König, D. (1931), bipartite matching min–max theorem.

### Online Resources
- Wikipedia: "Hall's marriage theorem", "König's theorem (graph theory)".

### Mathlib
- `Mathlib.Combinatorics.Hall.Basic` — `all_card_le_biUnion_card_iff_exists_injective`.
- `Mathlib.Combinatorics.SimpleGraph.Matching` — bipartite matchings / König.

## Metadata

```yaml
tags:
  - combinatorics
  - halls-theorem
  - matching
  - konigs-theorem
related_proofs:
  - halls-theorem-oq-01
  - halls-theorem-oq-01-oq-01
difficulty: medium
source: proof-suggestion
created: 2026-07-02
```

**Significance**: 6/10
**Tractability**: 7/10
