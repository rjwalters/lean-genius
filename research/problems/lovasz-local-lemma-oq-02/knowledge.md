# Knowledge Base: lovasz-local-lemma-oq-02

**Problem**: Prove that the LLL threshold T(d) is tight: there exist instances where p = T(d) is the exact threshold.

---

## Problem Understanding

The symmetric LLL gives a sufficient condition: if every event has probability ≤ T(d) = (1/(d+1)) · (d/(d+1))^d and the dependency graph has max degree ≤ d, then a good point exists. The open question is proving that this threshold is TIGHT — i.e., for every p > T(d), there exist instances where no good point exists.

The existing gallery proof (`LovaszLocalLemma.lean`) formalizes:
- Symmetric LLL algebraic core (`symmetric_lll_bound`)
- General LLL product positivity (`general_lll`)
- The threshold formula `lllThreshold d = (1/(d+1)) · (d/(d+1))^d`
- Bridge between threshold and general LLL (`threshold_satisfies_lll`)

What's missing: a lower bound construction showing T(d) cannot be improved.

---

## Insights

### Key Mathematical Approach (Tightness via k-SAT Construction)

The standard tightness proof uses a k-uniform k-regular hypergraph construction:

1. **Construction**: Take a k-uniform hypergraph where each edge has exactly d neighbors (shares at least one vertex with d other edges). Assign a random ±1 coloring.

2. **Bad events**: For each hyperedge, the "bad event" is that all k variables in the edge have a fixed pattern (say all +1). Each bad event has probability p = (1/2)^k.

3. **The first moment argument**: For p slightly above T(d), the expected number of proper colorings (avoiding all bad events) can be shown to be sub-exponential, and using Lovász's own second moment argument or the Janson inequality, there exist instances where no proper coloring exists.

4. **Key reference**: The tightness is established by the **Shearer bound** (Shearer 1985), which gives the exact threshold for the satisfiability problem associated to LLL.

### Shearer's Theorem Connection

Shearer (1985) proved that the LLL threshold is actually given by a fixed-point equation:
- The threshold for k-SAT via LLL is exactly p* = (k-1)^{k-1} / k^k = T(k-1) when d = k-1
- This matches the symmetric LLL threshold, confirming tightness

### Lean Infrastructure Available

- `lllThreshold` is already defined in `LovaszLocalLemma.lean`
- `symmetric_lll_complete` gives the positive direction
- Need: constructive witness showing threshold cannot be improved
- Could formalize: if p > T(d) then ∃ bad hypergraph instance (existential construction)

---

## Dead Ends

### Why exact tightness is hard to formalize directly
- Proving "no good point exists" requires probability theory at measure level
- Mathlib's probability infrastructure needed for expectation arguments
- The probabilistic method's second moment technique would require `ProbabilityTheory` imports

### Possible scope reduction
- Instead of full tightness, prove: **the algebraic condition is sharp** — i.e., if x_i = 1/(d+1) exactly satisfies p_i = x_i · ∏(1 - x_j) with equality, then removing any slack breaks the bound
- This is weaker but formalizable within the current algebraic framework
