# H1 CUBE25: CNF-side coverage audit

Status: source-level paper derivation, not a new accepted CNF-cover certificate or Lean theorem. No solver, DRAT replay, canonical regeneration, or queue mutation was performed.

## Exact target

For the candidate base CNF in review2653, show every satisfying Boolean assignment makes at least one literal301..305 true and at least one literal456..460 true. This yields one of the25 conjunctions, with no disjointness requirement. Review2019 already binds those literal ranges to edges(4,10..14) and(9,15..19), and proves the cover for constrained graphs. The existing graph-to-CNF satisfaction theorem goes in the opposite direction from an arbitrary-assignment decoder and cannot simply be reversed.

## Smaller sufficient clause set

Only the far-degree lower bound and block at-most-one clauses for vertices4 and9 are needed. For either vertex y, oneHighFamilyFarVertices gives30 vertices partitioned into six blocks of5: omit its own block and its mate. Since y mod5=4, oneHighFamilyFarDegreeBound is6 for every profile a. oneHighFamilyAtMostOneVertexStep emits all10 negative edge pairs in each eligible block. The lower half of seqCounterEquals requires at most24 false inputs among the30 far-edge literals.

Consequently, if one eligible block has no true edge, the other five contain at most five true edges altogether. At least25 inputs are false, contradicting the lower counter. For y=4 choose block2; for y=9 choose block3. Combining the choices gives the25-cube cover directly on Boolean assignments, without constructing a graph or proving all OneHighPureFamilyCnfConstraints.

## Reverse implication of the emitted counter, independently derived

Let inputs x[0..n-1] satisfy the nontrivial at-most-t counter (0<t<n-1), with auxiliary s[k,j], 0<=k<t and0<=j<n-t. The actual generator emits:

* x[j] -> s[0,j].
* s[k,j] -> s[k,j+1] whenever j<n-t-1.
* x[j+k+1] and s[k,j] -> s[k+1,j] for k<t-1.
* not(x[j+t] and s[t-1,j]).

Suppose t+1 inputs are true at increasing positions p[0]<...<p[t]. Put q[k]=p[k]-k. The q[k] are nondecreasing and0<=q[k]<=q[t]<=n-t-1. The base clause forces s[0,q[0]]. Inductively, horizontal clauses propagate s[k-1,q[k-1]] to s[k-1,q[k]], and the diagonal clause at(k-1,q[k]) uses x[p[k]] to force s[k,q[k]], for1<=k<t. Propagate the last state to s[t-1,q[t]]. The overflow clause at q[t] now contradicts x[p[t]]=true. Thus every satisfying assignment has at most t true inputs, regardless of auxiliary choices.

Apply this with n=30,t=24 to the negated far-edge inputs. All indices fall in the nontrivial core range. This proof requires no assumption that auxiliaries equal the canonical counting witness. It is therefore the reverse implication absent from the existing witness-producing reification theorem.

## Scope and remaining proof obligations

The source definitions establish which clause schemas are emitted. An exact candidate-CNF certificate still needs a checked join locating those schemas and their consistent auxiliary IDs in the archived base. Merely matching a generator source or a base hash is not that join. A bounded clause-extraction verifier could check, for each of the two vertices, the60 block pair clauses and270 lower-counter clauses (6base+120horizontal+138diagonal+6overflow), using a consistent24-by6 auxiliary grid. The union has at most660 required clause occurrences. It need not inspect the upper counter, lex constraints, or the rest of the graph encoding.

The extraction verifier must bind the base SHA256, positive edge-literal IDs and input order, record clause positions and auxiliary assignments, and check every required clause occurs. The semantic paper argument then applies to arbitrary satisfying assignments. Alternatively these schema and containment arguments can be formalized in Lean; no such compilation is claimed here.

This addresses only review2653 obligation(c). Fresh canonical input identity, per-cube proof verification, VERIFIED-run provenance versus NOT-VERIFIED siblings, and a reviewed historical-evidence category revision remain independent. No H1 case is closed by this audit.
