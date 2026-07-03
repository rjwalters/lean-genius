# Research State: schroeder-bernstein-oq-03

## Current State
**Phase**: DEVELOP
**Path**: full
**Since**: 2026-07-02
**Iteration**: 4

## Current Focus
Resolve the **termination↔stability fork** before assembling the outer scheduler. Both atomic
moves exist (`domain_step_exists` cons; `augment_domain_step`/`augment_range_step` reroute), but
they trade the two properties the limit read-off needs against each other.

## Active Approach
Stage-wise finite back-and-forth (Rogers §7.4). Even/odd moves DONE and VERIFIED 0-axiom
(`augment_domain_step` Section 4k, `augment_range_step` Section 4l, both with pair-level edge
preservation). The blocker is no longer atomic — it is which move to iterate:

- **cons** (`domain_step_exists`): stable read-off (`mLookup_stable` applies directly to a cons)
  but the anchor pair is not `BuiltFrom`, so `escape_exists` cannot bound the *next* chase.
- **reroute** (`augment_domain_step`): restores `BuiltFrom` (chase re-runnable) but removes pairs,
  breaking `mLookup_stable` → forces a finite-injury stabilization argument for the read-off.

## Attempt Count
- Approaches tried: 1 (stage-wise back-and-forth), advancing across sessions.

## Blockers
Strategic fork, not a missing atomic lemma. The read-off cannot cite `mLookup_stable` mechanically
under the rerouting move. Deciding between the two moves = deciding whether `escape_exists`
(chase termination) can be reproved from a **cons-preserved** invariant weaker than `BuiltFrom`.

## Next Action (revises prior 1–4; see knowledge.md 2026-07-03 r14 for the full reduction)
1. **Test the fork first.** State `OrbitGEdged f g L` ("every occupied range point on a fresh
   anchor's forward orbit sits on a g-edge") and check (a) it implies `escape_exists`'s conclusion
   by pigeonhole on `(mRan L).length` (BuiltFrom-free: else two `f(orbit_k)` collide ⟹ a periodic
   under g∘f), and (b) it survives a `domain_step_exists` cons of `(a, chaseTarget f g a N)`.
2. If (b) holds → build the **extension-only** scheduler on `domain_step_exists`; read off `e` with
   `mLookup` + `mLookup_stable` (values immutable); prove `.Computable`; discharge the sorry. Short path.
3. If (b) fails (concrete counterexample) → finite injury is unavoidable; commit to the rerouting
   scheduler and build the stabilization lemma (bound f↔g flips per point via the edge-preservation
   conjuncts). Long path. Record the counterexample either way.
4. Then coverage (`firstMissing_le_length`, `k ∈ mDom` by stage `2k+1`) + computable read-off.
