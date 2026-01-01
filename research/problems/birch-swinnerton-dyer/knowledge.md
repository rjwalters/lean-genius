# Knowledge Base: birch-swinnerton-dyer

## Problem Understanding

### Core Statement
For an elliptic curve E over Q, the rank of E(Q) equals the order of vanishing of L(E, s) at s = 1.

### Formalization Requirements
1. Elliptic curves over Q
2. Mordell-Weil group E(Q)
3. L-function attached to elliptic curve
4. Analytic continuation of L(E, s)
5. Order of vanishing at central point

## Blockers

### Primary Blocker: L-functions
**Status**: BLOCKED
**Severity**: Critical

Mathlib has elliptic curves but lacks:
- [ ] L-functions attached to elliptic curves
- [ ] Analytic continuation framework
- [ ] Modularity theorem machinery

### Secondary Blocker: Mordell-Weil
The algebraic side needs:
- [ ] Full Mordell-Weil theorem with rank computation
- [ ] Height pairings
- [ ] Tate-Shafarevich group (for full BSD)

## Tractable Partial Work

1. **Basic elliptic curve properties** - Mathlib has foundations
2. **Finite rank** - Mordell-Weil finiteness
3. **Computational examples** - Verify BSD for specific curves
4. **Weak BSD** - Just rank(E) = 0 ⟺ L(E,1) ≠ 0

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| (none yet) | - |

## Scouting Log

### Initial Assessment: 2026-01-01

**Current Status**: BLOCKED - Requires L-functions for elliptic curves

**Blocker Tracking**:
| Infrastructure | In Mathlib | Last Checked |
|----------------|------------|--------------|
| Elliptic curves | Yes | 2026-01-01 |
| Mordell-Weil | Partial | 2026-01-01 |
| E-L-functions | No | 2026-01-01 |
| Modularity | No | 2026-01-01 |

**Next Scout**: Track Mathlib elliptic curve development
