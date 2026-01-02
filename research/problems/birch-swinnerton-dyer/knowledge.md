# Knowledge Base: Birch and Swinnerton-Dyer Conjecture

## The Problem

The Birch and Swinnerton-Dyer (BSD) Conjecture connects the algebraic structure of elliptic curves to the analytic properties of their L-functions. It's one of the deepest unsolved problems in number theory.

### Core Statement

> For an elliptic curve E over Q, the rank of the Mordell-Weil group E(Q) equals the order of vanishing of L(E, s) at s = 1.

In symbols: rank(E(Q)) = ord_{s=1} L(E, s)

### Why It Matters

1. **Rational Points**: Predicts exactly how many independent rational points exist on an elliptic curve
2. **Computational**: Verified for millions of curves, provides practical predictions
3. **L-functions**: Central example of the Langlands philosophy
4. **Cryptography**: Elliptic curve cryptography relies on these structures

## Historical Context

| Year | Mathematician | Contribution |
|------|--------------|--------------|
| 1901 | Poincaré | Asked about rational points on curves |
| 1922 | Mordell | Proved E(Q) is finitely generated |
| 1965 | Birch, Swinnerton-Dyer | Formulated the conjecture via computer experiments |
| 1977 | Coates-Wiles | Proved BSD for CM curves with L(E,1) ≠ 0 |
| 1995 | Wiles | Proved modularity (key for BSD progress) |
| 2001 | Taylor et al. | More cases of BSD |

The conjecture emerged from early computer calculations at Cambridge in the 1960s.

## What This Means

### The Algebraic Side: E(Q)

An elliptic curve E over Q is a smooth cubic curve like y² = x³ + ax + b. The rational points E(Q) form a finitely generated abelian group:

E(Q) ≅ Z^r × (torsion)

The **rank** r tells us how many independent rational points of infinite order exist.

### The Analytic Side: L(E, s)

The L-function L(E, s) encodes information about how E reduces modulo primes. It's defined by an Euler product for Re(s) > 3/2 and has analytic continuation to all of C.

### The Connection

BSD says these completely different objects encode the same information:
- rank(E(Q)) = 0 ⟺ L(E, 1) ≠ 0
- rank(E(Q)) = 1 ⟺ L(E, 1) = 0, L'(E, 1) ≠ 0
- And so on...

## What We Could Build

### In Mathlib Now

| Component | Status | Notes |
|-----------|--------|-------|
| Elliptic curves | ✅ | Well-developed |
| Group structure | ✅ | E(K) is a group |
| Torsion subgroup | ⚠️ Partial | Some results |
| Mordell-Weil | ⚠️ Partial | Finite generation |
| L-functions | ❌ | Not available |

### Tractable Partial Work

1. **Basic Properties of E(Q)**
   - Torsion subgroup computations
   - Group law implementations

2. **Weak BSD Statement**
   - Axiomatize L(E, 1) = 0 ⟺ rank > 0
   - Prove consequences assuming BSD

3. **Specific Curve Verification**
   - For E: y² = x³ - x, verify rank = 0 and L(E,1) ≠ 0
   - For E: y² = x³ - 4x, verify rank = 1

4. **Modularity Connection**
   - State that E is modular (Wiles et al.)
   - Connect modular forms to L-functions

## Formalization Challenges

### Primary Blocker: L-functions

Defining L(E, s) requires:
1. **Reduction types** - Good, multiplicative, additive reduction mod p
2. **a_p coefficients** - #E(F_p) = p + 1 - a_p
3. **Euler product** - L(E, s) = ∏_p (1 - a_p p^{-s} + p^{1-2s})^{-1}
4. **Analytic continuation** - Extending past Re(s) = 3/2

### Secondary Blocker: Full Mordell-Weil

Computing ranks requires:
- Height pairings
- Descent methods
- Tate-Shafarevich group analysis

## The Full BSD Formula

The complete conjecture predicts not just the rank, but also:

L^(r)(E, 1) / r! = (Ω · Reg · ∏ c_p · |Sha|) / |E(Q)_tors|²

Where:
- Ω = real period
- Reg = regulator (determinant of height pairing)
- c_p = Tamagawa numbers
- Sha = Tate-Shafarevich group
- E(Q)_tors = torsion subgroup

## Key References

- Birch, B., Swinnerton-Dyer, H.P.F. (1965). "Notes on elliptic curves II"
- Silverman, J. (1986). "The Arithmetic of Elliptic Curves"
- Wiles, A. (1995). "Modular elliptic curves and Fermat's Last Theorem"
- Gross, B., Zagier, D. (1986). "Heegner points and derivatives of L-series"

## Scouting Log

### Assessment: 2026-01-01

**Current Status**: BLOCKED - Requires L-functions for elliptic curves

**Blocker Tracking**:
| Infrastructure | In Mathlib | Last Checked |
|----------------|------------|--------------|
| Elliptic curves | Yes | 2026-01-01 |
| Mordell-Weil | Partial | 2026-01-01 |
| E-L-functions | No | 2026-01-01 |
| Modularity | No | 2026-01-01 |

**Path Forward**:
1. State BSD as an axiom with well-defined terms
2. Prove consequences of BSD for specific curves
3. Build verification framework for computational checks

**Next Scout**: Track Mathlib elliptic curve and L-function development
