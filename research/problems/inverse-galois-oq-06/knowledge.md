# Knowledge Base: inverse-galois-oq-06

Kronecker-Weber Theorem: Can it be formalized in Lean/Mathlib?

---

## Problem Understanding

The Kronecker-Weber theorem states: every abelian extension of ℚ is contained
in a cyclotomic field ℚ(ζ_n) for some n. This is the complete solution to
Hilbert's 12th problem for ℚ.

OQ-06 asks whether this can be fully formalized. The existing file
`KroneckersJugendtraum.lean` states KW as a `Prop` but does not prove it.
The easy direction (cyclotomic ⟹ abelian) IS proved.

---

## Mathlib Gap Analysis (Session 1, 2026-03-30)

### Available in Mathlib

| Component | Mathlib Module | Status |
|-----------|---------------|--------|
| Cyclotomic fields | `NumberTheory.Cyclotomic.*` | Full support |
| Galois theory | `FieldTheory.Galois.*` | Full support |
| IntermediateField | `FieldTheory.IntermediateField.*` | Full support |
| NumberField | `NumberTheory.NumberField.Basic` | Full support |
| DedekindDomain | `RingTheory.DedekindDomain.*` | Full support |
| p-adic numbers | `NumberTheory.Padics.*` | Full support |
| Ramification groups | `RingTheory.Valuation.RamificationGroup` | Partial |
| Different ideal | `RingTheory.DedekindDomain.Different` | Available |
| Roots of unity | `RingTheory.RootsOfUnity.*` | Full support |
| Hilbert 90 | `RepresentationTheory.GroupCohomology.Hilbert90` | Available |
| Hensel's lemma | `NumberTheory.Padics.Hensel` | Available |

### **Critical Gap: Class Field Theory**

| Missing Component | Estimated Effort |
|-------------------|-----------------|
| Artin reciprocity | ~2000+ lines |
| Idele/adele groups | ~1000+ lines |
| Ray class groups | ~1000+ lines |
| Local class field theory | ~1500+ lines |
| Local Artin map | ~500+ lines |

**Total estimated gap**: ~5000-6000 lines for full class field theory

### Possible Approaches

1. **Axiomatize Artin reciprocity** (~100 lines) and prove KW from it (~500 lines)
   - Most pragmatic approach
   - Clean separation of concerns
   - Already done for related results (Hilbert9Reciprocity.lean)

2. **Minkowski bound approach** — prove KW without full CFT
   - Uses ramification theory + discriminant bounds
   - Needs: for abelian L/ℚ with Gal(L/ℚ) ≅ ℤ/pℤ, L is in some ℚ(ζ_n)
   - Still needs substantial local analysis

3. **Full class field theory** — develop the entire theory
   - Major multi-year project
   - Would enable many other results

---

## Dead Ends

(None yet — survey only)
