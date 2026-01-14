# Motivic Flag Maps - Formalization Roadmap

## Current State

**Axioms: 2** (down from implicit many)
- `motivicClassBasedMaps` — existence of moduli space motivic class
- `motivic_class_flag_maps` — main theorem (Bryan-Elek-Manners-Salafatinos-Vakil 2025)

**Proven:**
- `projective_class_formula` — (L-1)·[P^n] = L^{n+1} - 1
- `GL1_class`, `GL2_class` — explicit formulas
- `Fl1_class`, `Fl2_class` — explicit formulas
- `computeA_n1`, `computeA_n2` — dimension formula special cases

## Goal: Reduce Axiomatization

The main theorem is a deep result in algebraic geometry. Full formalization from first principles requires infrastructure not yet in Mathlib (moduli spaces, intersection theory, motivic integration). However, we can make the proof structure more transparent and reduce the "axiom gap."

## Roadmap

### Phase 1: Transparent Proof Structure (In Progress)

**1.1 Decompose Main Axiom into Fiber Class Formula**

The paper proves the theorem via a tower decomposition where each fiber has class:
```
[fiber of π_k] = L^{(k+1)d_k - kd_{k+1} - k} · (L^k - 1)
```

Replace the monolithic main axiom with:
- [ ] `fiberClassFormula` axiom — the single clean formula
- [ ] `motivic_class_from_fibers` theorem — derives main result from fiber axiom

**1.2 Add Stratification Structure**

- [ ] `SplittingType` structure — Birkhoff-Grothendieck decomposition data
- [ ] `nowhereVanishingClass` — the key Prop 2.3 from the paper
- [ ] Document tower structure: Ω²_{d_n,...,d_1} → ... → Ω²_{d_n}(P^n)

### Phase 2: More Special Cases

**2.1 GL_n Cases**
- [x] `GL1_class`: [GL_1] = L - 1
- [x] `GL2_class`: [GL_2] = (L-1)(L²-1)·L
- [ ] `GL3_class`: [GL_3] = (L-1)(L²-1)(L³-1)·L³
- [ ] `GL4_class`: [GL_4] = (L-1)(L²-1)(L³-1)(L⁴-1)·L⁶

**2.2 Flag Variety Cases**
- [x] `Fl1_class`: [Fl_1] = 1
- [x] `Fl2_class`: [Fl_2] = 1 + L
- [ ] `Fl3_class`: [Fl_3] = (1)(1+L)(1+L+L²)
- [ ] `Fl4_class`: [Fl_4] = (1)(1+L)(1+L+L²)(1+L+L²+L³)

**2.3 Dimension Formula Cases**
- [x] `computeA_n1`: a = d(d+1)/2 for n=1
- [x] `computeA_n2`: verified for n=2
- [ ] `computeA_n3`: verify for n=3
- [ ] Verify specific β: (1,1), (1,1,1), (2,1), etc.

### Phase 3: Cell Decomposition Infrastructure

**3.1 Abstract Cell Decomposition**
- [ ] `CellDecomposition` structure — cells indexed by dimension
- [ ] `motivicClassOfCells` — sum of L^dim over cells
- [ ] Theorem: motivic class from any cell decomposition

**3.2 Bruhat Decomposition**
- [ ] `BruhatDecomposition` — GL_n = ∐_{w ∈ S_n} BwB
- [ ] `bruhat_cell_dimension` — dimension formula
- [ ] `GLn_class_from_bruhat` — derive GL_n formula

**3.3 Fiber Bundle Structure**
- [ ] `MotivicFiberBundle` structure
- [ ] `fiber_bundle_multiplicativity` axiom
- [ ] `flag_bundle` — Fl_{n+1} → Fl_n is P^n bundle
- [ ] Derive flag formula from bundle structure

### Phase 4: Connect to Mathlib

**4.1 GL_n Connection**
- [ ] Show `GLn k n ≃ GL (Fin n) k` from Mathlib
- [ ] Connect our motivic class to matrix theory

**4.2 Borel Subgroups**
- [ ] Define upper triangular matrices B ⊂ GL_n
- [ ] Define unipotent radical U ⊂ B
- [ ] Levi decomposition B = U ⋊ T

### Phase 5: Long-term Goals

**5.1 K₀(Var) Construction**
- [ ] Define varieties properly (needs Mathlib schemes)
- [ ] Construct K₀ as quotient by scissors relations
- [ ] Define ring structure from product
- [ ] Prove Lefschetz motive properties

**5.2 Full Formalization** (multi-year)
- [ ] Moduli space construction
- [ ] Stratification theory
- [ ] Prove Prop 2.3 (nowhere-vanishing section formula)
- [ ] Prove main theorem from first principles

## Aristotle Candidates

Sorries that may be amenable to automated proof search:

1. **Ring identities** — `GL3_class`, `GL4_class` proofs are just `ring`
2. **Finset computations** — `Fl3_class`, `Fl4_class` involve `simp` + `ring`
3. **Arithmetic** — `computeA` special cases

Create `MotivicFlagMaps-provable.lean` with these sorries for Aristotle submission.

## References

- **Paper**: Bryan, Elek, Manners, Salafatinos, Vakil (2025). [arXiv:2601.07222](https://arxiv.org/abs/2601.07222)
- **HTML version**: [arxiv.org/html/2601.07222v1](https://arxiv.org/html/2601.07222v1)
- **Mathlib**: [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4)

## Notes

The key insight from the paper is that the fiber class formula (Corollary 2.5) is **independent of splitting type** due to the compensating stratification by basepoint depth. This is the mathematical miracle that makes the final formula simple.

Formalizing this independence would be significant progress — it reduces the main theorem to a single clean axiom about fiber classes.
