# Abel-Ruffini Galois Theory Extensions - Knowledge

## Problem
Extend the Abel-Ruffini theorem formalization with explicit proofs connecting
solvability by radicals to group-theoretic solvability, and characterizing
the degree-5 threshold.

## Status: COMPLETED

The file has been fully formalized with 44+ theorems, 0 sorries, 0 axioms.
All original goals have been achieved.

## Key Results

### Proved Theorems (44+ theorems, 0 sorries, 0 axioms)

**Part I: Small Symmetric Groups Are Solvable**
- `perm_fin_0_solvable`: S₀ is solvable (trivial)
- `perm_fin_1_solvable`: S₁ is solvable (trivial)
- `perm_fin_2_solvable`: S₂ is solvable (abelian via `perm_fin_2_comm`)
- `perm_fin_3_solvable`: S₃ is solvable (via A₃ → S₃ → ℤˣ)
- `perm_fin_4_solvable`: S₄ is solvable (via A₄ → S₄ → ℤˣ)
- `alternating_fin_3_solvable`: A₃ is solvable (abelian)
- `alternating_fin_4_solvable`: A₄ is solvable (via V₄ → A₄ → A₄/V₄)
- `klein_four`: V₄ as subgroup of A₄ (private)

**Part II: Sharp Threshold**
- `symmetric_not_solvable_of_five_le`: S_n not solvable for n ≥ 5
- `symmetric_solvable_of_le_four`: S_n is solvable for n ≤ 4
- `symmetric_solvable_iff`: Complete iff characterization

**Part III: Alternating Group Structure**
- `a5_simple`: A₅ is simple
- `card_a5`: |A₅| = 60

**Part IV: Connection to Radical Solvability**
- `not_solvable_by_rad_of_not_solvable_galois`: Contrapositive Abel-Ruffini

**Part V: Galois Extension Properties**
- `galois_group_order`: |Gal(E/F)| = [E:F]

**Part VI: Subgroup Solvability**
- `subgroup_solvable_of_solvable`: Subgroups of solvable groups are solvable

**Part VII: Alternating Group Non-Solvability**
- `alternating_not_solvable_of_five_le`: A_n not solvable for n ≥ 5
- `alternating_solvable_of_le_four`: A_n is solvable for n ≤ 4
- `alternating_solvable_iff`: Complete iff characterization

**Part VIII: Cardinalities**
- `card_s2`, `card_s3`, `card_s4`, `card_s5`: |S_n| = n!
- `card_a3`, `card_a4`: |A_n| = n!/2
- `card_s0`, `card_s1`: |S_0| = |S_1| = 1

**Part IX: Solvability Preservation**
- `quotient_solvable_of_solvable`: Quotients of solvable groups are solvable
- `solvable_of_mul_equiv`: Solvability preserved under isomorphism

**Part X: Index and Structure Theorems**
- `a5_not_solvable`: A₅ is not solvable

**Part XI: Specific Non-Solvability Results**
- `s7_not_solvable`, `s8_not_solvable`: S₇, S₈ not solvable
- `a6_not_solvable`, `a7_not_solvable`: A₆, A₇ not solvable
- `symmetric_not_solvable_of_alternating`: Non-solvable A_n implies non-solvable S_n

**Part XII: Solvable Group Chain Properties**
- `commutator_solvable`: Derived subgroup of solvable group is solvable
- `sign_kernel_is_alternating`: ker(sign) = A_n
- `solvable_small_has_abelian_factors`: S_n, A_n solvable for n ≤ 4

**Part XIII: Non-Commutativity Witnesses**
- `s3_not_comm`, `s4_not_comm`, `s5_not_comm`: S₃, S₄, S₅ non-abelian
- `a4_not_comm`, `a5_not_comm`: A₄, A₅ non-abelian

### Theorem Structure
The theorems form the complete Abel-Ruffini picture:
1. **Solvability classification**: S_n (and A_n) solvable iff n ≤ 4
2. **Galois connection**: Unsolvable Galois group ⟹ not solvable by radicals
3. **Obstruction**: A₅ is simple (the first non-abelian simple group)
4. **Infrastructure**: Cardinalities, preservation theorems, chain properties

## Previous Iterations

### Iteration 2 Progress (2026-02-04)
- Verified file is complete with 44+ theorems, 0 sorries, 0 axioms
- All S₀, S₁, S₂, S₃, S₄ solvability instances already proved
- All A₃, A₄ solvability instances already proved
- Complete iff characterizations for both S_n and A_n
- Non-commutativity witnesses for S₃, S₄, S₅, A₄, A₅
- Status: COMPLETED

### Iteration 1 Progress (2026-02-03)
- Initial formalization with core theorems

## Future Extensions (Optional)
- Construct explicit polynomial with Galois group S₅
- Formalize the specific unsolvability of x⁵ - x - 1
