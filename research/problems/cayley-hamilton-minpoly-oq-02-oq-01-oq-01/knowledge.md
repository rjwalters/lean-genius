# Skolem-Noether for Mn(K): Proof Strategy

## Status: ORIENT (proof strategy complete, implementation pending)

## Key Discovery: No Artin-Wedderburn Needed

The standard proof of Skolem-Noether uses Artin-Wedderburn theory (uniqueness of
simple modules over simple Artinian rings), which is NOT in Mathlib.

However, for Mn(K) specifically, there is an **elementary proof using matrix units**
that only requires basic linear algebra available in Mathlib.

## Elementary Proof via Matrix Units

Given φ : Mn(K) ≃_K Mn(K), we construct an invertible P with φ = conj(P).

### Step 1: Matrix Unit Images
Let E_ij = Matrix.single i j 1 (standard matrix units).
Let f_ij = φ(E_ij).

Since φ is a K-algebra homomorphism and E_ij * E_kl = δ_jk * E_il:
  f_ij * f_kl = δ_jk * f_il

### Step 2: Choose Reference Vector
f_{i0,i0} ≠ 0 (by injectivity of φ and E_{i0,i0} ≠ 0).
Choose v0 with f_{i0,i0} · v0 ≠ 0 (nonzero matrix has nonzero column action).

### Step 3: Define Column Vectors
p_j = f_{j,i0} · v0 for all j.

Key property (from Step 1):
  f_ij · p_k = δ_jk · p_i

### Step 4: Nonzero Vectors
If p_j = 0, then f_{i0,j} · p_j = p_{i0} = 0, contradicting v0 choice.

### Step 5: Linear Independence
If ∑ c_j p_j = 0, apply f_{kk}: c_k p_k = 0, so c_k = 0.

### Step 6: Matrix P is Invertible
P with columns p_j has linearly independent columns → det P ≠ 0 → P is a unit.

### Step 7: Intertwining
For all i,j: (f_ij * P)_{ab} = (P * E_ij)_{ab}
This follows entry-wise from the hfp property.

### Step 8: Conclusion
P * M = φ(M) * P for all M (by linearity from Step 7).
So φ(M) = P * M * P^{-1} = conj(P^{-1})(M). QED.

## Lean4 Implementation Notes

### Working API Names (verified against this Mathlib version)
- `Matrix.single i j c` — matrix unit (via Pi.single)
- `Pi.single_apply` — entry of Matrix.single
- `Matrix.single_mul_single_same` — E_ij * E_jk = E_ik
- `Matrix.mul_apply` — (M*N)_{ij} = ∑ M_{ik} N_{kj}
- `Matrix.mulVec_mulVec` — M(Nv) = (MN)v
- `Matrix.zero_mulVec` — 0v = 0
- `Matrix.mulVec_zero` — M0 = 0
- `Finset.sum_ite_eq` — extract term from conditional sum
- `linearIndependent_iff'` — coefficient extraction form

### Known Issues
- `Matrix.single_apply` does NOT exist — use `Pi.single_apply` (twice)
- `Matrix.single_mul_single_of_ne` has unexpected type signature — use ext + split_ifs instead
- `Matrix.dotProduct` may not exist — use `Matrix.dotProduct` or just unfold
- `Matrix.mulVec_sum` may not exist — use manual distribution via add_mulVec
- For invertibility: try `basisOfLinearIndependentOfCardEqFinrank` or `Matrix.isUnit_iff_isUnit_det`

### Recommended Approach for hf_mul
```lean
ext a b
simp only [Matrix.mul_apply, Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
split_ifs <;> simp -- or <;> first | rfl | exact absurd ‹_› h
```

### Recommended Approach for hP_isUnit
Construct a Basis from hp_li using `basisOfLinearIndependentOfCardEqFinrank`,
then use the basis to show the change-of-basis matrix is a unit.
