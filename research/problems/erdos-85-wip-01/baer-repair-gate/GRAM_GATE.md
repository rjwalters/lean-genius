# No loopless repair preserving the restored-loop Gram matrix

**Theorem.** For any odd integer r>=3, put q=r², h=q-r, m=q+r+1, and
N=mh=q²-r. There is no simple q-regular graph on N vertices partitioned
into m groups of size h such that distinct vertices in the same group have
zero common neighbors and vertices in different groups have exactly one.

This rules out a repair that preserves the square of the Baer-deletion
matrix **with its exterior absolute loops restored**. The loopless deficient
seed H in NOTE.md does not itself have this common-neighbor pattern.
Arbitrary repairs are not required to preserve the pattern and are not
excluded by this theorem. No Erdős85 or general odd-degree closure is claimed.

## Equitable quotient, proved directly

Suppose A is such a graph's adjacency matrix, and let K be block diagonal
with one h-by-h all-ones block per group. Then

    A²=qI+J-K.

Since A is regular, it commutes with J, and therefore with K=qI+J-A².
For x in group i and y in group j, (AK)_xy is the number of neighbors of
x in group j; (KA)_xy is the number of neighbors of y in group i. Equality
for every x,y proves that these numbers are constant within the groups and
symmetric in i,j. Write R for this integral, nonnegative, symmetric quotient.
It has row sum q. Restricting A² to group-constant vectors gives

    R²=(q-h)I+hJ=rI+hJ.

For each row i, sum_j R_ij²=(R²)_ii=r+h=q=sum_j R_ij. Each integer term
R_ij(R_ij-1) is nonnegative, so every R_ij is0 or1.

This is the standard equitable-quotient mechanism for divisible design
graphs; compare Theorem3.1 in
[Haemers, Kharaghani and Meulenberg, Divisible Design Graphs](https://www.cs.uleth.ca/~hadi/research/ddg-v4.pdf).
The proof here supplies all hypotheses directly, without assuming a design
completion or a particular projective plane.

## Triangle parity forces the wrong quotient diagonal

Fix a vertex v in group i. It has R_ii neighbors inside its group and
q-R_ii outside. An edge inside the group belongs to no triangle, whereas
an edge joining groups belongs to exactly one triangle, by the common-neighbor
conditions. Summing common-neighbor counts over neighbors of v counts twice
the number of triangles through v. Hence q-R_ii is even. Since q is odd
and R_ii is0 or1, R_ii=1 for every i.

Put C=J-R. This is a symmetric zero-diagonal 0/1 matrix, with row sum
m-q=r+1. The quotient identity gives

    C²=(J-R)²=rI+(m-2q+h)J=rI+J.

On the constant vector C has eigenvalue r+1. On its orthogonal complement
all eigenvalues are +/-sqrt(r). Thus trace(C)=0 would give

    0=r+1+z sqrt(r),        z an integer.

If r is not a square this is impossible by irrationality. If r=s² with
integer s>1, it implies s divides s²+1, again impossible. This proves the
theorem for every odd r>=3.

## Why this is the restored-loop Baer matrix

For an odd prime-power r, let B be the full polarity incidence matrix on
PG(2,r²), retaining absolute loops. Partition the exterior vertices by their
unique neighbor in S=PG(2,r). There are m=|S| groups, each of size h=q-r:
the polar line of a subplane point has q+1 total points and r+1 in S.

Let L be the principal submatrix of B on exterior vertices, retaining its
absolute loops, and let U be the exterior-to-subplane incidence block.
The full identity B²=qI+J gives

    L²=qI+J-UUᵀ=qI+J-K,

because each row of U has a single1, and two rows have that1 in the same
column exactly when their vertices belong to the same group. L has row
sum q and q-r loops. The theorem proves that no simple q-regular adjacency
matrix A can have A²=L². This excludes arbitrary square-preserving switches,
not merely swaps induced by geometric automorphisms. It does not forbid
changing L² as part of a larger repair.

`gram_check.py` verifies the restored-loop identity and quotient on the
deterministic q25 seed. It is a check of the dictionary; the nonexistence
theorem is the uniform proof above, not a finite computation. No Lean
formalization is claimed.
