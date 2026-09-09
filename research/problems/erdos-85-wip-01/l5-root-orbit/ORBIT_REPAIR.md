# Uniform repair of root-permutation arithmetic

The supplied weights' divisibility failure is repairable without changing
the five-cycle count, any unrooted count, or any moment matrix.

For the nine empty-root states in the saved certificate, let

    v = (-1,1,1,-1,1,-1,-1,1,0).

Direct polynomial multiplication proves sum_i v_i s_i s_i^T = 0 for
every q. Replace their weights w by w+2v, leaving every other state weight
unchanged. This is the degree-three alternating difference on the three
pair-common-neighbor bits (the all-three-neighbor state has coefficient0).
Its vanishing against these quadratic moments also explains the freedom.

check_orbit_repair.py verifies the polynomial identity, orbit invariance,
and nonnegativity of all repaired weights over the entire original rounding
interval. Nonnegativity uses shifted-polynomial coefficient certificates
at both endpoints, with affine interpolation between them.

For every state, let h be the order of its stabilizer in the automorphism
group of the labeled root type. After substituting error=c-c1, the repaired
weight divided by h has integer coefficient of c and a rational polynomial
constant term with denominator dividing720. At binary q>=16, the powers of
two modulo720 cycle with period12 starting at exponent4. The checker tests
all six residues for each exponent parity. Therefore every repaired weight
is divisible by h, uniformly for all relevant q and every integer c.

At q16, the two previously failing weights become7026 and11069826,
both divisible by6. The other 21 states across all four root types also
satisfy their orbit constraints. The original certified nonnegative integer
unrooted counts, eight Gram families, and local-state representations remain
valid because the moments and five-cycle choice have not changed.

This establishes feasibility of the specified relaxation with the additional
root-permutation arithmetic. It does not supply coherent assignments to
actual triples, consistency between different rooted embeddings, or a graph.
The new predicate therefore does not exclude a cofinal binary range here.
No Lean proof is claimed.

Evidence: check_orbit_repair.py, orbit-repair-check.json, and
orbit-repaired-certificate.json. The earlier ROOT_ORBITS.md accurately
describes failure of the original weights, not an obstruction to this repair.
