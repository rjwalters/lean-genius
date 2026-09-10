# H3 exact local Galois measures (2026-09-10)

Both H3 support profiles admit exact nonnegative local spectral measures for the fixed degree-42 polynomial in the reviewed sixth-moment note:

    psi=(x-3)^4(x+2)^4(x²-x-7)(x²-6)^4(x²+x-7)^2(x²+x-5)^10.

This is a necessary-condition relaxation control, not a graph or joint matrix realization. It closes the diagonal moments through six plus rational conjugate-weight test as a rejection route for this particular candidate. It does not close arbitrary-spectrum search or the Erdős-85 problem.

## Exact data and verification

Run `python3 verify_q7_h3_local_galois_measures.py` (SymPy required). The verifier uses exact rational arithmetic and no optimizer; the JSON supplies rational aggregate weights and positive integer type counts. It reconstructs all targets rather than trusting stored moment targets.

The polynomial has residual power sums -7,255,-106,1767,-947,13470. Thus T=29 low triangles, R=274 mixed overlap, and tr(D³)=36 (six defect triangles). The two support censuses are (25,18,3,0) and (24,21,0,1). In each case the integer type counts satisfy sum tau=87, sum local R=274 and sum delta=18.

For a quadratic x²+a x+b with discriminant d, roots are ordered increasingly. The JSON coordinates (u,v) encode weights u-v sqrt(d), u+v sqrt(d). The verifier checks either u=v=0 or u>0 and u²>d v². Linear-factor coordinates are nonnegative. Summed over types, u equals the factor multiplicity and v sums to zero. Weights are aggregated over the positive integer count n of a type; dividing by n gives its local measure. This checks rational/Galois compatibility as well as positivity.

## Local targets

For h=3, let U=[1,t], Q=[[7,3],[-1,0]], and G=UᵀU=[[46,24],[24,30]]. For a vertex with high incidence t, put u=[1,t], q_j=u Q^j G^-1 uᵀ and z=t(3-t)/21. Here z is the zero-C high-difference projector diagonal. On that sector D=-I; on the quotient D=Q-I; on the residual space D=6I-C².

With tau the number of all-low triangles at the vertex, local R=(CD²)vv, and delta the number of D-triangles at the vertex, residual diagonal moments are:

    r0=1-q0-z; r1=-q1; r2=7-t-q2; r3=2tau-q3;
    r4=(7-t)(13-t)-3-q4;
    r5=R+12r3-36r1-u Q(Q-I)² G^-1 uᵀ;
    r6=216r0-108r2+18r4+u(Q-I)³G^-1 uᵀ-z-2delta.

The fourth diagonal follows from C4-freeness: (C⁴)vv=d_C(v)²+sum_{w~C v}(d_C(w)-1), using d_C=7-t and Ct=3. The fifth follows by expanding C(6I-C²)² on the residual space; the sixth follows from (6I-C²)³. Quotient contributions and the D=-1 sector give the displayed corrections.

The verifier also checks the local matching constraint 0<=7-2t-2tau<=6-t, survivor count m=t+2tau-1, even local R between zero and 2 ex(C4,m), and 0<=delta<=choose(6-t,2). For m=0..5 the bound table is 0,0,1,3,4,6. The verified witness uses only the permitted local types.

## Discovery and limits

Numerical local feasibility and integer census discovery selected counts. An initial strict-positivity LP returned zero because a complete collection of quadratic sectors vanishes at one type. Maximizing individual weights identified that face; the remaining weights had positive slack. Rational affine reconstruction then produced the exact certificate. The standalone verifier canonicalizes conjugate roots by increasing order, independently of SymPy's solve-list order.

The data does not impose off-diagonal integrality, rank-one constraints for simple eigenvalues, simultaneous projector orthogonality, higher local walk moments, or adjacency entries in {0,1}. Those remain possible obstructions. No Lean theorem or profile exclusion is claimed here.
