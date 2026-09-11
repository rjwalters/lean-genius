# Review 2315 — PASS full vertex-stabilizer bound eight

Reviewer codex-sol-1. Source PROOF.md SHA256 c5b5cca589e22e0cebf9446e7b127ee5ea757e4f32f8552f90c2b1c1e96af892. All current packet pins and four external premise hashes verified; 2207/2257/2262/2264 are resolved PASS. The order-three independence/count statement is explicit in 2207, including its accepted2176 dependency. The local involution and six-fixed-graph statements are explicit in2257. No finite or graph search was run.

## Neighborhood kernel and the star case

An order-three element of H fixes no neighbor of fixed v, so its cycles on each H-invariant neighborhood orbit have length three. The only orbit sizes dividing12 or24 and fitting inside nine are3,6; at least one size3 orbit exists. The kernel L on it has order4/8 for H24 or2/4 for H12. Each involution in L fixes those three neighbors and no other neighbor. Any nonidentity two-element-power-order member fixing a remaining neighbor has an involution power doing so, impossible. Thus L acts freely on the remaining6, forcing |L|=2. This excludes H24 and forces H12/L=S3 and central L=<tau>.

Tau fixes v,T3. If it had six fixed vertices, v would be a cubic vertex of the triangle-with-leaves graph. The automorphism group of that graph fixing v has order two, so an order-three element commuting with tau would fix all six vertices, contradicting the fixed-count bound3. Consequently tau has exactly four fixed vertices. Odd fixed degrees and C4-freeness make their graph the star centered at v. This explicitly handles rather than discards the four-fixed star.

## Group and local matching

A transposition lift with square tau would have order four and only length-four cycles on B6, since its square is free there. This is impossible. Thus such lifts are involutions. The central order-two extension of S3 splits: each three-cycle has exactly one order-three lift; these give a normal C3, and an involutive transposition lift inverts it. Therefore H=S3 x C2. Central tau prevents a size3 B orbit, so B is transitive of size6.

The order-two B stabilizer generator a is noncentral and has centralizer order4, hence fixes exactly two B points, b and tau(b). The other noncentral involution class fixes none there. Both classes act as transpositions on T and fix one T point. Tau-invariance forbids T--B edges inside N(v), and the star gives no T edges. A fully independent N(v) would require82 vertices, so B induces a perfect matching; its H-equivariance forces b paired with tau(b).

Thus a fixes the triangle v,b,tau(b) and the additional edge vt. With exactly four fixed vertices, odd degrees at b and tau(b) would force both edges to t, producing a C4. Hence a has six fixed vertices and its other two fixed vertices are the pendant leaves at b and tau(b). The three conjugates of a have fixed count6.

## Deficiency set and final contradiction

The local matching shows exactly T lies in E(v) within N(v), so E(v)=T union Z2 with Z outside the neighborhood. Tau exchanges Z, while rho of order3 fixes it pointwise. Thus Fix(rho)={v} union Z and is independent. The a-fixed pendant leaves cannot lie in Z, since they are adjacent to neighbors of v; hence a cannot fix either point of Z and must exchange both. Tau*a consequently fixes Z pointwise.

The element-type inventory of S3 x C2 gives fixed counts78,4,3,1,6,m with multiplicities1,1,2,2,3,3. For order6, Fix(tau*rho)=Fix(tau) intersect Fix(rho)={v}, since each factor is a power of the product. Burnside gives9+m/4 integral; m in{2,4,6} therefore equals4. These four fixed vertices of tau*a are exactly v,t,Z2. A point of Z has no edge to v (outside N(v)), no edge to t (zero codegree with v), and no edge to the other Z point (Fix(rho) independent). Its fixed degree is zero, contradicting the odd fixed-degree rule. This closes H12.

Divisors of48 other than1,2,3,4,6,8 either are12/24, now excluded, or contain a vertex-fixing two-subgroup of order16, excluded by2262. Thus every full vertex stabilizer has order at most8. For |A|=48 the only possible orbit sizes are6,8,12,16,24,48.

PASS paper theorem. This applies beyond the three/four-orbit cases but does not exclude all N78 graphs or prove Erdős85. No Lean formalization is claimed.
