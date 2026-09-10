# Bipartite defect components split the high-pair graph — 2026-09-10

Owner: codex-sol-2. Status: paper derivation, pending independent review.
No profile is excluded. No claim of novelty pending the prior-filter inventory.
This extends the component review in squad42599/42602 and uses the checked
[block identities](Q7_BLOCK_IDENTITY_REVIEW_20260910.md).

## Statement and assumptions

Use the actual q7 block setup with h in {1,3,5,7}, low defect D, incidence B,
and t=B^T1. For a D-component S, suppose its high-pair graph is r-regular:
its vertices are the h high vertices, and an edge ij means their unique
common low neighbor belongs to S. The graph is simple by C4-freeness.

**Necessary condition:** if S is bipartite, then 4 divides r.
In particular the H3 component containing the shared pairs (r=2) is
nonbipartite. This also recovers nonbipartiteness for the H7/T0 connected
component (r=6), already obtained in sol3's worksheet by half-moment counts.
The condition alone supplies no restriction when r=0 or4.

## Proof

Put a=(7+sqrt(49-4h))/2 and rho=a-1. The positive vector z=a1-t satisfies
Dz=rho*z. On the rational invariant space U=span(im B^T,1), D has only
possible eigenvalues -1, rho, and rho'=(5-sqrt(49-4h))/2: the high-difference
subspace has eigenvalue-1, and span(1,t) has polynomial x²-5x+h-6.
Here rho>1, and -rho differs from all three eigenvalues. For the last claim,
rho+rho'=5, so rho'=-rho is impossible.

If S has bipartition X,Y, let epsilon be1 on X, -1 on Y and0 elsewhere.
Then v=epsilon*z is a -rho eigenvector of D. Symmetry of D and the invariant
space decomposition imply v is orthogonal to U. In particular

    0 = Bv = a B epsilon - B(epsilon*t).

Both vectors on the right have integer coordinates, while a is irrational
(the discriminants45,37,29,21 are nonsquares). Therefore each is zero:
B epsilon=0 and B(epsilon*t)=0. Thus, for each high i, both the number of
incident low vertices and the sum of their support sizes split equally
between X and Y. Subtracting the two equalities shows that

    sum_(v in X, i in support(v)) (t_v-1)
      = sum_(v in Y, i in support(v)) (t_v-1) = r/2.

Each side is the degree of i in the simple high-pair graph whose pair witness
lies on that side. These are two r/2-regular graphs on the odd number h of
vertices. The handshaking identity makes h*r/2 even, hence r/2 even. This
proves4|r. Triple-support witnesses contribute a triangle to the high-pair
graph, so they are included without changing the argument.

## H3 component review and a scope guard

Sol1's necessary component-size lists independently check out. Summing
DB^T=J-B^T on S gives |S|=6k_i-r_i, where k_i is the count of support-i
vertices in S and r_i is its high-pair degree. For h3, 0<=r_i<=2 makes all
k_i equal and all r_i equal. A regular graph on3 high vertices has degree0
or2. Consequently all shared pairs lie in one component, of size6k-2;
other components have size6k. Degree parity forces k positive even.
The total k across components is8.

The positive-Perron multiplicity argument makes the H3 component count odd:
all but the global rho eigenvector lie in K, where C²=6I-D; the irreducible
quartic x4-7x2+3 forces that extra multiplicity even. Hence the candidate
partitions are46 or12+12+22, with10+12+24 additionally allowed in the triple
profile. In the pair profile, the10-vertex case would have no singleton
support. A pair-support vertex would then require a D-neighbor supplying
its missing high, but every available such pair overlaps its support and
cannot be D-adjacent. This excludes that case only.

**Do not extend that positive-Perron quartic argument unchanged to h1:**
x4-7x2+1=(x²-3x+1)(x²+3x+1). Exact SymPy1.14.0 checks give irreducibility
for h3,5,7, not h1. By contrast, x4-17x2+60+h is irreducible for all four
h; thus the separate negative-Perron argument for an even number of
bipartite D-components survives in each case.

Combining the H3 results: its shared-pair component is nonbipartite; if
there are three components, the other two are either both bipartite or
both nonbipartite. These remain necessary conditions, not graph witnesses
or an exclusion of H3. No Lean theorem was produced for this note.
