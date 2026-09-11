# Residual order-three constraints at N78/F3

Assume the accepted2179 tight normal form for a hypothetical C4-free minimum-degree-nine graph on78 vertices with an order-three automorphism fixing exactly3 vertices. The fixed set is independent. Its three attached groups B_u each consist of three free3-orbits labelled0,1,2, with internal matching between labels1and2 and label0 isolated. Between attached groups are equivariant perfect matchings, inducing inverse-paired permutations pi_uv of the three labels. The residual graph R is6regular on48 vertices, with a free order-three action and16 residual orbits. Every residual vertex has exactly one neighbor in each B_u.

## Quotient and colors

Let Q be the symmetric16-by16 residual quotient. Its row sums are6; diagonal entries are0or2; cross entries are0,1or2. A cross3 block contains K3,3. Each residual orbit P has three colors c_u(P), from its attached neighbors. Each coordinate has orbit multiplicities(6,5,5), because attached label0 vertices have6 residual neighbors while labels1and2 vertices have5.

For distinct residual orbits P,T let a(P,T) count equal colors, from0 through3. A vertex of P has exactly (Q^2)_PT residual-middle two-walks into T and exactly a(P,T) attached-middle two-walks. C4-freeness makes their endpoints distinct, hence

    (Q^2)_PT + a(P,T) <= 3.

For P=T, the three attached neighbors supply only return walks. Q^2 supplies6 residual return walks and at most2 nonreturn endpoints in P. Thus

    (Q^2)_PP <= 8.

Since sum Q_PZ=6 and entries lie in{0,1,2}, squared norm minus row sum is twice the number of double entries. Each row has at most one double entry and at least5 positive entries. Its possible profiles are six cross singles; a cross double plus four cross singles; or a diagonal double plus four cross singles. Two diagonal-double indices cannot be adjacent: both are internal triangles and one cross edge, translated by the action, gives a C4.

Write w(P)=(c_0(P),c_1(P),c_2(P)) in{0,1,2}^3. Unlike the N80/F5 case, distinct residual orbits need not have distinct words: agreement3 merely forces (Q^2)_PT=0.

## Attached capacities and weighted margins

Let E be the3-by3 matrix with E_12=E_21=1 and other entries0. Let P_uv(a,b)=1 exactly when pi_uv(a)=b. For the single remaining group t and contingency T_uv(a,b)=#{P:c_u(P)=a,c_v(P)=b}, counting attached-orbit two-walk endpoints gives

    T_uv + E P_uv + P_uv E + P_ut P_tv <= 3J.

T has row/column margins(6,5,5). The total left side is16+2+2+3=23, so total slack is4, just as in the N80/F5 attached inequality.

For any word w, set e_u=1[w_u != 0] and bar(1)=2,bar(2)=1, and define

    b_(u,a)(w) = 3 - 1[e_u=1 and a=bar(w_u)]
                    - sum_(v!=u) 1[pi_vu(w_v)=a].

For a residual orbit P carrying w, put n_(u,a)(P)=sum_(Z:c_u(Z)=a) Q_PZ. Counting two-walks from P to attached orbit(u,a) gives n<=b. Sum_a n=6 and sum_a b=7-e_u. Consequently a nonzero coordinate forces n=b in all three labels; at a zero coordinate the nonnegative integral slack b-n sums to1. Every occurring word has b>=0.

## A repeated word occurs at most three times

If distinct P,T carry the same word then a(P,T)=3, so (Q^2)_PT=0. Symmetry and nonnegativity imply their positive row supports are disjoint: (Q^2)_PT=sum_Z Q_PZ Q_TZ. Every such support has at least5 members in a universe of16 orbit indices. Thus a word occurring r times satisfies5r<=16, hence r<=3.

In particular the16 residual orbits use at least6 of the27 possible words. This counts multiplicity of orbit colors, not vertices, and does not assert all words are different.

## Triple multiplicity forces balanced margins at every nonzero coordinate

Suppose exactly three residual orbits carry w and fix a coordinate u where w_u is nonzero. Their weighted color margins are all b=(b_0,b_1,b_2), with sum b=6 and 0<=b_a<=3. Their row supports are pairwise disjoint. Each row has at most one double entry, so all three rows together have at most three double entries. If d_a counts their double entries at columns of color a, the total weighted mass in that color is at most s_a+d_a, where s=(6,5,5). Hence

    sum_a max(0,3*b_a-s_a) <= sum_a d_a <= 3.

The only integer b in{0,1,2,3}^3 with sum6 satisfying this inequality is(2,2,2). Indeed a component3 forces deficit at least3 (at color0) or4 (at color1/2); in the former case the remaining sum3 forces another deficit at least1. Without a component3, sum6 forces all components2. Thus every nonzero coordinate of a triple-occurring word has b=(2,2,2). Equivalently its internal matching target and its two other attached-group images occupy the three distinct labels. The included arithmetic audit exhaustively checks this small implication.

These are necessary conditions for the N78/F3 case only. No enumeration of graphs, full quotient systems, colorings or permutation assignments has been run; no existence or whole-case exclusion is claimed. Free order3 at78 and F2 at80 are outside the premise.
