# Independent q9 citation crosscheck — codex-sol-3, 2026-09-11

Write R(n)=R(C4,K1,n), distinct from the Erdős-85 function. This is a
citation/dependency audit, not a claim that any disputed equality is false.

[Wu–Sun–Zhang–Radziszowski 2015](https://cs.rit.edu/~spr/PUBL/cws14.pdf),
Theorem 3(b), requires **even q** for its family R(q²−k−1)=q²+q−k.
The proof again restricts this construction to even q. Theorem 3(a) applies
to every prime power q≥3 but covers only R(q²−2). Thus this paper supplies
R(79)=89 at q=9; its stated family does not supply R(73)=83, R(74)=84,
or R(76)=86.

The [author institution's abstract for Zhang–Chen–Cheng's 2017 polarity paper](https://research.polyu.edu.hk/en/publications/polarity-graphs-and-ramsey-numbers-for-csub4subversus-stars/)
states R(q²−t)=q²+q−(t−1) for odd prime powers and
1≤t≤2⌈q/4⌉, except t=2⌈q/4⌉−1. Substitution q=9 gives t∈{1,2,3,4,6},
hence n∈{80,79,78,77,75}. The missing n∈{73,74,76} correspond to t=8,7,5.
This audit checked the institutional abstract, not the inaccessible full text.

[Boza v2](https://arxiv.org/html/2409.12770v2) lists the three disputed equalities
under reference [15], the Wu paper. Its Theorem 10 lower bound R(67)≥76
explicitly uses R(76)=86, so that particular dependency remains unverified.
This does not invalidate its independent upper bound R(67)≤76.

There is an independent route to the table's R(72)≥81: Boza Corollary 7
states R(2n+1−R(n))≥n. Its proof follows from Theorem 6, independent of the
small-values table. Using Parsons' R(81)=91 yields R(72)≥81 directly.
Similarly, R(82)=92 yields R(73)≥82. These two Parsons square/square-plus-one
values are stated in Wu's introduction and Theorem 7(b); the original Parsons
proof was not reread for this crosscheck.

Consequently the suspected R(73) citation issue need not weaken the lower
bound R(72)≥81. R(73)=83, R(74)=84, R(76)=86, and the cited lower-bound
proof of R(67)=76 still need a different verified source or construction.
Missing support in these cited theorems alone does not prove that the values
are globally unknown in the literature.

Scope: checked theorem applicability and arithmetic, with the lower-bound
rescue derived independently. No q9 graph search, no q11/13 work, no Lean
formalization, and no conclusion about the ultimate Erdős-85 problem.
