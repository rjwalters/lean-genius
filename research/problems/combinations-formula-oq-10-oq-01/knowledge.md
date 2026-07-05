# Knowledge: combinations-formula-oq-10-oq-01 (Weighted Vandermonde Diagonal ∑ k·C(n,k)²)

## RESOLVED-AS-DUPLICATE (researcher-4, 2026-07-02)

**This problem is DUPLICATE CONTENT of the existing gallery entry
`combinations-formula-oq-07-oq-03` ("The Weighted Sum of Squares of Binomial
Coefficients").** That entry already proves the identical result:
  2·∑_{k=0}^{n} k·C(n,k)² = n·C(2n,n),  equivalently  ∑ k·C(n,k)² = n·C(2n−1,n−1).

The seeker generated this slug without noticing the existing coverage. NO new
gallery entry was shipped (would be redundant).

**Note for future work:** I did write a *methodologically distinct* verified
(0-axiom) proof via the ABSORPTION identity (j+1)·C(n+1,j+1)=(n+1)·C(n,j) +
Vandermonde convolution (Nat.add_choose_eq on the antidiagonal), vs. the existing
entry's REFLECTION argument (k ↦ n−k, weight k+(n−k)=n collapse). If an alternative
proof is ever wanted, that route is: peel k=0 via Finset.sum_range_succ', absorb to
(n+1)·∑ C(n,j)C(n+1,j+1), then C(n+1,j+1)=C(n+1,n−j) (choose_symm) matches
Nat.add_choose_eq n (n+1) n → C(2n+1,n). Central form via C(2n,n)=2C(2n−1,n−1)
(one Nat.choose_succ_succ + choose_symm_of_eq_add).

Recommend: seeker should retire this slug (dup of oq-07-oq-03). The natural
extension ∑ k²·C(n,k)² is ALSO already taken (combinations-formula-oq-07-oq-03-oq-01).
