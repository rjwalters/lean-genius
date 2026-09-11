# Eight-fixed-vertex involution reductions

At order 78, a C4-free graph of minimum degree nine cannot have a nonidentity involution with exactly eight fixed vertices. Five possible fixed degree profiles all fail elementary local walk or triangle arguments. Review 2237 independently accepts the complete paper proof. Together with the earlier fixed-count bound (2220) and ten-fixed-vertex exclusion (2236), the only remaining involution fixed counts at order 78 are 0, 2, 4, and 6.

At order 80, eight fixed vertices force the fixed graph to be four disjoint edges. The other possible fixed graph, a star, fails an odd-matching argument. All eight attached eight-vertex sets and the residual eight-vertex set have prescribed internal and cross matchings. The zero-codegree graph has two isolated K8 components, on the fixed and residual sets, and perfect matchings between all distinct attached sets. Review 2239 accepts this necessary normal form; it does not exclude the entire order-80 case.

Review 2242 accepts the common parity argument in general: for odd d>=3 and even 2<=F<=d-1, a d-regular C4-free graph of order d(d-1)+F cannot have an involution whose F fixed vertices induce a star. Regularity is explicit. This is a paper theorem, not a full Lean formalization or a solution of Erdős 85.

Original proofs, finite fixed-subgraph checks, peer audits, PASS resolutions, and provenance are preserved byte-for-byte. Run `python3 verify_archive.py` for a read-only integrity and degree-profile/witness check. It does not rerun any capped graph search or purport to mechanically verify the paper arguments. Source scripts retain original paths where recorded. All supplementary eight-vertex checks completed within their original caps; no UNKNOWN is treated as negative.
