# Cayley census at q=11 and q=13 — 2026-09-13

Campaign status: **ALL_ATTEMPTS_TERMINAL**. Board40; local Kissat 4.0.4, seed0, proof logging OFF. Ten-minute cap per group,24-hour campaign limit, stop at first target SAT. No hand pruning and no retries.

One instance per SmallGroup:52 groups of order48,52 of order80,47 of order120 and57 of order168. Inverse-closed connection sets have exact sizes7,9,11 and13 respectively. Group tables came from the pinned GAP image `gapsystem/gap-docker@sha256:d66dca500c3d8b8ca88824d3c3c7315183335af029f6b74ce592ed0d148edaee`.

The [Cayley criterion review](cayley-lemma-review.json) establishes the mathematical equivalence used by the encoding. The [table audit](group-table-audit.json) checks all208 finite-group tables; the [complete encoding review](ENCODING_REVIEW.md) and [full constraint replay](full-encoding-audit.json), accepted in review2647, validate all208 exact production inputs. The earlier [sampled audit](encoding-audit.json) is preserved as historical evidence. Software fixtures are separate from graph controls.

## Order 48, degree 7

1 SAT, 51 UNSAT

| SmallGroup | Structure | Verdict | Wall seconds |
|---|---|---|---:|
| 48,1 | C3 : C16 | UNSAT | 0.112143 |
| 48,2 | C48 | UNSAT | 0.104765 |
| 48,3 | (C4 x C4) : C3 | UNSAT | 0.112476 |
| 48,4 | C8 x S3 | UNSAT | 0.112503 |
| 48,5 | C24 : C2 | UNSAT | 0.112282 |
| 48,6 | C24 : C2 | UNSAT | 0.111894 |
| 48,7 | D48 | UNSAT | 0.112740 |
| 48,8 | C3 : Q16 | UNSAT | 0.112338 |
| 48,9 | C2 x (C3 : C8) | UNSAT | 0.112770 |
| 48,10 | (C3 : C8) : C2 | UNSAT | 0.109327 |
| 48,11 | C4 x (C3 : C4) | UNSAT | 0.112086 |
| 48,12 | (C3 : C4) : C4 | UNSAT | 0.111498 |
| 48,13 | C12 : C4 | UNSAT | 0.110457 |
| 48,14 | (C12 x C2) : C2 | UNSAT | 0.109901 |
| 48,15 | (C3 x D8) : C2 | UNSAT | 0.107678 |
| 48,16 | (C3 : Q8) : C2 | UNSAT | 0.112745 |
| 48,17 | (C3 x Q8) : C2 | UNSAT | 0.106741 |
| 48,18 | C3 : Q16 | UNSAT | 0.112785 |
| 48,19 | (C6 x C2) : C4 | UNSAT | 0.112578 |
| 48,20 | C12 x C4 | UNSAT | 0.112505 |
| 48,21 | C3 x ((C4 x C2) : C2) | UNSAT | 0.102918 |
| 48,22 | C3 x (C4 : C4) | UNSAT | 0.112815 |
| 48,23 | C24 x C2 | UNSAT | 0.112569 |
| 48,24 | C3 x (C8 : C2) | UNSAT | 0.108517 |
| 48,25 | C3 x D16 | UNSAT | 0.103085 |
| 48,26 | C3 x QD16 | SAT | 0.103047 |
| 48,27 | C3 x Q16 | UNSAT | 0.110233 |
| 48,28 | C2 . S4 = SL(2,3) . C2 | UNSAT | 0.110454 |
| 48,29 | GL(2,3) | UNSAT | 0.112552 |
| 48,30 | A4 : C4 | UNSAT | 0.112791 |
| 48,31 | C4 x A4 | UNSAT | 0.104265 |
| 48,32 | C2 x SL(2,3) | UNSAT | 0.109456 |
| 48,33 | ((C4 x C2) : C2) : C3 | UNSAT | 0.104003 |
| 48,34 | C2 x (C3 : Q8) | UNSAT | 0.112472 |
| 48,35 | C2 x C4 x S3 | UNSAT | 0.108516 |
| 48,36 | C2 x D24 | UNSAT | 0.112468 |
| 48,37 | (C12 x C2) : C2 | UNSAT | 0.105975 |
| 48,38 | D8 x S3 | UNSAT | 0.106762 |
| 48,39 | (C4 x S3) : C2 | UNSAT | 0.112948 |
| 48,40 | Q8 x S3 | UNSAT | 0.112686 |
| 48,41 | (C4 x S3) : C2 | UNSAT | 0.113528 |
| 48,42 | C2 x C2 x (C3 : C4) | UNSAT | 0.112347 |
| 48,43 | C2 x ((C6 x C2) : C2) | UNSAT | 0.110687 |
| 48,44 | C12 x C2 x C2 | UNSAT | 0.110157 |
| 48,45 | C6 x D8 | UNSAT | 0.112372 |
| 48,46 | C6 x Q8 | UNSAT | 0.112248 |
| 48,47 | C3 x ((C4 x C2) : C2) | UNSAT | 0.104213 |
| 48,48 | C2 x S4 | UNSAT | 0.104161 |
| 48,49 | C2 x C2 x A4 | UNSAT | 0.113042 |
| 48,50 | (C2 x C2 x C2 x C2) : C3 | UNSAT | 0.108056 |
| 48,51 | C2 x C2 x C2 x S3 | UNSAT | 0.110410 |
| 48,52 | C6 x C2 x C2 x C2 | UNSAT | 0.106600 |

## Order 80, degree 9

52 UNSAT

| SmallGroup | Structure | Verdict | Wall seconds |
|---|---|---|---:|
| 80,1 | C5 : C16 | UNSAT | 0.111389 |
| 80,2 | C80 | UNSAT | 0.108273 |
| 80,3 | C5 : C16 | UNSAT | 0.217394 |
| 80,4 | C8 x D10 | UNSAT | 0.109533 |
| 80,5 | C40 : C2 | UNSAT | 0.113338 |
| 80,6 | C40 : C2 | UNSAT | 0.110305 |
| 80,7 | D80 | UNSAT | 0.874124 |
| 80,8 | C5 : Q16 | UNSAT | 0.107339 |
| 80,9 | C2 x (C5 : C8) | UNSAT | 0.107161 |
| 80,10 | (C5 : C8) : C2 | UNSAT | 0.106518 |
| 80,11 | C4 x (C5 : C4) | UNSAT | 0.108377 |
| 80,12 | (C5 : C4) : C4 | UNSAT | 0.106580 |
| 80,13 | C20 : C4 | UNSAT | 0.111117 |
| 80,14 | (C20 x C2) : C2 | UNSAT | 0.113709 |
| 80,15 | (C5 x D8) : C2 | UNSAT | 0.113497 |
| 80,16 | (C5 : Q8) : C2 | UNSAT | 0.107997 |
| 80,17 | (C5 x Q8) : C2 | UNSAT | 0.106925 |
| 80,18 | C5 : Q16 | UNSAT | 0.113232 |
| 80,19 | (C10 x C2) : C4 | UNSAT | 0.109280 |
| 80,20 | C20 x C4 | UNSAT | 0.107656 |
| 80,21 | C5 x ((C4 x C2) : C2) | UNSAT | 0.111827 |
| 80,22 | C5 x (C4 : C4) | UNSAT | 0.113326 |
| 80,23 | C40 x C2 | UNSAT | 0.113514 |
| 80,24 | C5 x (C8 : C2) | UNSAT | 0.111101 |
| 80,25 | C5 x D16 | UNSAT | 0.113500 |
| 80,26 | C5 x QD16 | UNSAT | 0.104548 |
| 80,27 | C5 x Q16 | UNSAT | 0.110464 |
| 80,28 | C5 : (C8 x C2) | UNSAT | 0.112786 |
| 80,29 | (C5 : C8) : C2 | UNSAT | 0.111175 |
| 80,30 | C4 x (C5 : C4) | UNSAT | 0.111790 |
| 80,31 | C20 : C4 | UNSAT | 0.113725 |
| 80,32 | C2 x (C5 : C8) | UNSAT | 0.104040 |
| 80,33 | (C5 : C8) : C2 | UNSAT | 0.112418 |
| 80,34 | (C10 x C2) : C4 | UNSAT | 0.113552 |
| 80,35 | C2 x (C5 : Q8) | UNSAT | 0.112472 |
| 80,36 | C2 x C4 x D10 | UNSAT | 0.113699 |
| 80,37 | C2 x D40 | UNSAT | 0.315699 |
| 80,38 | (C20 x C2) : C2 | UNSAT | 0.112697 |
| 80,39 | D8 x D10 | UNSAT | 0.113595 |
| 80,40 | (C4 x D10) : C2 | UNSAT | 0.113541 |
| 80,41 | Q8 x D10 | UNSAT | 0.113778 |
| 80,42 | (C4 x D10) : C2 | UNSAT | 0.222035 |
| 80,43 | C2 x C2 x (C5 : C4) | UNSAT | 0.108055 |
| 80,44 | C2 x ((C10 x C2) : C2) | UNSAT | 0.112055 |
| 80,45 | C20 x C2 x C2 | UNSAT | 0.104229 |
| 80,46 | C10 x D8 | UNSAT | 0.112661 |
| 80,47 | C10 x Q8 | UNSAT | 0.110587 |
| 80,48 | C5 x ((C4 x C2) : C2) | UNSAT | 0.107180 |
| 80,49 | (C2 x C2 x C2 x C2) : C5 | UNSAT | 0.113791 |
| 80,50 | C2 x C2 x (C5 : C4) | UNSAT | 0.107669 |
| 80,51 | C2 x C2 x C2 x D10 | UNSAT | 0.114050 |
| 80,52 | C10 x C2 x C2 x C2 | UNSAT | 0.109893 |

## Order 120, degree 11

47 UNSAT

| SmallGroup | Structure | Verdict | Wall seconds |
|---|---|---|---:|
| 120,1 | C5 x (C3 : C8) | UNSAT | 0.544244 |
| 120,2 | C3 x (C5 : C8) | UNSAT | 0.645980 |
| 120,3 | C3 : (C5 : C8) | UNSAT | 0.222981 |
| 120,4 | C120 | UNSAT | 0.215577 |
| 120,5 | SL(2,5) | UNSAT | 1.050919 |
| 120,6 | C3 x (C5 : C8) | UNSAT | 1.094152 |
| 120,7 | C3 : (C5 : C8) | UNSAT | 1.178768 |
| 120,8 | (C3 : C4) x D10 | UNSAT | 0.221372 |
| 120,9 | S3 x (C5 : C4) | UNSAT | 0.215098 |
| 120,10 | C3 : (C4 x D10) | UNSAT | 0.868264 |
| 120,11 | C3 : ((C10 x C2) : C2) | UNSAT | 0.328341 |
| 120,12 | C3 : D40 | UNSAT | 2.169493 |
| 120,13 | C3 : ((C10 x C2) : C2) | UNSAT | 1.510800 |
| 120,14 | C3 : (C5 : Q8) | UNSAT | 0.218859 |
| 120,15 | C5 x SL(2,3) | UNSAT | 1.185634 |
| 120,16 | C3 x (C5 : Q8) | UNSAT | 0.221057 |
| 120,17 | C12 x D10 | UNSAT | 0.437324 |
| 120,18 | C3 x D40 | UNSAT | 0.436832 |
| 120,19 | C6 x (C5 : C4) | UNSAT | 0.216128 |
| 120,20 | C3 x ((C10 x C2) : C2) | UNSAT | 0.433642 |
| 120,21 | C5 x (C3 : Q8) | UNSAT | 0.314511 |
| 120,22 | C20 x S3 | UNSAT | 0.437887 |
| 120,23 | C5 x D24 | UNSAT | 0.318360 |
| 120,24 | C10 x (C3 : C4) | UNSAT | 0.218310 |
| 120,25 | C5 x ((C6 x C2) : C2) | UNSAT | 0.543885 |
| 120,26 | C3 : (C5 : Q8) | UNSAT | 0.114104 |
| 120,27 | C4 x D30 | UNSAT | 0.536314 |
| 120,28 | D120 | UNSAT | 14.586287 |
| 120,29 | C2 x (C15 : C4) | UNSAT | 0.107450 |
| 120,30 | C3 : ((C10 x C2) : C2) | UNSAT | 0.537993 |
| 120,31 | C60 x C2 | UNSAT | 0.216595 |
| 120,32 | C15 x D8 | UNSAT | 0.425220 |
| 120,33 | C15 x Q8 | UNSAT | 0.321219 |
| 120,34 | S5 | UNSAT | 0.422435 |
| 120,35 | C2 x A5 | UNSAT | 0.540376 |
| 120,36 | S3 x (C5 : C4) | UNSAT | 0.323888 |
| 120,37 | C5 x S4 | UNSAT | 0.734859 |
| 120,38 | C5 : S4 | UNSAT | 0.744473 |
| 120,39 | A4 x D10 | UNSAT | 0.640540 |
| 120,40 | C6 x (C5 : C4) | UNSAT | 0.421422 |
| 120,41 | C2 x (C15 : C4) | UNSAT | 0.106345 |
| 120,42 | C2 x S3 x D10 | UNSAT | 0.739677 |
| 120,43 | C10 x A4 | UNSAT | 0.725874 |
| 120,44 | C2 x C6 x D10 | UNSAT | 0.209342 |
| 120,45 | C2 x C10 x S3 | UNSAT | 0.216247 |
| 120,46 | C2 x C2 x D30 | UNSAT | 4.069439 |
| 120,47 | C30 x C2 x C2 | UNSAT | 0.223864 |

## Order 168, degree 13

57 UNSAT

| SmallGroup | Structure | Verdict | Wall seconds |
|---|---|---|---:|
| 168,1 | C7 : C24 | UNSAT | 15.732164 |
| 168,2 | C8 x (C7 : C3) | UNSAT | 12.649383 |
| 168,3 | C7 x (C3 : C8) | UNSAT | 2.294959 |
| 168,4 | C3 x (C7 : C8) | UNSAT | 3.026414 |
| 168,5 | C3 : (C7 : C8) | UNSAT | 0.737031 |
| 168,6 | C168 | UNSAT | 0.418670 |
| 168,7 | C7 : (C3 x Q8) | UNSAT | 9.124191 |
| 168,8 | C4 x (C7 : C6) | UNSAT | 5.427076 |
| 168,9 | C7 : (C3 x D8) | UNSAT | 8.466386 |
| 168,10 | C2 x (C7 : C12) | UNSAT | 10.015738 |
| 168,11 | C7 : (C3 x D8) | UNSAT | 5.136982 |
| 168,12 | (C3 : C4) x D14 | UNSAT | 1.182381 |
| 168,13 | S3 x (C7 : C4) | UNSAT | 0.651743 |
| 168,14 | C3 : (C4 x D14) | UNSAT | 9.748735 |
| 168,15 | C3 : ((C14 x C2) : C2) | UNSAT | 1.060865 |
| 168,16 | C3 : D56 | UNSAT | 28.371912 |
| 168,17 | C3 : ((C14 x C2) : C2) | UNSAT | 11.394758 |
| 168,18 | C3 : (C7 : Q8) | UNSAT | 0.743364 |
| 168,19 | C2 x C4 x (C7 : C3) | UNSAT | 16.046739 |
| 168,20 | D8 x (C7 : C3) | UNSAT | 19.646163 |
| 168,21 | Q8 x (C7 : C3) | UNSAT | 18.933878 |
| 168,22 | C7 x SL(2,3) | UNSAT | 9.846836 |
| 168,23 | Q8 : (C7 : C3) | UNSAT | 32.478714 |
| 168,24 | C3 x (C7 : Q8) | UNSAT | 0.421336 |
| 168,25 | C12 x D14 | UNSAT | 0.972983 |
| 168,26 | C3 x D56 | UNSAT | 1.937460 |
| 168,27 | C6 x (C7 : C4) | UNSAT | 0.439935 |
| 168,28 | C3 x ((C14 x C2) : C2) | UNSAT | 1.385016 |
| 168,29 | C7 x (C3 : Q8) | UNSAT | 1.930327 |
| 168,30 | C28 x S3 | UNSAT | 1.886447 |
| 168,31 | C7 x D24 | UNSAT | 1.862820 |
| 168,32 | C14 x (C3 : C4) | UNSAT | 1.138282 |
| 168,33 | C7 x ((C6 x C2) : C2) | UNSAT | 5.048080 |
| 168,34 | C3 : (C7 : Q8) | UNSAT | 0.209409 |
| 168,35 | C4 x D42 | UNSAT | 3.458416 |
| 168,36 | D168 | UNSAT | 447.588432 |
| 168,37 | C2 x (C21 : C4) | UNSAT | 0.221565 |
| 168,38 | C3 : ((C14 x C2) : C2) | UNSAT | 3.976721 |
| 168,39 | C84 x C2 | UNSAT | 0.435903 |
| 168,40 | C21 x D8 | UNSAT | 1.185236 |
| 168,41 | C21 x Q8 | UNSAT | 1.072557 |
| 168,42 | PSL(3,2) | UNSAT | 3.812942 |
| 168,43 | (C2 x C2 x C2) : (C7 : C3) | UNSAT | 26.033816 |
| 168,44 | C3 x ((C2 x C2 x C2) : C7) | UNSAT | 14.933386 |
| 168,45 | C7 x S4 | UNSAT | 9.046361 |
| 168,46 | C7 : S4 | UNSAT | 3.248332 |
| 168,47 | C2 x C2 x (C7 : C6) | UNSAT | 4.169297 |
| 168,48 | A4 x D14 | UNSAT | 3.931994 |
| 168,49 | C7 : (C2 x A4) | UNSAT | 7.286891 |
| 168,50 | C2 x S3 x D14 | UNSAT | 6.331703 |
| 168,51 | C2 x C2 x C2 x (C7 : C3) | UNSAT | 23.731607 |
| 168,52 | C14 x A4 | UNSAT | 5.411772 |
| 168,53 | C2 x ((C14 x C2) : C3) | UNSAT | 14.749756 |
| 168,54 | C2 x C6 x D14 | UNSAT | 0.829599 |
| 168,55 | C2 x C14 x S3 | UNSAT | 1.045161 |
| 168,56 | C2 x C2 x D42 | UNSAT | 66.439778 |
| 168,57 | C42 x C2 x C2 | UNSAT | 0.419128 |

## Control witnesses

- SmallGroup(48,26): [adjacency and connection set](runs/48-26/graph.json), [author check](runs/48-26/graph-check.json). The [independent model and graph check](independent-reviews/48-26.json) accepts this 48-vertex,168-edge,7-regular C4-free witness.

## Verdict

All104 target instances returned UNSAT. No degree11 Cayley witness at order120 or degree13 Cayley witness at order168 was found in this complete SmallGroups census according to proof-OFF Kissat reports. These reports are not independently checked UNSAT certificates, and the Cayley-class result is not unrestricted nonexistence. Both controls and the independent208-run terminal audit passed. The only SAT result among all208 groups was SmallGroup(48,26), independently verified as a7-regular C4-free graph; all52 order80 controls returned UNSAT.

## Verification and literature

Both controls passed independent artifact checks: [order48 witness](independent-reviews/48-26.json) and [all52 order80 UNSAT reports](independent-reviews/order80-negative.json). The [order120 audit](independent-reviews/order120-target.json) binds its47 terminal outcomes. The [complete encoding review](ENCODING_REVIEW.md) and [constraint replay](full-encoding-audit.json) cover every production input; these are separate from solver verdicts.

The [literature check](LITERATURE_CHECK_20260913.md) confirms the119/167 exclusions and records what the traced sources do and do not establish for120/168. It does not certify a globally current open-problem status. Runner review2650 gave a scoped PASS: the live version can classify explicit UNKNOWN followed by a forced timeout as ERROR; the corrected candidate passed72 classification cases and was not deployed. Every production attempt completed normally before its cap, so this edge case did not arise. Final report publication review remains pending.

## Final accounting

All208 attempts are terminal, with no timeouts, retries, UNKNOWN or ERROR outcomes. Campaign wall time was954.3617592500523 seconds; summed solver wall time was944.5976699178573 seconds. The [independent terminal audit](independent-reviews/final-census.json) verifies the complete group cover, all result/ledger identities,208 log hashes,624 input hashes and serial timestamps. No further run was needed.
