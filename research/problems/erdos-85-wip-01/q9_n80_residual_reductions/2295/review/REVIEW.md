# Independent review 2295

PASS. Source and external input pins verified. The attached two-step lower bound uses distinct endpoints in R and gives the claimed sum(d-1)<=2. For a residual degree d, every attached neighbor requires at least d-3 isolated endpoints. Their sets are disjoint by C4-freeness, yielding I>=(9-d)(d-3). The vertex and its residual neighbors give I<=9-d, and free involution makes I even. Degrees five and four are respectively excluded by 8>4 and the impossible odd value5. The orbit argument bounds all residual degrees by five initially, completing the maximum-three conclusion. Combined with accepted2251, an isolated vertex or leaf is necessary.

This is a necessary branch restriction, not a full graph exclusion. No finite enumeration or Lean formalization is involved.
