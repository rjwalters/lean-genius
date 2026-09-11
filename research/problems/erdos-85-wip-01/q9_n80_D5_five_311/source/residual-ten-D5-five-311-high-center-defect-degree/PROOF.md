# Exact high-center degree from inactive pairs

In residual-matching D5/s5, let X be the five311 centers and Y the five111 centers. For f in X let i_f be the number of inactive low pairs among its two low pairs, and h_f be1 if its high pair is matched in the high-high graph, otherwise0. Then

 degree_H[X](f) = 1+i_f-h_f,
 degree_H(f,Y) = 2-i_f+h_f.

Proof. In a cubic C4-free fixed graph on ten vertices, each center has exactly six distinct other fixed vertices with a common fixed neighbor, leaving three fixed defect neighbors. The311 group covers every residual vertex once, so f has no residual defect neighbor. Its total defect degree is7, hence it has exactly four W defect neighbors. Low vertices have no fixed defect neighbors, by saturation of their seven permissible W-group slots. Therefore precisely six of the ten high vertices have a common G-neighbor with f.

Count those six via middle vertices. Each H-neighbor of f in X contributes the two highs in that center's group. The2-i_f active low pairs in B_f contribute two high endpoints each. If h_f=1, the two high vertices in B_f contribute their two high matching neighbors; otherwise they contribute none. Residual middle vertices contribute no fixed endpoint, and Y centers have no high vertices. All counted high endpoints are distinct, since a repeated endpoint would give it and f two common neighbors and hence a C4. Thus

 2 degree_H[X](f) + 2(2-i_f) + 2h_f = 6,

which yields the claimed equalities. The high-pair matching status is well-defined because the involution preserves the high graph. This proof permits an edge joining the two high vertices within B_f.

The center-structure theorem gives exactly two H[X] edges. Hence degree_H[X](f)<=2, so1<=degree_H(f,Y)<=3. In particular, an unmatched high group cannot contain two inactive low pairs. The five required X-Y degrees can be imposed before choosing the five111 groups. This is a necessary paper identity, not a full graph exclusion, and does not select any previously saved edge or center witness. No search, global Erdős85 conclusion or Lean theorem is claimed.
