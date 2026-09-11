# Linear double-entry budget

Extend accepted2205's symmetric fractional residual model. In an actual selected quotient row, every entry is0,1or2, the row sum is4, and its squared norm is<=6. Therefore the row has at most one entry2. For each incident residual weight y_wz introduce a separate endpoint excess t_wz>=0 satisfying y_wz-t_wz<=x_w, t_wz<=x_w, and sum_z t_wz<=x_w. Actual rows satisfy this with t_wz=1 precisely at an entry2, otherwise0. Nonselected rows have all these variables zero. Diagonal weights count once in the row and have one excess variable.

Also impose x_w+x_z<=1 when distinct words agree in more than three coordinates: accepted2184 disallows selecting both. These linear inequalities preserve every actual graph. They do not enforce integrality or the full quotient-square condition.

Two target cases669268/24538199 were checked in this strictly stronger model under original aggregate60second cap. Code669268 has an exact repaired integer Farkas certificate with RHS-999999723 and all variable coefficients nonnegative. Code24538199 returned no negative certificate and remains unresolved; no exact primal witness is claimed. This is not a rerun or extension of the old capped integer search or original fractional model.

The numerical candidate for669268 was saved before repair. Integer repair adds existing excess<=x inequalities first, then y<=2x inequalities, then x<=1 inequalities, in descending variable order. Every added multiplier is nonnegative. The final exact weighted sum is verified by verify.py. Its arithmetic is exact but shares model.py; independent model reconstruction remains pending. model.py imports the frozen predecessor model, linked by hash in dependency.json.

Combining this with accepted prior stages would leave only matching representative24538199 for the N80/F5 case, subject to this new proof/certificate review. This does not settle that case, the other order-three fixed counts, or Erdős85.
