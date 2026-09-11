# Symmetric fractional residual relaxation

Use accepted2184/2190/2194. Fix an attached matching assignment. Let W be all ternary color words with positive pair-contingency capacity everywhere and with nonnegative b(w). Introduce nonnegative real x_w<=1. Impose coordinate margins433 and pair contingency bounds on x as in2201.

An actual graph selects ten distinct words, so its x are0or1. For each unordered pair of words, introduce a nonnegative symmetric residual weight y_wz (one variable, used at both ends); diagonal weights count once in a row. In an actual graph these are Q entries on selected words, zero elsewhere. Impose:

* sum_z y_wz = 4 x_w;
* sum_{z:z_u=a} y_wz <= b_{u,a}(w) x_w, for every coordinate and label;
* y_wz <= 2 x_w and, for distinct endpoints, y_wz <= 2 x_z.

A cross variable can be omitted when the words agree in more than three coordinates: both words cannot be selected. It can also be omitted if either endpoint has zero capacity in any coordinate for the other's label. A diagonal variable can be omitted unless all b_{u,w_u}(w)>=2, since the actual diagonal must be0or2. These omissions preserve every actual graph solution.

These are linear constraints. They retain symmetry and simultaneous residual color marginals but omit integrality, the squared-quotient constraints and matching phases. A fractional solution is only a solution of this relaxation. An exact rational Farkas certificate excludes this matching assignment if it proves infeasibility. Applying it to the60 capped DFS cases is a different relaxation, not a continuation or enlarged run of that DFS.
