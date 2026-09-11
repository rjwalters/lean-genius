# Exact F2 quotient model generator

Implements the necessary integral quotient system proved exact in accepted squad review 2244, for all 117 representatives of accepted 2226. No optimizer is called, no feasibility verdict is reported, and graph edge phases are not encoded.

Run `python3 generate.py all-hashes` to generate the complete manifest and model 0, or `python3 generate.py INDEX OUTPUT` to materialize another model. Input paths and SHA-256 hashes are recorded in input-pins.json. The generator currently uses those absolute source paths; archive users must restore or adjust them explicitly.

Each canonical compact JSON model has 11820 variables: indices [0,420) are binary (domain {0,1}); indices [420,11820) are continuous with lower bound zero and no upper bound. All ranges are end-exclusive. Matrix pair order is explicit: the first 210 variables are b, the next 210 are d, with q=b+d. Constraint terms are [variable index, integer coefficient]; null lower/upper means unbounded on that side. Each row represents lower <= sum(terms) <= upper. Objective null means feasibility only.

There are 11980 rows: 210 double-implies-present, 20 diagonal equalities, 20 one-double bounds, 20 degree equalities, 120 attached margins, 11400 binary-product lower bounds, and 190 two-step upper bounds. Diagonal and degree rows are the 40 equalities. Nonnegative auxiliaries and the one-double rule make the two-step formulation exact for this quotient system, as proved in 2244.

All 117 models were constructed and structurally checked, then deterministically reconstructed and compared with every manifest digest. The saved model 0 matches its reconstructed bytes. This verifies artifact reproducibility, not independent correctness of the generator; independent review is requested separately.
