# Independent review2274: PASS

All five payload pins and three external digests verified. Audited the local pair obstructions: same-side leaves already share a central neighbor; opposite-side leaves share the other central vertex with a given central endpoint; both central vertices cannot be attached to u because its involution mate repeats the pair. These exhaust the possibilities and bound each attached residual degree by two, excluding type311 in this branch.

The accepted central sum8-2t over four positive degrees now gives exactly4-2t degrees equal to two. Their second neighbors must be same-side unmatched leaves. A matched leaf already shares its partner with the central vertex; repetition among attached vertices also gives C4. Equal cardinalities prove the claimed bijection. Therefore all four central groups are exceptional when t=0, excluding the three221-only count. No further count case is excluded.

Independently checked all3072 residual subsets using ordinary neighbor sets and involution reversal; all saved counts and central pairs agree. Also independently checked the filter on all24 saved t0 incidence witnesses:14 violate the new necessary condition. This rejects only those particular certificates, not their underlying roots, since other incidence matrices may work. No old search was rerun and no UNKNOWN was changed.

The result is a necessary attachment restriction in the degree-five branch, not a full t0/t1 or N80 exclusion. No Lean formalization is claimed.
