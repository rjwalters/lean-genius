# Selected H7 coverage: a6 F12 update

This one-row overlay extends the 26-root map banked at dff011aeef27c444e7017163dc146d76ea7482b6. Review 2713 adds cube_F6_t17, source F12. All other 27 rows are unchanged, including masks and CNF identities.

Reviewed selected coverage is 27 of 28 roots; only cube_F6_t18, source F14, remains outside the selected exclusions. F14 partial results do not promote its root. Run `python3 check.py` to check hashes, review snapshot, permutation and exact delta.

Source/quotient completeness remains inherited. This is not arbitrary CNF UNSAT, Lean/kernel closure, whole H7 closure or a global Erdős 85 proof.
