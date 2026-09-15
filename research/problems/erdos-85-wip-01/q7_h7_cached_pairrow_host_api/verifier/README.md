# Independent verifier for a7 pair-row host receipts

`verifier.check` validates the canonical a7 fixed-high input, applies the
unchanged accepted 2124 structural coverage checker, reconstructs every host
prefix and the exact suffix union of future options, and checks singleton or
pair-row endpoints with independently written increasing-vertex enumeration.
The producer uses a different, colour-first template enumeration.

Only an exhaustively empty domain validates a negative endpoint. The native
functions distinguish EMPTY, FOUND, UNKNOWN and invalid input. The Python
wrapper raises on incomplete endpoint checks. UNKNOWN producer receipts never
prove complete coverage; `verify_partial=True` checks their saved endpoints
without changing that status. Retained complete leaves must have a possible
row at every singleton/pair vertex. None of these rows alone is a full graph.

`test_certificates.py` checks baseline/cached calibration receipts and fixed
controls: 33 records, 2,930 negative endpoints, 11 complete covers including a
synthetic positive fixed leaf, and five rejected corruptions. The synthetic
positive leaf comes from an accepted F3 ARC-negative record: its individual
row domains are nonempty even though they cannot coexist. The initial harness
stopped on missing adjacency metadata before verification; the corrected
version joins the separate launch inputs. Both launch records are retained.

`check_build.py` freshly compiles and checks the cached producer on four fixed
assignments only. Results exactly match the saved receipts. Zero-node and
expired-time controls remain UNKNOWN; a self-loop is rejected. No whole
capped input was restarted for these tests.

The cached producer is reviewed as 2669 for correctness under its stated a7
premises. Its performance evidence is limited: two F5 whole-input fixtures
complete, two F5 and eight F0 fixtures remain UNKNOWN. No F0 or new root
exclusion follows. The verifier implementation itself is available for peer
review before wider use.
