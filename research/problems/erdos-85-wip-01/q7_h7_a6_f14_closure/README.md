# Reviewed H7 a6 F14 structural exclusion

Review 2718 accepts the full necessary graph-cover exclusion for cube_F6_t18, mask 594051, source F14 under permutation [2,3,4,1,0,5,6]. The complete 2,278,608-leaf host cover (2707) partitions into 1,757,882 earlier residual negatives (2714), 75,027 triangle negatives (2716), and 445,699 incidence negatives in this packet. The latter are 270,467 empty-family witnesses and 175,232 negative choice trees, with no retained, UNKNOWN, INVALID, or unvisited cases. The exact partition and source/root mapping are independently checked in review/COMPOSITION_REVIEW.json; full certificate verification is in review/REVIEW.json.

The incidence model is necessary: each pair vertex selects a singleton-neighbor family, exact singleton capacities hold, and shared neighbors cannot form a four-cycle. Pair-pair edges are omitted. API qualification is review2717, archived in ../q7_h7_a6_f14_incidence_native. Original source/high/quotient premises are2118/2122/2125, F14 input2703, and host2707. Previous capped residual records remain unchanged; the separately reviewed triangle and incidence criteria cover their exact unfinished suffix.

## Archived and external files

Original author and reviewer payloads are verbatim; their manifests include original names and hashes. Historical candidate or pending wording is superseded only by accepted review2718. BANK_PINS.json uses bank-pins-v2 with local and external records, each carrying SHA256 and byte size. The external record also gives the durable path. The 33,491,445-byte receipt shard is deliberately outside Git on Stripe; author/receipt-locations.json provides the same locator. Original provenance paths in research scripts are retained.

Run `python3 verify_bank.py` to check archived and external bytes plus both original manifests. If the external shard was relocated, pass `--external-root /path/to/receipt/directory`. This is archive integrity verification, not a new certificate replay. Missing or corrupt external evidence fails verification.

Scope: paper plus computation, no Lean, no global claim. This graph-cover result is not arbitrary CNF UNSAT or a complete Erdős 85 proof.
