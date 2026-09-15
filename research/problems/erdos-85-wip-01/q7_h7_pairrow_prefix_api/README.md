# Optimistic pair-row prefix predicate — reviewed API / prototype (review 2666), NOT an exclusion

Banked by claude. `original/` = codex-sol-2's package verbatim (files pinned in `original/pins.json`
plus that pin file): native + reference implementation of an optimistic pair-row domain predicate
for PARTIAL host prefixes in the a7 setting, its ctypes wrapper, fixtures and `SOUNDNESS.md`.
`review/review-2666.json` is codex-sol-1's PASS; `review/sol1-review2666/` is sol-1's independent
compile, distinct-F3-fixture suite and receipt.

What it is: at a partial host prefix, a pair-support vertex p has two fixed high neighbours; if its
host is already selected it needs a residual row of size 4, otherwise size 5, or size 4 only if
some unassigned empty vertex still has an admissible host option containing p (future-host
possible); at full depth 7 unhosted pairs use size 5 only. Enlarging candidate domains using only
selected host edges is optimistic, so an EMPTY optimistic domain (COMPLETE status) soundly prunes
the prefix. Reviewed premises (2666): the caller supplies a valid a7 prefix and complete future
host-option lists; only COMPLETE-empty may prune; node-0 / zero-time results are UNKNOWN; the
wrapper rejects wrapped vertex indices and non-bool future flags (sol-1's pre-review finding, room
51331, fixed before pinning). Fixture evidence: sol-2 1,071 domains (17 graphs × 21 pairs × depths
0/3/7), 357 exact matches with accepted 2127 final domains; sol-1 1,344 checks on distinct F3
fixtures at all 8 depths with relabelling, 168 exact 2127 final-domain equalities.

What it is NOT: no host search was run with it, no root is excluded by it, and integrating it into
the host enumerator (motivated by F0's 1,137 node-capped inputs, `../q7_h7_a7_f0_high_host_cover`)
still requires counted-budget propagation, legal-prefix / future-option coverage, and independent
empty-row endpoint checks (sol-2, room 51352). `BANK_PINS.json` = sha256 of every file here.
