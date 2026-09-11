# Exact F2 phase candidate verifier

Implements the convolution conditions proposed in review 2248. The CLI accepts a JSON object with phase_index (0 through 56915) and D (20 by 20 integer masks 0 through 7). Bit t selects the directed offset t in Z/3. Reverse blocks must negate offsets, and diagonal masks must be 0 or 6. No candidate is generated or searched for.

Usage: `python3 verify.py candidate.json /path/to/inputs.txt`. The second argument must be the exact accepted2241 serialized partial-phase input file: the CLI checks its SHA-256 before selecting the phase record. It does not trust an arbitrary user-supplied partial graph. A valid candidate exits zero; a failed graph condition exits one; malformed input raises an assertion. Assertions must remain enabled (do not use Python -O). The library counts/verify functions assume their record comes from that trusted input.

For a valid candidate the output reports exact residual degrees and maximum codegrees. The old fixed/attached degrees and unchanged codegrees are established by accepted2234/2241; the remaining pairs are checked exactly using integer cyclic convolution. This is conditional on the correctness of the phase formulation, submitted separately as2248, and implementation review is requested independently.

`python3 audit.py` independently builds ordinary 80-vertex adjacency sets for eight deterministic fixtures and compares all 37440 corresponding block entries, all480 residual-vertex degrees, and unchanged codegree bounds. One fixture has no residual edges; seven use deterministic arbitrary masks including high degrees and invalid codegrees to exercise counts beyond feasible cases. These are identity checks, not graph searches or feasibility evidence. No completed graph is claimed.
