The first retained-input prefix audit failed on 2026-09-10 before publication.
The initial decoder assumed the Python generator's high-edge allocation for
both H3 and H5. The retained H5 Lean freight instead uses lexicographic full
edge allocation: its high/high unit IDs begin 1,2,3,4,49,50,51,96,97,142.
The Python ordering would have used 1 through10.

Both encodings use the same lexicographic low/low suffix. The decoder now
reads only that suffix and adds the fixed high/support incidences, just as
for H7. The actual-prefix audit separately checks each retained encoding's
high units and all low/low variable IDs before any review or witness claim.
