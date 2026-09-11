# Exhaustive high-center assignments with fixedH[X]

For each of29 cases, enumerate all45 two-edge graphs on the five high centers, as required by2492. Choose one group option per high center, requiring its defect-derived degree to equal the selected graph degree. Require disjoint low orbits, every311/311 pair-domain constraint, and intersect all311/111 compatibility lists. Enumerate every complete assignment, not only a first witness.

For a complete high assignment, retain only low-group options contained in its15 unused low orbits. Necessary filters require at least five options, at least four all-active options, an inactive-containing option, and their union to cover all remaining orbits. These filters cannot remove a valid five-group cover. All needed option indices and remaining masks are saved.

The original30-second stage completes all29 cases in0.098642 seconds. It finds139 complete high assignments before the final low-option filters and136 afterward, across21 cases. The added high/high compatibility is a new mathematical restriction missing from the capped2497 model; this is not its restart or a reinterpretation of unfinished cases.
