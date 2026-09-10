# T1 fixed-partial empty-layer pilot (unreviewed)

These scripts were run beside the frozen T1 results in the private working directory. To reproduce, copy the scripts to a scratch directory together with singleton-results.json and singleton-tail-results.json from q7_h5_t1_heavy_core, then run empty-domains.py, empty-cover.py, empty-edges.py in order.

For each saved singleton completion, enumerate support-partition neighbourhoods for an empty vertex, with positive residual degree and no already-common neighbour between any two guests. Every neighbourhood has at least two guests, so it cannot repeat. Select exactly13 neighbourhoods meeting every nonempty low vertex residual degree, without guest-pair reuse. Seven saved partials fail, three yield a first cover (cores119,227,105). For each first cover, direct graph checks verify C4-freeness and completed nonempty degrees. Empty-empty degree completion fails immediately by legal-partner shortage on all three.

Scope is deliberately limited: seven fixed singleton completions fail; three fixed empty covers fail. Alternate covers and alternate singleton completions are unexamined. NO heavy-core or sector exclusion follows. All results are author checks, pending review. Next useful step is to move empty-edge feasibility inside complete cover enumeration, then assess the remaining singleton-completion domain.
