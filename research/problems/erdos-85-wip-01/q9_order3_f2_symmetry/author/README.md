# Complete relabelling cover of672 F2 contingency tables

Independent swaps of labels1/2 on A and B preserve their internal matchings. Exchanging the two fixed centres transposes both the cross matching and contingency table, and exchanges the distinct-missing label pair. These operations generate a group of order8. They preserve every graph realization and all2221 constraints.

run.py explicitly applies all8 transformations to every supplied rooted table, checks every image belongs to the original672-element set, and verifies disjoint orbits cover the entire set. The lexicographic minima yield117 representatives, stored with original state/table indices and orbit sizes. A partial matching uses-1 for its unmatched label; missing-label null/sentinel semantics follow2221. All672 tables are covered, conditional on accepted2221; no graph elimination is asserted.
