# Incidence capacity and neighbour cover — Lean checked

`Erdos85NeighborCover.lean` proves that a second-neighbour cover B excluding a vertex a has at least degree(a) elements in a C4-free graph, and states the C4-forcing contrapositive. `Erdos85IncidenceCapacity.lean` proves the degree-sum bound under zero/one incidence constraints and its equality case: every allowed receiver has exactly one neighbour in the source set.

Author targeted builds and combined direct-source audit passed. Independent review2189 compiled both full source bodies and passed. All four declarations use only propext, Classical.choice and Quot.sound. Sources, hashes and peer evidence are archived here.

These are generic ingredients for the last incidence steps of the order-seven proof. The attached-set application still needs to establish the incidence hypotheses and cardinalities. The package does not claim the complete no-order-seven theorem or unrestricted graph nonexistence.
