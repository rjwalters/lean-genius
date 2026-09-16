# H1 counter-to-block composition

Four lemmas identify the Boolean prefix count with a sum over Fin n, transport the 30-input count through an explicit equivalence Fin 6 x Fin 5 to Fin 30, derive the 25-pair cover from prefix lower bounds, and compose the arbitrary-auxiliary reverse-counter schemas with negative block pair clauses. The bijections are explicit assumptions, not hidden input-order claims.

Native compilation passed. A fresh Docker source chain compiled SequentialCounter, SequentialCounterReverse, OneHighCube25CnfCover, and OneHighCube25CountBridge with exit zero. The final four axiom audits list only propext, Classical.choice and Quot.sound. Each compile was bounded at 120 seconds. Initial Docker -o invocation failed because the working root was /workspace; launch2 sets it to /source and records the successful run without changing source.

The source/dependency copies, launch commands, logs and results are pinned. Build outputs are reproducible and excluded from the compact manifest. Actual DIMACS clause containment, concrete target literal identification, cube UNSAT and H1 exclusion remain separate. No proof replay or solver ran.
