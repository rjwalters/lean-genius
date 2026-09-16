# H1 cube-cover occupancy lemmas

Four Lean theorems formalize the block-occupancy step of the reviewed CUBE25 coverage argument. Generic block occupancy consumes at-most-one and a total lower bound. The specialized theorem selects a pair from any designated five-item blocks of two six-block rows. A complement-count lemma converts at most 24 false inputs into at least six true inputs. The final theorem consumes negative pair-clause disjunctions and the false-count bounds directly.

Docker source compile passed in 27.288 seconds using Lean 4.31.0. All four printed axiom lists contain only propext, Classical.choice and Quot.sound. Source contains no sorry/admit. Native compilation also passed. The recorded command mounts the resolved shared package cache because the worktree package directory is an absolute symlink. Earlier attempts without this resolved mount failed at importing Mathlib before checking any theorem.

Scope: propositional cardinality/occupancy only. Reverse-counter semantics, the Fin 30 to six-block count identification, actual DIMACS containment, cube UNSAT and final H1 exclusion are separate obligations. No solver or proof replay was run.
