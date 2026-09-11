# Semiregular cyclic C4-free minimum-degree CNF

Vertices are block*m+residue. Translation of residue by one acts freely, with n/m orbits. Each cross-block offset gets one edge variable; within-block shifts d and -d share a variable. Antipodal shifts contribute one to degree; other internal shifts contribute two. No regularity restriction is imposed.

For one representative of every unordered vertex-pair orbit, form the conjunction of its two incident edge variables for each potential common neighbour. At most one conjunction may hold. Repeated conjunctions represent DISTINCT common neighbours and are forced false. Translation covers all vertex pairs; a graph has a C4 exactly when some pair has two common neighbours.

For each vertex block, a threshold dynamic program enforces minimum degree, repeating a variable twice when its orbit contributes two incident edges. Every auxiliary is an equivalence to an AND gate (OR uses negation), so every edge assignment has a unique extension. The recurrence remains valid with repeated inputs. Variable 1 is forced true.

Run: python3 generate.py --n 48 --m 24 --d 7 --out /absolute/new-directory
This produces graph.cnf and map.json with complete edge-orbit expansion and source/CNF hashes. Existing output directories are refused. decode.py MAP MODEL OUTPUT expands SAT edges and checks minimum degree, simplicity, symmetry, common-neighbour counts and the cyclic action. Independent second-seat validation is still required, including binding map to generator and solver model.

Author validation: test_generate.py exhausts 3608 edge-orbit assignments across nine small (n,m) settings and degree thresholds, comparing all CNF clauses under the unique auxiliary extension against independent graph checks. These are software checks, not the two required graph controls. No solver verdict or existence claim has been made here.

Scope questions relayed to editor: m63 at n63 cannot give the requested positive degree-eight control (an undirected circulant with two noninverse generators contains a C4). The requested alternative m21 needs a known witness or clarification; the standard GF8 determinant construction has obvious m7/m9 actions, which are not silently substituted. Prime n79 only has m1 and m79. Solver launch scope is owned by the squad runner and operator board, not inferred from this generic generator's accepted inputs.
