# Complete permutation cover with simultaneous word support

Extends2193 by intersecting the243-word support sets from all ten attached pair capacity tables. A word is supported at pair(u,v) only if its contingency entry has positive upper capacity. Any actual ten residual orbits give ten distinct words (2184), with coordinate multiplicities4/3/3. Therefore the intersection must have at least10 words and each coordinate label must have at least4/3/3 supported words. These are necessary support counts, not a choice of compatible words.

Original total60second cap, six fixed-first-permutation roots, no retry. All six roots COMPLETE; producer loop0.706seconds, process including input0.815seconds. Retained labelled assignments: 4365056; compared with2193, another 250240 assignments are removed. No symmetry quotient. Nodes and partial h-capacity pruning are unchanged from2193. Output saves counts and one example per root, not a complete survivor payload.

prepare.py derives the input masks from the accepted local capacity tables and the earlier producer source. The frozen cover.cpp and input.txt are the actual run inputs. verify_examples.py independently counts attached-middle paths for every243 words of each saved example, without using the bitset lookup. All six examples pass the new support constraints. Enumeration counts and bitset preparation await peer review.

This still omits an actual ten-word selection, shared contingency counts, the b(w) conditions from2194, a compatible residual Q and matching phases. No graph witness or whole-case exclusion; no graph/CNF/SAT launch. The large surviving count argues against treating this support relaxation as decisive.
