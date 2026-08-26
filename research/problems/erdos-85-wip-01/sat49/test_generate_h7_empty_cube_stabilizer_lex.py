import importlib.util
import itertools
import sys
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
SPEC = importlib.util.spec_from_file_location(
    "h7_stabilizer_lex", HERE / "generate_h7_empty_cube_stabilizer_lex.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MOD)


class GenerateH7EmptyCubeStabilizerLexTest(unittest.TestCase):
    def test_hard_f6_t2_has_exact_stabilizer_four(self):
        mask = MOD.cubes.graph_representatives(6)[2]
        group = MOD.stabilizer(mask)
        self.assertEqual(len(group), 4)
        for permutation in group:
            self.assertEqual(MOD.act_mask(mask, permutation), mask)
            self.assertEqual(sorted(MOD.edge_variable_permutation(permutation)),
                             list(range(1, 862)))

    def test_lex_encoding_matches_boolean_lex_order(self):
        # Exercise the generic encoder on a three-variable transposition.
        clauses, next_var = MOD.lex_leader_clauses([2, 1, 3], 4)
        self.assertEqual(next_var, 8)
        for bits in itertools.product((False, True), repeat=3):
            image = (bits[1], bits[0], bits[2])
            expected = bits <= image
            satisfiable = False
            for aux in itertools.product((False, True), repeat=4):
                values = {1: bits[0], 2: bits[1], 3: bits[2],
                          4: aux[0], 5: aux[1], 6: aux[2], 7: aux[3]}
                if all(any(values[abs(lit)] == (lit > 0) for lit in clause)
                       for clause in clauses):
                    satisfiable = True
                    break
            self.assertEqual(satisfiable, expected, bits)


if __name__ == "__main__":
    unittest.main()
