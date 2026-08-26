import itertools
import sys
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import check_h7_t0_canonical_common_neighbor as common


def clause_true(clause: tuple[int, ...], values: dict[int, bool]) -> bool:
    return any(values[abs(literal)] == (literal > 0) for literal in clause)


class CheckH7T0CanonicalCommonNeighborTest(unittest.TestCase):
    def test_small_encoding_exactly_matches_at_most_one(self) -> None:
        cnf = common.compact.CompactCnf()
        inputs = [cnf.variable() for _ in range(6)]
        candidates = [(inputs[0], inputs[1]), (inputs[2], inputs[3]),
                      (inputs[4], inputs[5])]
        common.add_common_neighbor_at_most_one(cnf, candidates)
        auxiliaries = list(range(7, cnf.variable_count + 1))
        for bits in itertools.product((False, True), repeat=6):
            expected = sum(bits[2 * i] and bits[2 * i + 1]
                           for i in range(3)) <= 1
            satisfiable = False
            for aux in itertools.product((False, True), repeat=len(auxiliaries)):
                values = {index + 1: value for index, value in enumerate(bits)}
                values.update(dict(zip(auxiliaries, aux)))
                if all(clause_true(clause, values) for clause in cnf.clauses):
                    satisfiable = True
                    break
            self.assertEqual(satisfiable, expected, bits)

    def test_full_shape_and_semantic_edge_prefix(self) -> None:
        cnf, edges, c4_clauses = common.build_cnf()
        self.assertEqual(len(edges), 861)
        self.assertEqual(list(edges.values()), list(range(1, 862)))
        self.assertEqual(cnf.variable_count, 80010)
        self.assertEqual(len(cnf.clauses), 227556)
        self.assertEqual(c4_clauses, 194012)

    def test_forced_common_neighbor_cases(self) -> None:
        one = common.compact.CompactCnf()
        literal = one.variable()
        common.add_common_neighbor_at_most_one(
            one, [(True, True), (literal, True), (False, literal)])
        self.assertIn((-literal,), one.clauses)

        two = common.compact.CompactCnf()
        common.add_common_neighbor_at_most_one(two, [(True, True), (True, True)])
        self.assertIn((), two.clauses)


if __name__ == "__main__":
    unittest.main()
