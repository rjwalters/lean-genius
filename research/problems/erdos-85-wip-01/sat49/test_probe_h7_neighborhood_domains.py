import sys
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import probe_h7_neighborhood_domains as probe


class ProbeH7NeighborhoodDomainsTest(unittest.TestCase):
    def test_f6_t2_exact_row_domain_inventory(self) -> None:
        mask = probe.cubes.graph_representatives(6)[2]
        counts = [len(probe.row_domains(vertex, mask)) for vertex in range(42)]
        self.assertEqual(counts[:7], [210, 210, 840, 672, 672, 672, 672])
        self.assertEqual(counts[7:21], [9147] * 14)
        self.assertEqual(counts[21:], [2020] * 21)
        self.assertEqual(sum(counts), 174426)

    def test_every_row_has_exact_degree_and_support_partition(self) -> None:
        mask = probe.cubes.graph_representatives(6)[2]
        for vertex in range(42):
            for row in probe.row_domains(vertex, mask):
                self.assertEqual(row.bit_count(),
                                 7 - probe.SUPPORT[vertex].bit_count())
                support_union = 0
                for neighbor in range(42):
                    if (row >> neighbor) & 1:
                        self.assertEqual(support_union & probe.SUPPORT[neighbor], 0)
                        support_union |= probe.SUPPORT[neighbor]
                self.assertEqual(support_union, (1 << 7) - 1)


if __name__ == "__main__":
    unittest.main()
