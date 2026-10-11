"""Metadata-only checks. No Lean, native search, Docker or AWS calls."""
import copy
import hashlib
import re
import unittest
import common
import controller
import manifest


class Metadata(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest = manifest.build()

    def test_exact_census_and_existing_credits(self):
        m = self.manifest
        self.assertEqual(m['census_counts'], {'full': 261, 'deficient': 1554})
        self.assertEqual(m['compute_counts'], {'total': 1815, 'reused': 4, 'pending': 1811})
        self.assertEqual({r['id'] for r in m['cases'] if r['state'] == 'REUSED_PASS'},
                         {'full-u001-r15', 'full-u003-r03', 'deficient-u026-r02', 'deficient-u369-r11'})

    def test_generated_inputs_match_four_existing_diagnostics(self):
        for branch, u, r in [('full', 3, 3), ('full', 54, 20), ('deficient', 26, 2), ('deficient', 369, 11)]:
            c = next(c for c in self.manifest['cases'] if (c['branch'], c['u_index'], c['r_index']) == (branch, u, r))
            new = common.sources(c)[c['module_prefix'] + 'Inputs.lean']
            old = (common.RESEARCH / 'h3_varied_pilot_20261008' / ('Erdos85ThreeHighPilot' + c['tag'] + 'Inputs.lean')).read_text()
            for name in ('U', 'R'):
                def term(s):
                    return ''.join(re.search(r'def ' + name + r'\b.*?:=\s*(.*?)(?=\ndef |\nend )', s, re.S)[1].split())
                self.assertEqual(term(new), term(old))

    def test_all_source_hashes_and_names_are_unique(self):
        names = set()
        for c in self.manifest['cases']:
            for name, source in common.sources(c).items():
                self.assertNotIn(name, names)
                names.add(name)
                self.assertEqual(hashlib.sha256(source.encode()).hexdigest(), c['source_sha256'][name])
        self.assertEqual(len(names), 4 * 1815)

    def test_capacity_rejects_overcommit(self):
        self.assertEqual(controller.capacity(123, 16), 6)
        self.assertEqual(controller.capacity(61, 8), 3)
        for memory, cpus in [(16, 16), (123, 1), (-1, 16), (float('inf'), 16)]:
            with self.assertRaises(ValueError):
                controller.capacity(memory, cpus)

    def test_live_and_credited_cases_not_queued(self):
        p = controller.plan(self.manifest, 'metadata-fixture', 123, 16, 1, ['full-u054-r20'])
        self.assertEqual(len(p['queue']), 1810)
        self.assertNotIn('full-u054-r20', p['queue'])
        self.assertNotIn('full-u003-r03', p['queue'])

    def test_unknown_live_and_inconsistent_manifest_rejected(self):
        for live in [['typo'], ['full-u003-r03']]:
            with self.assertRaises(ValueError):
                controller.plan(self.manifest, 'fixture', 123, 16, 1, live)
        for mutate in [lambda m: m['cases'].append(m['cases'][0]),
                       lambda m: m['compute_counts'].update(pending=0),
                       lambda m: m['cases'][0].update(state='COMPLETE')]:
            bad = copy.deepcopy(self.manifest)
            mutate(bad)
            with self.assertRaises(ValueError):
                controller.plan(bad, 'fixture', 123, 16, 1)


if __name__ == '__main__':
    unittest.main(verbosity=2)
