import importlib.util
import sys
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "dependency_cone", HERE / "erdos85_audit_dependency_cone.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
sys.modules[SPEC.name] = MOD
SPEC.loader.exec_module(MOD)


class DependencyConeAuditTest(unittest.TestCase):
    @staticmethod
    def theorem(name):
        return MOD.ConeTheorem(name, "Proofs.Example", (), ())

    def test_private_environment_names_are_not_literal_nameable(self):
        public = self.theorem("Erdos85.publicTheorem")
        private = self.theorem("_private.Proofs.Example.0.Erdos85.helper")
        self.assertTrue(MOD.literal_nameable(public))
        self.assertFalse(MOD.literal_nameable(private))
        rendered = MOD.render_axiom_source("Proofs.Example", [public])
        self.assertIn("#print axioms Erdos85.publicTheorem", rendered)
        self.assertNotIn("_private", rendered)


if __name__ == "__main__":
    unittest.main()
