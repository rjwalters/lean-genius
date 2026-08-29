#!/usr/bin/env python3

import hashlib
import unittest
from pathlib import Path

import generate_tierA_four_parent_worker as module


TEMPLATE = f'''#!/usr/bin/env python3
from pathlib import Path
TOOLS = Path("/tools")
C = Path("/campaign")
CONFIG = {{
    "third": {{
        "generator": TOOLS / "generate_small_high_third_cube_jobs.py",
        "generator_sha": "{module.OLD_GENERATOR_SHA256}",
        "manifest": {module.OLD_MANIFEST_PATH},
        "manifest_sha": "{module.OLD_MANIFEST_SHA256}",
    }},
}}
'''


class FourParentWorkerTest(unittest.TestCase):
    def derive_template(self, text: str = TEMPLATE) -> str:
        source = text.encode()
        old = module.SOURCE_WORKER_SHA256
        module.SOURCE_WORKER_SHA256 = hashlib.sha256(source).hexdigest()
        try:
            return module.derive_worker(
                source,
                Path("/tools/generate_small_high_third_cube_jobs.py"),
                "1" * 64,
                Path("/campaign/tierA/dispatch/manifest.json"),
                "2" * 64,
            ).decode()
        finally:
            module.SOURCE_WORKER_SHA256 = old

    def test_replaces_only_third_config_pins(self) -> None:
        output = self.derive_template()
        self.assertIn('"generator_sha": "' + "1" * 64 + '"', output)
        self.assertIn('Path("/campaign/tierA/dispatch/manifest.json")', output)
        self.assertIn('"manifest_sha": "' + "2" * 64 + '"', output)
        self.assertNotIn(module.OLD_GENERATOR_SHA256, output)
        self.assertNotIn(module.OLD_MANIFEST_SHA256, output)

    def test_wrong_source_hash_fails_closed(self) -> None:
        with self.assertRaisesRegex(ValueError, "audited worker"):
            module.derive_worker(b"wrong", Path("/g"), "1" * 64, Path("/m"), "2" * 64)

    def test_shape_drift_fails_closed(self) -> None:
        with self.assertRaisesRegex(ValueError, "third-generator SHA pin"):
            self.derive_template(TEMPLATE.replace(module.OLD_GENERATOR_SHA256, "0" * 64))


if __name__ == "__main__":
    unittest.main()
