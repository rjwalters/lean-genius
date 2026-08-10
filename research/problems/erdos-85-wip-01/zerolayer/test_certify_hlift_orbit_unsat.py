#!/usr/bin/env python3
"""Unit test executable provenance used by the DRAT promotion runner."""

import hashlib
import os
import sys
import tempfile

from certify_hlift_orbit_unsat import drat_verified, executable_provenance

provenance = executable_provenance(sys.executable)
assert len(provenance["sha256"]) == 64
assert provenance["sha256"] == hashlib.sha256(
    open(provenance["path"], "rb").read()).hexdigest()
try:
    executable_provenance("definitely-not-an-installed-executable-85")
    raise AssertionError("missing executable accepted")
except SystemExit as exc:
    assert "not found" in str(exc)
with tempfile.NamedTemporaryFile(mode="w", delete=False) as handle:
    handle.write("c proof check\ns VERIFIED\n")
    path = handle.name
try:
    assert drat_verified(path)
    open(path, "w").write("s NOT VERIFIED\n")
    assert not drat_verified(path)
finally:
    os.unlink(path)
print("ALL OK")
