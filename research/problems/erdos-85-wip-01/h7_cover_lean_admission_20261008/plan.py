"""Print the frozen cover inventory and prior reuse evidence; never launch jobs."""

import json

import common as c


def main():
    reuse = c.pilot_reuse()
    print(json.dumps({"status": "PREPARED_NOT_LAUNCHED", "input_manifest_sha256": c.INPUT_SHA,
        "source_sha256": c.source_hashes(), "covers": [c.select(name) for name in c.hc.CUBES],
        "prior_pilot": reuse, "new_covers_pending": 27,
        "scope": "Optional cover-only admission after campaign/input freeze; no all-leaf replay."}, indent=2))


if __name__ == "__main__":
    main()
