import hashlib
import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("cold", HERE / "run_h1_endpoint_cold_build.py")
MOD = importlib.util.module_from_spec(SPEC); assert SPEC.loader is not None; SPEC.loader.exec_module(MOD)


def write(path, value): path.write_bytes(MOD.canonical(value)); return MOD.sha(path)


def fixture(root):
    root = root.resolve(); repo = root / "repo"; repo.mkdir()
    commit = "a" * 40; review = "review-123"
    source_raw = b"import Proofs.Generated.H1\n\ntheorem endpoint : True := by trivial\n"
    upstream = root / "upstream"; upstream.mkdir()
    upstream_paths = {}
    for name in ("adapter_receipt", "aggregate_layout", "bank_receipt", "capacity_reindex_receipt",
                 "leaf_module_index", "producer"):
        path = upstream / name; path.write_text(name + "\n"); upstream_paths[name] = path
    upstream_paths["producer"].write_bytes((HERE / "finalize_h1_leaf_module_evidence.py").read_bytes())
    identity = {"blob_oid": "c" * 40, "bytes": len(source_raw), "repo_path": MOD.SOURCE,
                "sha256": hashlib.sha256(source_raw).hexdigest()}
    row = {"capacity_local_index": 0, "leaf_blob_oid": "d" * 40,
        "leaf_repo_path": "proofs/Proofs/Generated/Leaf.lean", "leaf_source_bytes": 1,
        "leaf_source_sha256": "1" * 64, "ledger_path": "ledgers/leaf.line",
        "ledger_sha256": "2" * 64, "packed_path": "packed/leaf.lz4", "packed_sha256": "3" * 64,
        "profile": 0, "replay_evidence_path": "replay/leaf.json",
        "replay_evidence_sha256": "4" * 64, "tag": "0123456789abcdef"}
    rows = []
    for profile, count in enumerate((1485, 3617, 4717, 2693, 839)):
        for local in range(count):
            item = row.copy(); item["profile"] = profile; item["capacity_local_index"] = local
            item["tag"] = f"{len(rows):016x}"; rows.append(item)
    evidence = upstream / "leaf-evidence.json"
    evidence_pin = write(evidence, {"adapter_repo_path": MOD.SOURCE,
        "adapter_source_identity": identity, "aggregate_layout_source_identity": {
        "blob_oid": "e" * 40, "bytes": 1, "repo_path": "proofs/layout.json", "sha256": "5" * 64},
        "aggregate_tree_identity_sha256": "6" * 64, "generated_tree_identity_sha256": "b" * 64,
        "leaf_count": 13351, "leaf_tree_identity_sha256": "7" * 64,
        "profile_counts": [1485, 3617, 4717, 2693, 839], "review_id": review,
        "reviewed_commit": commit, "rows": rows,
        "schema": MOD.EVIDENCE_SCHEMA})
    post = upstream / "post.json"
    post_value = {"adapter_receipt_path": str(upstream_paths["adapter_receipt"]),
        "adapter_receipt_sha256": MOD.sha(upstream_paths["adapter_receipt"]),
        "aggregate_layout_path": str(upstream_paths["aggregate_layout"]),
        "aggregate_layout_sha256": MOD.sha(upstream_paths["aggregate_layout"]),
        "bank_receipt_path": str(upstream_paths["bank_receipt"]),
        "bank_receipt_sha256": MOD.sha(upstream_paths["bank_receipt"]),
        "capacity_reindex_receipt_path": str(upstream_paths["capacity_reindex_receipt"]),
        "capacity_reindex_receipt_sha256": MOD.sha(upstream_paths["capacity_reindex_receipt"]),
        "commit_object_oid": commit,
        "endpoint_module": MOD.MODULE, "endpoint_source_path": MOD.SOURCE,
        "endpoint_source_sha256": hashlib.sha256(source_raw).hexdigest(), "endpoint_theorem": MOD.THEOREM,
        "evidence_path": "leaf-evidence.json", "evidence_sha256": evidence_pin,
        "generated_tree_identity_sha256": "b" * 64, "leaf_count": 13351,
        "leaf_module_index_path": str(upstream_paths["leaf_module_index"]),
        "leaf_module_index_sha256": MOD.sha(upstream_paths["leaf_module_index"]),
        "producer_path": str(upstream_paths["producer"]), "producer_sha256": MOD.sha(upstream_paths["producer"]),
        "profile_counts": [1485, 3617, 4717, 2693, 839], "repo": str(repo), "review_id": review,
        "reviewed_commit": commit, "schema": MOD.POST_SCHEMA}
    post_pin = write(post, post_value)
    cache_root = root / "cache"; entry = cache_root / ".lake/packages/mathlib/.ready"
    entry.parent.mkdir(parents=True); entry.write_text("ready\n")
    entries = [{"bytes": entry.stat().st_size, "path": ".lake/packages/mathlib/.ready", "sha256": MOD.sha(entry)}]
    cache = root / "cache.json"; cache_pin = write(cache, {"entries": entries,
        "identity_sha256": hashlib.sha256(MOD.canonical(entries)).hexdigest(), "root": str(cache_root),
        "schema": MOD.CACHE_SCHEMA})
    git = root / "git"; git.write_text("fake git\n"); runtime = root / "runtime"; runtime.write_text("fake runtime\n")
    tools = {"command_identity_derivation": "sha256(canonical-json({argv,cwd,environment,kind}))",
        "command_templates": MOD.templates(), "container_runtime_path": str(runtime),
        "container_runtime_sha256": MOD.sha(runtime), "git_path": str(git), "git_sha256": MOD.sha(git),
        "image": MOD.IMAGE, "resource_policy": {"cpus": 8, "memory": "32g", "network": "none",
        "pids_limit": 4096, "read_only_container": True, "tmpfs": "/tmp:rw,noexec,nosuid,size=2g"},
        "schema": MOD.TOOLCHAIN_SCHEMA}
    toolchain = root / "tools.json"; toolchain_pin = write(toolchain, tools)
    state = {"wrong_head": False, "dirty": False, "build_rc": 0, "missing_olean": False,
             "empty_olean": False, "bad_lean": False, "bad_lake": False, "bad_hashes": False,
             "source_bad": False, "source_drift": False, "inherited_lake": False, "zero_metrics": False,
             "missing_control": False, "control_drift": False, "bad_control_oid": False}
    def runner(kind, argv, cwd, environment, stdout, stderr):
        stdout.write_bytes(b""); stderr.write_bytes(b"")
        checkout = root / "stage-placeholder"
        if kind == "clone":
            checkout = Path(argv[-1]); checkout.mkdir(); (checkout / ".git").mkdir()
        else:
            checkout = Path(next(token.split(":/workspace:rw", 1)[0] for token in argv
                                 if token.endswith(":/workspace:rw"))) if kind in {
                                     "tool_hashes", "lean_version", "lake_version", "build"} else Path(
                                         argv[argv.index("-C") + 1] if "-C" in argv else root)
        if kind == "checkout":
            source = checkout / MOD.SOURCE; source.parent.mkdir(parents=True)
            source.write_bytes(b"sorry\n" if state["source_bad"] else source_raw)
            for control in MOD.CONTROL_PATHS:
                path = checkout / control; path.parent.mkdir(parents=True, exist_ok=True); path.write_text(control + "\n")
            if state["missing_control"]: (checkout / MOD.CONTROL_PATHS[-1]).unlink()
            if state["inherited_lake"]:
                inherited = checkout / "proofs/.lake/inherited"; inherited.parent.mkdir(parents=True); inherited.write_text("bad\n")
        elif kind == "head": stdout.write_text(("f" * 40 if state["wrong_head"] else commit) + "\n")
        elif kind in ("control_commit_oids", "control_worktree_oids"):
            oids = ["c" * 40, "d" * 40, "e" * 40]
            if kind == "control_worktree_oids" and state["bad_control_oid"]: oids[0] = "f" * 40
            stdout.write_text("\n".join(oids) + "\n")
        elif kind in ("status", "status_after"):
            stdout.write_text(" M bad\n" if state["dirty"] or (kind == "status_after" and state["source_drift"]) else "")
        elif kind == "tool_hashes": stdout.write_text("bad\n" if state["bad_hashes"] else
            "1" * 64 + "  /root/.elan/bin/lean\n" + "2" * 64 + "  /root/.elan/bin/lake\n")
        elif kind == "lean_version": stdout.write_text("bad\n" if state["bad_lean"] else "Lean (version 4.31.0, fake)\n")
        elif kind == "lake_version": stdout.write_text("bad\n" if state["bad_lake"] else "Lake version 5.0.0-fake\n")
        elif kind == "build" and not state["missing_olean"]:
            target = checkout / "proofs" / MOD.OLEAN; target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(b"" if state["empty_olean"] else b"olean\n")
            if state["source_drift"]:
                (checkout / MOD.SOURCE).write_bytes(b"drift\n")
            if state["control_drift"]: (checkout / MOD.CONTROL_PATHS[0]).write_text("rehashed spoof\n")
        metric = 0 if state["zero_metrics"] else 1
        return {"cumulative_children_maxrss_kb": metric,
            "rc": state["build_rc"] if kind == "build" else 0,
            "system_ns": 1, "user_ns": 1, "wall_ns": metric}
    args = {"repo": repo, "source_commit": commit, "review_id": review, "post_receipt": post,
        "post_receipt_sha256": post_pin, "cache_manifest": cache, "cache_manifest_sha256": cache_pin,
        "toolchain": toolchain, "toolchain_sha256": toolchain_pin, "output": root / "out", "runner": runner}
    return args, state, {"post": post, "evidence": evidence, "cache": cache, "entry": entry, "git": git, "runtime": runtime,
                         "toolchain": toolchain}


class ColdBuildTest(unittest.TestCase):
    def test_happy_path_is_pinned_networkless_and_atomic(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); args, _, _ = fixture(root); receipt = MOD.build(**args); out = args["output"]
            self.assertEqual(receipt["schema"], MOD.SCHEMA)
            self.assertEqual(receipt["source_commit"], "a" * 40)
            self.assertEqual(receipt["target_olean_sha256"], hashlib.sha256(b"olean\n").hexdigest())
            self.assertEqual(MOD.sha(out / receipt["target_olean_path"]), receipt["target_olean_sha256"])
            self.assertEqual(receipt["target_olean_build_path"], MOD.OLEAN)
            build = receipt["commands"]["build"]
            self.assertIn("--network=none", build["argv"]); self.assertIn("--read-only", build["argv"])
            self.assertIn("--pull=never", build["argv"])
            self.assertEqual([item["path"] for item in receipt["reviewed_control_files"]], list(MOD.CONTROL_PATHS))
            self.assertEqual(build["argv"][-3:], ["lake", "build", MOD.MODULE])
            self.assertEqual(build["environment"], {})
            self.assertTrue((out / "logs/build.stdout").is_file())
            with self.assertRaisesRegex(ValueError, "output.*absent"): MOD.build(**args)

    def test_checkout_build_tool_and_source_adversaries(self):
        cases = (("head", "wrong_head", "checkout identity"), ("dirty", "dirty", "checkout identity"),
                 ("build-rc", "build_rc", "build command"), ("missing", "missing_olean", "target olean"),
                 ("empty", "empty_olean", "target olean is empty"), ("lean", "bad_lean", "Lean version"),
                 ("lake", "bad_lake", "Lake version"), ("hashes", "bad_hashes", "tool hash"),
                 ("source", "source_bad", "endpoint source"), ("inherited", "inherited_lake", "inherited .lake"),
                 ("source-drift", "source_drift", "source tree changed"),
                 ("missing-control", "missing_control", "lake-manifest.json"),
                 ("control-oid", "bad_control_oid", "control file Git identity"),
                 ("control-drift", "control_drift", "lean-toolchain.*hash mismatch"),
                 ("metrics", "zero_metrics", "malformed metrics"))
        for name, key, message in cases:
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                root = Path(directory); args, state, _ = fixture(root); state[key] = 20 if key == "build_rc" else True
                with self.assertRaisesRegex(ValueError, message): MOD.build(**args)
                self.assertFalse(args["output"].exists())

    def test_schema_cache_symlink_toctou_and_retry(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); args, _, paths = fixture(root)
            post = json.loads(paths["post"].read_text()); post["leaf_count"] = 2
            args["post_receipt_sha256"] = write(paths["post"], post)
            with self.assertRaisesRegex(ValueError, "post-module receipt"): MOD.build(**args)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); args, _, paths = fixture(root)
            cache = json.loads(paths["cache"].read_text()); cache["entries"][0]["path"] = "../bad"
            args["cache_manifest_sha256"] = write(paths["cache"], cache)
            with self.assertRaisesRegex(ValueError, "cache entry"): MOD.build(**args)
        for suffix in ("Leaf.olean", "Aggregate.ilean"):
            with self.subTest(generated_cache=suffix), tempfile.TemporaryDirectory() as directory:
                root = Path(directory); args, _, paths = fixture(root)
                cache = json.loads(paths["cache"].read_text())
                cache["entries"][0]["path"] = ".lake/build/lib/lean/Proofs/Generated/" + suffix
                cache["identity_sha256"] = hashlib.sha256(MOD.canonical(cache["entries"])).hexdigest()
                args["cache_manifest_sha256"] = write(paths["cache"], cache)
                with self.assertRaisesRegex(ValueError, "generated-tree Lean artifact"): MOD.build(**args)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); args, _, paths = fixture(root)
            evidence = json.loads(paths["evidence"].read_text()); evidence["rows"][0]["ledger_path"] = "bad\\path"
            evidence_pin = write(paths["evidence"], evidence)
            post = json.loads(paths["post"].read_text()); post["evidence_sha256"] = evidence_pin
            args["post_receipt_sha256"] = write(paths["post"], post)
            with self.assertRaisesRegex(ValueError, "evidence row ledger_path"): MOD.build(**args)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); args, _, paths = fixture(root)
            real = paths["entry"].with_suffix(".real"); paths["entry"].rename(real); paths["entry"].symlink_to(real)
            with self.assertRaisesRegex(ValueError, "cache entry"): MOD.build(**args)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); args, _, paths = fixture(root); original = paths["toolchain"].read_bytes()
            args["before_receipt"] = lambda: paths["toolchain"].write_bytes(original + b"x")
            with self.assertRaisesRegex(ValueError, "input drift"): MOD.build(**args)
            self.assertFalse(args["output"].exists())
            paths["toolchain"].write_bytes(original); del args["before_receipt"]
            MOD.build(**args); self.assertTrue((args["output"] / "receipt.json").is_file())
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); args, _, _ = fixture(root); real_copy = MOD.shutil.copyfile
            def corrupt_copy(source, destination):
                result = real_copy(source, destination)
                if str(destination).endswith(".lake/packages/mathlib/.ready"): Path(destination).write_bytes(b"corrupt\n")
                return result
            with mock.patch.object(MOD.shutil, "copyfile", side_effect=corrupt_copy):
                with self.assertRaisesRegex(ValueError, "staged dependency cache entry"): MOD.build(**args)

    def test_toolchain_commit_and_output_toctou_adversaries(self):
        for name, mutate, message in (
            ("image", lambda a, p: mutate_json_arg(a, p["toolchain"], "toolchain_sha256", "image", "wrong"),
             "toolchain contract"),
            ("network", lambda a, p: mutate_template(a, p["toolchain"], "build"), "toolchain contract"),
            ("commit", lambda a, p: a.__setitem__("source_commit", "c" * 40), "post-module receipt"),
        ):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                root = Path(directory); args, _, paths = fixture(root); mutate(args, paths)
                with self.assertRaisesRegex(ValueError, message): MOD.build(**args)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); args, _, paths = fixture(root)
            real = paths["runtime"].with_suffix(".real"); paths["runtime"].rename(real); paths["runtime"].symlink_to(real)
            with self.assertRaisesRegex(ValueError, "container runtime"): MOD.build(**args)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); args, _, _ = fixture(root)
            def mutate_olean():
                matches = list(root.glob(".h1-cold-build-stage.*/checkout/proofs/.lake/build/lib/lean/Proofs/Generated/*.olean"))
                assert len(matches) == 1; matches[0].write_bytes(b"drift\n")
            args["before_receipt"] = mutate_olean
            with self.assertRaisesRegex(ValueError, "target olean drift"): MOD.build(**args)
            self.assertFalse(args["output"].exists())


def mutate_json_arg(args, path, pin_key, key, value):
    document = json.loads(path.read_text()); document[key] = value; args[pin_key] = write(path, document)


def mutate_template(args, path, kind):
    document = json.loads(path.read_text()); document["command_templates"][kind] = ["wrong"]
    args["toolchain_sha256"] = write(path, document)


if __name__ == "__main__": unittest.main()
