"""Freeze the endpoint's project-source closure; performs no Lean execution."""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
ENDPOINT = "Erdos85FiniteDropCapstone"


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def uncomment(text):
    """Preserve strings/newlines while removing nested Lean comments."""
    result, i, depth, string = [], 0, 0, False
    while i < len(text):
        pair = text[i:i + 2]
        char = text[i]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                result.append(" ")
                i += 2
            else:
                result.append("\n" if char == "\n" else " ")
                i += 1
        elif string:
            result.append(char)
            i += 1
            if char == "\\" and i < len(text):
                result.append(text[i])
                i += 1
            elif char == '"':
                string = False
        elif pair == "/-":
            depth = 1
            i += 2
        elif pair == "--":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            result.append(char)
            string = char == '"'
            i += 1
    if depth or string:
        raise ValueError("Unterminated Lean comment/string")
    return "".join(result)


def closure(root):
    sources, visiting = {}, set()

    def visit(name):
        if name in visiting:
            raise ValueError("Cyclic project imports: " + name)
        if name in sources:
            return
        visiting.add(name)
        path = root / "proofs/Proofs" / (name.replace(".", "/") + ".lean")
        clean = uncomment(path.read_text())
        dependencies = []
        for line in re.findall(r"^\s*(?:public\s+|private\s+)?import\s+([^\n]+)", clean, re.M):
            for module in line.split():
                if module.startswith("Proofs."):
                    dep = module.removeprefix("Proofs.")
                    visit(dep)
                    dependencies.append(dep)
        if re.search(r"\b(sorry|admit)\b", re.sub(r'"(?:\\.|[^"\\])*"', '""', clean)):
            raise ValueError("Admission in source: " + name)
        sources[name] = {"sha256": sha(path), "dependencies": sorted(set(dependencies))}
        visiting.remove(name)

    visit(ENDPOINT)
    return sources


def make_plan(root):
    sources = closure(root)
    baseline = json.loads((root / "research/problems/erdos-85-wip-01/release_assembly_20261011/source-manifest.json").read_text())["sources"]
    if set(sources) != set(baseline) or len(sources) != 893:
        raise ValueError("Endpoint closure differs from accepted 893-source scope")
    changed = [n for n in sources if sources[n]["sha256"] != baseline[n]]
    allowed = re.compile(r"Erdos85OrderFortyNineSevenHighT[1-7]Rep[0-2]Certificate$")
    if any(not allowed.fullmatch(n) for n in changed):
        raise ValueError("Unexpected source change: " + repr(changed))
    for name in changed:
        rel = "proofs/Proofs/" + name + ".lean"
        old = subprocess.check_output(["git", "-C", str(root), "show", "a2204511564:" + rel], text=True)
        new = (root / rel).read_text()
        normalize = lambda text: re.sub(r'(\binclude_str\s+)"[^"\n]+"', r'\1"<certificate>"', text)
        if normalize(old) != normalize(new):
            raise ValueError("Certificate edit changes more than include path: " + name)
    artifacts = []
    for name in sources:
        file = root / "proofs/Proofs" / (name.replace(".", "/") + ".lean")
        for raw in re.findall(r'\binclude_str\s+"([^"\n]+)"', uncomment(file.read_text())):
            if Path(raw).is_absolute():
                raise ValueError("Unpublished absolute include path remains: " + name)
            path = (file.parent / raw).resolve()
            path.relative_to(root.resolve())
            artifacts.append({"module": name, "path": str(path.relative_to(root)),
                              "bytes": path.stat().st_size, "sha256": sha(path)})
    evidence = root / "research/problems/erdos-85-wip-01/order49_h3_closed_capstone_20261008/PLAN.json"
    manifest = json.loads((root / "research/problems/erdos-85-wip-01/release_assembly_20261011/source-manifest.json").read_text())
    if sha(evidence) != manifest["accepted_plan_sha256"]:
        raise ValueError("Accepted axiom plan identity changed")
    expected = json.loads(evidence.read_text())["exports"]
    return {"schema": 1, "endpoint": ENDPOINT,
            "source_commit": subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip(),
            "sources": sources, "changed_from_accepted": changed, "artifacts": artifacts,
            "config_sha256": {p: sha(root / "proofs" / p) for p in ("lean-toolchain", "lakefile.toml", "lake-manifest.json")},
            "runner_sha256": {p: sha(Path(__file__).parent / p) for p in ("prepare.py", "run.py", "audit.py")},
            "accepted_axiom_plan_sha256": sha(evidence),
            "expected_exports": expected,
            "limits": {"workers": 6, "memory_gib": 110, "cpus": 16, "wall_seconds": 35400},
            "scope": "Fresh project closure; pinned external Lean/Mathlib packages may be cached. No external SAT replay."}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    plan = make_plan(ROOT)
    with args.output.open("x") as stream:
        json.dump(plan, stream, indent=2)
        stream.write("\n")
    print(json.dumps({"plan": str(args.output), "sha256": sha(args.output), "sources": len(plan["sources"])}))
