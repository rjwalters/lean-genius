#!/usr/bin/env python3
"""Scope lint for the erdos85-drop paper thread (operator scope rules, BRIEF.md).

Usage: python3 scope_lint.py erdos85-drop.N/main.tex [--refs erdos85-drop/refs]

Checks, read-only:
 1. Banned claim patterns (overclaiming): Result A called a theorem/proof/decided; claims about
    Erdős 85 itself; A-REG called "our conjecture"; verdicts/certificates "prove".
 2. AI-tell words the reviewer flagged (honest, candid, genuinely) outside allowed phrases.
 3. Number traceability: every number with 4+ digits (with or without commas) or a decimal with a
    unit (TB, GB, h, hours, core-hours, $) must occur somewhere in the refs corpus, excluding the
    prior draft (refs/DRAFT.md) so the draft cannot vouch for itself.
 4. Lean identifiers in \\texttt{} must exist as declarations in proofs/Proofs (or be listed in
    the "planned names" allowlist below).
Exit 1 if any check fails. This is a helper for the reviser/operator, not part of the anvil rubric.
"""
from __future__ import annotations
import argparse, pathlib, re, subprocess, sys

BANNED = [
    (r"Result A (is|was|has been) (a |an )?(proved|proven|theorem|decided)", "Result A called proved/theorem/decided"),
    (r"(?<!not a )(?<!not )(decided|proved|proven) (strict )?drop(?![^.]*(to our knowledge|computational|evidence))", "'decided/proved drop' without the epistemic or evidence-level qualifier"),
    (r"(settles?|resolves?|answers?|refutes?|disproves?) Erd[őo]s Problem 85(?! itself)", "claim about Erdős 85 itself"),
    (r"our conjecture|we conjecture|the authors conjecture", "A-REG or another statement called the authors' conjecture"),
    (r"(verdicts?|certificates?) (prove|proves|proved|establish|establishes) (that )?(the|no|non)", "verdict/certificate said to prove"),
    (r"kernel[- ]checked (drop|nonexistence|Result A)", "verdict-level result described as kernel-checked"),
]
TELLS = [(r"\bhonest(ly)?\b(?! scoping)", "honest"), (r"\bcandid(ly)?\b", "candid"), (r"\bgenuinely\b", "genuinely")]
PLANNED = {"minDegreeForC4_fortyEight_fortyNine_exact_of_generatedSevenBaseCertificates",
           "minDegreeForC4_fortyNine_lt_fortyEight_of_generatedSevenBaseCertificates"}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("main_tex", type=pathlib.Path)
    ap.add_argument("--refs", type=pathlib.Path, default=None)
    ap.add_argument("--proofs", type=pathlib.Path, default=pathlib.Path("/Volumes/Stripe/lean-genius/claude-e85-wrapup/proofs/Proofs"))
    a = ap.parse_args()
    tex = a.main_tex.read_text()
    body = re.sub(r"(?m)^%.*$", "", tex)
    refs = a.refs or (a.main_tex.parent.parent / "erdos85-drop" / "refs")
    corpus = "\n".join(p.read_text(errors="replace") for p in refs.iterdir() if p.is_file() and p.name != "DRAFT.md")
    corpus_norm = corpus.replace(",", "")
    fails = 0
    for pat, why in BANNED:
        for m in re.finditer(pat, body, re.I):
            fails += 1; print(f"BANNED [{why}]: …{body[max(0,m.start()-60):m.end()+40].strip()}…")
    for pat, w in TELLS:
        n = len(re.findall(pat, body, re.I))
        if n: fails += 1; print(f"TELL: '{w}' x{n}")
    scan = re.sub(r"\\\{[^}]*\\\}", " ", body)                     # set notation like \{120,121\}
    scan = re.sub(r"(msgs?|messages?|entry|entries|divergence|#)\s*[0-9][0-9,\s\u2013\-and]*", " ", scan)  # transcript pointers
    scan = re.sub(r"10\.\d{4}/[^\s}]+", " ", scan)                    # DOIs
    scan = re.sub(r"\\real\{[0-9.]+\}", " ", scan)                    # table column widths
    scan = re.sub(r"\[Scale=[0-9.]+\]", " ", scan)
    nums = set(re.findall(r"(?<![\w.])(\d{1,3}(?:,\d{3})+|\d{4,}|\d+\.\d+)(?=\s*(?:TB|GB|MB|h\b|hours|core-hours|host-hours|box-hours|days|\\%|%|per|USD|\$)|\b)", scan))
    untraced = sorted(n for n in nums if n.replace(",", "") not in corpus_norm and not re.fullmatch(r"(19|20)\d\d", n))
    if untraced: fails += 1; print("UNTRACED NUMBERS (not found in refs, excluding DRAFT.md):", ", ".join(untraced))
    ids = {m.replace("\\_", "_") for m in re.findall(r"\\texttt\{([A-Za-z][A-Za-z0-9_.\\]*(?:\\?_[A-Za-z0-9]+)+)\}", body)}
    decls = subprocess.run(["grep", "-rhoE", r"^(theorem|lemma|def|abbrev|structure|inductive|noncomputable def|instance|class|opaque|axiom) +[A-Za-z0-9_.]+", str(a.proofs)], capture_output=True, text=True).stdout
    declset = {l.split()[-1] for l in decls.splitlines()}
    NOT_DECLS = {"m_c", "native_decide"}
    missing = sorted(i for i in ids if i.split(".")[-1] not in declset and i not in PLANNED and i not in NOT_DECLS
                     and not re.fullmatch(r"h1_[0-9a-f]{16}", i) and not i.endswith((".lean", ".md", ".py", ".json")) and "/" not in i)
    if missing: fails += 1; print("LEAN NAMES NOT FOUND:", ", ".join(missing))
    print("scope_lint:", "FAIL" if fails else "PASS", f"({len(nums)} numbers checked, {len(ids)} Lean names checked)")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
