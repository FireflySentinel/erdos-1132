#!/usr/bin/env python3
"""Compare proposed community statements with the locally proved bridge.

This is a source correspondence check, not a Lean parser or proof checker.
Lean compilation and the axiom guards in the bridge check the proofs.
"""

import argparse
import json
import re
import subprocess
from pathlib import Path


def uncomment(text):
    """Remove nested Lean block comments and line comments, preserving strings."""
    out = []
    i = 0
    depth = 0
    quoted = False
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                i += 2
            else:
                if text[i] == "\n":
                    out.append("\n")
                i += 1
        elif quoted:
            out.append(text[i])
            if text[i] == "\\" and i + 1 < len(text):
                i += 1
                out.append(text[i])
            elif text[i] == '"':
                quoted = False
            i += 1
        elif pair == "/-":
            depth = 1
            out.append(" ")
            i += 2
        elif pair == "--":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i])
            quoted = text[i] == '"'
            i += 1
    if depth or quoted:
        raise ValueError("Unclosed comment or string")
    return "".join(out)


def normalize(text):
    return " ".join(text.split())


def definitions(text):
    # These small, checked files separate each complete definition by a blank line.
    return {name: normalize(body) for body, name in re.findall(
        r"^((?:noncomputable )?def (\w+)\b.*?)(?=^\s*$|\Z)",
        text, re.MULTILINE | re.DOTALL)}


def theorem_types(text):
    return {name: normalize(body) for name, body in re.findall(
        r"^theorem ([\w.]+)\s*:\s*(.*?)\s*:= by\b",
        text, re.MULTILINE | re.DOTALL)}


def check(repo, upstream=None):
    spec = json.loads((repo / "submissions/upstream.json").read_text())
    number = spec["problem"]
    rel = Path(f"FormalConjectures/ErdosProblems/{number}.lean")
    payload = repo / "submissions/formal-conjectures" / rel
    bridge = repo / "checks/FormalConjecturesBridge.lean"
    fc = uncomment(payload.read_text())
    bridge_source = bridge.read_text()
    local = uncomment(bridge_source)
    if re.search(r"\b(sorry|admit|axiom|opaque|unsafe)\b", local):
        raise ValueError("An unfinished or unchecked declaration occurs in the bridge")
    if re.findall(r"^import (.+)$", local, re.MULTILINE) != [f"Erdos{number}"]:
        raise ValueError("The bridge must import only the proved project")
    if not definitions(fc) or definitions(fc) != definitions(local):
        raise ValueError("Community and bridge definitions differ")
    context = r"^(?:open .*|open scoped .*|namespace .*)$"
    if re.findall(context, fc, re.MULTILINE) != re.findall(context, local, re.MULTILINE):
        raise ValueError("Namespace or open declarations differ")
    links = {name: url for url, name in re.findall(
        r'@\[[^\]]*formal_proof using lean4 at "([^"]+)"[^\]]*\]\s*theorem ([\w.]+)',
        fc, re.MULTILINE)}
    actual = theorem_types(local)
    if not links or set(links) != set(actual):
        raise ValueError("The bridge does not cover exactly the external proof claims")
    commit = spec["bridge_commit"]
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise ValueError("The proof link must pin a full commit hash")
    prefix = f"https://github.com/FireflySentinel/erdos-{number}/blob/{commit}/"
    proposed = theorem_types(fc)
    for name, statement in actual.items():
        line = next(i for i, text in enumerate(bridge_source.splitlines(), 1)
                    if re.match(rf"theorem {re.escape(name)}\s*:", text))
        expected_url = f"{prefix}checks/FormalConjecturesBridge.lean#L{line}"
        if links[name] != expected_url:
            raise ValueError(f"Proof link does not select the pinned bridge declaration: {name}")
        expected = proposed[name].replace("answer(True)", "True").replace("answer(False)", "False")
        if statement != expected:
            raise ValueError(f"Statement differs: {name}")
        full = f"Erdos{number}.{name}"
        if f"#print axioms {full}\n" not in local:
            raise ValueError(f"Missing axiom check: {full}")
    if upstream is not None:
        head = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=upstream, text=True).strip()
        if head != spec["formal_conjectures"]["commit"]:
            raise ValueError("Upstream checkout is at a different revision")
        if (upstream / rel).read_bytes() != payload.read_bytes():
            raise ValueError("Upstream copy differs from the prepared file")
    print(f"#{number}: definitions, theorem types, and pinned proof links match the bridge.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, help="Also check the prepared upstream checkout")
    args = parser.parse_args()
    check(Path(__file__).resolve().parents[1], args.upstream)
