"""Remove cached project modules whose Lean source has been moved or deleted.

Mathlib and other dependency caches are left intact. This is needed before
leanchecker, which can otherwise load declarations from obsolete module paths.
"""

from pathlib import Path


root = Path(__file__).resolve().parents[1]
for directory in ("lib/lean", "ir"):
    cache = root / ".lake/build" / directory / "Erdos1132"
    if not cache.exists():
        continue
    for artifact in cache.rglob("*"):
        if not artifact.is_file():
            continue
        relative = artifact.relative_to(cache)
        source = root / "Erdos1132" / relative.parent / (artifact.name.split(".")[0] + ".lean")
        if not source.is_file():
            artifact.unlink()
