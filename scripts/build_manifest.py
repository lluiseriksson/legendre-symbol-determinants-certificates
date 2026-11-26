"""Build deterministic MANIFEST.sha256 for paper77-legendre-symbol-determinants-certificates."""

from __future__ import annotations

import hashlib
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]

EXCLUDED_DIRS = {".git", ".lake", "__pycache__", ".pytest_cache", ".venv"}
EXCLUDED_FILES = {"MANIFEST.sha256"}
EXCLUDED_SUFFIXES = {".aux", ".bbl", ".blg", ".log", ".out", ".toc", ".fls", ".fdb_latexmk", ".synctex.gz", ".pyc"}


def main() -> int:
    entries: list[str] = []
    for p in sorted(ROOT.rglob("*")):
        if not p.is_file():
            continue
        rel = p.relative_to(ROOT)
        if any(part in EXCLUDED_DIRS for part in rel.parts):
            continue
        if p.name in EXCLUDED_FILES or p.suffix in EXCLUDED_SUFFIXES:
            continue
        digest = hashlib.sha256(p.read_bytes()).hexdigest()
        entries.append(f"{digest}  {rel.as_posix()}")
    (ROOT / "MANIFEST.sha256").write_text("\n".join(entries) + "\n", encoding="utf-8")
    print(f"Wrote MANIFEST.sha256 with {len(entries)} entries.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
