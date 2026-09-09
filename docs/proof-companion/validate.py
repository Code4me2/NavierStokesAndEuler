#!/usr/bin/env python3
"""Read-only, standard-library documentation checks. NOT a Lean/math validator.

Run with Python 3 from any working directory. No network, Lake, imports of
project code, or writes. Source-map targets are checked only against declaration
spellings in the linked file; this does NOT resolve namespaces or hypotheses.
Markdown support: inline relative links, explicit HTML ids, simple heading slugs.
Reference-style links and external URLs are outside this check's scope.
"""
from pathlib import Path
import re
import sys
from urllib.parse import unquote, urlsplit

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
LINK = re.compile(r"(?<!!)\[[^\]\n]*\]\(([^)\n]+)\)")
ID = re.compile(r'^\s*<a\s+id="([^"]+)"\s*>', re.MULTILINE)
HUMAN = re.compile(r"(?:nsc|nsa|eul)-\d{3}\Z")
NAME = re.compile(r"`((?:NavierStokes\.|NavierStokesR3\.|Euler\.|Euler[A-Z])[A-Za-z0-9_.]+)`")
DECL = re.compile(r"\b(?:theorem|lemma|def|abbrev|structure|class|opaque|axiom)\s+([\w'.]+)")


def prose(text):
    # Fenced examples are not live Markdown links or declaration targets.
    return re.sub(r"^```[^\n]*\n.*?^```[^\n]*$", "", text,
                  flags=re.MULTILINE | re.DOTALL)


def anchors(text):
    result = set(ID.findall(text))
    for heading in re.findall(r"^#{1,6}\s+(.+)$", text, re.MULTILINE):
        slug = re.sub(r"[^\w\- ]", "", heading.lower()).replace(" ", "-")
        result.add(slug)
    return result


def main():
    errors = []
    links = targets = 0
    all_ids = []
    files = sorted(HERE.glob("*.md"))
    for path in files:
        text = prose(path.read_text(encoding="utf-8"))
        ids = ID.findall(text)
        if len(ids) != len(set(ids)):
            errors.append(f"{path.name}: duplicate explicit anchor")
        all_ids.extend(i for i in ids if HUMAN.fullmatch(i))
        for raw in LINK.findall(text):
            url = urlsplit(raw)
            if url.scheme or url.netloc:
                continue
            links += 1
            dest = (path.parent / unquote(url.path)).resolve() if url.path else path
            if not dest.exists():
                errors.append(f"{path.name}: missing file {raw}")
            elif url.fragment:
                if dest.suffix != ".md":
                    errors.append(f"{path.name}: unsupported non-Markdown fragment {raw}")
                elif unquote(url.fragment) not in anchors(prose(dest.read_text(encoding="utf-8"))):
                    errors.append(f"{path.name}: missing anchor {raw}")
    if len(all_ids) != len(set(all_ids)):
        errors.append("duplicate human IDs across chapters")
    source_map = (HERE / "SOURCE-MAP.md").read_text(encoding="utf-8")
    mapped = re.findall(r"^### \[((?:NSC|NSA|EUL)-\d{3})\]", source_map, re.MULTILINE)
    if len(mapped) != len(set(mapped)):
        errors.append("duplicate source-map lemma entries")
    if {s.lower() for s in mapped} != set(all_ids):
        errors.append("source-map/chapter human ID coverage differs")
    # Explicit source-map lines only: each file link scopes its backtick names.
    # Suffix spelling is deliberately weaker than qualified Lean name resolution.
    for line in source_map.splitlines():
        file_links = [s for s in LINK.findall(line) if s.endswith(".lean")]
        if not file_links:
            continue
        if len(file_links) != 1:
            errors.append("source-map source line must have exactly one Lean file link")
            continue
        path = (HERE / file_links[0]).resolve()
        if not path.is_file():
            continue  # already reported by link check
        declarations = set(DECL.findall(path.read_text(encoding="utf-8")))
        for name in NAME.findall(line):
            targets += 1
            if not any(name == d or name.endswith("." + d) for d in declarations):
                errors.append(f"{path.relative_to(ROOT)}: no lexical declaration suffix for {name}")
    root_readme = (ROOT / "README.md").read_text(encoding="utf-8")
    if "docs/proof-companion/README.md" not in LINK.findall(root_readme):
        errors.append("repository README missing companion discoverability link")
    print(f"Checked {len(files)} Markdown files, {links} relative links, "
          f"{len(all_ids)} human IDs, {len(mapped)} mapped lemmas, "
          f"{targets} lexical source targets.")
    for error in errors:
        print("ERROR:", error)
    print("FAIL" if errors else "PASS (mechanical scope only)")
    print("Not checked: Lean namespaces/elaboration, hypotheses, mathematics, "
          "external URLs, kernel validity, Comparator fidelity.")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
