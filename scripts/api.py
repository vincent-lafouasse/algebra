# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Bird's-eye view of the library: list every declaration in Algebra/ into API.md.

No parsing: a declaration starts on a line beginning with a keyword, and its
signature is everything up to the first `:=` or a trailing `where`.

    uv run scripts/api.py
"""

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "Algebra"
OUT = ROOT / "API.md"

DECL = re.compile(
    r"^((?:(?:@\[[^\]]*\]|noncomputable|protected|private|scoped)\s+)*"
    r"(?:theorem|lemma|def|instance|class|structure|abbrev))\s+(\S+)(.*)"
)


def flat(text: str) -> str:
    return " ".join(text.split())


def assign(line: str, depth: int) -> int:
    """Index of the first `:=` outside brackets, or -1 (`{ toFun := g }` doesn't count)."""
    for k, c in enumerate(line):
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif depth == 0 and line.startswith(":=", k):
            return k
    return -1


def render(name: str, rest: str) -> str:
    """Crude highlighting: **name** `binders` : **`statement`**.

    The statement starts at the first ` : ` outside brackets; colons inside
    binders like `(f : G →* H)` don't count.
    """
    rest = " " + rest.strip()  # so a leading `: T` (anonymous instance) is found too
    binders, statement, depth = rest.strip(), "", 0
    for k, c in enumerate(rest):
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        elif depth == 0 and rest[k - 1 : k + 2] == " : ":
            binders, statement = rest[:k].strip(), rest[k + 1 :].strip()
            break
    out = [f"**{name}**"] if name else []
    if binders:
        out.append(f"`{binders}`")
    if statement:
        out.append(f": **`{statement}`**")
    return " ".join(out)


def fields(body: list[str]) -> list[str]:
    """Fields of a class/structure: lines indented by exactly 2, plus deeper continuations."""
    out: list[str] = []
    for line in body:
        if re.match(r"^  \S", line) and not line.lstrip().startswith("--"):
            out.append(line.strip())
        elif out and line.startswith("   "):
            out[-1] += " " + line.strip()
    return [flat(f) for f in out]


def scan(path: Path) -> list[str]:
    lines = path.read_text().splitlines()
    out: list[str] = []
    namespaces: list[str] = []
    comment: list[str] = []
    attrs: list[str] = []
    i = 0
    while i < len(lines):
        line = lines[i]

        # comments: `/-- doc -/` and `--` lines become the description, `/- -/` is skipped
        if line.startswith("/-"):
            block = [line]
            while "-/" not in block[-1][2:] and i + 1 < len(lines):
                i += 1
                block.append(lines[i])
            if line.startswith("/--"):
                comment = [flat(" ".join(block).removeprefix("/--").removesuffix("-/"))]
            i += 1
            continue
        if line.startswith("--"):
            comment.append(line.removeprefix("--").strip())
            i += 1
            continue

        # an attribute on its own line belongs to the next declaration
        if re.match(r"^@\[[^\]]*\]\s*$", line):
            attrs.append(line.strip())
            i += 1
            continue

        if m := re.match(r"^namespace (\S+)", line):
            namespaces += m.group(1).split(".")
        elif m := re.match(r"^end (\S+)", line):
            del namespaces[-len(m.group(1).split(".")) :]
        elif m := DECL.match(line):
            # signature: everything up to `:=` (outside brackets) or a trailing `where`
            sig, body, depth = [], [], 0
            while i < len(lines):
                cur = lines[i]
                if (k := assign(cur, depth)) >= 0:
                    sig.append(cur[:k])
                    body = [cur[k + 2 :]]
                    break
                depth += sum(cur.count(c) for c in "([{") - sum(cur.count(c) for c in ")]}")
                if re.search(r"\bwhere\s*$", cur):
                    sig.append(re.sub(r"\bwhere\s*$", "", cur))
                    break
                sig.append(cur)
                i += 1
            # body: the rest of the line, then indented or blank lines
            i += 1
            while i < len(lines) and (not lines[i].strip() or lines[i][0].isspace()):
                body.append(lines[i])
                i += 1

            keyword, name = flat(m.group(1)), m.group(2)
            rest = flat(" ".join(sig)).removeprefix(keyword).lstrip()
            if name[0] in ":([{":  # anonymous instance
                name = ""
            else:
                rest = rest.removeprefix(name)
                prefix = ".".join(n for n in namespaces if n != "My")
                name = f"{prefix}.{name}" if prefix else name
            head = " ".join(f"`{a}`" for a in attrs)
            entry = f"- {head + ' ' if head else ''}*{keyword}* {render(name, rest)}"
            if re.search(r"\bsorry\b", " ".join(body)):
                entry += " **(sorry)**"
            if comment:
                entry += f"  \n  {' '.join(comment)}"
            if keyword.endswith(("class", "structure")):
                for f in fields(body):
                    fname, _, frest = f.partition(" ")
                    entry += f"\n  - {render(fname, frest)}"
            out.append(entry)
            comment, attrs = [], []
            continue

        comment, attrs = [], []
        i += 1
    return out


def main() -> None:
    parts = ["# API\n", "Generated by `uv run scripts/api.py`, do not edit by hand.\n"]
    for path in sorted(SRC.rglob("*.lean")):
        if entries := scan(path):
            parts += [f"## {path.relative_to(ROOT)}\n", "\n".join(entries) + "\n"]
    OUT.write_text("\n".join(parts))
    print(f"wrote {OUT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
