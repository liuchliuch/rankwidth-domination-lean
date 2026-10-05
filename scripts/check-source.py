#!/usr/bin/env python3
"""Conservative source hygiene check; kernel and axiom audits remain mandatory.

Challenge files and negative controls are intentionally outside the submitted
proof source tree. This lexical check is not a proof validator.
"""
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]


def code_only(text: str) -> str:
    """Remove Lean's nested comments and string literals, preserving newlines."""
    output = []
    position = 0
    depth = 0
    quoted = False
    while position < len(text):
        pair = text[position:position + 2]
        char = text[position]
        if depth:
            if pair == "/-":
                depth += 1
                output.extend("  ")
                position += 2
            elif pair == "-/":
                depth -= 1
                output.extend("  ")
                position += 2
            else:
                output.append("\n" if char == "\n" else " ")
                position += 1
        elif quoted:
            if char == "\\" and position + 1 < len(text):
                output.extend("  ")
                position += 2
            else:
                quoted = char != '"'
                output.append("\n" if char == "\n" else " ")
                position += 1
        elif pair == "/-":
            depth = 1
            output.extend("  ")
            position += 2
        elif pair == "--":
            end = text.find("\n", position)
            end = len(text) if end == -1 else end
            output.extend(" " * (end - position))
            position = end
        elif char == '"':
            quoted = True
            output.append(" ")
            position += 1
        else:
            output.append(char)
            position += 1
    if depth or quoted:
        raise ValueError("Unclosed comment or string")
    return "".join(output)


def main() -> int:
    sources = sorted((ROOT / "RankwidthDomination").rglob("*.lean"))
    sources.append(ROOT / "RankwidthDomination.lean")
    sources.extend(sorted((ROOT / "verification/comparator/solution").rglob("*.lean")))
    forbidden = re.compile(
        r"\b(?:sorry|admit|axiom|unsafe|native_decide|run_cmd|run_elab|"
        r"implemented_by|extern)\b|debug\.skipKernelTC|Lean\.ofReduceBool"
    )
    errors = []
    for source in sources:
        text = source.read_text(encoding="utf-8")
        code = code_only(text)
        for match in forbidden.finditer(code):
            line = code.count("\n", 0, match.start()) + 1
            errors.append(f"{source.relative_to(ROOT)}:{line}: {match.group()}")
        if re.search(r"[\u3400-\u9fff]", text):
            errors.append(f"{source.relative_to(ROOT)}: non-English prose requires review")
    if errors:
        print("FAIL: submitted proof source hygiene", file=sys.stderr)
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"PASS: {len(sources)} submitted source files; no proof placeholders, "
          "custom axioms, unsafe declarations, or kernel-bypass constructs")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
