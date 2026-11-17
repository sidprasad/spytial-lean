"""Prepare Gillon's Appendix A as an inspectable module in the mathlib example project."""

import argparse
import re
import subprocess
import tempfile
from collections import defaultdict
from pathlib import Path
from xml.etree import ElementTree

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent


def read_listing(pdf, work):
    # The PDF paints some subscripts separately from the rest of the identifier.
    # Sort glyphs by their coordinates so rₗ is reconstructed as one Lean name.
    subprocess.run(
        ["gs", "-q", "-dBATCH", "-dNOPAUSE", "-sDEVICE=txtwrite", "-dTextFormat=0",
         "-dFirstPage=6", "-dLastPage=47", f"-sOutputFile={work}/page-%03d.xml", str(pdf)],
        check=True,
    )
    lines = []
    for page in sorted(work.glob("page-*.xml")):
        rows = defaultdict(list)
        for glyph in ElementTree.parse(page).iter("char"):
            x, y, _, _ = map(float, glyph.attrib["bbox"].split())
            rows[y].append((x, glyph.attrib["c"]))
        last_y = 0
        for y, row in sorted(rows.items()):
            if y - last_y > 14:
                lines.append("")
            lines.append("".join(char for _, char in sorted(row, key=lambda g: g[0])).rstrip())
            last_y = y
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("pdf", type=Path, help="Verified AVL Trees in Lean 4, April 30, 2024")
    args = parser.parse_args()
    destination = PROJECT / ".lake" / "gillon" / "Gillon.lean"
    destination.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=destination.parent) as tmp:
        work = Path(tmp)
        listing = read_listing(args.pdf.resolve(), work)
        # Restore the local-definition unfolding used by the published simp scripts.
        listing = re.sub(r"\bsimp only\b", "simp +zetaDelta -failIfUnchanged only", listing)
        module = work / "Gillon.lean"
        module.write_text(listing, encoding="utf-8")
        subprocess.run(
            ["patch", "-s", "-F", "0", str(module), str(HERE / "lean-4.33.patch")],
            cwd=work, check=True,
        )
        module.replace(destination)
    print(destination)


if __name__ == "__main__":
    main()
