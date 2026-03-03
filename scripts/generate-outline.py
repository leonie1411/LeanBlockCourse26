#!/usr/bin/env -S uv run --quiet --script
# /// script
# requires-python = ">=3.11"
# ///
"""Generate OUTLINE.md from repo contents (slides, sections, exercise blocks)."""

import re
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CODE_DIR = ROOT / "LeanBlockCourse26"
SLIDES_DIR = ROOT / "lecture-slides"
OUT = ROOT / "OUTLINE.md"

GITHUB_BLOB = "https://github.com/FordUniver/LeanBlockCourse26/blob/main"

# Static part metadata: (directory_name, description)
# Only parts listed here appear in the outline.
PARTS = [
    ("P01_Introduction", "Why formalize maths? The tech stack: how to properly organize a formalization project."),
    ("P02_Logic", "Foundations of logic in Lean: what is a type and what does being classical vs. intuitionistic mean?"),
    ("P03_SetTheory", "Set theory in Lean: why you should rarely do set theory in Lean."),
    ("P04_TypeTheory", "Dependent type theory: where do the axioms live?"),
    ("P05_NaturalNumbers", "Natural numbers in Lean: why inductive types are so powerful."),
]

TITLE_RE = re.compile(r"^# (.+)$", re.MULTILINE)
BLOCK_RE = re.compile(r"^## .*[Ee]xercise.*$", re.MULTILINE)
EXERCISE_RE = re.compile(r"^-- Exercise (.+)$", re.MULTILINE)


@dataclass
class Exercise:
    label: str
    line: int
    description: str = ""


@dataclass
class ExerciseBlock:
    heading: str
    line: int
    exercises: list[Exercise] = field(default_factory=list)


@dataclass
class Section:
    name: str
    topic: str
    rel_path: str
    blocks: list[ExerciseBlock] = field(default_factory=list)


def line_of(text: str, pos: int) -> int:
    """Convert byte offset to 1-based line number."""
    return text[:pos].count("\n") + 1


def github_url(rel_path: str, line: int | None = None) -> str:
    url = f"{GITHUB_BLOB}/{rel_path}"
    if line is not None:
        url += f"#L{line}"
    return url


def find_slides(part: str) -> Path | None:
    pdf = SLIDES_DIR / f"{part}.pdf"
    return pdf if pdf.exists() else None


def find_sections(part: str) -> list[Section]:
    part_dir = CODE_DIR / part
    if not part_dir.is_dir():
        return []

    sections = []
    for f in sorted(part_dir.glob("S*.lean")):
        text = f.read_text()
        lines = text.splitlines()
        rel_path = f.relative_to(ROOT)

        # Extract topic from first `# Title` inside a doc comment
        topic = ""
        if m := TITLE_RE.search(text):
            topic = m.group(1).strip().rstrip("=").strip()

        # Find exercise blocks and their positions
        block_matches = list(BLOCK_RE.finditer(text))
        blocks: list[ExerciseBlock] = []

        for i, bm in enumerate(block_matches):
            block_line = line_of(text, bm.start())
            heading = bm.group(0).removeprefix("## ")

            # Region: from block heading to next block heading or EOF
            start = bm.end()
            end = block_matches[i + 1].start() if i + 1 < len(block_matches) else len(text)
            region = text[start:end]
            region_offset = start

            # Find individual exercises in this region
            exercises: list[Exercise] = []
            for em in EXERCISE_RE.finditer(region):
                ex_line = line_of(text, region_offset + em.start())
                label = em.group(1).strip()

                # Extract description from following `-- ` comment lines
                desc_parts = []
                for subsequent in lines[ex_line:]:  # lines after the exercise label
                    if subsequent.startswith("-- ") and not subsequent.startswith("-- Exercise "):
                        desc_parts.append(subsequent[3:].strip())
                    else:
                        break
                description = " ".join(desc_parts)

                exercises.append(Exercise(label=label, line=ex_line, description=description))

            blocks.append(ExerciseBlock(heading=heading, line=block_line, exercises=exercises))

        sections.append(Section(
            name=f.stem,
            topic=topic,
            rel_path=str(rel_path),
            blocks=blocks,
        ))

    return sections


def generate() -> str:
    lines = [
        "---",
        "title: Outline",
        "nav_order: 2",
        "---",
        "",
        "# Course Outline",
        "",
        "The course outline is still subject to change, but will roughly be as follows.",
    ]

    for part, description in PARTS:
        lines.append("")
        lines.append("---")
        lines.append("")
        lines.append(f"## {part}")
        lines.append("")
        lines.append(description)

        # Slides
        if pdf := find_slides(part):
            rel = pdf.relative_to(ROOT)
            lines.append("")
            lines.append(f"**Slides:** [{pdf.name}]({rel})")

        # Sections
        sections = find_sections(part)
        if not sections:
            continue

        lines.append("")
        lines.append("| Section | Topic |")
        lines.append("|---------|-------|")
        for sec in sections:
            link = f"[{sec.name}]({github_url(sec.rel_path)})"
            lines.append(f"| {link} | {sec.topic} |")

        # Exercise details
        has_exercises = any(sec.blocks for sec in sections)
        if not has_exercises:
            continue

        lines.append("")
        lines.append("**Exercises:**")
        for sec in sections:
            for block in sec.blocks:
                block_link = f"[{block.heading}]({github_url(sec.rel_path, block.line)})"
                lines.append(f"- **{sec.name}** — {block_link}")
                for ex in block.exercises:
                    ex_link = f"[{ex.label}]({github_url(sec.rel_path, ex.line)})"
                    desc = f" — {ex.description}" if ex.description else ""
                    lines.append(f"  - {ex_link}{desc}")

    # Examination (static)
    lines.append("")
    lines.append("---")
    lines.append("")
    lines.append("## Examination")
    lines.append("")
    lines.append("Final exam and distribution of formalization projects for Master-level students.")
    lines.append("")

    return "\n".join(lines)


if __name__ == "__main__":
    content = generate()
    OUT.write_text(content)
    print(f"Generated {OUT.relative_to(ROOT)}")
