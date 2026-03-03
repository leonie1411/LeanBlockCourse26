#!/usr/bin/env -S uv run --quiet --script
# /// script
# requires-python = ">=3.11"
# ///
"""Generate OUTLINE.md and inject announcements into HOME.md."""

import re
import subprocess
from dataclasses import dataclass, field
from datetime import date, datetime, timedelta, timezone
from pathlib import Path
from zoneinfo import ZoneInfo

ROOT = Path(__file__).resolve().parent.parent
CODE_DIR = ROOT / "LeanBlockCourse26"
SLIDES_DIR = ROOT / "lecture-slides"
OUT = ROOT / "OUTLINE.md"
HOME = ROOT / "HOME.md"
README = ROOT / "README.md"

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
BLOCK_LABEL_RE = re.compile(r"B(\d+)")
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

    # Slides table (all parts with available PDFs)
    slide_rows = []
    for part, _ in PARTS:
        if pdf := find_slides(part):
            rel = pdf.relative_to(ROOT)
            slide_rows.append(f"| `{part}` | [{pdf.name}]({rel}) |")
    if slide_rows:
        lines.append("")
        lines.append("## Slides")
        lines.append("")
        lines.append("| Part | PDF |")
        lines.append("|------|-----|")
        lines.extend(slide_rows)

    for part, description in PARTS:
        lines.append("")
        lines.append("---")
        lines.append("")
        lines.append(f"## `{part}`")
        lines.append("")
        lines.append(description)

        # Sections
        sections = find_sections(part)
        if not sections:
            continue

        has_exercises = any(sec.blocks for sec in sections)
        lines.append("")
        if has_exercises:
            lines.append("| Section | Topic | Exercises |")
            lines.append("|---------|-------|-----------|")
        else:
            lines.append("| Section | Topic |")
            lines.append("|---------|-------|")
        for sec in sections:
            link = f"[`{sec.name}`]({github_url(sec.rel_path)})"
            if has_exercises:
                if sec.blocks:
                    def block_label(b: ExerciseBlock, i: int) -> str:
                        if m := BLOCK_LABEL_RE.search(b.heading):
                            return f"B{int(m.group(1)):02d}"
                        return f"B{i + 1:02d}"

                    block_links = " \\| ".join(
                        f"[`{block_label(b, i)}`]({github_url(sec.rel_path, b.line)})"
                        for i, b in enumerate(sec.blocks)
                    )
                else:
                    block_links = "—"
                lines.append(f"| {link} | {sec.topic} | {block_links} |")
            else:
                lines.append(f"| {link} | {sec.topic} |")

    # Examination (static)
    lines.append("")
    lines.append("---")
    lines.append("")
    lines.append("## Examination")
    lines.append("")
    lines.append("Final exam and distribution of formalization projects for Master-level students.")
    lines.append("")

    return "\n".join(lines)


ANNOUNCE_RE = re.compile(
    r"^## Announcements\n(.*?)(?=\n## |\Z)",
    re.MULTILINE | re.DOTALL,
)
ANNOUNCE_DATE_RE = re.compile(r"^\s*-\s+\*\*(\d{4}-\d{2}-\d{2}):\*\*")
BEGIN_MARKER = "<!-- begin announcements -->"
END_MARKER = "<!-- end announcements -->"

RECENT_DAYS = 3
BERLIN = ZoneInfo("Europe/Berlin")


def blame_timestamps(filepath: Path) -> dict[int, datetime]:
    """Map 1-based line numbers to author timestamps via git blame."""
    try:
        result = subprocess.run(
            ["git", "blame", "--porcelain", str(filepath)],
            capture_output=True, text=True, cwd=ROOT, check=True,
        )
    except (subprocess.CalledProcessError, FileNotFoundError):
        return {}

    timestamps: dict[int, datetime] = {}
    sha_cache: dict[str, datetime] = {}
    current_sha: str | None = None
    current_line: int | None = None
    author_time: int | None = None

    for raw in result.stdout.splitlines():
        # New blame entry: <sha> <orig-line> <final-line> [<count>]
        if len(raw) >= 40 and raw[0] in "0123456789abcdef":
            parts = raw.split()
            if len(parts) >= 3:
                current_sha = parts[0]
                current_line = int(parts[2])
                author_time = None
                # If we've seen this sha before, reuse its timestamp
                if current_sha in sha_cache and current_line is not None:
                    timestamps[current_line] = sha_cache[current_sha]
        elif raw.startswith("author-time "):
            author_time = int(raw.split()[1])
        elif raw.startswith("author-tz "):
            if author_time is not None and current_line is not None:
                dt = datetime.fromtimestamp(author_time, tz=timezone.utc)
                ts = dt.astimezone(BERLIN)
                timestamps[current_line] = ts
                if current_sha is not None:
                    sha_cache[current_sha] = ts

    return timestamps


@dataclass
class Announcement:
    d: date
    body: str
    timestamp: datetime | None = None


def parse_announcements() -> list[Announcement]:
    """Parse announcements from README.md with git-blame timestamps."""
    readme_text = README.read_text()
    m = ANNOUNCE_RE.search(readme_text)
    if not m:
        return []

    # Find the line offset of the announcements section in the file
    section_start = readme_text[:m.start()].count("\n") + 1  # 1-based
    body_start = section_start + 1  # skip "## Announcements" line

    lines = [l for l in m.group(1).strip().splitlines() if l.strip()]
    if not lines:
        return []

    # Get timestamps from git blame
    ts_map = blame_timestamps(README)

    # Map each announcement line to its file line number
    all_readme_lines = readme_text.splitlines()
    announcements: list[Announcement] = []
    search_from = body_start - 1  # 0-based index

    for line in lines:
        line_num = None
        for i in range(search_from, len(all_readme_lines)):
            if all_readme_lines[i].strip() == line.strip():
                line_num = i + 1  # 1-based
                search_from = i + 1
                break

        ann_date = date.today()
        body = line.lstrip("- ").strip()
        if dm := ANNOUNCE_DATE_RE.match(line):
            ann_date = date.fromisoformat(dm.group(1))
            body = line[dm.end():].strip()

        ts = ts_map.get(line_num) if line_num else None
        announcements.append(Announcement(d=ann_date, body=body, timestamp=ts))

    return announcements


def inline_md_to_html(text: str) -> str:
    """Convert basic inline markdown (**bold** and `code`) to HTML."""
    text = re.sub(r"\*\*(.+?)\*\*", r"<strong>\1</strong>", text)
    text = re.sub(r"`(.+?)`", r"<code>\1</code>", text)
    return text


def format_label(ann: Announcement) -> str:
    """Format announcement as a date+time label pill."""
    if ann.timestamp:
        text = ann.timestamp.strftime("%a, %b %-d · %-H:%M")
    else:
        text = ann.d.strftime("%a, %b %-d")
    return f'<span class="label label-yellow">{text}</span>'


def render_announcement(ann: Announcement) -> str:
    """Render a single announcement as an HTML paragraph with date label."""
    return f"<p>{format_label(ann)} {inline_md_to_html(ann.body)}</p>"


def inject_announcements() -> None:
    """Extract ## Announcements from README.md and inject into HOME.md.

    Recent announcements (within RECENT_DAYS) are shown in a highlighted
    callout at the top. Older ones are collapsed in a <details> block.
    Timestamps are inferred from git blame.
    """
    announcements = parse_announcements()
    if not announcements:
        return

    cutoff = date.today() - timedelta(days=RECENT_DAYS)
    recent = [a for a in announcements if a.d >= cutoff]
    older = [a for a in announcements if a.d < cutoff]

    parts: list[str] = []

    if recent:
        parts.append('<blockquote class="highlight">')
        for ann in recent:
            parts.append(render_announcement(ann))
        parts.append("</blockquote>")
        parts.append("")

    if older:
        parts.append("<details>")
        summary = "Older announcements" if recent else "Announcements"
        parts.append(f"<summary>{summary}</summary>")
        parts.append('<blockquote class="highlight">')
        for ann in older:
            parts.append(render_announcement(d, body))
        parts.append("</blockquote>")
        parts.append("</details>")
        parts.append("")

    body = "\n".join(parts)

    home = HOME.read_text()
    begin = home.find(BEGIN_MARKER)
    end = home.find(END_MARKER)
    if begin == -1 or end == -1:
        return

    home = home[:begin + len(BEGIN_MARKER)] + "\n" + body + home[end:]
    HOME.write_text(home)


if __name__ == "__main__":
    content = generate()
    OUT.write_text(content)
    print(f"Generated {OUT.relative_to(ROOT)}")

    inject_announcements()
    print(f"Injected announcements into {HOME.relative_to(ROOT)}")
