#!/usr/bin/env python3
"""Strip author-side comments from prose before a blind-read subagent sees it.

The blind-read loop hands a piece of prose to a fresh, context-free subagent so it
reads ONLY what a real reader would see. Source files carry author-side notes the
reader never sees: LaTeX `%` comments (in this project, Chinese margin notes that
record the author's intent and reasoning) and HTML/Markdown `<!-- ... -->` comments.
Those notes are exactly the curse-of-knowledge channel the blind read exists to close,
so they must be removed from the TARGET (and CONTEXT) files first.

Reads from a file argument or stdin, writes the comment-free text to stdout:

    sed -n '100,160p' src.tex | strip-comments.py --style latex > "$target"
    strip-comments.py README.md > "$target"          # style auto-detected from .md

Offensive programming: an unknown style or an unrecognized extension under
`--style auto` raises ValueError immediately rather than guessing wrong and
silently leaking notes to the reader.
"""

from __future__ import annotations

import argparse
import logging
import re
import sys
from collections.abc import Iterable

logger = logging.getLogger(__name__)

_EXTENSION_STYLES = {
    ".tex": "latex",
    ".sty": "latex",
    ".cls": "latex",
    ".md": "html",
    ".markdown": "html",
    ".html": "html",
    ".htm": "html",
}

_HTML_COMMENT = re.compile(r"<!--.*?-->", re.DOTALL)


def _latex_comment_start(line: str) -> int | None:
    """Index of the unescaped `%` that starts a LaTeX comment, or None.

    Walks the line as LaTeX tokenizes it: a backslash forms a control sequence with
    the next character, so `\\%` is a literal percent and `\\\\%` is a line break
    followed by a comment. A `%` reached outside such an escape starts the comment.
    """
    index = 0
    length = len(line)
    while index < length:
        character = line[index]
        if character == "\\":
            index += 2
            continue
        if character == "%":
            return index
        index += 1
    return None


def strip_latex(text: str) -> str:
    """Remove LaTeX `%` comments, dropping lines that were nothing but a comment.

    A `%` comment is invisible to LaTeX and never breaks a paragraph, so a
    comment-only line is dropped entirely instead of being left as a blank line that
    would read as a spurious paragraph break. An inline comment keeps the prose
    before the `%`.
    """
    kept_lines = []
    for line in text.splitlines():
        comment_start = _latex_comment_start(line)
        if comment_start is None:
            kept_lines.append(line)
            continue
        prefix = line[:comment_start]
        if prefix.strip() == "":
            logger.debug("dropping comment-only line: %(line)r", {"line": line})
            continue
        kept_lines.append(prefix.rstrip())
    return _join_lines(kept_lines, trailing_newline=text.endswith("\n"))


def strip_html(text: str) -> str:
    """Remove `<!-- ... -->` comments (including multi-line ones) from prose.

    After removal a run of blank lines left where a comment used to stand is collapsed
    to a single blank line: multiple blank lines render the same as one in Markdown, so
    this preserves genuine paragraph breaks while erasing comment-induced gaps.
    """
    without_comments = _HTML_COMMENT.sub("", text)
    collapsed = _collapse_blank_runs(without_comments.splitlines())
    return _join_lines(collapsed, trailing_newline=text.endswith("\n"))


def _collapse_blank_runs(lines: Iterable[str]) -> list[str]:
    kept_lines = []
    previous_blank = False
    for line in lines:
        stripped = line.rstrip()
        is_blank = stripped == ""
        if is_blank and previous_blank:
            continue
        kept_lines.append(stripped)
        previous_blank = is_blank
    return kept_lines


def _join_lines(lines: list[str], trailing_newline: bool) -> str:
    if not lines:
        return ""
    body = "\n".join(lines)
    return body + "\n" if trailing_newline else body


_STRIPPERS = {
    "latex": strip_latex,
    "html": strip_html,
}


def resolve_style(style: str, source_name: str | None) -> str:
    """Resolve the requested comment style, expanding `auto` from the file extension."""
    if style != "auto":
        if style not in _STRIPPERS:
            raise ValueError(
                f"unknown style {style!r}; choose one of {sorted(_STRIPPERS)} or 'auto'"
            )
        return style
    if source_name is None:
        raise ValueError(
            "style 'auto' needs a file argument to read the extension from; "
            "pass --style latex or --style html when reading stdin"
        )
    suffix = _suffix_of(source_name)
    if suffix not in _EXTENSION_STYLES:
        raise ValueError(
            f"cannot auto-detect comment style for {source_name!r} "
            f"(extension {suffix!r}); pass --style latex or --style html"
        )
    return _EXTENSION_STYLES[suffix]


def _suffix_of(source_name: str) -> str:
    dot_index = source_name.rfind(".")
    if dot_index == -1:
        return ""
    return source_name[dot_index:].lower()


def strip_comments(text: str, style: str, source_name: str | None) -> str:
    resolved = resolve_style(style, source_name)
    stripper = _STRIPPERS[resolved]
    logger.debug("stripping with style=%(style)s", {"style": resolved})
    return stripper(text)


def main(argv: tuple[str, ...]) -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "input",
        nargs="?",
        help="prose file to read; omit to read stdin (then --style is required)",
    )
    parser.add_argument(
        "--style",
        choices=("auto", "latex", "html"),
        default="auto",
        help="comment syntax to strip; 'auto' detects from the file extension",
    )
    arguments = parser.parse_args(argv)

    if arguments.input is None:
        text = sys.stdin.read()
        source_name = None
    else:
        with open(arguments.input, encoding="utf-8") as handle:
            text = handle.read()
        source_name = arguments.input

    sys.stdout.write(strip_comments(text, arguments.style, source_name))


if __name__ == "__main__":
    main(tuple(sys.argv[1:]))
