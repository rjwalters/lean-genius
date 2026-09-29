"""Shared fixture text for `anvil:deslop` tests (issue #898).

Small, deterministic prose samples used across the ingest/orchestrate/
readonly test files.
"""

from __future__ import annotations

# A markdown snippet carrying a handful of AI-tell rhetoric_lint should
# flag by default (boilerplate hedge + a "it's not just X, it's Y" trope +
# an em-dash aside), so tests can assert the lint pass actually fires.
SLOPPY_MARKDOWN = (
    "# Our Product\n\n"
    "It's important to note that our product isn't just a tool"
    " — it's a movement.\n"
)

CLEAN_MARKDOWN = (
    "# Our Product\n\n"
    "Our product helps teams ship faster.\n"
)

SLOPPY_HTML = (
    "<html><head><title>Ignore me</title>"
    "<style>body{color:red}</style></head>"
    "<body>\n"
    "  <h1>Our Product</h1>\n"
    "  <p>It's important to note that our product isn't just a tool"
    " — it's a movement.</p>\n"
    "  <script>console.log('ignore me too')</script>\n"
    "</body></html>\n"
)

PASTED_SLOPPY_TEXT = (
    "It's important to note that this paragraph isn't just filler"
    " — it's a demonstration."
)
