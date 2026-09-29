"""memo_image_dimensions helpers (issue #395) — issue #1128 package split.

Pure-stdlib PNG/JPEG header parsing, the declared-``figsize``-vs-actual
divergence check, the optional PIL/numpy content-bbox check, image
enumeration over the body + ``exhibits/`` glob, and the top-level
``memo_image_dimensions`` check runner
(:func:`_check_memo_image_dimensions`).

Also carries :func:`_resolve_target_length` and :func:`_gate_memo` — the
``target_length`` resolver and the seven-dimension memo gate dispatcher
respectively. Both are physically part of this module because that is
where they lived in the pre-split file's "memo_image_dimensions
helpers" section banner (the file grew issue-by-issue without a banner
reorganization — see issue #1128); keeping them here (rather than
moving them to ``memo.py``, where they would conceptually fit better)
avoids a real import cycle: ``_gate_memo`` calls
:func:`_check_memo_image_dimensions` (defined in this module) as well as
several ``memo.py`` internals, but nothing in ``memo.py`` needs
anything from this module — so the dependency stays one-directional
(this module imports from ``memo.py``, never the reverse). Split out of
the former monolithic ``anvil/lib/render_gate.py`` along its existing
section banners — see ``anvil/lib/render_gate/__init__.py`` for the
full package rationale.
"""

from __future__ import annotations

import re
import struct
from pathlib import Path
from typing import Optional

from anvil.lib.rhetoric_lint import lint_rhetoric

from anvil.lib.render_gate.constants import (
    COMPILE_FAILED,
    COMPILE_OK,
    COMPILE_UNAVAILABLE,
    DEFAULT_MEMO_PLACEHOLDER_PATTERNS,
    DIM_MEMO_COMPILE,
    DIM_MEMO_IMAGE_DIMENSIONS,
    DIM_MEMO_IMAGE_REFS,
    DIM_MEMO_OVERFULL,
    DIM_MEMO_PAGE_FIT,
    DIM_MEMO_PLACEHOLDERS,
    DIM_MEMO_RHETORIC,
    MEMO_ENGINE_XELATEX,
    MEMO_IMAGE_DECLARED_TOLERANCE,
    MEMO_IMAGE_MAX_ASPECT,
    MEMO_IMAGE_MAX_PX,
    MEMO_IMAGE_MIN_CONTENT_RATIO,
    MEMO_WORDS_PER_PAGE,
    _MEMO_IMAGE_EXTENSIONS,
)
from anvil.lib.render_gate.helpers import _count_pages_with_pdfinfo, _which_pdfinfo
from anvil.lib.render_gate.memo import (
    _coerce_image_max_px,
    _coerce_words_per_page,
    _collect_memo_disabled_lines,
    _memo_body_filename,
    _parse_memo_overfull,
    _render_memo_source,
    _scan_memo_placeholders,
)
from anvil.lib.render_gate.results import GateFinding, GateResult


#
# Pure-stdlib image header parsing. The PNG path is the inverse of the
# struct+zlib chunk builder proven in
# ``anvil/skills/deck/tests/test_imagegen.py::_make_tiny_png``: a
# signature-verified PNG carries big-endian u32 width/height at bytes
# 16-24 (the IHDR payload). The JPEG path walks segment markers to the
# first SOFn frame header. No PIL, no subprocess (``sips`` is
# macOS-only; ``identify`` needs ImageMagick).
#
# Helper placement: module-private for v1. Promote to
# ``anvil/lib/image_meta.py`` when the deck ``figures/`` pass (the named
# second consumer) lands — "wait for the second consumer" discipline.

_PNG_SIGNATURE = b"\x89PNG\r\n\x1a\n"

# JPEG SOFn markers carry frame dimensions. 0xC4 (DHT), 0xC8 (JPG
# extension), and 0xCC (DAC) sit inside the 0xC0-0xCF range but are NOT
# frame headers.
_JPEG_SOF_MARKERS = frozenset(range(0xC0, 0xD0)) - {0xC4, 0xC8, 0xCC}

# Cheap declarative-source regexes for the declared-vs-actual check.
# Intentionally loose (this is a best-effort signal, not a Python
# parser): ``figsize=(12, 7.5)`` / ``figsize=[12, 7.5]`` and ``dpi=150``
# anywhere in the sibling source.
_FIGSIZE_RE = re.compile(
    r"figsize\s*=\s*[\(\[]\s*(\d+(?:\.\d+)?)\s*,\s*(\d+(?:\.\d+)?)\s*[\)\]]"
)
_DPI_RE = re.compile(r"\bdpi\s*=\s*(\d+(?:\.\d+)?)")


def _read_png_dimensions(data: bytes) -> Optional[tuple[int, int]]:
    """Return ``(width, height)`` from a PNG IHDR, or ``None``.

    Bytes 16-24 of a signature-verified PNG are big-endian u32
    width/height (the IHDR chunk is mandated first by the PNG spec).
    Returns ``None`` for non-PNG bytes, truncated headers, or
    degenerate (zero) dimensions.
    """
    if len(data) < 24 or not data.startswith(_PNG_SIGNATURE):
        return None
    if data[12:16] != b"IHDR":
        return None
    width, height = struct.unpack(">II", data[16:24])
    if width <= 0 or height <= 0:
        return None
    return (int(width), int(height))


def _read_png_phys_dpi(data: bytes) -> Optional[float]:
    """Return the horizontal DPI from a PNG ``pHYs`` chunk, or ``None``.

    Walks the chunk stream (length + tag + payload + CRC) up to the
    first IDAT — ``pHYs`` must precede image data per the spec. Only
    ``unit == 1`` (pixels per meter) is meaningful; ``unit == 0``
    declares an aspect ratio without absolute density and returns
    ``None``. ``ppu × 0.0254`` converts pixels-per-meter to DPI
    (matplotlib writes this chunk on every ``savefig`` PNG).
    """
    if len(data) < 8 or not data.startswith(_PNG_SIGNATURE):
        return None
    offset = 8
    while offset + 8 <= len(data):
        (length,) = struct.unpack(">I", data[offset : offset + 4])
        tag = data[offset + 4 : offset + 8]
        if tag == b"pHYs":
            if length == 9 and offset + 17 <= len(data):
                ppu_x, _ppu_y, unit = struct.unpack(
                    ">IIB", data[offset + 8 : offset + 17]
                )
                if unit == 1 and ppu_x > 0:
                    return ppu_x * 0.0254
            return None
        if tag in (b"IDAT", b"IEND"):
            return None
        offset += 12 + length  # 4 length + 4 tag + payload + 4 CRC
    return None


def _read_jpeg_dimensions(data: bytes) -> Optional[tuple[int, int]]:
    """Return ``(width, height)`` from a JPEG SOFn frame header, or ``None``.

    Marker walk: skip past each ``0xFF``-prefixed segment using its
    declared length until the first SOFn marker; the frame header
    payload is ``precision(1) height(2) width(2)`` big-endian after the
    2-byte segment length. Standalone markers (RST/SOI/EOI/TEM) carry
    no length and are stepped over. Returns ``None`` for non-JPEG
    bytes, truncated streams, or degenerate dimensions.
    """
    if len(data) < 4 or data[0:2] != b"\xff\xd8":
        return None
    n = len(data)
    offset = 2
    while offset + 4 <= n:
        if data[offset] != 0xFF:
            # Out of marker sync (corrupt stream) — bail rather than
            # scan-and-guess.
            return None
        marker = data[offset + 1]
        if marker == 0xFF:
            # Fill byte; markers may be padded with extra 0xFFs.
            offset += 1
            continue
        if marker == 0x01 or 0xD0 <= marker <= 0xD9:
            # Standalone marker (TEM, RSTn, SOI, EOI) — no length word.
            offset += 2
            continue
        (seg_len,) = struct.unpack(">H", data[offset + 2 : offset + 4])
        if seg_len < 2:
            return None
        if marker in _JPEG_SOF_MARKERS:
            if offset + 9 > n:
                return None
            height, width = struct.unpack(
                ">HH", data[offset + 5 : offset + 9]
            )
            if width <= 0 or height <= 0:
                return None
            return (int(width), int(height))
        offset += 2 + seg_len
    return None


def _read_image_dimensions(path: Path) -> Optional[tuple[int, int]]:
    """Return ``(width, height)`` for a PNG/JPEG on disk, or ``None``.

    Dispatches on extension, falling back to signature sniffing for
    unrecognized suffixes. Unreadable files, truncated headers, and
    non-raster formats all return ``None`` — the caller skips silently
    (this check must never false-positive on exotic inputs).
    """
    try:
        data = path.read_bytes()
    except OSError:
        return None
    suffix = path.suffix.lower()
    if suffix == ".png":
        return _read_png_dimensions(data)
    if suffix in (".jpg", ".jpeg"):
        return _read_jpeg_dimensions(data)
    return _read_png_dimensions(data) or _read_jpeg_dimensions(data)


def _find_figure_source(image_path: Path) -> Optional[Path]:
    """Locate the declarative ``src/<stem>.py`` sibling for an image.

    Checked in order: ``<image_dir>/src/<stem>.py`` (the memo exhibits
    convention — figure sources under ``exhibits/src/`` next to
    ``exhibits/<stem>.png``), ``<image_dir>/<stem>.py`` (flat layout),
    then ``<image_dir>/../src/<stem>.py`` (image one level below the
    src dir, e.g. ``exhibits/figures/<stem>.png`` with
    ``exhibits/src/<stem>.py``). First existing file wins; ``None``
    when no candidate exists (the declared-vs-actual check then skips
    silently).
    """
    stem = image_path.stem
    candidates = (
        image_path.parent / "src" / f"{stem}.py",
        image_path.parent / f"{stem}.py",
        image_path.parent.parent / "src" / f"{stem}.py",
    )
    for candidate in candidates:
        if candidate.is_file():
            return candidate
    return None


def _parse_declared_figure_params(
    source_text: str,
) -> tuple[Optional[tuple[float, float]], Optional[float]]:
    """Best-effort ``(figsize, dpi)`` extraction from a figure source.

    Cheap regex, not a Python parser — the first ``figsize=(W, H)`` and
    the first ``dpi=N`` in the file win. Either slot is independently
    ``None`` when unparseable. This check must never false-positive on
    hand-made images, so the caller skips silently when ``figsize`` is
    absent.
    """
    figsize: Optional[tuple[float, float]] = None
    dpi: Optional[float] = None
    m = _FIGSIZE_RE.search(source_text)
    if m:
        w, h = float(m.group(1)), float(m.group(2))
        if w > 0 and h > 0:
            figsize = (w, h)
    m = _DPI_RE.search(source_text)
    if m:
        value = float(m.group(1))
        if value > 0:
            dpi = value
    return (figsize, dpi)


def _image_content_ratio(path: Path) -> Optional[float]:
    """Content-bbox area as a fraction of canvas area, or ``None``.

    A module-private adaptation of the corner-patch background-sampling
    algorithm from
    ``anvil/skills/deck/lib/auto_shrink_detector.py::_content_bbox``
    (the #102 precedent), with two deltas for the memo image surface:

    - operates in **RGBA** space (vs RGB) so a fully-transparent canvas
      — the exact canary mode, ``savefig.transparent: True`` — reads as
      background and the opaque drawing reads as content;
    - returns the bbox **area ratio** rather than the bottom margin
      (the discriminative signal here is "content occupies a corner of
      a giant canvas", not slide auto-shrink).

    Promotion to a shared location waits for the second consumer per
    repo convention. Returns ``None`` when PIL/numpy are missing, the
    image cannot be decoded (e.g. a truncated or header-only file), or
    the canvas is too small to corner-sample; returns ``0.0`` for a
    completely blank canvas.
    """
    try:
        import numpy as np
        from PIL import Image
    except ImportError:
        return None
    try:
        with Image.open(path) as im:
            arr = np.asarray(im.convert("RGBA"), dtype=np.int16)
    except Exception:
        # Undecodable (header-only fixture, corrupt file, exotic
        # subformat) — skip silently; the stdlib checks already ran.
        return None
    h, w, _ = arr.shape
    corner_margin_px = 4
    corner_patch_px = 16
    if h < 2 * corner_margin_px + corner_patch_px:
        return None
    if w < 2 * corner_margin_px + corner_patch_px:
        return None
    cm, cp = corner_margin_px, corner_patch_px
    patches = [
        arr[cm : cm + cp, cm : cm + cp],
        arr[cm : cm + cp, w - cm - cp : w - cm],
        arr[h - cm - cp : h - cm, cm : cm + cp],
        arr[h - cm - cp : h - cm, w - cm - cp : w - cm],
    ]
    stacked = np.concatenate([p.reshape(-1, 4) for p in patches], axis=0)
    bg = np.median(stacked, axis=0).astype(np.int16)
    diff = np.abs(arr - bg)
    # A pixel is "content" when ANY channel (including alpha) differs
    # from the corner-sampled background by more than the tolerance.
    content_mask = (diff > 8).any(axis=2)
    if not content_mask.any():
        return 0.0
    rows = content_mask.any(axis=1)
    cols = content_mask.any(axis=0)
    top = int(np.argmax(rows))
    bottom = int(h - 1 - np.argmax(rows[::-1]))
    left = int(np.argmax(cols))
    right = int(w - 1 - np.argmax(cols[::-1]))
    bbox_area = (bottom - top + 1) * (right - left + 1)
    return bbox_area / float(h * w)


def _enumerate_memo_images(
    version_dir: Path,
) -> tuple[dict[Path, Optional[int]], list[str]]:
    """Enumerate the images the ``memo_image_dimensions`` check inspects.

    Union of two sources (per the issue's "and/or" ask):

    1. Body-referenced images — every markdown ``![..](..)`` / HTML
       ``<img>`` ref in ``<thread>.md``, via the
       ``memo_image_refs._extract_refs`` extractor (URL and absolute
       refs skipped per ``_is_skipped`` semantics). These carry their
       1-based body line for suppression.
    2. Present-but-unreferenced exhibits — a recursive glob over
       ``<version_dir>/exhibits/`` for PNG/JPEG files. No body line
       (and therefore no suppression surface in v1 — acceptable, since
       findings are advisory).

    Returns ``(images, breadcrumbs)`` where ``images`` maps each
    resolved path to its body line (``None`` for glob-discovered) and
    ``breadcrumbs`` carries skip notes (SVG refs; refs extractor not
    importable). First body occurrence wins for the line number.
    """
    images: dict[Path, Optional[int]] = {}
    breadcrumbs: list[str] = []

    body_filename = _memo_body_filename(version_dir)
    memo_md = version_dir / body_filename
    if memo_md.is_file():
        try:
            from anvil.skills.memo.lib import memo_image_refs as _img_refs

            source = memo_md.read_text(encoding="utf-8", errors="replace")
            for ref in _img_refs._extract_refs(source):
                if _img_refs._is_skipped(ref.path):
                    continue
                if ref.path.lower().endswith(".svg"):
                    breadcrumbs.append(
                        f"{DIM_MEMO_IMAGE_DIMENSIONS}: SVG ref "
                        f"{ref.path!r} skipped (viewBox semantics make "
                        "pixel dims ill-defined)."
                    )
                    continue
                resolved = (version_dir / ref.path).resolve()
                if not resolved.is_file():
                    # Missing files are memo_image_refs_exist's job.
                    continue
                if resolved not in images:
                    images[resolved] = ref.line
        except ImportError:
            breadcrumbs.append(
                f"{DIM_MEMO_IMAGE_DIMENSIONS}: image-ref extractor not "
                "importable; body-referenced images skipped (exhibits "
                "glob still checked)."
            )

    exhibits_dir = version_dir / "exhibits"
    if exhibits_dir.is_dir():
        for candidate in sorted(exhibits_dir.rglob("*")):
            if not candidate.is_file():
                continue
            if candidate.suffix.lower() not in _MEMO_IMAGE_EXTENSIONS:
                continue
            resolved = candidate.resolve()
            if resolved not in images:
                images[resolved] = None
    return (images, breadcrumbs)


def _check_memo_image_dimensions(
    version_dir: Path,
    *,
    image_max_px: Optional[int] = None,
) -> tuple[list[GateFinding], list[str]]:
    """Run the advisory ``memo_image_dimensions`` checks (issue #395).

    Returns ``(findings, reasons)`` for the caller (:func:`_gate_memo`)
    to fold in. ALL findings are warning severity (info when
    suppressed) and the dimension never joins ``failed_gates`` — the
    same advisory model as ``memo_overfull_check``. Findings flow to
    ``_progress.json.render_gate.findings`` through the existing
    ``GateResult`` → memo-render wiring with no new plumbing.

    Checks per image (see the module docstring memo-mode section for
    the full prose): (1) pixel ceiling, (1b) extreme aspect, (2)
    declared-vs-actual (silent skip when nothing declarative is
    parseable), (3) content-bbox vs canvas (``[image_lint]`` extra;
    breadcrumb-and-skip when PIL/numpy are absent).

    Suppression: ``<!-- anvil-lint-disable: memo_image_dimensions -->``
    (same line or line above the body ref) downgrades that image's
    hits to info findings, mirroring the placeholder-scan pattern.
    Exhibits-glob-discovered images with no body line have no
    suppression surface in v1.
    """
    findings: list[GateFinding] = []
    reasons: list[str] = []

    effective_max = _coerce_image_max_px(image_max_px)
    if effective_max is None:
        effective_max = MEMO_IMAGE_MAX_PX

    images, breadcrumbs = _enumerate_memo_images(version_dir)
    if not images:
        reasons.extend(breadcrumbs)
        return (findings, reasons)
    reasons.extend(breadcrumbs)

    # Suppressed-line set from the body source (body-referenced images
    # only; glob-discovered images carry line=None and never suppress).
    disabled_lines: set[int] = set()
    memo_md = version_dir / _memo_body_filename(version_dir)
    if memo_md.is_file():
        disabled_lines = _collect_memo_disabled_lines(
            memo_md.read_text(encoding="utf-8", errors="replace"),
            rule=DIM_MEMO_IMAGE_DIMENSIONS,
        )

    # Preflight the optional content-bbox deps ONCE per gate run; a
    # single breadcrumb (not one per image) keeps reasons readable.
    from anvil.lib.render import (
        IMAGE_LINT_REMEDIATION,
        check_image_lint_deps_available,
    )

    bbox_available = check_image_lint_deps_available()
    if not bbox_available:
        reasons.append(
            f"{DIM_MEMO_IMAGE_DIMENSIONS}: content-bbox check skipped. "
            f"{IMAGE_LINT_REMEDIATION}"
        )

    warning_count = 0
    for image_path, body_line in sorted(images.items()):
        try:
            rel = str(image_path.relative_to(version_dir.resolve()))
        except ValueError:
            rel = str(image_path)
        location = (
            f"{memo_md}:L{body_line}" if body_line is not None else str(image_path)
        )
        suppressed = body_line is not None and body_line in disabled_lines

        hits: list[str] = []
        dims = _read_image_dimensions(image_path)
        if dims is not None:
            width, height = dims
            # Check 1: pixel ceiling (effective ceiling recorded in the
            # message so a reviewer can see which calibration applied).
            if width > effective_max or height > effective_max:
                hits.append(
                    f"Image `{rel}` is {width}x{height} px — exceeds the "
                    f"{effective_max} px ceiling. Likely a runaway canvas "
                    "(matplotlib `bbox_inches=\"tight\"` inflated by a "
                    "rogue artist); a style-conformant anvil.mplstyle "
                    "figure is 2400x1400 px (12x7 in @ 200 dpi)."
                )
            # Check 1b: extreme aspect (either orientation).
            aspect = max(width / height, height / width)
            if aspect > MEMO_IMAGE_MAX_ASPECT:
                hits.append(
                    f"Image `{rel}` is {width}x{height} px — aspect ratio "
                    f"{aspect:.1f}:1 exceeds {MEMO_IMAGE_MAX_ASPECT:.0f}:1 "
                    "(degenerate strip render)."
                )
            # Check 2: declared-vs-actual (best-effort; silent skip when
            # nothing declarative is parseable — never false-positives
            # on hand-made images).
            src_path = _find_figure_source(image_path)
            figsize: Optional[tuple[float, float]] = None
            declared_dpi: Optional[float] = None
            if src_path is not None:
                try:
                    figsize, declared_dpi = _parse_declared_figure_params(
                        src_path.read_text(encoding="utf-8", errors="replace")
                    )
                except OSError:
                    figsize, declared_dpi = (None, None)
            if declared_dpi is None and image_path.suffix.lower() == ".png":
                try:
                    declared_dpi = _read_png_phys_dpi(image_path.read_bytes())
                except OSError:
                    declared_dpi = None
            if figsize is not None and declared_dpi is not None:
                expected_w = figsize[0] * declared_dpi
                expected_h = figsize[1] * declared_dpi
                tol = MEMO_IMAGE_DECLARED_TOLERANCE
                divergent = any(
                    actual > expected * tol or actual < expected / tol
                    for actual, expected in (
                        (width, expected_w),
                        (height, expected_h),
                    )
                )
                if divergent:
                    hits.append(
                        f"Image `{rel}` is {width}x{height} px but its "
                        f"source declares figsize=({figsize[0]:g}, "
                        f"{figsize[1]:g}) @ {declared_dpi:g} dpi — "
                        f"expected ~{expected_w:.0f}x{expected_h:.0f} px "
                        f"(divergence > {tol:g}x). The tight-bbox "
                        "rogue-artist failure inflates saved dims past "
                        "the declared canvas."
                    )
        # Check 3: content-bbox vs canvas (optional extra). Runs even
        # when the header parse failed — PIL may decode formats the
        # stdlib parsers skip. Deliberately SKIPPED for images already
        # over the pixel ceiling: the runaway-canvas diagnosis is on
        # record from check 1, and decoding a 90-megapixel canvas
        # inside the gate costs hundreds of MB (and trips PIL's
        # decompression-bomb guard) — the exact hazard this dimension
        # exists to flag.
        over_ceiling = dims is not None and (
            dims[0] > effective_max or dims[1] > effective_max
        )
        if bbox_available and not over_ceiling:
            ratio = _image_content_ratio(image_path)
            if ratio is not None and ratio < MEMO_IMAGE_MIN_CONTENT_RATIO:
                hits.append(
                    f"Image `{rel}` content bbox occupies "
                    f"{ratio * 100:.1f}% of the canvas (< "
                    f"{MEMO_IMAGE_MIN_CONTENT_RATIO * 100:.0f}%) — the "
                    "tight-bbox rogue-artist signature (drawing in a "
                    "corner of a mostly-blank canvas). Regenerate the "
                    "figure without the stray artist or drop "
                    "`bbox_inches=\"tight\"`."
                )

        for hit in hits:
            if suppressed:
                findings.append(
                    GateFinding(
                        gate=DIM_MEMO_IMAGE_DIMENSIONS,
                        severity="info",
                        message=f"{hit} (suppressed)",
                        location=location,
                    )
                )
            else:
                warning_count += 1
                findings.append(
                    GateFinding(
                        gate=DIM_MEMO_IMAGE_DIMENSIONS,
                        severity="warning",
                        message=hit,
                        location=location,
                    )
                )

    if warning_count:
        reasons.append(
            f"{DIM_MEMO_IMAGE_DIMENSIONS}: {warning_count} image-dimension "
            f"warning(s) (advisory; ceiling={effective_max} px)."
        )
    return (findings, reasons)


def _resolve_target_length(
    target_length: Optional[dict],
    *,
    words_per_page: Optional[int] = None,
) -> tuple[Optional[tuple[int, int]], Optional[tuple[int, int]], str, int]:
    """Resolve ``target_length`` into
    ``(page_range, word_range, source, effective_wpp)``.

    The ``target_length`` shape mirrors what the drafter writes into
    ``_progress.json.metadata.target_length_resolved`` (per
    ``commands/memo-draft.md`` step 5):

    - ``{"words": [min, max]}`` — word-count range; the gate computes a
      page-count range via the wpp proxy (default 400, overridable via
      ``words_per_page``).
    - ``{"pages": [min, max]}`` — page-count range; the gate uses it
      directly. ``source`` is ``"pages"`` so the gate fires errors
      (vs warnings) per architect Q3. The ``words_per_page`` override
      is a **no-op** on this path (no conversion happens).
    - ``None`` or malformed — returns ``(None, None, "none", <wpp>)``;
      the page-fit check is skipped.

    Parameters
    ----------
    target_length:
        The resolved-target dict from ``_progress.json`` or ``None``.
    words_per_page:
        Optional per-thread override for the words→pages conversion
        factor. ``None`` (the default) uses :data:`MEMO_WORDS_PER_PAGE`.
        Already validated by :func:`_coerce_words_per_page` (the public
        ``gate`` entry coerces before passing through).

    Returns
    -------
    A 4-tuple:

    - ``page_range``: ``(min_pages, max_pages)`` or ``None``.
    - ``word_range``: ``(min_words, max_words)`` or ``None`` (only set
      when ``words`` is the declared shape).
    - ``source``: one of ``"pages"``, ``"words"``, ``"none"``.
    - ``effective_wpp``: the wpp value used for the conversion (the
      override when set, otherwise :data:`MEMO_WORDS_PER_PAGE`). Always
      returned (even when the conversion didn't happen) so the caller
      can surface it in the finding message.
    """
    effective_wpp = (
        words_per_page if words_per_page is not None else MEMO_WORDS_PER_PAGE
    )
    if not isinstance(target_length, dict):
        return (None, None, "none", effective_wpp)
    pages = target_length.get("pages")
    words = target_length.get("words")
    # Reject both-keys-set per the malformed-shape contract documented in
    # SKILL.md §Length targets.
    if pages is not None and words is not None:
        return (None, None, "none", effective_wpp)
    if pages is not None:
        if (
            isinstance(pages, (list, tuple))
            and len(pages) == 2
            and all(isinstance(p, int) and p > 0 for p in pages)
            and pages[0] <= pages[1]
        ):
            return ((int(pages[0]), int(pages[1])), None, "pages", effective_wpp)
        return (None, None, "none", effective_wpp)
    if words is not None:
        if (
            isinstance(words, (list, tuple))
            and len(words) == 2
            and all(isinstance(w, int) and w > 0 for w in words)
            and words[0] <= words[1]
        ):
            min_w, max_w = int(words[0]), int(words[1])
            # wpp proxy → page range. Round to int; the gate's
            # comparison is inclusive both sides so a memo word-count
            # that converts to exactly N pages should pass an [N, N+k]
            # range. ``effective_wpp`` is the override when set,
            # otherwise the 400-wpp default.
            min_pages = max(1, min_w // effective_wpp)
            max_pages = max(1, (max_w + effective_wpp - 1) // effective_wpp)
            return ((min_pages, max_pages), (min_w, max_w), "words", effective_wpp)
    return (None, None, "none", effective_wpp)


def _gate_memo(
    *,
    version_dir: Path,
    out_pdf: Optional[Path],
    target_length: Optional[dict],
    placeholder_patterns: Optional[tuple[str, ...]],
    pdfinfo_path: Optional[str],
    words_per_page: Optional[int] = None,
    image_max_px: Optional[int] = None,
    render_engine: Optional[str] = None,
    latex_header_includes: Optional[str] = None,
    render_template: Optional[str] = None,
    render_lua_filters: Optional[list[str]] = None,
    render_metadata: Optional[dict] = None,
    rhetoric_rules_path: Optional[Path] = None,
) -> GateResult:
    """Seven-dimension memo render-gate (kind="memo").

    See the module docstring for the dimension list and severity model.
    The function is structured to mirror the LaTeX gate's "all checks run
    independently, no short-circuit" contract.

    The optional ``render_engine`` parameter (issue #320) carries the
    per-document override forwarded from
    ``BriefDocument.render_engine`` via the public :func:`gate`
    dispatcher. It is plumbed verbatim to
    :func:`_render_memo_source`; the actual honor-or-fallthrough
    decision lives in :func:`_select_memo_engine`. When ``None``, the
    auto-priority order applies (no regression on legacy callers).

    The optional ``image_max_px`` parameter (issue #395) is the
    per-thread pixel ceiling for the advisory ``memo_image_dimensions``
    check (check 5). Coerced via :func:`_coerce_image_max_px` (the
    ``words_per_page`` coerce-or-silently-fallback pattern); ``None``
    or a malformed value uses :data:`MEMO_IMAGE_MAX_PX` (6000), and
    the effective ceiling is recorded in the finding/reason message.

    The optional ``latex_header_includes`` parameter (issue #347)
    carries per-document free-form LaTeX preamble text forwarded from
    ``BriefDocument.latex_header_includes``. Plumbed verbatim to
    :func:`_render_memo_source`, which threads it into pandoc's
    ``header-includes`` slot via ``--include-in-header=<tempfile>``
    **only when** the dispatched engine resolves to ``xelatex``.
    Silent-with-record skip when the engine is HTML-side: the skip is
    appended to ``reasons`` for the audit trail without flipping any
    gate status. When ``None``, no include is added (no regression on
    legacy callers).

    The optional ``render_template`` / ``render_lua_filters`` /
    ``render_metadata`` parameters (issue #391) carry the per-document
    consumer pandoc passthrough knobs forwarded from the matching
    ``BriefDocument`` fields. Plumbed verbatim to
    :func:`_render_memo_source` (see its docstring for the resolution,
    extension-matching, and ``{N}``-expansion semantics). Skip
    breadcrumbs the renderer records (template extension/engine
    mismatch, missing template or filter file) are appended to
    ``reasons`` — silent-with-record, never a gate failure on their
    own. Render provenance lands on ``GateResult.engine_used`` /
    ``template_used`` so memo-render can persist
    ``_progress.json.phases.render.engine`` / ``.template``.

    The optional ``rhetoric_rules_path`` parameter (issue #463) is a
    consumer JSON rule file for the advisory ``memo_rhetoric_lint``
    dimension (check 7), forwarded verbatim to
    :func:`anvil.lib.rhetoric_lint.lint_rhetoric` as
    ``extra_rules_path``. ``None`` runs the framework defaults. The
    BRIEF-side carrier is ``voice.rhetoric_rules``, resolved by
    ``anvil.lib.project_brief.resolve_rhetoric_rules`` (issue #468).
    """
    if out_pdf is None:
        # PDF output basename echoes the thread slug per #295 (e.g.
        # ``investment-memo.1/investment-memo.pdf``).
        out_pdf = version_dir / f"{version_dir.parent.name}.pdf"
    out_pdf = Path(out_pdf)

    findings: list[GateFinding] = []
    reasons: list[str] = []
    failed: set[str] = set()

    # --- Step 1: invoke the renderer ---------------------------------------
    # ``render_provenance`` is the issue #391 out-channel: the renderer
    # fills ``template`` (provenance string) + ``skips`` (breadcrumbs)
    # without disturbing the pinned 4-tuple return contract.
    render_provenance: dict = {}
    compile_status, exit_code, engine_used, stderr_text = _render_memo_source(
        version_dir,
        out_pdf,
        requested_engine=render_engine,
        latex_header_includes=latex_header_includes,
        render_template=render_template,
        render_lua_filters=render_lua_filters,
        render_metadata=render_metadata,
        provenance=render_provenance,
    )

    # --- Record fallthrough when the requested engine was overridden ------
    # Issue #320: when the caller requested a specific engine but the
    # selector returned a different one (because the requested binary is
    # not on PATH), surface the rationale in reasons so the operator can
    # see why their requested engine wasn't used. This is silent-with-
    # record: not a gate failure, not a finding, just a breadcrumb in
    # ``reasons``.
    if (
        render_engine is not None
        and engine_used
        and engine_used != render_engine
    ):
        reasons.append(
            f"{DIM_MEMO_COMPILE}: requested render_engine={render_engine!r} "
            f"not available on PATH; fell through to {engine_used!r} per "
            f"auto-priority (weasyprint > wkhtmltopdf > xelatex)."
        )

    # --- Record skip when latex_header_includes did not reach pandoc ------
    # Issue #347: ``latex_header_includes`` is engine-scoped to xelatex
    # (the HTML chain has a parallel ``header-includes`` slot in
    # ``template.html``, but the contents are LaTeX). When the operator
    # set the BRIEF knob but the dispatched engine resolved to a non-
    # xelatex chain (e.g., the requested engine fell through to
    # weasyprint), surface the skip as a breadcrumb in ``reasons`` so
    # the operator can see why their preamble didn't apply. This is
    # silent-with-record: not a gate failure, not a finding.
    if (
        latex_header_includes is not None
        and engine_used
        and engine_used != MEMO_ENGINE_XELATEX
    ):
        reasons.append(
            f"{DIM_MEMO_COMPILE}: latex_header_includes provided but "
            f"dispatched engine={engine_used!r} is not xelatex; preamble "
            f"include skipped (latex_header_includes is xelatex-only)."
        )

    # --- Record consumer template/filter skips (issue #391) ----------------
    # The renderer recorded a breadcrumb for each consumer passthrough
    # input it had to skip (template extension/engine mismatch, missing
    # template file, missing Lua filter file). Surface them in
    # ``reasons`` — silent-with-record per the #347 skip contract: not
    # a gate failure, not a finding, just an audit trail entry so the
    # operator can see why their template/filter didn't apply.
    reasons.extend(render_provenance.get("skips", []))

    # --- Check 1: memo_compile_success -------------------------------------
    compile_exit_code: Optional[int] = exit_code if exit_code != -1 else None
    pdf_pages: Optional[int] = None
    if compile_status == COMPILE_UNAVAILABLE:
        # Engine missing — graceful-degrade per architect Q7. Recorded as
        # an info-level reason; the gate does NOT fail the compile dim
        # because we cannot prove the artifact is broken.
        # Lazy import to keep render decoupled from gate at module load.
        from anvil.lib.render import MEMO_RENDERER_REMEDIATION

        reasons.append(
            f"{DIM_MEMO_COMPILE}: pandoc and/or HTML-to-PDF engine not on "
            f"PATH; memo render skipped. {MEMO_RENDERER_REMEDIATION}"
        )
    elif compile_status == COMPILE_FAILED:
        failed.add(DIM_MEMO_COMPILE)
        msg = (
            f"{DIM_MEMO_COMPILE}: pandoc exited "
            f"{exit_code if exit_code != -1 else 'non-zero'}"
            f"{' (engine=' + engine_used + ')' if engine_used else ''}."
        )
        reasons.append(msg)
        findings.append(
            GateFinding(
                gate=DIM_MEMO_COMPILE,
                severity="error",
                message=(
                    f"Memo render failed (exit {exit_code}); engine="
                    f"{engine_used or 'unknown'}. stderr: "
                    f"{stderr_text.strip()[:500] or '(empty)'}"
                ),
                location=str(out_pdf),
            )
        )
    elif compile_status == COMPILE_OK:
        # PDF should now exist; double-check + page count.
        if not out_pdf.exists():
            failed.add(DIM_MEMO_COMPILE)
            msg = (
                f"{DIM_MEMO_COMPILE}: pandoc exited 0 but output PDF was "
                f"not produced at {out_pdf}."
            )
            reasons.append(msg)
            findings.append(
                GateFinding(
                    gate=DIM_MEMO_COMPILE,
                    severity="error",
                    message=f"Expected PDF not found at {out_pdf} after pandoc exit 0.",
                    location=str(out_pdf),
                )
            )
        else:
            pdf_pages = _count_pages_with_pdfinfo(
                out_pdf, pdfinfo_path=pdfinfo_path
            )
            if pdf_pages is not None and pdf_pages <= 0:
                failed.add(DIM_MEMO_COMPILE)
                msg = f"{DIM_MEMO_COMPILE}: PDF reports {pdf_pages} pages."
                reasons.append(msg)
                findings.append(
                    GateFinding(
                        gate=DIM_MEMO_COMPILE,
                        severity="error",
                        message=f"Rendered PDF has {pdf_pages} pages (expected > 0).",
                        location=str(out_pdf),
                    )
                )
            elif pdf_pages is None and _which_pdfinfo(pdfinfo_path) is None:
                # pdfinfo missing — informational reason only; compile dim
                # does NOT fail (the PDF exists, we just can't introspect it).
                reasons.append(
                    f"{DIM_MEMO_COMPILE}: pdfinfo not on PATH; page-count "
                    "check skipped (PDF was produced successfully)."
                )

    # --- Check 2: memo_page_fit --------------------------------------------
    # ``words_per_page`` is already coerced by the public ``gate`` entry
    # (via :func:`_coerce_words_per_page`); when callers invoke ``_gate_memo``
    # directly, we re-coerce here so the validation contract is uniform and
    # a malformed direct-call argument graceful-degrades the same way.
    effective_override = _coerce_words_per_page(words_per_page)
    page_range, word_range, target_source, effective_wpp = _resolve_target_length(
        target_length, words_per_page=effective_override
    )
    if page_range is None:
        if target_source == "none":
            reasons.append(
                f"{DIM_MEMO_PAGE_FIT}: page-fit check skipped (no "
                "target_length declared)."
            )
    elif pdf_pages is None:
        reasons.append(
            f"{DIM_MEMO_PAGE_FIT}: page-fit check skipped (page count "
            "unavailable — see compile dim)."
        )
    else:
        min_pages, max_pages = page_range
        if min_pages <= pdf_pages <= max_pages:
            # In range — informational reason. When the range was
            # derived from word count, surface the effective wpp so the
            # reviewer can see which calibration the gate used (relevant
            # when a per-thread override is in play).
            if target_source == "words":
                reasons.append(
                    f"{DIM_MEMO_PAGE_FIT}: rendered {pdf_pages} pages within "
                    f"target [{min_pages}, {max_pages}] "
                    f"(source={target_source} @ {effective_wpp} wpp)."
                )
            else:
                reasons.append(
                    f"{DIM_MEMO_PAGE_FIT}: rendered {pdf_pages} pages within "
                    f"target [{min_pages}, {max_pages}] (source={target_source})."
                )
        else:
            # Out of range. Severity = error if source="pages" (the
            # author declared the page range explicitly); warning if
            # source="words" (the page range is derived via the
            # 400-wpp proxy and dim 7 word-count is authoritative).
            severity = "error" if target_source == "pages" else "warning"
            failed.add(DIM_MEMO_PAGE_FIT)
            if target_source == "words" and word_range is not None:
                msg = (
                    f"{DIM_MEMO_PAGE_FIT}: rendered {pdf_pages} pages "
                    f"outside derived range [{min_pages}, {max_pages}] "
                    f"(from target_length.words=[{word_range[0]}, "
                    f"{word_range[1]}] @ {effective_wpp} wpp). "
                    "Word-count proxy in dim 7 remains authoritative; "
                    "this is an advisory second-layer warning."
                )
            else:
                msg = (
                    f"{DIM_MEMO_PAGE_FIT}: rendered {pdf_pages} pages "
                    f"outside declared range [{min_pages}, {max_pages}]."
                )
            reasons.append(msg)
            findings.append(
                GateFinding(
                    gate=DIM_MEMO_PAGE_FIT,
                    severity=severity,
                    message=msg.split(": ", 1)[1],
                    location=f"{out_pdf}:pages={pdf_pages}",
                )
            )

    # --- Check 3: memo_overfull_check --------------------------------------
    if not stderr_text:
        # Renderer emitted no stderr — graceful-degrade (the common case
        # on a clean memo). Record as an info reason so the operator
        # sees the check ran.
        reasons.append(
            f"{DIM_MEMO_OVERFULL}: overflow check ran with no stderr "
            "warnings detected."
        )
    else:
        overfull_hits = _parse_memo_overfull(stderr_text)
        if overfull_hits:
            # Warnings (not errors) per architect Q3.
            reasons.append(
                f"{DIM_MEMO_OVERFULL}: {len(overfull_hits)} overflow-style "
                "warning(s) in renderer stderr."
            )
            for hit in overfull_hits:
                findings.append(
                    GateFinding(
                        gate=DIM_MEMO_OVERFULL,
                        severity="warning",
                        message=(
                            f"Renderer warning: {hit['raw'][:200]}"
                        ),
                        location=f"stderr:L{hit['line']}",
                    )
                )

    # --- Check 4: memo_image_refs_exist ------------------------------------
    # Calls into PR #160's lint module (anvil/skills/memo/lib/memo_image_refs.py).
    # The source-side lint runs at review phase; this is the post-render
    # catch (refs that exist but pandoc's resolver flagged, or symlink /
    # case edge cases). Lazy import keeps the lib lookup off the module
    # load path and makes test-side mocking straightforward.
    try:
        from anvil.skills.memo.lib import memo_image_refs as _img_refs

        lint_result = _img_refs.lint_memo_image_refs(version_dir)
        # Body filename echoes the thread slug per #295.
        body_filename = _memo_body_filename(version_dir)
        if lint_result.errors:
            failed.add(DIM_MEMO_IMAGE_REFS)
            reasons.append(
                f"{DIM_MEMO_IMAGE_REFS}: {len(lint_result.errors)} broken "
                "image reference(s) detected (post-render)."
            )
            for err in lint_result.errors:
                findings.append(
                    GateFinding(
                        gate=DIM_MEMO_IMAGE_REFS,
                        severity="error",
                        message=err.message,
                        location=f"{version_dir / body_filename}:L{err.line}",
                    )
                )
        # Surface suppressed (info) hits too so the reviewer sees what
        # was disabled, mirroring marp_lint's pattern.
        for info in lint_result.infos:
            findings.append(
                GateFinding(
                    gate=DIM_MEMO_IMAGE_REFS,
                    severity="info",
                    message=info.message,
                    location=f"{version_dir / body_filename}:L{info.line}",
                )
            )
    except ImportError:
        # Skill-local lint module is not on the import path (e.g., the
        # caller is running anvil/lib/ standalone). Record an info
        # reason; the gate dim does NOT fail because the absence of the
        # check is not evidence of a broken artifact.
        reasons.append(
            f"{DIM_MEMO_IMAGE_REFS}: image-ref lint module not "
            "importable; check skipped."
        )

    # --- Check 5: memo_image_dimensions (issue #395, advisory) -------------
    # Image-dimension/aspect sanity check over body-referenced images +
    # the exhibits glob. Warning severity throughout; the dimension is
    # NOT added to ``failed`` — the same advisory model as
    # memo_overfull_check (findings recorded, ``passed`` unaffected, no
    # CriticalFlag). See _check_memo_image_dimensions for the per-image
    # check list (pixel ceiling, aspect, declared-vs-actual, optional
    # content-bbox).
    img_dim_findings, img_dim_reasons = _check_memo_image_dimensions(
        version_dir, image_max_px=image_max_px
    )
    findings.extend(img_dim_findings)
    reasons.extend(img_dim_reasons)

    # --- Check 6: memo_placeholder_scan ------------------------------------
    # Body filename echoes the thread slug per #295.
    body_filename = _memo_body_filename(version_dir)
    memo_md = version_dir / body_filename
    if not memo_md.is_file():
        reasons.append(
            f"{DIM_MEMO_PLACEHOLDERS}: {body_filename} not found; placeholder "
            "scan skipped."
        )
    else:
        memo_patterns = (
            placeholder_patterns
            if placeholder_patterns is not None
            else DEFAULT_MEMO_PLACEHOLDER_PATTERNS
        )
        memo_source = memo_md.read_text(encoding="utf-8", errors="replace")
        active_hits, suppressed_hits = _scan_memo_placeholders(
            memo_source, memo_patterns
        )
        if active_hits:
            failed.add(DIM_MEMO_PLACEHOLDERS)
            reasons.append(
                f"{DIM_MEMO_PLACEHOLDERS}: {len(active_hits)} placeholder "
                f"hit(s) in {body_filename}."
            )
            for hit in active_hits:
                findings.append(
                    GateFinding(
                        gate=DIM_MEMO_PLACEHOLDERS,
                        severity="error",
                        message=(
                            f"Placeholder pattern {hit['pattern']!r} matched "
                            f"{hit['match']!r}."
                        ),
                        location=f"{memo_md}:L{hit['line']}",
                    )
                )
        # Suppressed → info findings for reviewer visibility.
        for hit in suppressed_hits:
            findings.append(
                GateFinding(
                    gate=DIM_MEMO_PLACEHOLDERS,
                    severity="info",
                    message=(
                        f"Placeholder pattern {hit['pattern']!r} matched "
                        f"{hit['match']!r} (suppressed)."
                    ),
                    location=f"{memo_md}:L{hit['line']}",
                )
            )

    # --- Check 7: memo_rhetoric_lint (issue #463, advisory) -----------------
    # Deterministic rhetoric lint over the body markdown (phrase / regex /
    # frequency AI-tell rules; see anvil/lib/rhetoric_lint.py). Warning
    # severity throughout (info when suppressed via
    # ``<!-- anvil-lint-disable: memo_rhetoric_lint -->`` or consumer-
    # downgraded); the dimension is NOT added to ``failed`` — the same
    # advisory model as memo_image_dimensions (#395): findings recorded,
    # ``passed`` unaffected, no CriticalFlag. Findings flow to
    # ``_progress.json.render_gate.findings`` with zero new plumbing.
    if not memo_md.is_file():
        reasons.append(
            f"{DIM_MEMO_RHETORIC}: {body_filename} not found; rhetoric "
            "lint skipped."
        )
    else:
        rhetoric_result = lint_rhetoric(
            memo_md.read_text(encoding="utf-8", errors="replace"),
            extra_rules_path=rhetoric_rules_path,
            suppress_rules=(DIM_MEMO_RHETORIC,),
        )
        rhetoric_warning_count = 0
        for rf in rhetoric_result.findings:
            if rf.severity == "warning":
                rhetoric_warning_count += 1
            matched = (
                f" (matched {rf.match!r})"
                if rf.match is not None and rf.line is not None
                else ""
            )
            findings.append(
                GateFinding(
                    gate=DIM_MEMO_RHETORIC,
                    severity=rf.severity,
                    message=f"[{rf.rule_id}] {rf.message}{matched}",
                    location=(
                        f"{memo_md}:L{rf.line}"
                        if rf.line is not None
                        else str(memo_md)
                    ),
                )
            )
        if rhetoric_warning_count:
            reasons.append(
                f"{DIM_MEMO_RHETORIC}: {rhetoric_warning_count} rhetoric "
                "warning(s) (advisory; mechanical evidence for dim 9 "
                "Rhetorical economy)."
            )

    # Build the GateResult. Keep the existing JSON shape (LaTeX-style
    # fields stay) and let the dim names disambiguate downstream
    # consumers. ``overfull_boxes`` is reused for the memo overflow hits
    # so the to_json shape is uniform across kinds.
    overfull_list: list[dict] = []
    for f in findings:
        if f.gate == DIM_MEMO_OVERFULL:
            # Lift back to the dict shape used in the JSON block.
            overfull_list.append({"kind": "overflow", "raw": f.message})
    placeholder_list: list[dict] = []
    for f in findings:
        if f.gate == DIM_MEMO_PLACEHOLDERS and f.severity == "error":
            placeholder_list.append(
                {
                    "pattern": None,
                    "path": str(memo_md),
                    "line": int(f.location.rsplit(":L", 1)[1])
                    if f.location and ":L" in f.location
                    else None,
                    "match": f.message,
                }
            )

    return GateResult(
        pdf_path=str(out_pdf),
        log_path=None,
        pages=pdf_pages,
        page_cap=page_range[1] if page_range is not None else None,
        overfull_boxes=overfull_list,
        overfull_threshold_pt=0.0,  # not meaningful for memo
        compile_status=compile_status,
        compile_exit_code=compile_exit_code,
        placeholders=placeholder_list,
        findings=findings,
        passed=not failed,
        reasons=reasons,
        failed_gates=failed,
        engine_used=engine_used or None,
        template_used=render_provenance.get("template"),
    )

