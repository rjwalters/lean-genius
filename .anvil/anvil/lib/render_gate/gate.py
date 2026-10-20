"""Public API: ``gate()`` (issue #1128 package split).

The four-dimension LaTeX-side render gate, dispatching to the seven-
dimension memo gate (:func:`anvil.lib.render_gate.memo_image_dimensions._gate_memo`)
when ``kind="memo"``. See the package ``__init__.py`` / former module
docstring for the full check list and calibration notes. Split out of
the former monolithic ``anvil/lib/render_gate.py`` along its existing
section banners.
"""

from __future__ import annotations

from pathlib import Path
from typing import Optional

from anvil.lib.render_gate.constants import (
    COMPILE_FAILED,
    COMPILE_SKIPPED,
    COMPILE_UNAVAILABLE,
    DEFAULT_PLACEHOLDER_PATTERNS,
    DIM_COMPILE,
    DIM_EMBEDDED_IMAGES,
    DIM_GLYPH_VERIFICATION,
    DIM_OVERFULL,
    DIM_PAGE_FIT,
    DIM_PLACEHOLDERS,
    PANDOC_ENGINE,
)
from anvil.lib.render_gate.helpers import (
    _count_pages_with_pdfinfo,
    _extract_engine_errors,
    _parse_overfull_boxes,
    _scan_placeholders,
    _which_pdfinfo,
)
from anvil.lib.render_gate.memo_image_dimensions import _gate_memo
from anvil.lib.render_gate.probes import (
    _count_body_image_refs,
    _count_pdf_embedded_images,
    _extract_pdf_text,
    _verify_source_glyphs,
    _which_pdfimages,
    _which_pdftotext,
)
from anvil.lib.render_gate.results import GateFinding, GateResult




def gate(
    pdf_path: Optional[Path] = None,
    *,
    kind: str = "latex",
    version_dir: Optional[Path] = None,
    out_pdf: Optional[Path] = None,
    target_length: Optional[dict] = None,
    words_per_page: Optional[int] = None,
    image_max_px: Optional[int] = None,
    render_engine: Optional[str] = None,
    latex_header_includes: Optional[str] = None,
    render_template: Optional[str] = None,
    render_lua_filters: Optional[list[str]] = None,
    render_metadata: Optional[dict] = None,
    rhetoric_rules_path: Optional[Path] = None,
    log_path: Optional[Path] = None,
    source_paths: Optional[list[Path]] = None,
    page_cap: Optional[int] = None,
    overfull_threshold_pt: float = 5.0,
    placeholder_patterns: Optional[tuple[str, ...]] = None,
    pdfinfo_path: Optional[str] = None,
    pdftotext_path: Optional[str] = None,
    pdfimages_path: Optional[str] = None,
    engine: Optional[str] = None,
    compile_status: Optional[str] = None,
    compile_exit_code: Optional[int] = None,
) -> GateResult:
    """Run the render gate over a compiled artifact.

    Dispatches by ``kind``:

    - ``kind="latex"`` (default): the four-dimension LaTeX-side gate. The
      historical signature (``pdf_path`` + ``log_path`` + ``source_paths``
      + ``page_cap`` + ``overfull_threshold_pt`` + ``placeholder_patterns``
      + ``pdfinfo_path`` + ``engine`` + ``compile_status`` +
      ``compile_exit_code``) is preserved verbatim.
    - ``kind="memo"``: the seven-dimension memo gate (Epic #158 / Phase 2;
      sixth dimension ``memo_image_dimensions`` added by issue #395;
      seventh dimension ``memo_rhetoric_lint`` added by issue #463).
      Requires ``version_dir``; ``out_pdf`` defaults to
      ``<version_dir>/memo.pdf``. ``target_length`` is the resolved
      ``{"words": [min, max]}`` or ``{"pages": [min, max]}`` dict (per
      ``SKILL.md`` §Length targets). Optional ``words_per_page`` is the
      per-thread override for the words→pages conversion factor (see
      module docstring §"page_cap calibration"); ``None`` uses
      :data:`MEMO_WORDS_PER_PAGE` (400). Malformed overrides
      (non-numeric or ``<= 0``) silently fall back to the default.
      Optional ``image_max_px`` (issue #395) is the per-thread pixel
      ceiling for the advisory ``memo_image_dimensions`` check;
      ``None`` uses :data:`MEMO_IMAGE_MAX_PX` (6000). Malformed
      overrides (non-numeric or ``<= 0``) silently fall back to the
      default — the same coerce-or-fallback contract as
      ``words_per_page``; the effective ceiling is recorded in the
      finding message.
      Optional ``render_engine`` (issue #320) is the per-document
      override resolved from ``BriefDocument.render_engine`` (one of
      ``"weasyprint"``, ``"xelatex"``, ``"wkhtmltopdf"``); when set and
      available on PATH it overrides the auto-priority, otherwise
      falls through gracefully.
      Optional ``latex_header_includes`` (issue #347) is per-document
      free-form LaTeX preamble text resolved from
      ``BriefDocument.latex_header_includes``. Threaded into pandoc's
      ``header-includes`` slot via ``--include-in-header=<tempfile>``
      **only when** the dispatched engine resolves to ``xelatex``;
      silently skipped (with a breadcrumb in ``reasons``) for the
      HTML chain. Enables consumers with table-dense memos to load
      ``xcolor`` / ``tabularx`` / custom environments referenced by
      ``{=latex}`` raw blocks without maintaining a full
      ``template.tex`` override.
      Optional ``render_template`` / ``render_lua_filters`` /
      ``render_metadata`` (issue #391) are the per-document consumer
      pandoc passthrough knobs resolved from the matching
      ``BriefDocument`` fields. ``render_template`` is a consumer-owned
      pandoc template path (BRIEF-relative paths are resolved against
      ``version_dir.parent.parent``, the project root under the
      post-#295/#296 canonical model; absolute paths used as-is) — it
      short-circuits the theme/framework template **iff** its extension
      matches the dispatched engine chain and the file exists; on
      mismatch or missing file the default chain applies with a
      breadcrumb in ``reasons`` (the #347 silent-with-record skip).
      ``render_lua_filters`` (``--lua-filter`` per entry, declaration
      order) and ``render_metadata`` (``-M key=value`` per entry, with
      the literal ``{N}`` token in values expanded to the version
      number parsed from the ``<slug>.{N}`` version-dir name) are
      engine-agnostic and always applied when set. Render provenance is
      surfaced on ``GateResult.engine_used`` / ``template_used``.
      Optional ``rhetoric_rules_path`` (issue #463) is a consumer JSON
      rule file for the advisory ``memo_rhetoric_lint`` dimension
      (check 7), merged over ``rhetoric_lint.DEFAULT_RHETORIC_RULES``;
      malformed input graceful-degrades to a defaults-only run with a
      warning finding naming the parse error. ``None`` (the default)
      runs the framework defaults — defaults-only behavior is
      byte-identical whether or not any consumer declaration exists.
      Wired (issue #468) from the #461 voice contract's
      ``voice.rhetoric_rules`` sub-key: memo-render step 4g calls
      ``anvil.lib.project_brief.resolve_rhetoric_rules`` and forwards
      the resolved path (or the joined declared path when the file is
      missing, so the lint surfaces the broken declaration as a
      warning finding).
      Routes through :func:`_gate_memo` which invokes
      :func:`_render_memo_source` for pandoc + the preferred HTML/PDF
      engine, then runs the memo-specific checks. See module
      docstring for the full check list.

    Parameters (kind="latex")
    -------------------------
    pdf_path:
        Path to the compiled PDF. May or may not exist; a missing PDF
        skips the PDF-dependent checks gracefully.
    log_path:
        Optional path to the LaTeX/engine log file. When ``None`` (or the
        file is missing), the overfull check is skipped with a note in
        ``reasons``.
    source_paths:
        List of source files (``.tex`` / ``.md``) to grep for placeholders.
        When ``None`` or empty, the placeholder check is skipped.
    page_cap:
        Hard cap on page count. ``None`` (the common case) skips the
        page-fit check — the actual page count is still recorded in
        ``GateResult.pages`` for informational purposes.
    overfull_threshold_pt:
        Overfull-box tolerance in points. Boxes with amount strictly
        greater than this threshold fail. Default ``5.0``.
    placeholder_patterns:
        Tuple of regex patterns. When ``None``, uses
        ``DEFAULT_PLACEHOLDER_PATTERNS``. When the caller wants to
        *extend* the defaults (e.g. ip-uspto's ``\\refnum{??}``), pass
        ``DEFAULT_PLACEHOLDER_PATTERNS + ("...",)``.
    pdfinfo_path:
        Override for the ``pdfinfo`` executable path (testability).
    engine:
        Optional engine label echoed into reasons (e.g., ``"pandoc"``).
        When ``engine == "pandoc"`` the overfull-box check is skipped
        with a documented note (pandoc has no ``Overfull`` semantics).
    compile_status, compile_exit_code:
        Caller-supplied compile outcome. When the caller has already
        compiled (or this is a pre-built PDF), pass these to populate the
        ``compile`` JSON block. When both are ``None`` the gate assumes
        ``COMPILE_SKIPPED`` (the PDF was prepared elsewhere).

    All four checks run independently — no short-circuit. ``passed``
    reflects the AND of the gates that did NOT skip.
    """
    if kind == "memo":
        if version_dir is None:
            raise ValueError(
                "gate(kind='memo') requires version_dir (the "
                "<thread>.{N}/ directory containing <thread>.md)."
            )
        return _gate_memo(
            version_dir=Path(version_dir),
            out_pdf=Path(out_pdf) if out_pdf is not None else None,
            target_length=target_length,
            placeholder_patterns=placeholder_patterns,
            pdfinfo_path=pdfinfo_path,
            words_per_page=words_per_page,
            image_max_px=image_max_px,
            render_engine=render_engine,
            latex_header_includes=latex_header_includes,
            render_template=render_template,
            render_lua_filters=render_lua_filters,
            render_metadata=render_metadata,
            rhetoric_rules_path=rhetoric_rules_path,
        )
    if kind != "latex":
        raise ValueError(
            f"gate(kind={kind!r}): unsupported kind. "
            "Expected 'latex' (default) or 'memo'."
        )
    if pdf_path is None:
        raise ValueError(
            "gate(kind='latex') requires pdf_path (the compiled PDF)."
        )
    pdf_path = Path(pdf_path)
    log_p = Path(log_path) if log_path is not None else None
    sources = [Path(s) for s in (source_paths or [])]
    placeholder_patterns = (
        placeholder_patterns
        if placeholder_patterns is not None
        else DEFAULT_PLACEHOLDER_PATTERNS
    )

    findings: list[GateFinding] = []
    reasons: list[str] = []
    failed: set[str] = set()

    # --- Compile status -----------------------------------------------------
    if compile_status is None:
        # Caller didn't run a compile; assume the PDF was prepared upstream.
        # If the PDF is missing, we record a compile failure surrogate so
        # the gate fails for the right reason.
        if pdf_path.exists():
            compile_status_eff = COMPILE_SKIPPED
        else:
            compile_status_eff = COMPILE_FAILED
            compile_exit_code = compile_exit_code if compile_exit_code is not None else -1
            failed.add(DIM_COMPILE)
            msg = f"{DIM_COMPILE}: PDF not produced ({pdf_path} missing)"
            reasons.append(msg)
            findings.append(
                GateFinding(
                    gate=DIM_COMPILE,
                    severity="error",
                    message=f"Expected PDF not found at {pdf_path}.",
                    location=str(pdf_path),
                )
            )
    else:
        compile_status_eff = compile_status
        if compile_status == COMPILE_FAILED:
            failed.add(DIM_COMPILE)
            msg = (
                f"{DIM_COMPILE}: engine exited "
                f"{compile_exit_code if compile_exit_code is not None else 'non-zero'}."
            )
            reasons.append(msg)
            findings.append(
                GateFinding(
                    gate=DIM_COMPILE,
                    severity="error",
                    message=(
                        f"Compile failed (exit "
                        f"{compile_exit_code if compile_exit_code is not None else '?'}); "
                        f"see log at {log_p}."
                        if log_p is not None
                        else f"Compile failed (exit "
                        f"{compile_exit_code if compile_exit_code is not None else '?'})."
                    ),
                    location=str(log_p) if log_p else str(pdf_path),
                )
            )
            # Pull the last few engine error lines into the findings stream.
            if log_p is not None and log_p.exists():
                try:
                    log_text = log_p.read_text(encoding="utf-8", errors="replace")
                except OSError:
                    log_text = ""
                for err in _extract_engine_errors(log_text):
                    findings.append(
                        GateFinding(
                            gate=DIM_COMPILE,
                            severity="error",
                            message=err,
                            location=str(log_p),
                        )
                    )
        elif compile_status == COMPILE_UNAVAILABLE:
            # The engine isn't installed. We don't *fail* the compile gate
            # (the gate cannot prove the artifact is broken), but we DO
            # record an actionable reason so the operator knows to install
            # the toolchain. Failing closed would block reviews on every
            # machine without LaTeX; failing open keeps the rest of the
            # pipeline usable.
            reasons.append(
                f"{DIM_COMPILE}: engine not on PATH; compile skipped. "
                "Install the engine (e.g., `brew install --cask mactex` / "
                "`apt-get install texlive-xetex`)."
            )

    # --- Page fit -----------------------------------------------------------
    page_count: Optional[int] = None
    if pdf_path.exists():
        page_count = _count_pages_with_pdfinfo(
            pdf_path, pdfinfo_path=pdfinfo_path
        )
        if page_count is None and _which_pdfinfo(pdfinfo_path) is None:
            reasons.append(
                f"{DIM_PAGE_FIT}: page-fit check skipped: pdfinfo not on PATH "
                "(install poppler-utils: `brew install poppler` / "
                "`apt-get install poppler-utils`)."
            )
        elif page_count is None:
            reasons.append(
                f"{DIM_PAGE_FIT}: pdfinfo returned non-zero or unparsable output."
            )
    if page_cap is not None and page_count is not None:
        if page_count > page_cap:
            failed.add(DIM_PAGE_FIT)
            msg = (
                f"{DIM_PAGE_FIT}: PDF has {page_count} pages, exceeding "
                f"cap of {page_cap}."
            )
            reasons.append(msg)
            findings.append(
                GateFinding(
                    gate=DIM_PAGE_FIT,
                    severity="error",
                    message=msg.split(": ", 1)[1],
                    location=f"{pdf_path}:pages={page_count}",
                )
            )

    # --- Overfull boxes -----------------------------------------------------
    overfull: list[dict] = []
    if engine == PANDOC_ENGINE:
        reasons.append(
            f"{DIM_OVERFULL}: overfull-box check skipped: engine is pandoc "
            "(no `Overfull` semantics in pandoc/CSS output)."
        )
    elif log_p is None or not log_p.exists():
        reasons.append(
            f"{DIM_OVERFULL}: overfull-box check skipped: compile log not "
            "available."
        )
    else:
        try:
            log_text = log_p.read_text(encoding="utf-8", errors="replace")
        except OSError:
            log_text = ""
        # Best-effort fallback name for the top-level document, used only
        # when the log itself has no recognizable file-open marker (so the
        # scope-stack walk in ``_parse_overfull_boxes`` can't resolve a
        # file at all). ``sources[0]`` is the tex_path passed to
        # ``compile_and_gate``/``gate`` when the caller supplies one;
        # otherwise fall back to the PDF's stem (``compile_and_gate`` names
        # the PDF after ``tex_path.stem``).
        root_name = sources[0].name if sources else f"{pdf_path.stem}.tex"
        overfull = _parse_overfull_boxes(
            log_text, overfull_threshold_pt, root_name=root_name
        )
        if overfull:
            failed.add(DIM_OVERFULL)
            reasons.append(
                f"{DIM_OVERFULL}: {len(overfull)} overfull box(es) over "
                f"{overfull_threshold_pt}pt threshold."
            )
            for box in overfull:
                line_note = f"L{box['line']}" if box["line"] else "L?"
                # File-relative attribution (issue #961): a box emitted
                # while an \input'd child file was open on the TeX log's
                # scope stack is attributed to that child (e.g.
                # ``claims.tex``), not the top-level document, with a line
                # number relative to the file it names.
                file_note = box["file"] if box["file"] else str(log_p)
                findings.append(
                    GateFinding(
                        gate=DIM_OVERFULL,
                        severity="error",
                        message=(
                            f"Overfull \\{box['kind']} "
                            f"({box['amount_pt']:.1f}pt over) in "
                            f"{file_note} at {line_note}."
                        ),
                        location=f"{file_note}:{line_note}",
                    )
                )

    # --- Placeholders -------------------------------------------------------
    placeholders: list[dict] = []
    if sources:
        placeholders = _scan_placeholders(sources, placeholder_patterns)
        if placeholders:
            failed.add(DIM_PLACEHOLDERS)
            reasons.append(
                f"{DIM_PLACEHOLDERS}: {len(placeholders)} placeholder hit(s) "
                "across source files."
            )
            for hit in placeholders:
                findings.append(
                    GateFinding(
                        gate=DIM_PLACEHOLDERS,
                        severity="error",
                        message=(
                            f"Placeholder pattern {hit['pattern']!r} matched "
                            f"{hit['match']!r}."
                        ),
                        location=f"{hit['path']}:L{hit['line']}",
                    )
                )

    # --- Glyph verification (issue #692) ------------------------------------
    # Source-driven: sweep the body for EVERY non-ASCII codepoint and assert
    # each survives into the pdftotext extraction at >= its source count.
    # Catches the silent font glyph-drop (STIX Two Text ``≠``) that a
    # hardcoded allow-list misses by construction. Error severity — the ``≠``
    # canary shipped a semantically-wrong PDF while every other gate was green.
    if sources and pdf_path.exists():
        if _which_pdftotext(pdftotext_path) is None:
            reasons.append(
                f"{DIM_GLYPH_VERIFICATION}: glyph check skipped: pdftotext "
                "not on PATH (install poppler-utils: `brew install poppler` / "
                "`apt-get install poppler-utils`)."
            )
        else:
            pdf_text = _extract_pdf_text(pdf_path, pdftotext_path=pdftotext_path)
            if pdf_text is None:
                reasons.append(
                    f"{DIM_GLYPH_VERIFICATION}: glyph check skipped: pdftotext "
                    "returned non-zero or no output."
                )
            else:
                dropped = _verify_source_glyphs(sources, pdf_text)
                if dropped:
                    failed.add(DIM_GLYPH_VERIFICATION)
                    reasons.append(
                        f"{DIM_GLYPH_VERIFICATION}: {len(dropped)} source "
                        "codepoint(s) missing or under-counted in the rendered "
                        "PDF (silent glyph drop)."
                    )
                    for d in dropped:
                        findings.append(
                            GateFinding(
                                gate=DIM_GLYPH_VERIFICATION,
                                severity="error",
                                message=(
                                    f"Codepoint {d['codepoint']} "
                                    f"({d['name']!r}) appears {d['source_count']}× "
                                    f"in source but {d['pdf_count']}× in the PDF "
                                    "— the font likely dropped this glyph."
                                ),
                                location=f"{pdf_path}:{d['codepoint']}",
                            )
                        )

    # --- Embedded-image assertion (issue #692) ------------------------------
    # Count ``![…](path)`` refs in the body; assert pdfimages -list reports
    # at least that many embedded images. Catches the "zero embedded images,
    # every other gate green" failure (botho v2 canary). Error severity — it
    # must block, not just warn (the whole point is that no other gate caught
    # it). Only runs when the body actually references images.
    ref_count = _count_body_image_refs(sources) if sources else 0
    if ref_count > 0 and pdf_path.exists():
        if _which_pdfimages(pdfimages_path) is None:
            reasons.append(
                f"{DIM_EMBEDDED_IMAGES}: embedded-image check skipped: "
                "pdfimages not on PATH (install poppler-utils: "
                "`brew install poppler` / `apt-get install poppler-utils`)."
            )
        else:
            embedded = _count_pdf_embedded_images(
                pdf_path, pdfimages_path=pdfimages_path
            )
            if embedded is None:
                reasons.append(
                    f"{DIM_EMBEDDED_IMAGES}: embedded-image check skipped: "
                    "pdfimages returned non-zero or unparsable output."
                )
            elif embedded < ref_count:
                failed.add(DIM_EMBEDDED_IMAGES)
                msg = (
                    f"body references {ref_count} image(s) but the PDF embeds "
                    f"only {embedded}."
                )
                reasons.append(f"{DIM_EMBEDDED_IMAGES}: {msg}")
                findings.append(
                    GateFinding(
                        gate=DIM_EMBEDDED_IMAGES,
                        severity="error",
                        message=(
                            f"Embedded-image shortfall: {msg} Every referenced "
                            "figure should render into the PDF as an embedded "
                            "image."
                        ),
                        location=f"{pdf_path}:embedded={embedded}",
                    )
                )

    return GateResult(
        pdf_path=str(pdf_path),
        log_path=str(log_p) if log_p else None,
        pages=page_count,
        page_cap=page_cap,
        overfull_boxes=overfull,
        overfull_threshold_pt=overfull_threshold_pt,
        compile_status=compile_status_eff,
        compile_exit_code=compile_exit_code,
        placeholders=placeholders,
        findings=findings,
        passed=not failed,
        reasons=reasons,
        failed_gates=failed,
    )

