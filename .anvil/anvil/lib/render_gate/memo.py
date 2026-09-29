"""Memo-mode internals (``kind="memo"``) — issue #1128 package split.

Engine selection (:func:`_select_memo_engine`), theme-context discovery
(:func:`_discover_memo_theme_context`, issue #322), the pandoc render
invocation (:func:`_render_memo_source`), the memo-side overfull-stderr
parser, the placeholder scanner + lint-disable directive handling, and
the ``words_per_page`` / ``image_max_px`` override coercers. The top-
level memo dispatcher (:func:`_gate_memo`) and the ``target_length``
resolver live in ``memo_image_dimensions.py`` (unchanged physical
section boundary from the pre-split file — see that module's docstring
for why). Split out of the former monolithic
``anvil/lib/render_gate.py`` along its existing section banners — see
``anvil/lib/render_gate/__init__.py`` for the full package rationale.
"""

from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path
from typing import Optional

from anvil.lib.render_gate.constants import (
    COMPILE_FAILED,
    COMPILE_OK,
    COMPILE_UNAVAILABLE,
    DIM_MEMO_COMPILE,
    DIM_MEMO_PLACEHOLDERS,
    MEMO_ENGINE_WEASYPRINT,
    MEMO_ENGINE_WKHTMLTOPDF,
    MEMO_ENGINE_XELATEX,
    _MEMO_LINT_DISABLE_RE,
    _MEMO_OVERFULL_RES,
)




def _select_memo_engine(requested: Optional[str] = None) -> Optional[str]:
    """Return the preferred memo HTML/PDF engine that is available on PATH.

    Default priority per architect Q1 (Epic #158): ``weasyprint`` >
    ``wkhtmltopdf`` > ``xelatex``. Returns ``None`` when none are
    available — callers surface ``MEMO_RENDERER_REMEDIATION`` in that
    case.

    When ``requested`` is one of the recognized engine names AND that
    engine is available on PATH, it wins over the default priority
    order. When the requested engine is NOT available, the function
    falls through to the default order rather than returning ``None``
    — the "respect the brand pin if you can, but render something
    rather than nothing" contract that matches the broader anvil
    graceful-degrade discipline. The caller can detect a mismatch by
    comparing the returned engine to ``requested``.

    The ``requested`` knob is the integration point for two related
    features:

    - The per-theme ``render_engine`` default from
      ``<consumer>/.anvil/themes/<theme>/theme.yml`` (issue #322).
    - The per-document ``documents[].render_engine`` override from
      the project BRIEF (issue #320).

    Per-document > per-theme > framework default. The caller in
    :func:`_render_memo_source` is responsible for resolving the
    precedence and passing the winning value as ``requested``.

    The optional ``requested`` parameter (issue #320) carries the
    per-document override from ``BriefDocument.render_engine`` (one of
    ``"weasyprint"``, ``"xelatex"``, ``"wkhtmltopdf"``). When set AND the
    requested engine is available on PATH, this function returns the
    requested engine regardless of the default priority order. When the
    requested engine is set but NOT available on PATH, the function
    **gracefully falls through** to the existing auto-priority — it does
    NOT raise (consistent with the graceful-degrade contract called out
    in architect Q7). When ``requested`` is ``None``, behavior is
    identical to the pre-#320 contract: no regression on legacy callers.

    Indirected through :mod:`anvil.lib.render` so monkeypatched
    ``check_*_available`` functions in tests take effect uniformly.
    """
    # Lazy import to avoid a circular dep at module load time and to let
    # tests monkeypatch the checks on the render module.
    from anvil.lib import render as _render

    # Issue #320 + #322: honor a per-thread or per-theme requested engine
    # when both (a) it is one of the known values AND (b) the corresponding
    # binary is available on PATH. Unknown / unavailable requests fall
    # through to the priority order below — no exception. The
    # ``str(...).strip().lower()`` normalization tolerates loose YAML
    # input shapes (whitespace, mixed case) from theme.yml or BRIEF.md.
    if requested:
        req = str(requested).strip().lower()
        if req == MEMO_ENGINE_WEASYPRINT and _render.check_weasyprint_available():
            return MEMO_ENGINE_WEASYPRINT
        if req == MEMO_ENGINE_WKHTMLTOPDF and _render.check_wkhtmltopdf_available():
            return MEMO_ENGINE_WKHTMLTOPDF
        if req == MEMO_ENGINE_XELATEX and shutil.which(MEMO_ENGINE_XELATEX) is not None:
            return MEMO_ENGINE_XELATEX
        # Requested-but-unavailable (or unknown value): fall through.

    if _render.check_weasyprint_available():
        return MEMO_ENGINE_WEASYPRINT
    if _render.check_wkhtmltopdf_available():
        return MEMO_ENGINE_WKHTMLTOPDF
    if shutil.which(MEMO_ENGINE_XELATEX) is not None:
        return MEMO_ENGINE_XELATEX
    return None


def _memo_body_filename(version_dir: Path) -> str:
    """Return the body markdown filename for a memo version directory.

    Body filename echoes the thread slug per the issue #295 project-org
    model lock: the on-disk shape is ``<thread>/<thread>.{N}/<thread>.md``,
    so the body filename is ``<version_dir.parent.name>.md``.
    """
    return f"{version_dir.parent.name}.md"


def _discover_memo_theme_context(
    version_dir: Path,
) -> tuple[Optional[Path], Optional[str], Optional[str]]:
    """Return ``(consumer_root, theme_name, requested_engine)`` for the memo.

    Walks upward from ``version_dir`` to:

    1. Locate the consumer root (the directory containing ``.anvil/``).
    2. Locate the enclosing project root and read its BRIEF.md.
    3. Resolve the project's theme (if any) and load
       ``<consumer>/.anvil/themes/<theme>/theme.yml`` for the
       ``render_engine`` default.

    All three return slots are independently optional — the caller
    handles ``None`` for each gracefully. Discovery never raises; any
    error in BRIEF parsing or theme loading is swallowed and the
    relevant slot returns ``None``. This matches the graceful-degrade
    contract of the existing memo render path.

    Issue #322 (theme primitive) + issue #320 (per-doc render_engine)
    integration point. The per-doc override from #320 is currently
    sourced by the caller of :func:`_render_memo_source`; this helper
    deliberately stops at the theme tier so the two issues don't fight
    over the same code surface.
    """
    consumer_root: Optional[Path] = None
    theme_name: Optional[str] = None
    requested_engine: Optional[str] = None

    # Tier 1: locate consumer root (the directory containing .anvil/).
    try:
        from anvil.lib.theme import find_consumer_root, load_theme

        consumer_root = find_consumer_root(version_dir)
    except Exception:
        # Defensive — theme.py is part of the framework so import should
        # always succeed; this guard exists for future-proofing.
        return (None, None, None)

    # Tier 2: locate project root + read BRIEF for theme: field.
    try:
        # Lazy import: keeps the pydantic dependency of project_brief
        # off this module's import-time path. The discovery + BRIEF
        # primitives were promoted from the memo skill's lib/ to
        # anvil/lib/ under issue #382, so this is now a plain sibling
        # import (no sys.path injection needed).
        from anvil.lib.project_brief import load_project_brief
        from anvil.lib.project_discovery import discover_thread_root

        discovery = discover_thread_root(version_dir)
        if discovery is not None:
            brief = load_project_brief(discovery.project_root)
            if brief is not None and brief.theme:
                theme_name = brief.theme
    except Exception:
        # Any BRIEF discovery or parse failure → no theme available;
        # render falls through to framework defaults.
        return (consumer_root, None, None)

    # Tier 3: load theme.yml for render_engine default.
    if theme_name is not None and consumer_root is not None:
        try:
            theme = load_theme(consumer_root, theme_name)
            if theme is not None:
                requested_engine = theme.render_engine
        except Exception:
            requested_engine = None

    return (consumer_root, theme_name, requested_engine)


def _render_memo_source(
    version_dir: Path,
    out_pdf: Path,
    requested_engine: Optional[str] = None,
    latex_header_includes: Optional[str] = None,
    render_template: Optional[str] = None,
    render_lua_filters: Optional[list[str]] = None,
    render_metadata: Optional[dict] = None,
    provenance: Optional[dict] = None,
) -> tuple[str, int, str, str]:
    """Run pandoc → (weasyprint OR wkhtmltopdf OR xelatex) over the
    version dir's body markdown and write ``out_pdf``.

    Body filename echoes the thread slug per #295 — for a
    ``investment-memo/investment-memo.1/`` version dir the body is
    ``investment-memo.md``.

    This is the memo-side analog of :func:`compile_and_gate`'s LaTeX
    invocation: a single deterministic shell-out that the gate then
    inspects. The chain matches the documented pin in
    ``anvil/lib/memo/README.md``: pandoc is the common front-end; the
    HTML-to-PDF leg prefers weasyprint, falls back to wkhtmltopdf, falls
    back to xelatex as the engine-of-last-resort.

    Parameters
    ----------
    version_dir:
        ``<thread>.{N}/`` directory containing ``<thread>.md`` (body
        filename echoes the thread slug per #295).
    out_pdf:
        Output PDF path. Parent directory must exist.
    requested_engine:
        Optional per-document engine override (issue #320). Composed
        with the per-theme ``render_engine`` default from issue #322
        as ``effective_engine = requested_engine or theme_engine``;
        the result is threaded through to :func:`_select_memo_engine`.
        Per-thread wins by short-circuit: when ``requested_engine`` is
        truthy it is used directly; when ``None`` the per-theme default
        from ``theme.yml`` (discovered via
        :func:`_discover_memo_theme_context`) takes over; when both are
        absent, :func:`_select_memo_engine` falls through to the
        framework auto-priority (weasyprint > wkhtmltopdf > xelatex).
        When set and available on PATH, the effective engine is used;
        otherwise auto-priority applies.
    latex_header_includes:
        Optional per-document free-form LaTeX preamble text (issue
        #347). When set AND the dispatched engine resolves to
        ``xelatex``, the content is written to a tempfile and passed
        to pandoc via ``--include-in-header=<tempfile>``; pandoc
        emits the content into the xelatex template's
        ``$for(header-includes)$`` slot. The tempfile is removed
        before this function returns (whether the subprocess
        succeeded or failed). When the engine is NOT xelatex, the
        include is silently skipped (caller is expected to record
        the skip in the audit trail) — this matches the
        engine-scoping policy that ``latex_header_includes`` is for
        LaTeX content only and the HTML chain has no analogue.
    render_template:
        Optional per-document consumer-owned pandoc template path
        (issue #391). Relative paths are resolved against
        ``version_dir.parent.parent`` (the project root — the
        directory containing ``BRIEF.md`` under the post-#295/#296
        canonical ``<project>/<slug>/<slug>.{N}/`` model); absolute
        paths are used as-is. Applied as ``--template <path>``
        *instead of* the theme/framework template **iff** the file
        exists AND its extension matches the dispatched chain
        (``.tex`` / ``.latex`` on xelatex; ``.html`` / ``.htm`` on
        weasyprint / wkhtmltopdf). On mismatch or missing file the
        existing resolver chain applies and a skip breadcrumb is
        recorded in ``provenance["skips"]`` (the caller surfaces it
        in ``reasons``). The HTML chain's ``--css`` flag is NOT
        suppressed by a consumer template — a self-contained
        template simply ignores it.
    render_lua_filters:
        Optional list of pandoc Lua filter paths (issue #391),
        resolved like ``render_template``. Engine-agnostic: each
        existing filter is passed as ``--lua-filter <path>`` in
        declaration order on every chain; a missing filter file is
        skipped with a ``provenance["skips"]`` breadcrumb (remaining
        filters still apply).
    render_metadata:
        Optional map of pandoc metadata entries (issue #391). Each
        ``key: value`` pair is passed as ``-M key=value``.
        Engine-agnostic. The literal token ``{N}`` in a *value* is
        expanded to the version number parsed from the
        ``<slug>.{N}`` version-dir name (e.g., ``Draft v{N}`` →
        ``Draft v7`` for ``<slug>.7/``); when the dir name carries
        no version suffix the value passes through verbatim.
    provenance:
        Optional caller-owned dict the function fills with render
        provenance (issue #391): ``provenance["template"]`` is the
        template provenance string (resolved consumer path,
        ``"theme:<name>"``, ``"framework-default"``, or
        ``"pandoc-default"`` when no ``--template`` flag was passed)
        and ``provenance["skips"]`` is a list of breadcrumb strings
        for skipped consumer inputs. Untouched when no engine ran
        (pandoc/engines unavailable, missing body markdown).

    Returns
    -------
    A 4-tuple of ``(compile_status, exit_code, engine_used, stderr)``:

    - ``compile_status``: one of :data:`COMPILE_OK`,
      :data:`COMPILE_FAILED`, :data:`COMPILE_UNAVAILABLE`,
      :data:`COMPILE_SKIPPED`.
    - ``exit_code``: subprocess exit code, or ``-1`` when the engine
      raised before producing one.
    - ``engine_used``: the engine name (``"weasyprint"``,
      ``"wkhtmltopdf"``, ``"xelatex"``, or ``""`` when no engine ran).
    - ``stderr``: captured stderr text from the pandoc invocation
      (used by the overfull-check pass; empty when nothing ran).

    Does NOT raise on engine absence. Returns
    ``(COMPILE_UNAVAILABLE, -1, "", "")`` instead so the caller can
    surface :data:`MEMO_RENDERER_REMEDIATION` without an exception
    handler. This matches the graceful-degrade contract called out in
    architect Q7 (Epic #158).
    """
    # Lazy import — see :func:`_select_memo_engine`.
    from anvil.lib import render as _render

    body_filename = _memo_body_filename(version_dir)
    memo_md = version_dir / body_filename
    if not memo_md.is_file():
        # Missing source — surrogate "failed" outcome so the compile gate
        # fires for the right reason without a Python exception.
        return (COMPILE_FAILED, -1, "", f"{body_filename} not found at {memo_md}")

    if not _render.check_pandoc_available():
        return (COMPILE_UNAVAILABLE, -1, "", "")

    # Issue #322: discover the project's theme context (consumer_root,
    # theme_name, theme-default render_engine). All three slots are
    # optional — when no theme is declared (the canary's existing
    # single-tenant flow), this returns ``(None, None, None)`` and the
    # render path is byte-identical to pre-#322 behavior.
    consumer_root, theme_name, theme_engine = _discover_memo_theme_context(
        version_dir
    )

    # Issue #320 + #322 precedence: per-thread (``requested_engine`` from
    # ``documents[].render_engine``) wins over per-theme
    # (``theme.yml.render_engine``). The ``or`` short-circuit yields the
    # first truthy value, so a per-thread override (when set) wins; when
    # absent (``None``), the per-theme default takes over; when both are
    # absent, ``_select_memo_engine`` falls through to the framework
    # auto-priority (weasyprint > wkhtmltopdf > xelatex).
    effective_engine = requested_engine or theme_engine
    engine = _select_memo_engine(requested=effective_engine)
    if engine is None:
        return (COMPILE_UNAVAILABLE, -1, "", "")

    # Construct the pandoc command. The HTML chain uses --pdf-engine; the
    # xelatex chain uses the same flag (pandoc dispatches internally).
    cmd = [
        "pandoc",
        str(memo_md),
        "-o",
        str(out_pdf),
        f"--pdf-engine={engine}",
    ]
    # Resolve template + stylesheet paths through the theme-aware
    # resolver (issue #322). When no theme is declared or no per-theme
    # override exists for an asset, the resolver returns the framework
    # default — identical to the pre-#322 ``memo_lib / <asset>`` lookup.
    # Lazy import to keep the resolver module out of the load-time
    # circular dep chain with anvil.lib.render.
    import sys as _sys

    # NOTE (issue #1128 package split): this module now lives one
    # directory deeper than the pre-split ``anvil/lib/render_gate.py``
    # (``anvil/lib/render_gate/memo.py``), so the walk up to the
    # ``anvil/`` package root needs one more ``.parent`` than the
    # original ``Path(__file__).parent.parent``.
    _memo_lib_path = (
        Path(__file__).parent.parent.parent / "skills" / "memo" / "lib"
    )
    _memo_lib_str = str(_memo_lib_path)
    if _memo_lib_str not in _sys.path:
        _sys.path.insert(0, _memo_lib_str)
    try:
        from theme_resolver import (  # type: ignore
            MEMO_ASSET_STYLES_CSS,
            MEMO_ASSET_TEMPLATE_HTML,
            MEMO_ASSET_TEMPLATE_TEX,
            resolve_memo_asset,
        )
    except ImportError:
        # Defensive — should never trigger in a sane install; fall back
        # to the framework default lookup.
        resolve_memo_asset = None  # type: ignore[assignment]
        MEMO_ASSET_TEMPLATE_HTML = "template.html"  # type: ignore[assignment]
        MEMO_ASSET_STYLES_CSS = "styles.css"  # type: ignore[assignment]
        MEMO_ASSET_TEMPLATE_TEX = "template.tex"  # type: ignore[assignment]

    memo_lib = Path(_render.__file__).parent / "memo"

    def _resolve(asset_name: str) -> Path:
        if resolve_memo_asset is None:
            return memo_lib / asset_name
        return resolve_memo_asset(
            asset_name,
            consumer_root=consumer_root,
            theme_name=theme_name,
        )

    # Issue #391: per-doc consumer pandoc passthrough. Paths are
    # BRIEF-relative — resolved against the project root
    # (``version_dir.parent.parent`` under the post-#295/#296 canonical
    # ``<project>/<slug>/<slug>.{N}/`` model — the directory containing
    # BRIEF.md). Resolution happens here at render time (not persisted
    # as absolute paths) so ``_progress.json`` stays portable across
    # repo moves/clones and re-running memo-render alone picks up
    # template/filter edits. Absolute paths are used as-is.
    project_root = version_dir.parent.parent

    def _resolve_consumer_path(raw: str) -> Path:
        p = Path(raw)
        return p if p.is_absolute() else (project_root / p)

    def _note_skip(msg: str) -> None:
        if provenance is not None:
            provenance.setdefault("skips", []).append(msg)

    def _record_template(value: str) -> None:
        if provenance is not None:
            provenance["template"] = value

    def _default_template_provenance(resolved: Path, asset_name: str) -> str:
        if resolved == memo_lib / asset_name:
            return "framework-default"
        if theme_name:
            return f"theme:{theme_name}"
        return str(resolved)

    # Consumer template: extension-matched against the dispatched chain
    # (the #347 silent-with-record pattern — no parse-time engine
    # coupling, because the requested engine can legitimately fall
    # through on a machine missing the binary). A ``.tex`` template on
    # an HTML-chain dispatch (the canary's regression shape) is skipped
    # with a breadcrumb and the default resolver chain applies.
    consumer_template: Optional[Path] = None
    if render_template is not None:
        candidate = _resolve_consumer_path(render_template)
        suffix = candidate.suffix.lower()
        chain_exts = (
            (".html", ".htm")
            if engine in (MEMO_ENGINE_WEASYPRINT, MEMO_ENGINE_WKHTMLTOPDF)
            else (".tex", ".latex")
        )
        if suffix not in chain_exts:
            _note_skip(
                f"{DIM_MEMO_COMPILE}: render_template {render_template!r} "
                f"extension {suffix or '(none)'} does not match the "
                f"dispatched engine={engine!r} chain (expected one of "
                f"{list(chain_exts)}); consumer template skipped, "
                f"default template chain used."
            )
        elif not candidate.is_file():
            _note_skip(
                f"{DIM_MEMO_COMPILE}: render_template {render_template!r} "
                f"not found at {candidate}; consumer template skipped, "
                f"default template chain used."
            )
        else:
            consumer_template = candidate

    if engine in (MEMO_ENGINE_WEASYPRINT, MEMO_ENGINE_WKHTMLTOPDF):
        styles_css = _resolve(MEMO_ASSET_STYLES_CSS)
        if consumer_template is not None:
            cmd.extend(["--template", str(consumer_template)])
            _record_template(str(consumer_template))
        else:
            html_template = _resolve(MEMO_ASSET_TEMPLATE_HTML)
            if html_template.exists():
                cmd.extend(["--template", str(html_template)])
                _record_template(
                    _default_template_provenance(
                        html_template, MEMO_ASSET_TEMPLATE_HTML
                    )
                )
            else:
                _record_template("pandoc-default")
        if styles_css.exists():
            cmd.extend(["--css", str(styles_css)])
        cmd.append("--standalone")
    else:  # xelatex
        if consumer_template is not None:
            cmd.extend(["--template", str(consumer_template)])
            _record_template(str(consumer_template))
        else:
            tex_template = _resolve(MEMO_ASSET_TEMPLATE_TEX)
            if tex_template.exists():
                cmd.extend(["--template", str(tex_template)])
                _record_template(
                    _default_template_provenance(
                        tex_template, MEMO_ASSET_TEMPLATE_TEX
                    )
                )
            else:
                _record_template("pandoc-default")

    # Issue #391: Lua filters + metadata flags. Both are
    # engine-agnostic — they act on pandoc's front-end and are valid on
    # every chain — so they are always passed when set. Filters apply
    # in declaration order (pandoc applies ``--lua-filter`` flags in
    # order); a missing filter file is skipped with a breadcrumb while
    # the remaining filters still apply (non-blocking render contract).
    if render_lua_filters:
        for raw_filter in render_lua_filters:
            filter_path = _resolve_consumer_path(raw_filter)
            if not filter_path.is_file():
                _note_skip(
                    f"{DIM_MEMO_COMPILE}: render_lua_filters entry "
                    f"{raw_filter!r} not found at {filter_path}; "
                    f"filter skipped."
                )
                continue
            cmd.extend(["--lua-filter", str(filter_path)])
    if render_metadata:
        # ``{N}`` version-token expansion: the single recognized token
        # in metadata *values* is the version number parsed from the
        # ``<slug>.{N}`` version-dir name (load-bearing for the
        # canary's ``doc-version: "Draft v{N}"`` stamp). No other
        # tokens; other brace text passes through verbatim.
        version_match = re.match(r"^.+\.(\d+)$", version_dir.name)
        version_number = version_match.group(1) if version_match else None
        for meta_key, meta_value in render_metadata.items():
            value_str = str(meta_value)
            if version_number is not None:
                value_str = value_str.replace("{N}", version_number)
            cmd.extend(["-M", f"{meta_key}={value_str}"])
    # --fail-if-warnings rolls unresolved template variables into the
    # compile gate (per Epic #158 §"Out of v0 gate scope") so the
    # placeholder + image checks don't have to re-derive them.
    cmd.append("--fail-if-warnings")

    # Issue #347: per-doc LaTeX preamble extension. Engine-scoped to
    # xelatex — the shipped ``template.tex`` already wires
    # ``$for(header-includes)$``, and pandoc's ``--include-in-header``
    # is the canonical way to inject content into that slot from a
    # caller-owned tempfile. The HTML chain has a parallel
    # ``header-includes`` slot in ``template.html``, but
    # ``latex_header_includes`` is named-and-scoped to LaTeX content;
    # injecting raw LaTeX into the HTML chain would be a user-error
    # trap. The caller (``_gate_memo``) records the skip in
    # ``reasons`` when the engine resolves to non-xelatex.
    import tempfile as _tempfile  # local import: not used elsewhere

    header_tmp: Optional[str] = None
    if (
        latex_header_includes is not None
        and engine == MEMO_ENGINE_XELATEX
    ):
        try:
            with _tempfile.NamedTemporaryFile(
                mode="w",
                suffix=".tex",
                delete=False,
                encoding="utf-8",
            ) as f:
                f.write(latex_header_includes)
                header_tmp = f.name
            cmd.extend(["--include-in-header", header_tmp])
        except OSError:
            # Tempfile creation failure is rare but not catastrophic —
            # surface as a compile-side stderr-style note so the caller
            # records the failure but does not raise.
            header_tmp = None

    try:
        try:
            proc = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                check=False,
            )
        except (OSError, FileNotFoundError) as exc:
            return (COMPILE_FAILED, -1, engine, str(exc))

        status = COMPILE_OK if proc.returncode == 0 else COMPILE_FAILED
        return (status, proc.returncode, engine, proc.stderr or "")
    finally:
        # Clean up the include-in-header tempfile regardless of outcome.
        # Pandoc has already read it (or never opened it on subprocess
        # failure); leaving it around would clutter ``$TMPDIR`` over
        # repeated renders. ``unlink`` swallows the file-not-found case
        # (tempfile creation failed earlier).
        if header_tmp is not None:
            try:
                Path(header_tmp).unlink(missing_ok=True)
            except OSError:
                pass


def _parse_memo_overfull(stderr_text: str) -> list[dict]:
    """Return overfull-style warnings parsed from a memo renderer's stderr.

    Each hit: ``{kind, line, raw}``. ``kind`` is always ``"overflow"``;
    the memo gate does not distinguish hbox/vbox the way LaTeX does
    (weasyprint and wkhtmltopdf surface a single "doesn't fit" / "line
    too long" warning class). ``line`` is the stderr line number (1-based)
    so a reviewer can search the captured log.

    Empty list when no patterns match — the check graceful-degrades for
    renderers that emit no such warnings (the common case on a clean
    memo). See :data:`_MEMO_OVERFULL_PATTERNS` for the recognized set.
    """
    if not stderr_text:
        return []
    hits: list[dict] = []
    for lineno, line in enumerate(stderr_text.splitlines(), start=1):
        for regex in _MEMO_OVERFULL_RES:
            if regex.search(line):
                hits.append(
                    {
                        "kind": "overflow",
                        "line": lineno,
                        "raw": line.strip(),
                    }
                )
                break  # one finding per stderr line
    return hits


def _collect_memo_disabled_lines(
    source: str, rule: str = DIM_MEMO_PLACEHOLDERS
) -> set[int]:
    """Return source-line numbers (1-based) on which ``rule`` is suppressed.

    Mirrors ``memo_image_refs._collect_disabled_lines`` so the placeholder
    scan honors the same ``<!-- anvil-lint-disable: ... -->`` directive
    shape: same-line OR the line immediately above. Comma-separated rule
    lists are honored.
    """
    disabled: set[int] = set()
    lines = source.splitlines()
    for i, line in enumerate(lines):
        for m in _MEMO_LINT_DISABLE_RE.finditer(line):
            rules = {r.strip() for r in m.group("rules").split(",") if r.strip()}
            if rule not in rules:
                continue
            disabled.add(i + 1)
            tail = line[m.end():].strip()
            head = line[: m.start()].strip()
            if tail or head:
                # Inline directive — only same-line suppression.
                continue
            # Standalone directive line — suppress the next non-blank,
            # non-directive line.
            for j in range(i + 1, len(lines)):
                next_line = lines[j]
                if not next_line.strip():
                    continue
                if _MEMO_LINT_DISABLE_RE.search(next_line):
                    continue
                disabled.add(j + 1)
                break
    return disabled


def _scan_memo_placeholders(
    source: str,
    patterns: tuple[str, ...],
) -> tuple[list[dict], list[dict]]:
    """Scan a memo source for placeholder patterns.

    Returns ``(active_hits, suppressed_hits)``:

    - ``active_hits``: not suppressed by ``<!-- anvil-lint-disable:
      memo_placeholder_scan -->`` — fire as errors.
    - ``suppressed_hits``: matched a pattern but on a disabled line —
      recorded as info-severity findings (mirrors memo_image_refs).

    Each hit: ``{pattern, line, match}``. Suppression and pattern
    semantics match :func:`_collect_memo_disabled_lines` and the
    ``re.compile`` defaults.
    """
    if not patterns:
        return ([], [])
    compiled = [(p, re.compile(p)) for p in patterns]
    disabled = _collect_memo_disabled_lines(source)
    active: list[dict] = []
    suppressed: list[dict] = []
    for lineno, line in enumerate(source.splitlines(), start=1):
        # The lint-disable directive itself contains a placeholder-looking
        # comment; skip lines whose only content is a directive so the
        # scan does not flag its own escape hatch.
        stripped = line.strip()
        if stripped.startswith("<!--") and stripped.endswith("-->"):
            if _MEMO_LINT_DISABLE_RE.fullmatch(stripped):
                continue
        for pattern_str, regex in compiled:
            m = regex.search(line)
            if not m:
                continue
            hit = {
                "pattern": pattern_str,
                "line": lineno,
                "match": m.group(0),
            }
            if lineno in disabled:
                suppressed.append(hit)
            else:
                active.append(hit)
    return active, suppressed


def _coerce_words_per_page(value: object) -> Optional[int]:
    """Validate a caller-supplied ``words_per_page`` override.

    Returns the effective ``int`` to use, or ``None`` when the value is
    absent / malformed (in which case the caller falls back to
    :data:`MEMO_WORDS_PER_PAGE`). Accepts ``int`` and ``float``; rejects
    booleans (``isinstance(True, int)`` is the trap), strings,
    ``None``, and non-positive values.

    The graceful-degrade contract matches :func:`_resolve_target_length`
    for malformed ``target_length`` inputs — a bad override never
    raises; the gate continues with the documented default.
    """
    if value is None:
        return None
    # bool is a subclass of int; reject ``True`` / ``False`` explicitly
    # so a "truthy override" doesn't sneak through as 1 wpp.
    if isinstance(value, bool):
        return None
    if isinstance(value, (int, float)):
        if value <= 0:
            return None
        # Floats are tolerated (matches the curation's "positive number")
        # but downstream we operate in ints — round to nearest, with a
        # 1-floor so a 0.4 → 0 collapse can't slip past the >0 check.
        coerced = int(value)
        if coerced <= 0:
            return None
        return coerced
    return None


def _coerce_image_max_px(value: object) -> Optional[int]:
    """Validate a caller-supplied ``image_max_px`` override (issue #395).

    Returns the effective ``int`` to use, or ``None`` when the value is
    absent / malformed (in which case the caller falls back to
    :data:`MEMO_IMAGE_MAX_PX`). Same accept/reject table as
    :func:`_coerce_words_per_page`: ``int`` and ``float`` accepted;
    booleans, strings, ``None``, and non-positive values rejected. A bad
    override never raises; the gate continues with the documented
    default and the effective ceiling is recorded in the finding
    message.
    """
    if value is None:
        return None
    if isinstance(value, bool):
        return None
    if isinstance(value, (int, float)):
        if value <= 0:
            return None
        coerced = int(value)
        if coerced <= 0:
            return None
        return coerced
    return None

