"""Result types for the render-gate (issue #1128 package split).

``GateFinding`` (one render-gate hit) and ``GateResult`` (the outcome of
one render-gate pass — JSON-serializable + ``Review``-emitter via
``to_review``). Split out of the former monolithic
``anvil/lib/render_gate.py`` along its existing section banners — see
``anvil/lib/render_gate/__init__.py`` for the full package rationale.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional

from anvil.lib.review_schema import (
    CriticalFlag,
    Finding,
    Kind,
    Review,
    Score,
)

from anvil.lib.render_gate.constants import (
    DIM_COMPILE,
    DIM_EMBEDDED_IMAGES,
    DIM_GLYPH_VERIFICATION,
    DIM_MEMO_COMPILE,
    DIM_MEMO_IMAGE_DIMENSIONS,
    DIM_MEMO_IMAGE_REFS,
    DIM_MEMO_OVERFULL,
    DIM_MEMO_PAGE_FIT,
    DIM_MEMO_PLACEHOLDERS,
    DIM_MEMO_RHETORIC,
    DIM_OVERFULL,
    DIM_PAGE_FIT,
    DIM_PLACEHOLDERS,
    GATE_NAME,
)




@dataclass
class GateFinding:
    """One render-gate hit. Mirrors the shape of ``marp_lint.Finding``."""

    gate: str       # one of DIM_PAGE_FIT / DIM_OVERFULL / DIM_COMPILE / DIM_PLACEHOLDERS
    severity: str   # "error" | "warning" | "info"
    message: str
    location: Optional[str] = None  # e.g. "paper.pdf:page=12" or "spec.tex:L142"

    def to_dict(self) -> dict:
        return {
            "gate": self.gate,
            "severity": self.severity,
            "message": self.message,
            "location": self.location,
        }


@dataclass
class GateResult:
    """Outcome of one render-gate pass. JSON-serializable + Review-emitter.

    The JSON shape matches the issue body's contract:
    ``{gate, pages, page_cap, overfull_boxes, compile, placeholders, pass,
    reasons}``. The typed ``Review`` emitted by ``to_review`` carries one
    ``CriticalFlag`` per failed gate dimension, which forces
    ``Verdict.BLOCK`` in the aggregator without any schema change.
    """

    pdf_path: str
    log_path: Optional[str]
    pages: Optional[int]
    page_cap: Optional[int]
    overfull_boxes: list[dict]
    overfull_threshold_pt: float
    compile_status: str
    compile_exit_code: Optional[int]
    placeholders: list[dict]
    findings: list[GateFinding] = field(default_factory=list)
    passed: bool = True
    reasons: list[str] = field(default_factory=list)
    # Internal: which gate dimensions failed. Drives to_review's CriticalFlag
    # emission and to_json's per-dimension status.
    failed_gates: set[str] = field(default_factory=set)
    # Render provenance (issue #391, memo kind only; None on the LaTeX
    # gate). ``engine_used`` is the engine that actually ran (may differ
    # from the requested one on PATH fallthrough); ``template_used`` is
    # the resolved consumer template path string, or a symbolic
    # "framework-default" / "theme:<name>" / "pandoc-default" marker
    # when no consumer template applied. Recorded so the
    # "re-rendered with the wrong template" regression class is
    # detectable on disk by diffing ``_progress.json`` across versions.
    engine_used: Optional[str] = None
    template_used: Optional[str] = None

    def to_json(self) -> dict:
        """Emit the JSON shape called out in the issue body.

        Keys: ``gate``, ``pages``, ``page_cap``, ``overfull_boxes``,
        ``compile``, ``placeholders``, ``pass``, ``reasons``. ``compile``
        is an object ``{status, exit_code}``.
        """
        return {
            "gate": GATE_NAME,
            "pdf_path": self.pdf_path,
            "log_path": self.log_path,
            "pages": self.pages,
            "page_cap": self.page_cap,
            "overfull_boxes": list(self.overfull_boxes),
            "overfull_threshold_pt": self.overfull_threshold_pt,
            "compile": {
                "status": self.compile_status,
                "exit_code": self.compile_exit_code,
            },
            "placeholders": list(self.placeholders),
            "findings": [f.to_dict() for f in self.findings],
            "pass": self.passed,
            "reasons": list(self.reasons),
            "engine_used": self.engine_used,
            "template_used": self.template_used,
        }

    def to_critical_flags(self) -> list[CriticalFlag]:
        """One ``CriticalFlag`` per failed gate dimension.

        Empty list when ``passed=True``. The flag ``type`` follows the
        ``render_gate_<dim>`` convention so downstream consumers can route on
        the specific failure (e.g., a compile failure is operationally
        distinct from a placeholder hit).
        """
        flags: list[CriticalFlag] = []
        if not self.failed_gates:
            return flags
        # Stable emission order: LaTeX dimensions first, memo dimensions
        # second. Within each block the order matches the documented gate
        # check order so the JSON shape is reproducible.
        ordered_dims = [
            DIM_PAGE_FIT,
            DIM_OVERFULL,
            DIM_COMPILE,
            DIM_PLACEHOLDERS,
            DIM_GLYPH_VERIFICATION,
            DIM_EMBEDDED_IMAGES,
            DIM_MEMO_COMPILE,
            DIM_MEMO_PAGE_FIT,
            DIM_MEMO_OVERFULL,
            DIM_MEMO_IMAGE_REFS,
            # memo_image_dimensions is advisory today (never joins
            # failed_gates) — listed here so a future severity promotion
            # emits flags in the documented check order without a code
            # change (issue #395).
            DIM_MEMO_IMAGE_DIMENSIONS,
            DIM_MEMO_PLACEHOLDERS,
            # memo_rhetoric_lint is advisory today (never joins
            # failed_gates) — listed here so a future severity promotion
            # emits flags in the documented check order without a code
            # change (issue #463).
            DIM_MEMO_RHETORIC,
        ]
        for dim in ordered_dims:
            if dim not in self.failed_gates:
                continue
            justification = "; ".join(
                r for r in self.reasons if r.startswith(f"{dim}:")
            ) or f"{dim} gate failed"
            flags.append(
                CriticalFlag(
                    type=f"render_gate_{dim}",
                    justification=justification,
                )
            )
        return flags

    def to_review(self, *, version_dir: str, critic_id: str) -> Review:
        """Build a typed ``Review`` (``kind=Kind.TOOL_EVIDENCE``) for the
        critics aggregator.

        The review carries:
        - a one-row scorecard with ``score=None`` (the gate owns no rubric
          dimension; it is a pre-flight pass/fail), so ``aggregate`` treats
          this critic as null-everywhere for scoring purposes.
        - one ``CriticalFlag`` per failed gate dimension (via
          ``to_critical_flags``), which forces ``Verdict.BLOCK`` in
          ``compute_verdict``.
        - one ``Finding`` per recorded ``GateFinding`` (with the gate name
          as the dimension and the message as both rationale + suggested
          fix).
        - ``tool_calls=[]`` on every finding to satisfy the
          ``Kind.TOOL_EVIDENCE`` schema requirement (``tool_calls`` must be
          a list, not ``None``, when ``kind=tool_evidence``).
        """
        # A single null-scored dim so ``scores`` is non-empty (the schema
        # requires it) but contributes nothing to the aggregated total.
        scores = [
            Score(
                dimension=GATE_NAME,
                score=None,
                max=1,
                justification="render-gate is pre-flight pass/fail; owns no rubric dim.",
            )
        ]
        findings: list[Finding] = []
        for gf in self.findings:
            findings.append(
                Finding(
                    severity="blocker" if gf.severity == "error" else "minor",
                    dimension=gf.gate,
                    evidence_span=gf.location,
                    rationale=gf.message,
                    suggested_fix=gf.message,
                    tool_calls=[],
                )
            )
        return Review(
            schema_version="1",
            kind=Kind.TOOL_EVIDENCE,
            version_dir=version_dir,
            critic_id=critic_id,
            scores=scores,
            findings=findings,
            critical_flags=self.to_critical_flags(),
        )

