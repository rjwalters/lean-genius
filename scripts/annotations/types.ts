/**
 * Anchor-based annotation system types
 *
 * Annotations reference Lean code by stable anchors (declaration names, patterns)
 * rather than fragile line numbers. Line numbers are resolved at build time.
 */

/**
 * Types of Lean constructs that can be anchored to
 */
export type AnchorType =
  | 'declaration'    // theorem, lemma, def, abbrev, structure, axiom, instance
  | 'section-doc'    // /-! ... -/ module docstrings
  | 'doc-comment'    // /-- ... -/ attached to next item
  | 'block-comment'  // /- ... -/ standalone comments
  | 'namespace'      // namespace declarations
  | 'imports'        // import statement block
  | 'pattern';       // fallback: match by content pattern

/**
 * Kind of declaration for 'declaration' anchor type
 */
export type DeclarationKind =
  | 'theorem'
  | 'lemma'
  | 'def'
  | 'abbrev'
  | 'structure'
  | 'axiom'
  | 'instance'
  | 'class'
  | 'inductive';

/**
 * An anchor that identifies a location in a Lean file by semantic reference
 */
export interface AnnotationAnchor {
  /** Type of Lean construct to anchor to */
  type: AnchorType;

  /** For declarations: the name (e.g., "knights_tour_oblique_min") */
  name?: string;

  /** For declarations: the kind (e.g., "theorem", "def") */
  kind?: DeclarationKind;

  /** For pattern-based: string to match (supports regex) */
  pattern?: string;

  /** For section-doc/block-comment: text the comment must contain */
  contains?: string;

  /** Extend range to include N lines before the matched construct */
  extendBefore?: number;

  /** Extend range to include N lines after the matched construct */
  extendAfter?: number;

  /** For declarations: include the doc comment above (default: true) */
  includeDocComment?: boolean;
}

/**
 * Source annotation with anchor (what authors write)
 */
export interface SourceAnnotation {
  id: string;
  proofId: string;
  anchor: AnnotationAnchor;
  type: AnnotationType;
  title: string;
  content: string;
  mathContext?: string;
  significance: AnnotationSignificance;
  prerequisites?: string[];
  relatedConcepts?: string[];
}

/**
 * Resolved annotation with line numbers (what frontend uses)
 */
export interface ResolvedAnnotation {
  id: string;
  proofId: string;
  range: {
    startLine: number;
    endLine: number;
  };
  type: AnnotationType;
  title: string;
  content: string;
  mathContext?: string;
  significance: AnnotationSignificance;
  prerequisites?: string[];
  relatedConcepts?: string[];

  /** Original anchor for debugging/regeneration */
  _anchor?: AnnotationAnchor;
}

/**
 * Section definition with anchor (what authors write)
 */
export interface SourceSection {
  id: string;
  title: string;
  anchor: AnnotationAnchor;
  summary: string;
}

/**
 * Resolved section with line numbers (what frontend uses)
 */
export interface ResolvedSection {
  id: string;
  title: string;
  startLine: number;
  endLine: number;
  summary: string;

  /** Original anchor for debugging */
  _anchor?: AnnotationAnchor;
}

export type AnnotationType =
  | 'theorem'
  | 'lemma'
  | 'definition'
  | 'tactic'
  | 'concept'
  | 'insight'
  | 'warning';

export type AnnotationSignificance =
  | 'critical'
  | 'key'
  | 'supporting';

/**
 * A parsed Lean construct with its location
 */
export interface LeanConstruct {
  type: AnchorType;
  kind?: DeclarationKind;
  name?: string;
  startLine: number;
  endLine: number;
  docCommentStart?: number;  // Line where doc comment starts (if any)
  content: string;           // The actual text content
}

/**
 * Result of parsing a Lean file
 */
export interface ParsedLeanFile {
  path: string;
  constructs: LeanConstruct[];
  lines: string[];
}

/**
 * Resolution result for a single annotation
 */
export interface ResolutionResult {
  annotation: SourceAnnotation;
  resolved?: ResolvedAnnotation;
  error?: string;
}

/**
 * Full resolution report for a proof
 */
export interface ResolutionReport {
  proofId: string;
  sourcePath: string;
  totalAnnotations: number;
  resolved: number;
  failed: number;
  results: ResolutionResult[];
  sections?: {
    total: number;
    resolved: number;
    failed: number;
  };
}
