export interface Proof {
  id: string
  title: string
  slug: string
  description: string
  source: string
  sections: ProofSection[]
  meta: ProofMeta
  overview?: ProofOverview
  conclusion?: ProofConclusion
}

export interface ProofOverview {
  historicalContext: string
  problemStatement: string
  proofStrategy: string
  keyInsights: string[]
}

export interface ProofConclusion {
  summary: string
  implications: string
  openQuestions?: string[]
  alternativeInterpretation?: AlternativeInterpretation
}

export interface AlternativeInterpretation {
  title: string
  summary: string
  perspective: string
  computationalView?: string
  historicalContext?: string
  leanFoundations?: string
}

/**
 * Badge types for categorizing proofs based on their relationship to Mathlib
 * See proofs/BADGE_TAXONOMY.md for full documentation
 */
export type ProofBadge =
  | 'original'           // 🏆 Novel formalization with minimal Mathlib delegation
  | 'mathlib'            // 📚 Uses Mathlib theorems (standard approach)
  | 'pedagogical'        // 🎓 Focused on teaching Lean techniques
  | 'from-axioms'        // ⚡ Proves from first principles, no/minimal imports
  | 'fallacy'            // ⚠️ Demonstrates a mathematical fallacy or invalid argument
  | 'wip'                // 🚧 Has sorries or incomplete sections

/**
 * Display information for proof badges
 */
export const BADGE_INFO: Record<ProofBadge, { emoji: string; label: string; color: string; description: string }> = {
  'original': {
    emoji: '🏆',
    label: 'Original Proof',
    color: '#F59E0B',
    description: 'Novel formalization with minimal Mathlib delegation'
  },
  'mathlib': {
    emoji: '📚',
    label: 'Mathlib',
    color: '#3B82F6',
    description: 'Uses Mathlib theorems for the main result'
  },
  'pedagogical': {
    emoji: '🎓',
    label: 'Learning Example',
    color: '#10B981',
    description: 'Focused on teaching Lean techniques'
  },
  'from-axioms': {
    emoji: '⚡',
    label: 'From Axioms',
    color: '#8B5CF6',
    description: 'Proves from first principles with no/minimal imports'
  },
  'fallacy': {
    emoji: '⚠️',
    label: 'Fallacy',
    color: '#EF4444',
    description: 'Demonstrates a mathematical fallacy or invalid argument'
  },
  'wip': {
    emoji: '🚧',
    label: 'Work in Progress',
    color: '#F97316',
    description: 'Has sorries or incomplete sections'
  }
}

/**
 * Display information for Wiedijk's 100 Famous Theorems badge
 */
export const WIEDIJK_BADGE_INFO = {
  color: '#f59e0b', // Amber (matches annotation color)
  textColor: '#f59e0b', // Same amber for text
  label: "Wiedijk's 100",
  description: "One of Freek Wiedijk's 100 Famous Theorems",
  url: 'https://www.cs.ru.nl/~freek/100/'
}

/**
 * Mapping of Wiedijk theorem numbers to their names
 * See: https://www.cs.ru.nl/~freek/100/
 */
export const WIEDIJK_THEOREMS: Record<number, string> = {
  1: 'Irrationality of √2',
  2: 'Fundamental Theorem of Algebra',
  4: 'Pythagorean Theorem',
  6: "Gödel's Incompleteness Theorem",
  11: 'Infinitude of Primes',
  15: 'Fundamental Theorem of Integral Calculus',
  16: 'Insolvability of Higher Degree Equations',
  22: 'Non-Denumerability of the Continuum',
  32: 'Four Color Problem',
  33: "Fermat's Last Theorem",
  36: 'Brouwer Fixed Point Theorem',
  47: 'Central Limit Theorem'
}

/**
 * A theorem or lemma imported from Mathlib
 */
export interface MathlibDependency {
  /** The theorem name (e.g., "Complex.exists_root") */
  theorem: string
  /** Brief description of what it provides */
  description: string
  /** The Mathlib module (e.g., "Mathlib.Analysis.Complex.Polynomial.Basic") */
  module?: string
}

export interface ProofMeta {
  author?: string
  authorHandle?: string
  sourceUrl?: string
  date?: string
  /** Date when proof was added to the site (MM/DD/YY format) */
  dateAdded?: string
  mathlib_version?: string
  status: 'verified' | 'pending' | 'disputed'
  tags: string[]
  /** Path to verified Lean source in proofs/ directory (e.g., "Proofs/Sqrt2Irrational.lean") */
  proofRepoPath?: string

  // Badge system fields
  /** The proof's category badge - see BADGE_TAXONOMY.md */
  badge?: ProofBadge
  /** Key theorems imported from Mathlib */
  mathlibDependencies?: MathlibDependency[]
  /** Number of sorry statements in the Lean file (0 = complete) */
  sorries?: number
  /** What this proof contributes beyond Mathlib */
  originalContributions?: string[]
  /** Wiedijk's 100 Famous Theorems number (1-100) if applicable */
  wiedijkNumber?: number
}

export interface ProofSection {
  id: string
  title: string
  startLine: number
  endLine: number
  summary: string
}

export interface Annotation {
  id: string
  proofId: string
  range: AnnotationRange
  type: AnnotationType
  title: string
  content: string
  mathContext?: string
  significance: AnnotationSignificance
  prerequisites?: string[]
  relatedConcepts?: string[]
}

export interface AnnotationRange {
  startLine: number
  endLine: number
  startCol?: number
  endCol?: number
}

export type AnnotationType =
  | 'theorem'
  | 'lemma'
  | 'definition'
  | 'tactic'
  | 'concept'
  | 'insight'
  | 'warning'

export type AnnotationSignificance =
  | 'critical'  // Core to the proof
  | 'key'       // Important step
  | 'supporting' // Helpful context

export interface ProofData {
  proof: Proof
  annotations: Annotation[]
  tacticStates?: TacticState[]
  /** Version metadata for proofs with version history */
  versionInfo?: ProofVersionInfo
}

/**
 * Version information for a proof with multiple revisions
 */
export interface ProofVersionInfo {
  /** Currently displayed version (e.g., "v3") */
  currentVersion: string
  /** History of all versions */
  versionHistory: VersionHistoryEntry[]
}

/**
 * Entry in the version history
 */
export interface VersionHistoryEntry {
  /** Version identifier (e.g., "v1", "v2") */
  version: string
  /** Human-readable name for this version */
  name: string
  /** Date of this version (ISO format) */
  date: string
  /** Status of this version */
  status: 'verified' | 'pending' | 'disputed' | 'conditional' | 'axiomatized' | 'revised'
  /** Path to version file (relative to proof data directory) */
  file: string
  /** Brief summary of changes in this version */
  summary?: string
  /** Full content of this version (loaded from file) */
  content?: VersionContent
}

/**
 * Content of a historical version snapshot
 */
export interface VersionContent {
  /** Description of this version */
  description: string
  /** Overview content */
  overview?: ProofOverview
  /** Conclusion content */
  conclusion?: ProofConclusion
  /** Objection/analysis details */
  objection?: {
    verdict: string
    summary: string
    coreIssue?: string
  }
}

// LeanInk-extracted tactic goal states
export interface TacticState {
  line: number
  tactic: string
  goalsBefore: GoalState[]
  goalsAfter: GoalState[]
}

export interface GoalState {
  name?: string
  hypotheses: Hypothesis[]
  conclusion: string
}

export interface Hypothesis {
  names: string[]
  type: string
}
