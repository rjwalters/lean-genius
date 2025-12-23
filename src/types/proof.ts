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
}

/**
 * Badge types for categorizing proofs based on their relationship to Mathlib
 * See proofs/BADGE_TAXONOMY.md for full documentation
 */
export type ProofBadge =
  | 'original'           // 🏆 Novel formalization with minimal Mathlib delegation
  | 'mathlib-exploration' // 📚 Uses Mathlib for main theorem, proves extensions
  | 'mathlib-extension'  // 🔧 Extends Mathlib with new results or frameworks
  | 'pedagogical'        // 🎓 Focused on teaching Lean techniques
  | 'from-axioms'        // ⚡ Proves from first principles, no/minimal imports
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
  'mathlib-exploration': {
    emoji: '📚',
    label: 'Mathlib Exploration',
    color: '#3B82F6',
    description: 'Uses Mathlib for main theorem, proves extensions/corollaries'
  },
  'mathlib-extension': {
    emoji: '🔧',
    label: 'Mathlib Extension',
    color: '#14B8A6',
    description: 'Extends Mathlib with new results or frameworks'
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
  'wip': {
    emoji: '🚧',
    label: 'Work in Progress',
    color: '#F97316',
    description: 'Has sorries or incomplete sections'
  }
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
