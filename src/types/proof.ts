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
  | 'ai-solved'          // 🤖 Open problem solved by AI
  | 'axiom'              // 📜 States key results as axioms (axiomatized formalization)

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
  },
  'ai-solved': {
    emoji: '🤖',
    label: 'AI-Solved',
    color: '#06B6D4',
    description: 'Open problem solved by AI'
  },
  'axiom': {
    emoji: '📜',
    label: 'Axiomatized',
    color: '#A855F7',
    description: 'States key results as axioms for formalization'
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
  3: 'Denumerability of the Rationals',
  4: 'Pythagorean Theorem',
  6: "Gödel's Incompleteness Theorem",
  11: 'Infinitude of Primes',
  15: 'Fundamental Theorem of Integral Calculus',
  16: 'Insolvability of Higher Degree Equations',
  22: 'Non-Denumerability of the Continuum',
  32: 'Four Color Problem',
  33: "Fermat's Last Theorem",
  36: 'Brouwer Fixed Point Theorem',
  47: 'Central Limit Theorem',
  51: "Wilson's Theorem",
  59: 'Laws of Large Numbers',
  61: "Ceva's Theorem",
  63: "Cantor's Theorem",
  66: 'Sum of a Geometric Series',
  74: "The Principle of Mathematical Induction",
  83: "Friendship Theorem",
  87: "Desargues's Theorem"
}

/**
 * Display information for Hilbert's 23 Problems badge
 */
export const HILBERT_BADGE_INFO = {
  color: '#8B5CF6', // Purple
  textColor: '#8B5CF6',
  label: "Hilbert's Problems",
  description: "One of Hilbert's 23 Problems presented in 1900",
  url: 'https://en.wikipedia.org/wiki/Hilbert%27s_problems'
}

/**
 * Mapping of Hilbert problem numbers to their names
 * See: https://en.wikipedia.org/wiki/Hilbert's_problems
 */
export const HILBERT_PROBLEMS: Record<number, string> = {
  1: 'Continuum Hypothesis',
  2: 'Consistency of Arithmetic',
  3: 'Equality of Volumes of Tetrahedra',
  4: 'Straight Line as Shortest Distance',
  5: 'Lie Groups without Differentiability',
  6: 'Axiomatization of Physics',
  7: 'Transcendence of Certain Numbers (Gelfond-Schneider)',
  8: 'Riemann Hypothesis',
  9: 'Reciprocity Laws in Number Fields',
  10: 'Solvability of Diophantine Equations',
  11: 'Quadratic Forms over Number Fields',
  12: 'Kronecker-Weber Theorem Extension',
  13: 'Solution of 7th Degree Equations',
  14: 'Finiteness of Complete Systems of Functions',
  15: 'Schubert Calculus',
  16: 'Topology of Algebraic Curves and Surfaces',
  17: 'Expression of Definite Forms by Squares',
  18: 'Non-periodic Tilings and Sphere Packing',
  19: 'Analyticity of Variational Problems',
  20: 'General Boundary Value Problems',
  21: 'Existence of Differential Equations with Monodromy',
  22: 'Uniformization by Automorphic Functions',
  23: 'Development of Calculus of Variations'
}

/**
 * Display information for Millennium Prize Problems badge
 */
export const MILLENNIUM_BADGE_INFO = {
  color: '#EC4899', // Pink
  textColor: '#EC4899',
  label: 'Millennium Prize',
  description: 'One of the Clay Mathematics Institute Millennium Prize Problems',
  url: 'https://www.claymath.org/millennium-problems'
}

/**
 * The seven Millennium Prize Problems
 * See: https://www.claymath.org/millennium-problems
 */
export type MillenniumProblem =
  | 'birch-swinnerton-dyer'
  | 'hodge'
  | 'navier-stokes'
  | 'p-vs-np'
  | 'poincare'  // Solved by Perelman
  | 'riemann'
  | 'yang-mills'

export const MILLENNIUM_PROBLEMS: Record<MillenniumProblem, string> = {
  'birch-swinnerton-dyer': 'Birch and Swinnerton-Dyer Conjecture',
  'hodge': 'Hodge Conjecture',
  'navier-stokes': 'Navier-Stokes Existence and Smoothness',
  'p-vs-np': 'P vs NP Problem',
  'poincare': 'Poincaré Conjecture (Solved)',
  'riemann': 'Riemann Hypothesis',
  'yang-mills': 'Yang-Mills Existence and Mass Gap'
}

/**
 * Display information for Erdős Problems badge
 */
export const ERDOS_BADGE_INFO = {
  color: '#22C55E', // Green - distinct from other collections
  textColor: '#22C55E',
  label: 'Erdős Problems',
  description: 'A problem from Paul Erdős\'s collection at erdosproblems.com',
  url: 'https://www.erdosproblems.com/'
}

/**
 * Status of an Erdős problem
 */
export type ErdosProblemStatus = 'open' | 'solved' | 'partially-solved' | 'disproved'

/**
 * Mapping of some notable Erdős problem numbers to their names
 * See: https://www.erdosproblems.com/
 */
export const ERDOS_PROBLEMS: Record<number, string> = {
  1: 'Covering Congruences',
  28: 'Sum-Free Sets',
  99: 'Squares in Arithmetic Progression',
  124: 'Prime Gaps Conjecture',
  178: 'Distinct Sums from Sets',
  206: 'Chromatic Number of the Plane',
  365: 'Erdős-Straus Conjecture',
  396: 'Cameron-Erdős Conjecture',
  434: 'Erdős-Ko-Rado Problem',
  461: 'Multiplication Table Problem',
  702: 'Erdős-Turán Conjecture on Additive Bases'
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
  /** Hilbert's 23 Problems number (1-23) if applicable */
  hilbertNumber?: number
  /** Millennium Prize Problem identifier if applicable */
  millenniumProblem?: MillenniumProblem

  // Erdős Problems fields
  /** Erdős problem number from erdosproblems.com */
  erdosNumber?: number
  /** Direct URL to the problem on erdosproblems.com */
  erdosUrl?: string
  /** Who solved the problem (person or AI system) */
  erdosSolvedBy?: string
  /** When the problem was solved (date string) */
  erdosSolvedDate?: string
  /** Prize money if applicable */
  erdosPrizeValue?: string
  /** Current status of the Erdős problem */
  erdosProblemStatus?: ErdosProblemStatus
  /** URL to forum discussion thread on erdosproblems.com */
  erdosForumUrl?: string
  /** URL to announcement post about the solution */
  erdosAnnouncementUrl?: string
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
 * Lightweight proof metadata for gallery listing.
 * Contains only the fields needed by HomePage for display and filtering.
 */
export interface ProofListing {
  id: string
  title: string
  slug: string
  description: string
  status: 'verified' | 'pending' | 'disputed'
  badge?: ProofBadge
  tags: string[]
  dateAdded?: string
  wiedijkNumber?: number
  hilbertNumber?: number
  millenniumProblem?: MillenniumProblem
  erdosNumber?: number
  mathlibCount?: number
  sorries?: number
  annotationCount: number
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
