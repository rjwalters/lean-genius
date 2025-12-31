/**
 * Research system types for the OODA-based mathematical research workflow.
 * See /research/STATE_MACHINE.md for full phase definitions.
 */

/**
 * OODA phases for the research workflow
 */
export type ResearchPhase =
  | 'NEW'          // Problem identified, not yet started
  | 'OBSERVE'      // Understanding problem context
  | 'ORIENT'       // Exploring literature and approaches
  | 'DECIDE'       // Selecting approach to try
  | 'ACT'          // Implementing proof attempt
  | 'VERIFY'       // Testing and validating proof
  | 'LEARN'        // Documenting insights from attempt
  | 'BREAKTHROUGH' // Proof succeeded
  | 'PIVOT'        // Changing direction after failure

/**
 * Value tier for problem significance (from VALUE_ASSESSMENT.md)
 */
export type ValueTier = 'S' | 'A' | 'B' | 'C' | 'D'

/**
 * Problem status in the research registry
 */
export type ResearchStatus = 'active' | 'graduated' | 'abandoned' | 'blocked'

/**
 * Research path type - fast (quick wins) vs full (deep research)
 */
export type ResearchPath = 'fast' | 'full'

/**
 * Display information for research phases
 */
export interface PhaseInfo {
  phase: ResearchPhase
  label: string
  description: string
  color: string
  order: number
}

export const PHASE_INFO: Record<ResearchPhase, PhaseInfo> = {
  NEW: {
    phase: 'NEW',
    label: 'New',
    description: 'Problem identified',
    color: '#6B7280',
    order: 0
  },
  OBSERVE: {
    phase: 'OBSERVE',
    label: 'Observe',
    description: 'Understanding problem',
    color: '#3B82F6',
    order: 1
  },
  ORIENT: {
    phase: 'ORIENT',
    label: 'Orient',
    description: 'Exploring literature',
    color: '#8B5CF6',
    order: 2
  },
  DECIDE: {
    phase: 'DECIDE',
    label: 'Decide',
    description: 'Selecting approach',
    color: '#EC4899',
    order: 3
  },
  ACT: {
    phase: 'ACT',
    label: 'Act',
    description: 'Implementing proof',
    color: '#F59E0B',
    order: 4
  },
  VERIFY: {
    phase: 'VERIFY',
    label: 'Verify',
    description: 'Testing proof',
    color: '#10B981',
    order: 5
  },
  LEARN: {
    phase: 'LEARN',
    label: 'Learn',
    description: 'Documenting insights',
    color: '#6366F1',
    order: 6
  },
  BREAKTHROUGH: {
    phase: 'BREAKTHROUGH',
    label: 'Success',
    description: 'Proof completed',
    color: '#22C55E',
    order: 7
  },
  PIVOT: {
    phase: 'PIVOT',
    label: 'Pivot',
    description: 'Changing direction',
    color: '#EF4444',
    order: 8
  }
}

/**
 * Display information for value tiers
 */
export interface TierInfo {
  tier: ValueTier
  label: string
  color: string
  description: string
}

export const TIER_INFO: Record<ValueTier, TierInfo> = {
  S: {
    tier: 'S',
    label: 'Millennium',
    color: '#EC4899',
    description: 'Millennium Prize level problem'
  },
  A: {
    tier: 'A',
    label: 'Famous',
    color: '#F59E0B',
    description: 'Famous open conjecture'
  },
  B: {
    tier: 'B',
    label: 'Research',
    color: '#3B82F6',
    description: 'Research-level open problem'
  },
  C: {
    tier: 'C',
    label: 'Formalization',
    color: '#10B981',
    description: 'Known result, needs formalization'
  },
  D: {
    tier: 'D',
    label: 'Exercise',
    color: '#6B7280',
    description: 'Textbook-level, low novelty'
  }
}

/**
 * Lightweight research listing for gallery page.
 * Mirrors ProofListing pattern for consistency.
 */
export interface ResearchListing {
  slug: string
  title: string
  description: string
  phase: ResearchPhase
  status: ResearchStatus
  tier: ValueTier
  path: ResearchPath
  tags: string[]
  started: string
  lastUpdate?: string
  completed?: string
  attemptCount: number
  approachCount: number
  linkedProof?: string
  significance?: number
  tractability?: number
}

/**
 * Problem statement with formal and plain language versions
 */
export interface ProblemStatement {
  formal: string
  plain: string
  whyMatters: string[]
}

/**
 * Known results for a problem
 */
export interface KnownResults {
  proven: string[]
  open: string[]
  goal: string
}

/**
 * Current state of research on a problem
 */
export interface ResearchState {
  phase: ResearchPhase
  since: string
  iteration: number
  focus: string
  activeApproach?: string
  blockers: string[]
  nextAction: string
  attemptCounts: {
    total: number
    currentApproach: number
    approachesTried: number
  }
}

/**
 * Item in the knowledge base
 */
export interface KnowledgeItem {
  name: string
  description: string
  proven: boolean
}

/**
 * Accumulated knowledge from research
 */
export interface ResearchKnowledge {
  progressSummary: string
  builtItems: KnowledgeItem[]
  insights: string[]
  mathlibGaps: string[]
  nextSteps: string[]
}

/**
 * A single proof attempt
 */
export interface ResearchAttempt {
  file: string
  timestamp?: string
  succeeded: boolean
  notes?: string
}

/**
 * Post-mortem analysis for failed approaches
 */
export interface PostMortem {
  whatWorked: string[]
  whatFailed: string[]
  lessonsLearned: string[]
}

/**
 * Success recap for completed proofs
 */
export interface SuccessRecap {
  keyTheorem: string
  techniquesUsed: string[]
  linesOfProof?: number
  timeToSuccess?: string
}

/**
 * An approach to solving the problem
 */
export interface ResearchApproach {
  id: string
  name: string
  status: 'active' | 'completed' | 'abandoned'
  hypothesis: string
  strategy: string
  risks: string[]
  attempts: ResearchAttempt[]
  postMortem?: PostMortem
  successRecap?: SuccessRecap
}

/**
 * References for a problem
 */
export interface ResearchReferences {
  papers: string[]
  urls: string[]
  mathlib: string[]
}

/**
 * Full research problem data for detail page
 */
export interface ResearchProblem {
  slug: string
  title: string
  phase: ResearchPhase
  status: ResearchStatus
  tier: ValueTier
  path: ResearchPath

  problemStatement: ProblemStatement
  knownResults: KnownResults
  currentState: ResearchState
  knowledge: ResearchKnowledge
  approaches: ResearchApproach[]

  tags: string[]
  relatedProofs: string[]
  references: ResearchReferences

  started: string
  lastUpdate?: string
  completed?: string
  linkedProof?: string

  significance?: number
  tractability?: number
}

/**
 * Registry entry from registry.json
 */
export interface RegistryEntry {
  slug: string
  phase: ResearchPhase
  path: ResearchPath
  started: string
  status: ResearchStatus
  lastUpdate?: string
  completed?: string
  template?: string
  template_value?: string
  derived_from?: string
}

/**
 * Full registry structure
 */
export interface ResearchRegistry {
  version: string
  problems: RegistryEntry[]
  config: {
    maxActiveProblemsPerAgent: number
    oodaTimeoutMinutes: number
    attemptsBeforePivot: number
  }
}
