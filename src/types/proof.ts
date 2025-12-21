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

export interface ProofMeta {
  author?: string
  authorHandle?: string
  sourceUrl?: string
  date?: string
  mathlib_version?: string
  status: 'verified' | 'pending' | 'disputed'
  tags: string[]
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
}
