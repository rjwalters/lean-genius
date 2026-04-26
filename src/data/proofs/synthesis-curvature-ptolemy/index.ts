import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'

// Type assertion for JSON import
const meta = metaJson as {
  id: string
  title: string
  slug: string
  description: string
  meta: ProofMeta
  sections: ProofSection[]
  overview?: ProofOverview
  conclusion?: ProofConclusion
  crossReferences?: CrossReference[]
}

// Import the Lean source file
const leanSource = () => import('../../../../proofs/Proofs/SynthesisCurvaturePtolemy.lean?raw')

const annotationsData = annotationsJson as { annotations: Annotation[] }

export const proof: ProofData = {
  id: meta.id,
  title: meta.title,
  slug: meta.slug,
  description: meta.description,
  meta: meta.meta,
  sections: meta.sections,
  overview: meta.overview,
  conclusion: meta.conclusion,
  crossReferences: meta.crossReferences,
  annotations: annotationsData.annotations,
  leanSource,
}

export default proof
