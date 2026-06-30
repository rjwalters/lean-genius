import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/DerangementsConvergenceOQ05OQ01.lean?raw'

const meta = metaJson as unknown as {
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

export const derangementsConvergenceOQ05OQ01Proof: Proof = {
  id: meta.id,
  title: meta.title,
  slug: meta.slug,
  description: meta.description,
  meta: meta.meta,
  sections: meta.sections,
  source: sourceRaw,
  overview: meta.overview,
  conclusion: meta.conclusion,
  crossReferences: meta.crossReferences,
}

export const derangementsConvergenceOQ05OQ01Annotations: Annotation[] = annotationsJson as unknown as Annotation[]

export const derangementsConvergenceOQ05OQ01Data: ProofData = {
  proof: derangementsConvergenceOQ05OQ01Proof,
  annotations: derangementsConvergenceOQ05OQ01Annotations,
}
