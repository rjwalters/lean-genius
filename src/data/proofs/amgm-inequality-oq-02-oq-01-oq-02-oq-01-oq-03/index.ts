import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference, ProofReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/AmgmInequalityOQ02OQ01OQ02OQ01OQ03.lean?raw'

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
  references?: ProofReference[]
}

export const amgmInequalityOQ02OQ01OQ02OQ01OQ03Proof: Proof = {
  id: meta.id,
  title: meta.title,
  slug: meta.slug,
  description: meta.description,
  meta: meta.meta,
  sections: meta.sections ?? [],
  source: sourceRaw,
  overview: meta.overview,
  conclusion: meta.conclusion,
  crossReferences: meta.crossReferences,
  references: meta.references,
}

export const amgmInequalityOQ02OQ01OQ02OQ01OQ03Annotations: Annotation[] = annotationsJson as unknown as Annotation[]

export const amgmInequalityOQ02OQ01OQ02OQ01OQ03Data: ProofData = {
  proof: amgmInequalityOQ02OQ01OQ02OQ01OQ03Proof,
  annotations: amgmInequalityOQ02OQ01OQ02OQ01OQ03Annotations,
}

export default amgmInequalityOQ02OQ01OQ02OQ01OQ03Data
