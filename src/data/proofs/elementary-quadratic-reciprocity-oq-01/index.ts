import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/ElementaryQuadraticReciprocityOQ01.lean?raw'

const meta = metaJson as {
  id: string
  title: string
  slug: string
  description: string
  meta: ProofMeta
  sections: ProofSection[]
  overview?: ProofOverview
  conclusion?: ProofConclusion
}

export const elementaryQuadraticReciprocityOQ01Proof: Proof = {
  id: meta.id,
  title: meta.title,
  slug: meta.slug,
  description: meta.description,
  meta: meta.meta,
  sections: meta.sections,
  source: sourceRaw,
  overview: meta.overview,
  conclusion: meta.conclusion,
}

export const elementaryQuadraticReciprocityOQ01Annotations: Annotation[] = annotationsJson as unknown as Annotation[]

export const elementaryQuadraticReciprocityOQ01Data: ProofData = {
  proof: elementaryQuadraticReciprocityOQ01Proof,
  annotations: elementaryQuadraticReciprocityOQ01Annotations,
}
