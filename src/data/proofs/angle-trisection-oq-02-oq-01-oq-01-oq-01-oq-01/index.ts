import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/AngleTrisectionOQ02OQ01OQ01OQ01OQ01.lean?raw'

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

export const angleTrisectionOQ02OQ01OQ01OQ01OQ01Proof: Proof = {
  id: meta.id,
  title: meta.title,
  slug: meta.slug,
  description: meta.description,
  meta: meta.meta,
  sections: meta.sections ?? [],
  overview: meta.overview,
  conclusion: meta.conclusion,
  crossReferences: meta.crossReferences,
  source: sourceRaw,
}

export const angleTrisectionOQ02OQ01OQ01OQ01OQ01Annotations: Annotation[] = annotationsJson as unknown as Annotation[]

export const angleTrisectionOQ02OQ01OQ01OQ01OQ01Data: ProofData = {
  proof: angleTrisectionOQ02OQ01OQ01OQ01OQ01Proof,
  annotations: angleTrisectionOQ02OQ01OQ01OQ01OQ01Annotations,
}

export default angleTrisectionOQ02OQ01OQ01OQ01OQ01Data
