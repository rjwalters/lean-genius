import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/AngleTrisectionOQ02OQ01OQ02Incomplete01.lean?raw'

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

export const angleTrisectionOq02Oq01Oq02Incomplete01Proof: Proof = {
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

export const angleTrisectionOq02Oq01Oq02Incomplete01Annotations: Annotation[] = annotationsJson as unknown as Annotation[]

export const angleTrisectionOq02Oq01Oq02Incomplete01Data: ProofData = {
  proof: angleTrisectionOq02Oq01Oq02Incomplete01Proof,
  annotations: angleTrisectionOq02Oq01Oq02Incomplete01Annotations,
}

export default angleTrisectionOq02Oq01Oq02Incomplete01Data
