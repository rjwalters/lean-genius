import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference, ProofReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/BuffonsNeedleOQ02OQ02OQ01.lean?raw'

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

export const buffonsNeedleOq02Oq02Oq01Proof: Proof = {
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
  references: meta.references,
}

export const buffonsNeedleOq02Oq02Oq01Annotations: Annotation[] = annotationsJson as unknown as Annotation[]

export const buffonsNeedleOq02Oq02Oq01Data: ProofData = {
  proof: buffonsNeedleOq02Oq02Oq01Proof,
  annotations: buffonsNeedleOq02Oq02Oq01Annotations,
}
