import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference, ProofReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/AbelRuffiniOQ04OQ01OQ02.lean?raw'

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

export const abelRuffiniOq04Oq01Oq02Proof: Proof = {
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

export const abelRuffiniOq04Oq01Oq02Annotations: Annotation[] = annotationsJson as unknown as Annotation[]

export const abelRuffiniOq04Oq01Oq02Data: ProofData = {
  proof: abelRuffiniOq04Oq01Oq02Proof,
  annotations: abelRuffiniOq04Oq01Oq02Annotations,
}
