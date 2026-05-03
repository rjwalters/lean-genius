import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/AngleTrisectionOQ02OQ03Ext.lean?raw'

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

export const angleTrisectionOQ02OQ03ExtProof: Proof = {
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

export const angleTrisectionOQ02OQ03ExtAnnotations: Annotation[] = annotationsJson as unknown as Annotation[]

export const angleTrisectionOQ02OQ03ExtData: ProofData = {
  proof: angleTrisectionOQ02OQ03ExtProof,
  annotations: angleTrisectionOQ02OQ03ExtAnnotations,
}

export default angleTrisectionOQ02OQ03ExtData
