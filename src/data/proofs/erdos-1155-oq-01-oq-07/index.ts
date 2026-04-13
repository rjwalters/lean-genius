import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/Erdos1155OQ01OQ07.lean?raw'

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

export const erdos1155OQ01OQ07Proof: Proof = {
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

export const erdos1155OQ01OQ07Annotations: Annotation[] = annotationsJson as unknown as Annotation[]

export const erdos1155OQ01OQ07Data: ProofData = {
  proof: erdos1155OQ01OQ07Proof,
  annotations: erdos1155OQ01OQ07Annotations,
}

export default erdos1155OQ01OQ07Data
