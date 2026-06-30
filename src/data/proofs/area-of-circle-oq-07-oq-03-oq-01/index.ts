import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/AreaOfCircleOQ07OQ03OQ01.lean?raw'

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

export const areaOfCircleOq07Oq03Oq01Proof: Proof = {
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

export const areaOfCircleOq07Oq03Oq01Annotations: Annotation[] = annotationsJson as unknown as Annotation[]

export const areaOfCircleOq07Oq03Oq01Data: ProofData = {
  proof: areaOfCircleOq07Oq03Oq01Proof,
  annotations: areaOfCircleOq07Oq03Oq01Annotations,
}
