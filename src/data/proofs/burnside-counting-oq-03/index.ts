import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/BurnsideCountingOQ03.lean?raw'

const meta = metaJson as unknown as {
  id: string
  title: string
  slug: string
  description: string
  meta: ProofMeta
  sections: ProofSection[]
  overview?: ProofOverview
  crossReferences?: CrossReference[]
}

export const burnsideCountingOQ03Proof: Proof = {
  id: meta.id,
  title: meta.title,
  slug: meta.slug,
  description: meta.description,
  meta: meta.meta,
  sections: meta.sections,
  source: sourceRaw,
  overview: meta.overview,
  crossReferences: meta.crossReferences,
}

export const burnsideCountingOQ03Annotations: Annotation[] = annotationsJson as unknown as Annotation[]

export const burnsideCountingOQ03Data: ProofData = {
  proof: burnsideCountingOQ03Proof,
  annotations: burnsideCountingOQ03Annotations,
}
