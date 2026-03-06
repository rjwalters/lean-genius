import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/LebesgueMeasureOQ01.lean?raw'

const meta = metaJson as unknown as {
  id: string
  title: string
  slug: string
  description: string
  meta: ProofMeta
  sections: ProofSection[]
  overview?: ProofOverview
  conclusion?: ProofConclusion
}

export const lebesgueMeasureOQ01Proof: Proof = {
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

export const lebesgueMeasureOQ01Annotations: Annotation[] = annotationsJson as unknown as Annotation[]

export const lebesgueMeasureOQ01Data: ProofData = {
  proof: lebesgueMeasureOQ01Proof,
  annotations: lebesgueMeasureOQ01Annotations,
}

export default lebesgueMeasureOQ01Data
