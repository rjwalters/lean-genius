import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/LagrangeFourSquaresWaringG2.lean?raw'

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

export const lagrangeFourSquaresWaringG2Proof: Proof = {
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

export const lagrangeFourSquaresWaringG2Annotations: Annotation[] = annotationsJson as unknown as Annotation[]

export const lagrangeFourSquaresWaringG2Data: ProofData = {
  proof: lagrangeFourSquaresWaringG2Proof,
  annotations: lagrangeFourSquaresWaringG2Annotations,
}

export default lagrangeFourSquaresWaringG2Data
