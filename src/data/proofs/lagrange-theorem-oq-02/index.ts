import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference, TacticState } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/LagrangeTheoremOQ02.lean?raw'

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

export const lagrangeTheoremOQ02Proof: Proof = {
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

export const lagrangeTheoremOQ02Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const lagrangeTheoremOQ02TacticStates: TacticState[] = []

export const lagrangeTheoremOQ02Data: ProofData = {
  proof: lagrangeTheoremOQ02Proof,
  annotations: lagrangeTheoremOQ02Annotations,
  tacticStates: lagrangeTheoremOQ02TacticStates,
}
