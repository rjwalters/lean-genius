import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference, TacticState } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'

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

export const lagrangeTheoremOQ02OQ02Proof: Proof = {
  id: meta.id,
  title: meta.title,
  slug: meta.slug,
  description: meta.description,
  meta: meta.meta,
  sections: meta.sections,
  source: '',
  overview: meta.overview,
  conclusion: meta.conclusion,
  crossReferences: meta.crossReferences,
}

export const lagrangeTheoremOQ02OQ02Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const lagrangeTheoremOQ02OQ02TacticStates: TacticState[] = []

export const lagrangeTheoremOQ02OQ02Data: ProofData = {
  proof: lagrangeTheoremOQ02OQ02Proof,
  annotations: lagrangeTheoremOQ02OQ02Annotations,
  tacticStates: lagrangeTheoremOQ02OQ02TacticStates,
}
