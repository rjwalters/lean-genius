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

export const erdos1149Proof: Proof = {
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

export const erdos1149Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const erdos1149TacticStates: TacticState[] = []

export const erdos1149Data: ProofData = {
  proof: erdos1149Proof,
  annotations: erdos1149Annotations,
  tacticStates: erdos1149TacticStates,
}
