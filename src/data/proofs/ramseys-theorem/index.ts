import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference, TacticState } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import tacticStatesJson from './tacticStates.json'

const meta = metaJson as {
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

export const ramseysTheoremProof: Proof = {
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

export const ramseysTheoremAnnotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const ramseysTheoremTacticStates: TacticState[] = tacticStatesJson as TacticState[]

export const ramseysTheoremData: ProofData = {
  proof: ramseysTheoremProof,
  annotations: ramseysTheoremAnnotations,
  tacticStates: ramseysTheoremTacticStates,
}
