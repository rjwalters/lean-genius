import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference, TacticState } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import tacticStatesJson from './tacticStates.json'

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

export const erdos490Oq01Proof: Proof = {
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

export const erdos490Oq01Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const erdos490Oq01TacticStates: TacticState[] = tacticStatesJson as TacticState[]

export const erdos490Oq01Data: ProofData = {
  proof: erdos490Oq01Proof,
  annotations: erdos490Oq01Annotations,
  tacticStates: erdos490Oq01TacticStates,
}

export default erdos490Oq01Data
