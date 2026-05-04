import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference, TacticState } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import tacticStatesJson from './tacticStates.json'
import sourceRaw from '../../../../proofs/Proofs/Erdos100OQ01WIP01.lean?raw'

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

export const erdos100OQ01WIP01Proof: Proof = {
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

export const erdos100OQ01WIP01Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const erdos100OQ01WIP01TacticStates: TacticState[] = tacticStatesJson as TacticState[]

export const erdos100OQ01WIP01Data: ProofData = {
  proof: erdos100OQ01WIP01Proof,
  annotations: erdos100OQ01WIP01Annotations,
  tacticStates: erdos100OQ01WIP01TacticStates,
}
