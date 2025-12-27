import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, TacticState } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import tacticStatesJson from './tacticStates.json'
import sourceRaw from '../../../../proofs/Proofs/Sqrt2.lean?raw'

const meta = metaJson as {
  id: string
  title: string
  slug: string
  description: string
  meta: ProofMeta
  sections: ProofSection[]
  overview?: ProofOverview
  conclusion?: ProofConclusion
}

export const sqrt2ExamplesProof: Proof = {
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

export const sqrt2ExamplesAnnotations: Annotation[] = annotationsJson as Annotation[]
export const sqrt2ExamplesTacticStates: TacticState[] = tacticStatesJson as TacticState[]

export const sqrt2ExamplesData: ProofData = {
  proof: sqrt2ExamplesProof,
  annotations: sqrt2ExamplesAnnotations,
  tacticStates: sqrt2ExamplesTacticStates,
}
