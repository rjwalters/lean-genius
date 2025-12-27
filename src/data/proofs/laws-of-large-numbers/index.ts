import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, TacticState } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import tacticStatesJson from './tacticStates.json'
import sourceRaw from '../../../../proofs/Proofs/LawsOfLargeNumbers.lean?raw'

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

export const lawsOfLargeNumbersProof: Proof = {
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

export const lawsOfLargeNumbersAnnotations: Annotation[] = annotationsJson as Annotation[]
export const lawsOfLargeNumbersTacticStates: TacticState[] = tacticStatesJson as TacticState[]

export const lawsOfLargeNumbersData: ProofData = {
  proof: lawsOfLargeNumbersProof,
  annotations: lawsOfLargeNumbersAnnotations,
  tacticStates: lawsOfLargeNumbersTacticStates,
}
