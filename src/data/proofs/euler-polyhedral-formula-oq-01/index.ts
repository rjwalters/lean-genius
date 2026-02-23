import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, TacticState } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import tacticStatesJson from './tacticStates.json'
import sourceRaw from '../../../../proofs/Proofs/EulerPolyhedralOQ01.lean?raw'

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

export const eulerPolyhedralFormulaOQ01Proof: Proof = {
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

export const eulerPolyhedralFormulaOQ01Annotations: Annotation[] = annotationsJson as Annotation[]
export const eulerPolyhedralFormulaOQ01TacticStates: TacticState[] = tacticStatesJson as TacticState[]

export const eulerPolyhedralFormulaOQ01Data: ProofData = {
  proof: eulerPolyhedralFormulaOQ01Proof,
  annotations: eulerPolyhedralFormulaOQ01Annotations,
  tacticStates: eulerPolyhedralFormulaOQ01TacticStates,
}
