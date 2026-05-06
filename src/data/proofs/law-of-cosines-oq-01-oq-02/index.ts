import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/LawOfCosinesOQ01OQ02.lean?raw'

export const meta: ProofMeta = metaJson as ProofMeta
export const annotations: Annotation[] = annotationsJson as Annotation[]
export const source: string = sourceRaw

export const proof: ProofData = {
  meta,
  annotations,
  source
}

export default proof
