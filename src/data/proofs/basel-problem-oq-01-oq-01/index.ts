import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
const meta = metaJson as any
const leanSource = () => import('../../../../proofs/Proofs/BaselProblemOQ01OQ01.lean?raw')
export const proof: Proof = {
  id: meta.id, title: meta.title, slug: meta.slug, description: meta.description,
  meta: meta.meta, sections: meta.sections, source: '',
  overview: meta.overview, conclusion: meta.conclusion, crossReferences: meta.crossReferences,
}
export const annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const proofData: ProofData = { proof, annotations }
export async function getProofSource(): Promise<string> { return (await leanSource()).default }
export default proofData
