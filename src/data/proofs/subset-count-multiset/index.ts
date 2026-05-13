import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
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

const leanSource = () => import('../../../../proofs/Proofs/SubsetCountOQ02.lean?raw')

export const subsetCountMultisetProof: Proof = {
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

export const subsetCountMultisetAnnotations: Annotation[] = annotationsJson as unknown as Annotation[]

export const subsetCountMultisetData: ProofData = {
  proof: subsetCountMultisetProof,
  annotations: subsetCountMultisetAnnotations,
}

export async function getProofSource(): Promise<string> {
  const module = await leanSource()
  return module.default
}

export default subsetCountMultisetData
