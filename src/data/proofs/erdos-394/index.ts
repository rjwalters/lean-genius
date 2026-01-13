import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'

// Type assertion for JSON import
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

// Import the Lean source file
const leanSource = () => import('../../../../proofs/Proofs/Erdos394Problem.lean?raw')

export const proof: Proof = {
  id: meta.id,
  title: meta.title,
  slug: meta.slug,
  description: meta.description,
  meta: meta.meta,
  sections: meta.sections,
  source: '', // Loaded dynamically
  overview: meta.overview,
  conclusion: meta.conclusion,
}

export const annotations: Annotation[] = annotationsJson as Annotation[]

export const proofData: ProofData = {
  proof,
  annotations,
}

export async function getProofSource(): Promise<string> {
  const module = await leanSource()
  return module.default
}

export default proofData
