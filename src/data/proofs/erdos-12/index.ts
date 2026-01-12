import type { ProofData } from '@/types/proof'
import metaData from './meta.json'
import annotationsData from './annotations.json'

// Import the Lean source file
const leanSource = () => import('../../../../proofs/Proofs/Erdos12Problem.lean?raw')

export const proofData: ProofData = {
  proof: {
    ...metaData,
    source: '', // Loaded dynamically
  },
  annotations: annotationsData,
}

export async function getProofSource(): Promise<string> {
  const module = await leanSource()
  return module.default
}

export default proofData
