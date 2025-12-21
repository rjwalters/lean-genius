import { navierStokesData } from './navier-stokes'
import type { ProofData } from '@/types/proof'

export const proofs: Record<string, ProofData> = {
  'navier-stokes': navierStokesData,
}

export function getProof(slug: string): ProofData | undefined {
  return proofs[slug]
}

export function getAllProofs(): ProofData[] {
  return Object.values(proofs)
}
