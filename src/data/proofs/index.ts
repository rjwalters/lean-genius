import { navierStokesData } from './navier-stokes'
import { sqrt2Data } from './sqrt2-irrational'
import { infinitudePrimesData } from './infinitude-primes'
import { russell1Plus1Data } from './russell-1-plus-1'
import { cantorDiagonalizationData } from './cantor-diagonalization'
import { fundamentalTheoremCalculusData } from './fundamental-theorem-calculus'
import { godelIncompletenessData } from './godel-incompleteness'
import type { ProofData } from '@/types/proof'

export const proofs: Record<string, ProofData> = {
  'navier-stokes': navierStokesData,
  'sqrt2-irrational': sqrt2Data,
  'infinitude-primes': infinitudePrimesData,
  'russell-1-plus-1': russell1Plus1Data,
  'cantor-diagonalization': cantorDiagonalizationData,
  'fundamental-theorem-calculus': fundamentalTheoremCalculusData,
  'godel-incompleteness': godelIncompletenessData,
}

export function getProof(slug: string): ProofData | undefined {
  return proofs[slug]
}

export function getAllProofs(): ProofData[] {
  return Object.values(proofs)
}
