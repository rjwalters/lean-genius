import { navierStokesData } from './navier-stokes'
import { sqrt2Data } from './sqrt2-irrational'
import { infinitudePrimesData } from './infinitude-primes'
import { knightsTourObliqueData } from './knights-tour-oblique'
import { russell1Plus1Data } from './russell-1-plus-1'
import { cantorDiagonalizationData } from './cantor-diagonalization'
import { fundamentalTheoremCalculusData } from './fundamental-theorem-calculus'
import { fundamentalTheoremAlgebraData } from './fundamental-theorem-algebra'
import { godelIncompletenessData } from './godel-incompleteness'
import { pythagoreanTheoremData } from './pythagorean-theorem'
import { haltingProblemData } from './halting-problem'
import { fourColorTheoremData } from './four-color-theorem'
import { eulerIdentityData } from './euler-identity'
import { brouwerFixedPointData } from './brouwer-fixed-point'
import { ramanujanSumFallacyData } from './ramanujan-sum-fallacy'
import { abelRuffiniData } from './abel-ruffini'
import { borsukUlamData } from './borsuk-ulam'
import { centralLimitTheoremData } from './central-limit-theorem'
import { fermatsLastTheoremData } from './fermats-last-theorem'
import { randomizedMaxCutData } from './randomized-maxcut'
import { threePlaceIdentityData } from './three-place-identity'
import { lagrangeFourSquaresData } from './lagrange-four-squares'
import { fermatTwoSquaresData } from './fermat-two-squares'
import { harmonicDivergenceData } from './harmonic-divergence'
import { denumerabilityRationalsData } from './denumerability-rationals'
import { hurwitzTheoremData } from './hurwitz-theorem'
import { schroederBernsteinData } from './schroeder-bernstein'
import { cantorsTheoremData } from './cantors-theorem'
import { wilsonsTheoremData } from './wilsons-theorem'
import { intermediateValueTheoremData } from './intermediate-value-theorem'
import { arithmeticSeriesData } from './arithmetic-series'
import type { ProofData } from '@/types/proof'

export const proofs: Record<string, ProofData> = {
  'navier-stokes': navierStokesData,
  'sqrt2-irrational': sqrt2Data,
  'infinitude-primes': infinitudePrimesData,
  'knights-tour-oblique': knightsTourObliqueData,
  'russell-1-plus-1': russell1Plus1Data,
  'cantor-diagonalization': cantorDiagonalizationData,
  'fundamental-theorem-calculus': fundamentalTheoremCalculusData,
  'fundamental-theorem-algebra': fundamentalTheoremAlgebraData,
  'godel-incompleteness': godelIncompletenessData,
  'pythagorean-theorem': pythagoreanTheoremData,
  'halting-problem': haltingProblemData,
  'four-color-theorem': fourColorTheoremData,
  'euler-identity': eulerIdentityData,
  'brouwer-fixed-point': brouwerFixedPointData,
  'ramanujan-sum-fallacy': ramanujanSumFallacyData,
  'abel-ruffini': abelRuffiniData,
  'borsuk-ulam': borsukUlamData,
  'central-limit-theorem': centralLimitTheoremData,
  'fermats-last-theorem': fermatsLastTheoremData,
  'randomized-maxcut': randomizedMaxCutData,
  'three-place-identity': threePlaceIdentityData,
  'lagrange-four-squares': lagrangeFourSquaresData,
  'fermat-two-squares': fermatTwoSquaresData,
  'harmonic-divergence': harmonicDivergenceData,
  'denumerability-rationals': denumerabilityRationalsData,
  'hurwitz-theorem': hurwitzTheoremData,
  'schroeder-bernstein': schroederBernsteinData,
  'cantors-theorem': cantorsTheoremData,
  'wilsons-theorem': wilsonsTheoremData,
  'intermediate-value-theorem': intermediateValueTheoremData,
  'arithmetic-series': arithmeticSeriesData,
}

export function getProof(slug: string): ProofData | undefined {
  return proofs[slug]
}

export function getAllProofs(): ProofData[] {
  return Object.values(proofs)
}
