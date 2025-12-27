import { navierStokesData } from './navier-stokes'
import { sqrt2Data } from './sqrt2-irrational'
import { infinitudePrimesData } from './infinitude-primes'
import { knightsTourObliqueData } from './knights-tour-oblique'
import { russell1Plus1Data } from './russell-1-plus-1'
import { cantorDiagonalizationData } from './cantor-diagonalization'
import { cayleyHamiltonData } from './cayley-hamilton'
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
import { bertrandsPostulateData } from './bertrands-postulate'
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
import { geometricSeriesData } from './geometric-series'
import { intermediateValueTheoremData } from './intermediate-value-theorem'
import { gcdAlgorithmData } from './gcd-algorithm'
import { mathematicalInductionData } from './mathematical-induction'
import { arithmeticSeriesData } from './arithmetic-series'
import { subsetCountData } from './subset-count'
import { divisibilityBy3Data } from './divisibility-by-3'
import { inclusionExclusionData } from './inclusion-exclusion'
import { triangleInequalityData } from './triangle-inequality'
import { konigsbergData } from './konigsberg'
import { productOfSegmentsOfChordsData } from './product-of-segments-of-chords'
import { lawOfCosinesData } from './law-of-cosines'
import { birthdayProblemData } from './birthday-problem'
import { quadraticReciprocityData } from './quadratic-reciprocity'
import { lhopitalData } from './lhopital'
import { areaOfCircleData } from './area-of-circle'
import { eulerTotientData } from './euler-totient'
import { deMoivreData } from './de-moivre'
import { pythagoreanTriplesData } from './pythagorean-triples'
import { triangleAngleSumData } from './triangle-angle-sum'
import { taylorTheoremData } from './taylor-theorem'
import { triangularReciprocalsData } from './triangular-reciprocals'
import { binomialTheoremData } from './binomial-theorem'
import { heronsFormulaData } from './herons-formula'
import { bezoutIdentityData } from './bezout-identity'
import { isoscelesTriangleData } from './isosceles-triangle'
import { lagrangeTheoremData } from './lagrange-theorem'
import { meanValueTheoremData } from './mean-value-theorem'
import { cauchySchwarzData } from './cauchy-schwarz'
import { fundamentalArithmeticData } from './fundamental-arithmetic'
import { derangementsData } from './derangements'
import { cramersRuleData } from './cramers-rule'
import { amgmInequalityData } from './amgm-inequality'
import { combinationsFormulaData } from './combinations-formula'
import { factorRemainderTheoremData } from './factor-remainder-theorem'
import { leibnizPiData } from './leibniz-pi'
import { perfectNumbersData } from './perfect-numbers'
import type { ProofData } from '@/types/proof'

export const proofs: Record<string, ProofData> = {
  'navier-stokes': navierStokesData,
  'sqrt2-irrational': sqrt2Data,
  'infinitude-primes': infinitudePrimesData,
  'knights-tour-oblique': knightsTourObliqueData,
  'russell-1-plus-1': russell1Plus1Data,
  'cantor-diagonalization': cantorDiagonalizationData,
  'cayley-hamilton': cayleyHamiltonData,
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
  'bertrands-postulate': bertrandsPostulateData,
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
  'geometric-series': geometricSeriesData,
  'intermediate-value-theorem': intermediateValueTheoremData,
  'gcd-algorithm': gcdAlgorithmData,
  'mathematical-induction': mathematicalInductionData,
  'arithmetic-series': arithmeticSeriesData,
  'subset-count': subsetCountData,
  'divisibility-by-3': divisibilityBy3Data,
  'inclusion-exclusion': inclusionExclusionData,
  'triangle-inequality': triangleInequalityData,
  'konigsberg': konigsbergData,
  'product-of-segments-of-chords': productOfSegmentsOfChordsData,
  'law-of-cosines': lawOfCosinesData,
  'birthday-problem': birthdayProblemData,
  'quadratic-reciprocity': quadraticReciprocityData,
  'lhopital': lhopitalData,
  'area-of-circle': areaOfCircleData,
  'euler-totient': eulerTotientData,
  'de-moivre': deMoivreData,
  'pythagorean-triples': pythagoreanTriplesData,
  'triangle-angle-sum': triangleAngleSumData,
  'taylor-theorem': taylorTheoremData,
  'triangular-reciprocals': triangularReciprocalsData,
  'binomial-theorem': binomialTheoremData,
  'herons-formula': heronsFormulaData,
  'bezout-identity': bezoutIdentityData,
  'isosceles-triangle': isoscelesTriangleData,
  'lagrange-theorem': lagrangeTheoremData,
  'mean-value-theorem': meanValueTheoremData,
  'cauchy-schwarz': cauchySchwarzData,
  'fundamental-arithmetic': fundamentalArithmeticData,
  'derangements': derangementsData,
  'cramers-rule': cramersRuleData,
  'amgm-inequality': amgmInequalityData,
  'combinations-formula': combinationsFormulaData,
  'factor-remainder-theorem': factorRemainderTheoremData,
  'leibniz-pi': leibnizPiData,
  'perfect-numbers': perfectNumbersData,
}

export function getProof(slug: string): ProofData | undefined {
  return proofs[slug]
}

export function getAllProofs(): ProofData[] {
  return Object.values(proofs)
}
