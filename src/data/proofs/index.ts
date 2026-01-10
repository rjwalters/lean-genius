/**
 * Proof Data Index
 *
 * Exports:
 * - listings: Lightweight metadata for HomePage gallery (small bundle)
 * - getProofAsync: Dynamic import for full proof data (lazy loaded)
 * - getProof/getAllProofs: Synchronous access (pulls in full bundle - use sparingly)
 */

import listingsData from './listings.json'
import type { ProofData, ProofListing } from '@/types/proof'

// Lightweight listings for HomePage - does not pull in proof data
export const listings: ProofListing[] = listingsData as ProofListing[]

// Dynamic import map for lazy loading proof data
// eslint-disable-next-line @typescript-eslint/no-explicit-any
const proofModules: Record<string, () => Promise<any>> = {
  'navier-stokes': () => import('./navier-stokes'),
  'sqrt2-irrational': () => import('./sqrt2-irrational'),
  'infinitude-primes': () => import('./infinitude-primes'),
  'knights-tour-oblique': () => import('./knights-tour-oblique'),
  'russell-1-plus-1': () => import('./russell-1-plus-1'),
  'cantor-diagonalization': () => import('./cantor-diagonalization'),
  'cayley-hamilton': () => import('./cayley-hamilton'),
  'cevas-theorem': () => import('./cevas-theorem'),
  'fundamental-theorem-calculus': () => import('./fundamental-theorem-calculus'),
  'fundamental-theorem-algebra': () => import('./fundamental-theorem-algebra'),
  'godel-incompleteness': () => import('./godel-incompleteness'),
  'pythagorean-theorem': () => import('./pythagorean-theorem'),
  'halting-problem': () => import('./halting-problem'),
  'hilbert-10': () => import('./hilbert-10'),
  'four-color-theorem': () => import('./four-color-theorem'),
  'euler-identity': () => import('./euler-identity'),
  'brouwer-fixed-point': () => import('./brouwer-fixed-point'),
  'buffons-needle': () => import('./buffons-needle'),
  'ramanujan-sum-fallacy': () => import('./ramanujan-sum-fallacy'),
  'ramseys-theorem': () => import('./ramseys-theorem'),
  'abel-ruffini': () => import('./abel-ruffini'),
  'bertrands-postulate': () => import('./bertrands-postulate'),
  'borsuk-ulam': () => import('./borsuk-ulam'),
  'central-limit-theorem': () => import('./central-limit-theorem'),
  'fermats-last-theorem': () => import('./fermats-last-theorem'),
  'randomized-maxcut': () => import('./randomized-maxcut'),
  'three-place-identity': () => import('./three-place-identity'),
  'lagrange-four-squares': () => import('./lagrange-four-squares'),
  'fermat-two-squares': () => import('./fermat-two-squares'),
  'friendship-theorem': () => import('./friendship-theorem'),
  'harmonic-divergence': () => import('./harmonic-divergence'),
  'denumerability-rationals': () => import('./denumerability-rationals'),
  'hurwitz-theorem': () => import('./hurwitz-theorem'),
  'schroeder-bernstein': () => import('./schroeder-bernstein'),
  'cantors-theorem': () => import('./cantors-theorem'),
  'wilsons-theorem': () => import('./wilsons-theorem'),
  'geometric-series': () => import('./geometric-series'),
  'intermediate-value-theorem': () => import('./intermediate-value-theorem'),
  'gcd-algorithm': () => import('./gcd-algorithm'),
  'mathematical-induction': () => import('./mathematical-induction'),
  'arithmetic-series': () => import('./arithmetic-series'),
  'subset-count': () => import('./subset-count'),
  'divisibility-by-3': () => import('./divisibility-by-3'),
  'inclusion-exclusion': () => import('./inclusion-exclusion'),
  'triangle-inequality': () => import('./triangle-inequality'),
  'konigsberg': () => import('./konigsberg'),
  'product-of-segments-of-chords': () => import('./product-of-segments-of-chords'),
  'law-of-cosines': () => import('./law-of-cosines'),
  'laws-of-large-numbers': () => import('./laws-of-large-numbers'),
  'birthday-problem': () => import('./birthday-problem'),
  'quadratic-reciprocity': () => import('./quadratic-reciprocity'),
  'lhopital': () => import('./lhopital'),
  'area-of-circle': () => import('./area-of-circle'),
  'euler-totient': () => import('./euler-totient'),
  'de-moivre': () => import('./de-moivre'),
  'pythagorean-triples': () => import('./pythagorean-triples'),
  'triangle-angle-sum': () => import('./triangle-angle-sum'),
  'taylor-theorem': () => import('./taylor-theorem'),
  'triangular-reciprocals': () => import('./triangular-reciprocals'),
  'binomial-theorem': () => import('./binomial-theorem'),
  'herons-formula': () => import('./herons-formula'),
  'bezout-identity': () => import('./bezout-identity'),
  'isosceles-triangle': () => import('./isosceles-triangle'),
  'lagrange-theorem': () => import('./lagrange-theorem'),
  'mean-value-theorem': () => import('./mean-value-theorem'),
  'cauchy-schwarz': () => import('./cauchy-schwarz'),
  'fundamental-arithmetic': () => import('./fundamental-arithmetic'),
  'derangements': () => import('./derangements'),
  'cramers-rule': () => import('./cramers-rule'),
  'amgm-inequality': () => import('./amgm-inequality'),
  'combinations-formula': () => import('./combinations-formula'),
  'factor-remainder-theorem': () => import('./factor-remainder-theorem'),
  'leibniz-pi': () => import('./leibniz-pi'),
  'perfect-numbers': () => import('./perfect-numbers'),
  'angle-trisection': () => import('./angle-trisection'),
  'basel-problem': () => import('./basel-problem'),
  'ballot-problem': () => import('./ballot-problem'),
  'euler-polyhedral-formula': () => import('./euler-polyhedral-formula'),
  'prime-reciprocal-divergence': () => import('./prime-reciprocal-divergence'),
  'sqrt2-examples': () => import('./sqrt2-examples'),
  'sqrt2-from-axioms': () => import('./sqrt2-from-axioms'),
  'stirling-formula': () => import('./stirling-formula'),
  'sum-of-kth-powers': () => import('./sum-of-kth-powers'),
  'sylow-theorems': () => import('./sylow-theorems'),
  'erdos-szekeres': () => import('./erdos-szekeres'),
  'erdos-124-complete-sequences': () => import('./erdos-124-complete-sequences'),
  'platonic-solids': () => import('./platonic-solids'),
  'ptolemys-theorem': () => import('./ptolemys-theorem'),
  'desargues-theorem': () => import('./desargues-theorem'),
  'descartes-rule-of-signs': () => import('./descartes-rule-of-signs'),
  'pell-equation': () => import('./pell-equation'),
  'riemann-hypothesis': () => import('./riemann-hypothesis'),
  'dissection-of-cubes': () => import('./dissection-of-cubes'),
  'dirichlets-theorem': () => import('./dirichlets-theorem'),
  'continuum-hypothesis': () => import('./continuum-hypothesis'),
  'e-transcendental': () => import('./e-transcendental'),
  'fair-games-theorem': () => import('./fair-games-theorem'),
  'feuerbachs-theorem': () => import('./feuerbachs-theorem'),
  'fourier-series': () => import('./fourier-series'),
  'general-quartic': () => import('./general-quartic'),
  'greens-theorem': () => import('./greens-theorem'),
  'hermite-lindemann': () => import('./hermite-lindemann'),
  'isoperimetric-theorem': () => import('./isoperimetric-theorem'),
  'lebesgue-measure': () => import('./lebesgue-measure'),
  'liouville-theorem': () => import('./liouville-theorem'),
  'minkowski-theorem': () => import('./minkowski-theorem'),
  'morleys-theorem': () => import('./morleys-theorem'),
  'parallel-postulate-independence': () => import('./parallel-postulate-independence'),
  'partition-theorem': () => import('./partition-theorem'),
  'pascals-hexagon': () => import('./pascals-hexagon'),
  'pi-transcendental': () => import('./pi-transcendental'),
  'picks-theorem': () => import('./picks-theorem'),
  'prime-number-theorem': () => import('./prime-number-theorem'),
  'puiseux-theorem': () => import('./puiseux-theorem'),
  'solution-of-cubic': () => import('./solution-of-cubic'),
  'gelfond-schneider': () => import('./gelfond-schneider'),
  'hilbert-3': () => import('./hilbert-3'),
  'hilbert-5': () => import('./hilbert-5'),
  'hilbert-11': () => import('./hilbert-11'),
  'hilbert-13': () => import('./hilbert-13'),
  'hilbert-16': () => import('./hilbert-16'),
  'hilbert-17': () => import('./hilbert-17'),
  'hodge-conjecture': () => import('./hodge-conjecture'),
  'kepler-conjecture': () => import('./kepler-conjecture'),
  'kroneckers-jugendtraum': () => import('./kroneckers-jugendtraum'),
  'p-vs-np': () => import('./p-vs-np'),
  'yang-mills': () => import('./yang-mills'),
  'poincare-conjecture': () => import('./poincare-conjecture'),
  'birch-swinnerton-dyer': () => import('./birch-swinnerton-dyer'),
  'hilbert-15': () => import('./hilbert-15'),
  'hilbert-4': () => import('./hilbert-4'),
  'hilbert-6': () => import('./hilbert-6'),
  'hilbert-14': () => import('./hilbert-14'),
  'hilbert-19': () => import('./hilbert-19'),
  'hilbert-20': () => import('./hilbert-20'),
  'hilbert-21': () => import('./hilbert-21'),
  'hilbert-22': () => import('./hilbert-22'),
  'hilbert-23': () => import('./hilbert-23'),
  'hilbert-9-reciprocity': () => import('./hilbert-9-reciprocity'),
  'primitive-roots': () => import('./primitive-roots'),
  'kummer-theorem': () => import('./kummer-theorem'),
  'chinese-remainder-constructive': () => import('./chinese-remainder-constructive'),
  'collatz-structured': () => import('./collatz-structured'),
  'legendre-partial': () => import('./legendre-partial'),
  'sophie-germain': () => import('./sophie-germain'),
  'szemeredi-theorem': () => import('./szemeredi-theorem'),
  'twin-primes-special': () => import('./twin-primes-special'),
  'vietas-formulas': () => import('./vietas-formulas'),
  'wolstenholme-theorem': () => import('./wolstenholme-theorem'),
}

/**
 * Convert kebab-case slug to camelCase export name
 * e.g., "navier-stokes" -> "navierStokesData"
 */
function slugToExportName(slug: string): string {
  const camel = slug.replace(/-([a-z0-9])/g, (_, c) => c.toUpperCase())
  return camel + 'Data'
}

/**
 * Asynchronously load proof data for a given slug.
 * This enables per-proof code splitting - only loads the requested proof.
 */
export async function getProofAsync(slug: string): Promise<ProofData | undefined> {
  const loader = proofModules[slug]
  if (!loader) return undefined

  try {
    const module = await loader()
    // Try default export first, then named export
    return module.default || module[slugToExportName(slug)]
  } catch (e) {
    console.error(`Failed to load proof: ${slug}`, e)
    return undefined
  }
}

// Cache for synchronous access (populated on first use)
let proofsCache: Record<string, ProofData> | null = null

/**
 * Synchronously get a proof by slug.
 * WARNING: This pulls in ALL proof data into the bundle.
 * Prefer getProofAsync for better code splitting.
 */
export function getProof(slug: string): ProofData | undefined {
  if (!proofsCache) {
    proofsCache = {}
    // This will be tree-shaken if only getProofAsync is used
  }
  return proofsCache[slug]
}

/**
 * Get all proofs synchronously.
 * WARNING: This pulls in ALL proof data into the bundle.
 * Prefer using `listings` for HomePage gallery.
 */
export function getAllProofs(): ProofData[] {
  if (!proofsCache) {
    return []
  }
  return Object.values(proofsCache)
}
