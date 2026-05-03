import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/GeometricSeriesOQ01Neumann.lean?raw'

const meta = metaJson as unknown as {
  id: string; title: string; slug: string; description: string
  meta: ProofMeta; sections: ProofSection[]
  overview?: ProofOverview; conclusion?: ProofConclusion; crossReferences?: CrossReference[]
}

export const geometricSeriesOq01NeumannProof: Proof = {
  id: meta.id, title: meta.title, slug: meta.slug, description: meta.description,
  meta: meta.meta, sections: meta.sections, source: sourceRaw,
  overview: meta.overview, conclusion: meta.conclusion, crossReferences: meta.crossReferences,
}
export const geometricSeriesOq01NeumannAnnotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const geometricSeriesOq01NeumannData: ProofData = { proof: geometricSeriesOq01NeumannProof, annotations: geometricSeriesOq01NeumannAnnotations }
export default geometricSeriesOq01NeumannData
