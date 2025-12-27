import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/IsoscelesTriangle.lean?raw'
const meta = metaJson as { id: string; title: string; slug: string; description: string; meta: ProofMeta; sections: ProofSection[]; overview?: ProofOverview; conclusion?: ProofConclusion }
export const isoscelesTriangleProof: Proof = { id: meta.id, title: meta.title, slug: meta.slug, description: meta.description, meta: meta.meta, sections: meta.sections, source: sourceRaw, overview: meta.overview, conclusion: meta.conclusion }
export const isoscelesTriangleAnnotations: Annotation[] = annotationsJson as Annotation[]
export const isoscelesTriangleData: ProofData = { proof: isoscelesTriangleProof, annotations: isoscelesTriangleAnnotations }
