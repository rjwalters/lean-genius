import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/CubeRoot3IrrationalOQ02OQ02.lean?raw'
const meta = metaJson as { id: string; title: string; slug: string; description: string; meta: ProofMeta; sections: ProofSection[]; overview?: ProofOverview; conclusion?: ProofConclusion; crossReferences?: CrossReference[] }
export const cubeRoot3IrrationalOq02Oq02Proof: Proof = { id: meta.id, title: meta.title, slug: meta.slug, description: meta.description, meta: meta.meta, sections: meta.sections, source: sourceRaw, overview: meta.overview, conclusion: meta.conclusion, crossReferences: meta.crossReferences }
export const cubeRoot3IrrationalOq02Oq02Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const cubeRoot3IrrationalOq02Oq02Data: ProofData = { proof: cubeRoot3IrrationalOq02Oq02Proof, annotations: cubeRoot3IrrationalOq02Oq02Annotations }
