import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/BrouwerFixedPointOQ02Ext.lean?raw'

const meta = metaJson as unknown as {
  id: string; title: string; slug: string; description: string
  meta: ProofMeta; sections: ProofSection[]
  overview?: ProofOverview; conclusion?: ProofConclusion; crossReferences?: CrossReference[]
}

export const brouwerFixedPointOq02ExtProof: Proof = {
  id: meta.id, title: meta.title, slug: meta.slug, description: meta.description,
  meta: meta.meta, sections: meta.sections, source: sourceRaw,
  overview: meta.overview, conclusion: meta.conclusion, crossReferences: meta.crossReferences,
}
export const brouwerFixedPointOq02ExtAnnotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const brouwerFixedPointOq02ExtData: ProofData = { proof: brouwerFixedPointOq02ExtProof, annotations: brouwerFixedPointOq02ExtAnnotations }
export default brouwerFixedPointOq02ExtData
