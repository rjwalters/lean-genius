import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/RamseysTheoremOQ02.lean?raw'

const meta = metaJson as unknown as {
  id: string; title: string; slug: string; description: string
  meta: ProofMeta; sections: ProofSection[]
  overview?: ProofOverview; conclusion?: ProofConclusion; crossReferences?: CrossReference[]
}

export const ramseysTheoremOq02Proof: Proof = {
  id: meta.id, title: meta.title, slug: meta.slug, description: meta.description,
  meta: meta.meta, sections: meta.sections, source: sourceRaw,
  overview: meta.overview, conclusion: meta.conclusion, crossReferences: meta.crossReferences,
}
export const ramseysTheoremOq02Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const ramseysTheoremOq02Data: ProofData = { proof: ramseysTheoremOq02Proof, annotations: ramseysTheoremOq02Annotations }
export default ramseysTheoremOq02Data
