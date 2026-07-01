import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/FourierDivergenceResonance.lean?raw'

const meta = metaJson as unknown as {
  id: string
  title: string
  slug: string
  description: string
  meta: ProofMeta
  sections: ProofSection[]
  overview?: ProofOverview
  conclusion?: ProofConclusion
  crossReferences?: CrossReference[]
}

export const banachSteinhausTheoremOQ01OQ01Proof: Proof = {
  id: meta.id,
  title: meta.title,
  slug: meta.slug,
  description: meta.description,
  meta: meta.meta,
  sections: meta.sections,
  source: sourceRaw,
  overview: meta.overview,
  conclusion: meta.conclusion,
  crossReferences: meta.crossReferences,
}

export const banachSteinhausTheoremOQ01OQ01Annotations: Annotation[] = annotationsJson as unknown as Annotation[]

export const banachSteinhausTheoremOQ01OQ01Data: ProofData = {
  proof: banachSteinhausTheoremOQ01OQ01Proof,
  annotations: banachSteinhausTheoremOQ01OQ01Annotations,
}
