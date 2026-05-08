import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ03.lean?raw'

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

export const binomialTheoremOq02Oq01Oq01Oq03Proof: Proof = {
  id: meta.id,
  title: meta.title,
  slug: meta.slug,
  description: meta.description,
  meta: meta.meta,
  sections: meta.sections ?? [],
  source: sourceRaw,
  overview: meta.overview,
  conclusion: meta.conclusion,
  crossReferences: meta.crossReferences,
}

export const binomialTheoremOq02Oq01Oq01Oq03Annotations: Annotation[] = annotationsJson as Annotation[]

export const binomialTheoremOq02Oq01Oq01Oq03Data: ProofData = {
  proof: binomialTheoremOq02Oq01Oq01Oq03Proof,
  annotations: binomialTheoremOq02Oq01Oq01Oq03Annotations,
}

export default binomialTheoremOq02Oq01Oq01Oq03Data
