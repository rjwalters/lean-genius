import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/BinaryGcdOQ02OQ01.lean?raw'

const meta = metaJson as {
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

export const binaryGcdOq02Oq01Proof: Proof = {
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

export const binaryGcdOq02Oq01Annotations: Annotation[] = annotationsJson as unknown as Annotation[]

export const binaryGcdOq02Oq01Data: ProofData = {
  proof: binaryGcdOq02Oq01Proof,
  annotations: binaryGcdOq02Oq01Annotations,
}

export default binaryGcdOq02Oq01Data
