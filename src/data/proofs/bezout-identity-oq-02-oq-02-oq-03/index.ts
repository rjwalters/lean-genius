import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/BezoutIdentityOQ02OQ02OQ03.lean?raw'

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

export const bezoutIdentityOq02Oq02Oq03Proof: Proof = {
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

export const bezoutIdentityOq02Oq02Oq03Annotations: Annotation[] = annotationsJson as unknown as Annotation[]

export const bezoutIdentityOq02Oq02Oq03Data: ProofData = {
  proof: bezoutIdentityOq02Oq02Oq03Proof,
  annotations: bezoutIdentityOq02Oq02Oq03Annotations,
}
