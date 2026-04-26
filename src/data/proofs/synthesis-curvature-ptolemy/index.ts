import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/SynthesisCurvaturePtolemy.lean?raw'

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

const annotationsData = annotationsJson as { annotations: Annotation[] }

export const synthesisCurvaturePtolemyProof: Proof = {
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

export const synthesisCurvaturePtolemyAnnotations: Annotation[] = annotationsData.annotations

export const synthesisCurvaturePtolemyData: ProofData = {
  proof: synthesisCurvaturePtolemyProof,
  annotations: synthesisCurvaturePtolemyAnnotations,
}

export default synthesisCurvaturePtolemyData
