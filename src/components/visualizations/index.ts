import type { ComponentType } from 'react'
import { KnightsTourVisualization } from './KnightsTourVisualization'

export { KnightsTourVisualization }

interface VisualizationProps {
  compact?: boolean
  className?: string
}

// Registry mapping proof slugs to their visualization components
// This allows ProofOverview to conditionally render visualizations
export const VISUALIZATION_REGISTRY: Record<string, ComponentType<VisualizationProps>> = {
  'knights-tour-oblique': KnightsTourVisualization,
}

// Helper to check if a proof has a visualization
export function hasVisualization(proofSlug: string): boolean {
  return proofSlug in VISUALIZATION_REGISTRY
}

// Helper to get the visualization component for a proof
export function getVisualization(proofSlug: string): ComponentType<VisualizationProps> | null {
  return VISUALIZATION_REGISTRY[proofSlug] ?? null
}
