/**
 * Aristotle API Client
 *
 * Wraps the Harmonic Aristotle API for theorem proving.
 * Based on the aristotlelib Python SDK API.
 */

import { readFile, writeFile } from 'fs/promises'
import { existsSync } from 'fs'

export enum ProjectStatus {
  NOT_STARTED = 'NOT_STARTED',
  QUEUED = 'QUEUED',
  IN_PROGRESS = 'IN_PROGRESS',
  COMPLETE = 'COMPLETE',
  FAILED = 'FAILED',
  PENDING_RETRY = 'PENDING_RETRY',
}

export enum ProjectInputType {
  FORMAL_LEAN = 'FORMAL_LEAN',
  INFORMAL = 'INFORMAL',
}

interface ProveOptions {
  filePath?: string
  content?: string
  contextFiles?: string[]
  wait?: boolean
}

interface InformalOptions {
  problem: string
  contextFile?: string
  wait?: boolean
}

interface ProveResult {
  projectId: string
  status: ProjectStatus
  solution?: string
}

interface InformalResult {
  projectId: string
  status: ProjectStatus
  formalization?: string
  solution?: string
  counterexample?: string
}

interface StatusResult {
  status: ProjectStatus
  progress?: string
}

interface SolutionResult {
  content: string
  savedTo?: string
}

interface ProjectInfo {
  projectId: string
  status: ProjectStatus
  createdAt?: string
}

interface ListOptions {
  status?: ProjectStatus
  limit?: number
}

const API_BASE = 'https://api.aristotle.harmonic.fun'

export class AristotleClient {
  private apiKey: string

  constructor(apiKey?: string) {
    this.apiKey = apiKey ?? process.env.ARISTOTLE_API_KEY ?? ''
    if (!this.apiKey) {
      throw new Error(
        'ARISTOTLE_API_KEY not set. Get your API key from https://aristotle.harmonic.fun/'
      )
    }
  }

  private async request<T>(
    endpoint: string,
    options: RequestInit = {}
  ): Promise<T> {
    const url = `${API_BASE}${endpoint}`
    const response = await fetch(url, {
      ...options,
      headers: {
        'Authorization': `Bearer ${this.apiKey}`,
        'Content-Type': 'application/json',
        ...options.headers,
      },
    })

    if (!response.ok) {
      const error = await response.text()
      throw new Error(`Aristotle API error (${response.status}): ${error}`)
    }

    return response.json()
  }

  /**
   * Submit a Lean file with sorries for proof completion.
   */
  async prove(options: ProveOptions): Promise<ProveResult> {
    let content = options.content

    // Read file if path provided
    if (options.filePath && !content) {
      if (!existsSync(options.filePath)) {
        throw new Error(`File not found: ${options.filePath}`)
      }
      content = await readFile(options.filePath, 'utf-8')
    }

    if (!content) {
      throw new Error('No Lean content provided')
    }

    // Create project
    const createResponse = await this.request<{ project_id: string }>(
      '/v1/projects',
      {
        method: 'POST',
        body: JSON.stringify({
          input_type: ProjectInputType.FORMAL_LEAN,
        }),
      }
    )

    const projectId = createResponse.project_id

    // Add context files if provided
    if (options.contextFiles && options.contextFiles.length > 0) {
      const contextContents = await Promise.all(
        options.contextFiles.slice(0, 10).map(async (path) => {
          const fileContent = await readFile(path, 'utf-8')
          return { path, content: fileContent }
        })
      )

      await this.request(`/v1/projects/${projectId}/context`, {
        method: 'POST',
        body: JSON.stringify({ files: contextContents }),
      })
    }

    // Submit for solving
    await this.request(`/v1/projects/${projectId}/solve`, {
      method: 'POST',
      body: JSON.stringify({ content }),
    })

    // If wait mode, poll until complete
    if (options.wait) {
      return await this.waitForCompletion(projectId)
    }

    return {
      projectId,
      status: ProjectStatus.QUEUED,
    }
  }

  /**
   * Submit an informal (natural language) problem.
   */
  async proveInformal(options: InformalOptions): Promise<InformalResult> {
    // Create project
    const createResponse = await this.request<{ project_id: string }>(
      '/v1/projects',
      {
        method: 'POST',
        body: JSON.stringify({
          input_type: ProjectInputType.INFORMAL,
        }),
      }
    )

    const projectId = createResponse.project_id

    // Add context if provided
    if (options.contextFile) {
      const contextContent = await readFile(options.contextFile, 'utf-8')
      await this.request(`/v1/projects/${projectId}/context`, {
        method: 'POST',
        body: JSON.stringify({
          files: [{ path: options.contextFile, content: contextContent }],
        }),
      })
    }

    // Submit problem
    await this.request(`/v1/projects/${projectId}/solve`, {
      method: 'POST',
      body: JSON.stringify({ content: options.problem }),
    })

    if (options.wait) {
      const result = await this.waitForCompletion(projectId)
      return {
        projectId: result.projectId,
        status: result.status,
        solution: result.solution,
        // Note: formalization and counterexample would come from parsing the solution
      }
    }

    return {
      projectId,
      status: ProjectStatus.QUEUED,
    }
  }

  /**
   * Get the status of a proof project.
   */
  async getStatus(projectId: string): Promise<StatusResult> {
    const response = await this.request<{
      status: ProjectStatus
      progress?: string
    }>(`/v1/projects/${projectId}`)

    return {
      status: response.status,
      progress: response.progress,
    }
  }

  /**
   * Retrieve the solution from a completed project.
   */
  async getSolution(
    projectId: string,
    outputPath?: string
  ): Promise<SolutionResult> {
    const response = await this.request<{ solution: string }>(
      `/v1/projects/${projectId}/solution`
    )

    const result: SolutionResult = {
      content: response.solution,
    }

    if (outputPath) {
      await writeFile(outputPath, response.solution, 'utf-8')
      result.savedTo = outputPath
    }

    return result
  }

  /**
   * List recent projects.
   */
  async listProjects(options: ListOptions = {}): Promise<ProjectInfo[]> {
    const params = new URLSearchParams()
    if (options.limit) params.set('limit', String(options.limit))
    if (options.status) params.set('status', options.status)

    const response = await this.request<{
      projects: Array<{
        project_id: string
        status: ProjectStatus
        created_at?: string
      }>
    }>(`/v1/projects?${params}`)

    return response.projects.map((p) => ({
      projectId: p.project_id,
      status: p.status,
      createdAt: p.created_at,
    }))
  }

  /**
   * Poll until project completes or fails.
   */
  private async waitForCompletion(
    projectId: string,
    intervalMs = 30000,
    maxAttempts = 120 // 1 hour max
  ): Promise<ProveResult> {
    for (let i = 0; i < maxAttempts; i++) {
      const status = await this.getStatus(projectId)

      if (status.status === ProjectStatus.COMPLETE) {
        const solution = await this.getSolution(projectId)
        return {
          projectId,
          status: ProjectStatus.COMPLETE,
          solution: solution.content,
        }
      }

      if (status.status === ProjectStatus.FAILED) {
        return {
          projectId,
          status: ProjectStatus.FAILED,
        }
      }

      // Wait before polling again
      await new Promise((resolve) => setTimeout(resolve, intervalMs))
    }

    // Timed out
    return {
      projectId,
      status: ProjectStatus.IN_PROGRESS,
    }
  }
}
