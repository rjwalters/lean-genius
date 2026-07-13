/**
 * Aristotle Client - Wraps the official aristotlelib CLI
 *
 * Uses uvx to run aristotlelib, which is the official Harmonic SDK.
 * This approach is more robust than reverse-engineering their HTTP API.
 */

import { spawn } from 'child_process'
import { readFile, writeFile, unlink, mkdtemp } from 'fs/promises'
import { tmpdir } from 'os'
import { join } from 'path'

export enum ProjectStatus {
  NOT_STARTED = 'NOT_STARTED',
  QUEUED = 'QUEUED',
  IN_PROGRESS = 'IN_PROGRESS',
  COMPLETE = 'COMPLETE',
  FAILED = 'FAILED',
  PENDING_RETRY = 'PENDING_RETRY',
}

interface ProveOptions {
  filePath?: string
  content?: string
  outputPath?: string
  informal?: boolean
  formalContext?: string
}

interface ProveResult {
  success: boolean
  solution?: string
  outputPath?: string
  projectId?: string
  error?: string
  logs: string
}

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

  /**
   * Run the aristotle CLI command
   */
  private async runCli(args: string[]): Promise<{ stdout: string; stderr: string; code: number }> {
    return new Promise((resolve) => {
      const proc = spawn('uvx', ['--from', 'aristotlelib', 'aristotle', ...args], {
        env: {
          ...process.env,
          ARISTOTLE_API_KEY: this.apiKey,
        },
      })

      let stdout = ''
      let stderr = ''

      proc.stdout.on('data', (data) => {
        stdout += data.toString()
      })

      proc.stderr.on('data', (data) => {
        stderr += data.toString()
      })

      proc.on('close', (code) => {
        resolve({ stdout, stderr, code: code ?? 0 })
      })

      proc.on('error', (err) => {
        resolve({ stdout, stderr: err.message, code: 1 })
      })
    })
  }

  /**
   * Prove theorems from a Lean file with sorries.
   */
  async prove(options: ProveOptions): Promise<ProveResult> {
    let tempDir: string | undefined
    let inputPath: string
    let outputPath: string

    try {
      // If content provided, write to temp file
      if (options.content && !options.filePath) {
        tempDir = await mkdtemp(join(tmpdir(), 'aristotle-'))
        inputPath = join(tempDir, 'input.lean')
        outputPath = options.outputPath ?? join(tempDir, 'output.lean')
        await writeFile(inputPath, options.content, 'utf-8')
      } else if (options.filePath) {
        inputPath = options.filePath
        outputPath = options.outputPath ?? options.filePath.replace('.lean', '-solved.lean')
      } else {
        return {
          success: false,
          error: 'Either filePath or content is required',
          logs: '',
        }
      }

      // Build CLI args
      const args = ['prove-from-file', inputPath, '--output-file', outputPath]

      if (options.informal) {
        args.push('--informal')
      }

      if (options.formalContext) {
        args.push('--formal-input-context', options.formalContext)
      }

      // Run aristotle
      const result = await this.runCli(args)
      const logs = result.stderr + result.stdout

      // Extract project ID from logs
      const projectIdMatch = logs.match(/Created project ([a-f0-9-]+)/i)
      const projectId = projectIdMatch?.[1]

      if (result.code === 0 && logs.includes('Solution saved')) {
        // Read the solution
        const solution = await readFile(outputPath, 'utf-8')
        return {
          success: true,
          solution,
          outputPath,
          projectId,
          logs,
        }
      }

      // Check for common error patterns
      if (logs.includes('FAILED')) {
        return {
          success: false,
          error: 'Aristotle could not find a proof',
          projectId,
          logs,
        }
      }

      return {
        success: false,
        error: `Aristotle exited with code ${result.code}`,
        projectId,
        logs,
      }
    } finally {
      // Clean up temp files if we created them
      if (tempDir && !options.outputPath) {
        try {
          await unlink(join(tempDir, 'input.lean')).catch(() => {})
          await unlink(join(tempDir, 'output.lean')).catch(() => {})
        } catch {
          // Ignore cleanup errors
        }
      }
    }
  }

  /**
   * Prove from informal (natural language) problem description.
   */
  async proveInformal(problem: string, formalContext?: string): Promise<ProveResult> {
    const tempDir = await mkdtemp(join(tmpdir(), 'aristotle-'))
    const inputPath = join(tempDir, 'problem.txt')
    const outputPath = join(tempDir, 'solution.lean')

    try {
      await writeFile(inputPath, problem, 'utf-8')

      const args = ['prove-from-file', inputPath, '--informal', '--output-file', outputPath]

      if (formalContext) {
        args.push('--formal-input-context', formalContext)
      }

      const result = await this.runCli(args)
      const logs = result.stderr + result.stdout

      const projectIdMatch = logs.match(/Created project ([a-f0-9-]+)/i)
      const projectId = projectIdMatch?.[1]

      if (result.code === 0 && logs.includes('Solution saved')) {
        const solution = await readFile(outputPath, 'utf-8')
        return {
          success: true,
          solution,
          outputPath,
          projectId,
          logs,
        }
      }

      return {
        success: false,
        error: `Aristotle exited with code ${result.code}`,
        projectId,
        logs,
      }
    } finally {
      try {
        await unlink(inputPath).catch(() => {})
        await unlink(outputPath).catch(() => {})
      } catch {
        // Ignore cleanup errors
      }
    }
  }

  /**
   * Get CLI version info
   */
  async getVersion(): Promise<string> {
    const result = await this.runCli(['--version'])
    return result.stdout.trim() || result.stderr.trim()
  }

  /**
   * Submit a file for proving WITHOUT waiting (async workflow).
   * Returns immediately with project_id.
   */
  async submit(filePath: string, outputPath?: string): Promise<{ projectId: string; error?: string }> {
    const args = ['prove-from-file', filePath, '--no-wait']
    if (outputPath) {
      args.push('--output-file', outputPath)
    }

    const result = await this.runCli(args)
    const logs = result.stderr + result.stdout

    const projectIdMatch = logs.match(/Created project ([a-f0-9-]+)/i)
    const projectId = projectIdMatch?.[1]

    if (projectId) {
      return { projectId }
    }

    return { projectId: '', error: logs }
  }

  /**
   * Check status of a project via Python API (non-blocking).
   */
  async getStatus(projectId: string): Promise<{
    status: ProjectStatus
    percentComplete: number
    description?: string
    error?: string
  }> {
    const pythonScript = `
import asyncio
import json
from aristotlelib import Project

async def check():
    project = await Project.from_id("${projectId}")
    print(json.dumps({
        "status": project.status.name,
        "percentComplete": project.percent_complete or 0,
        "description": project.description
    }))

asyncio.run(check())
`
    const result = await this.runPython(pythonScript)

    if (result.code !== 0) {
      return {
        status: ProjectStatus.FAILED,
        percentComplete: 0,
        error: result.stderr,
      }
    }

    try {
      const data = JSON.parse(result.stdout.trim())
      return {
        status: data.status as ProjectStatus,
        percentComplete: data.percentComplete,
        description: data.description,
      }
    } catch {
      return {
        status: ProjectStatus.FAILED,
        percentComplete: 0,
        error: `Failed to parse response: ${result.stdout}`,
      }
    }
  }

  /**
   * Retrieve solution for a completed project.
   */
  async getSolution(projectId: string, outputPath: string): Promise<{
    success: boolean
    solution?: string
    error?: string
  }> {
    const pythonScript = `
import asyncio
from aristotlelib import Project

async def retrieve():
    project = await Project.from_id("${projectId}")
    if project.status.name != "COMPLETE":
        print(f"ERROR:Project not complete, status: {project.status.name}")
        return
    path = await project.get_solution("${outputPath}")
    print(f"SUCCESS:{path}")

asyncio.run(retrieve())
`
    const result = await this.runPython(pythonScript)
    const output = result.stdout.trim()

    if (output.startsWith('SUCCESS:')) {
      try {
        const solution = await readFile(outputPath, 'utf-8')
        return { success: true, solution }
      } catch (e) {
        return { success: false, error: `Failed to read solution: ${e}` }
      }
    }

    if (output.startsWith('ERROR:')) {
      return { success: false, error: output.slice(6) }
    }

    return { success: false, error: result.stderr || 'Unknown error' }
  }

  /**
   * List all projects.
   */
  async listProjects(): Promise<{
    projects: Array<{
      projectId: string
      status: string
      fileName?: string
      percentComplete?: number
      createdAt?: string
      lastUpdatedAt?: string
    }>
    error?: string
  }> {
    const pythonScript = `
import asyncio
import json
from aristotlelib import Project

async def list_all():
    projects, _ = await Project.list_projects()
    result = []
    for p in projects:
        result.append({
            "projectId": p.project_id,
            "status": p.status.name,
            "fileName": p.file_name,
            "percentComplete": p.percent_complete,
            "createdAt": p.created_at.isoformat() if p.created_at else None,
            "lastUpdatedAt": p.last_updated_at.isoformat() if p.last_updated_at else None
        })
    print(json.dumps(result))

asyncio.run(list_all())
`
    const result = await this.runPython(pythonScript)

    if (result.code !== 0) {
      return { projects: [], error: result.stderr }
    }

    try {
      const projects = JSON.parse(result.stdout.trim())
      return { projects }
    } catch {
      return { projects: [], error: `Failed to parse: ${result.stdout}` }
    }
  }

  /**
   * Check for completed projects and retrieve their solutions.
   * Useful for async workflow - submit jobs, check later for results.
   */
  async checkAndRetrieveCompleted(outputDir: string): Promise<{
    retrieved: Array<{
      projectId: string
      fileName: string
      outputPath: string
    }>
    pending: Array<{
      projectId: string
      fileName?: string
      status: string
      percentComplete: number
    }>
    error?: string
  }> {
    const pythonScript = `
import asyncio
import json
import os
from aristotlelib import Project

async def check_and_retrieve():
    projects, _ = await Project.list_projects()
    retrieved = []
    pending = []
    output_dir = "${outputDir}"

    os.makedirs(output_dir, exist_ok=True)

    for p in projects:
        if p.status.name == "COMPLETE":
            # Generate output path from file name
            base_name = os.path.basename(p.file_name) if p.file_name else f"{p.project_id}.lean"
            output_path = os.path.join(output_dir, base_name.replace(".lean", "-solved.lean"))

            try:
                await p.get_solution(output_path)
                retrieved.append({
                    "projectId": p.project_id,
                    "fileName": p.file_name or "unknown",
                    "outputPath": output_path
                })
            except Exception as e:
                pending.append({
                    "projectId": p.project_id,
                    "fileName": p.file_name,
                    "status": f"RETRIEVE_FAILED: {str(e)}",
                    "percentComplete": 100
                })
        elif p.status.name not in ["FAILED"]:
            pending.append({
                "projectId": p.project_id,
                "fileName": p.file_name,
                "status": p.status.name,
                "percentComplete": p.percent_complete or 0
            })

    print(json.dumps({"retrieved": retrieved, "pending": pending}))

asyncio.run(check_and_retrieve())
`
    const result = await this.runPython(pythonScript)

    if (result.code !== 0) {
      return { retrieved: [], pending: [], error: result.stderr }
    }

    try {
      const data = JSON.parse(result.stdout.trim())
      return { retrieved: data.retrieved, pending: data.pending }
    } catch {
      return { retrieved: [], pending: [], error: `Failed to parse: ${result.stdout}` }
    }
  }

  /**
   * Run Python code via uvx with aristotlelib.
   */
  private async runPython(script: string): Promise<{ stdout: string; stderr: string; code: number }> {
    return new Promise((resolve) => {
      const proc = spawn('uvx', ['--from', 'aristotlelib', 'python3', '-c', script], {
        env: {
          ...process.env,
          ARISTOTLE_API_KEY: this.apiKey,
        },
      })

      let stdout = ''
      let stderr = ''

      proc.stdout.on('data', (data) => {
        stdout += data.toString()
      })

      proc.stderr.on('data', (data) => {
        stderr += data.toString()
      })

      proc.on('close', (code) => {
        resolve({ stdout, stderr, code: code ?? 0 })
      })

      proc.on('error', (err) => {
        resolve({ stdout, stderr: err.message, code: 1 })
      })
    })
  }
}
