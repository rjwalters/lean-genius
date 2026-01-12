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
}
