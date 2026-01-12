#!/usr/bin/env node
/**
 * MCP Server for Harmonic Aristotle Theorem Prover
 *
 * Integrates Aristotle's proof-search capabilities into the OODA loop:
 * - ORIENT: Use aristotle_informal to sanity-check conjectures
 * - DECIDE: Determine whether to attempt manually or delegate to Aristotle
 * - ACT: Use aristotle_prove to fill sorries
 * - LEARN: Analyze results and integrate into knowledge base
 *
 * This server wraps the official aristotlelib CLI tool.
 */

import { Server } from '@modelcontextprotocol/sdk/server/index.js'
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js'
import {
  CallToolRequestSchema,
  ListToolsRequestSchema,
  Tool,
} from '@modelcontextprotocol/sdk/types.js'
import { AristotleClient } from './client.js'

const TOOLS: Tool[] = [
  {
    name: 'aristotle_prove',
    description: `Submit a Lean 4 file with sorries to Aristotle for proof completion.

WHEN TO USE:
- After you've structured the proof but have sorries you can't fill
- When manual proof search has stalled
- For complex lemmas requiring deep search

IMPORTANT:
- Proofs typically take 1-5 minutes for simple theorems
- Complex proofs may take 10-30+ minutes
- Uses Lean 4.24.0 / Mathlib 4.24.0 (may differ from your project)

RETURNS:
- The completed proof with sorries filled
- Aristotle adds comments explaining the proof steps`,
    inputSchema: {
      type: 'object',
      properties: {
        file_path: {
          type: 'string',
          description: 'Absolute path to Lean file with sorries to prove',
        },
        lean_content: {
          type: 'string',
          description: 'Alternative: provide Lean code directly instead of file path',
        },
        output_path: {
          type: 'string',
          description: 'Optional: path to save the solved proof (default: input-solved.lean)',
        },
      },
    },
  },
  {
    name: 'aristotle_informal',
    description: `Submit a mathematical problem in natural language for formalization and proof.

USE CASES:
- Convert textbook problems to Lean
- Explore whether a conjecture is true/false
- Get counterexamples for invalid statements
- Quick sanity checks during ORIENT phase

INPUT:
- Natural language description of theorem/problem
- Can use LaTeX or markdown formatting

RETURNS:
- Formalized Lean statement
- Proof (if true) or counterexample (if false)`,
    inputSchema: {
      type: 'object',
      properties: {
        problem: {
          type: 'string',
          description: 'Mathematical problem in natural language, LaTeX, or markdown',
        },
        context_file: {
          type: 'string',
          description: 'Optional: Lean file with relevant definitions for context',
        },
      },
      required: ['problem'],
    },
  },
  {
    name: 'aristotle_version',
    description: 'Check the installed Aristotle CLI version and verify setup is working.',
    inputSchema: {
      type: 'object',
      properties: {},
    },
  },
  {
    name: 'aristotle_submit',
    description: `Submit a Lean file for proving WITHOUT waiting (async workflow).

USE THIS FOR:
- Long-running proofs (10+ minutes expected)
- Batch submissions where you want to continue working
- When you want to monitor progress manually

WORKFLOW:
1. Call aristotle_submit → get project_id
2. Continue working on other tasks
3. Periodically call aristotle_status to check progress
4. When COMPLETE, call aristotle_retrieve to get solution

RETURNS:
- project_id: Use this to check status and retrieve results later`,
    inputSchema: {
      type: 'object',
      properties: {
        file_path: {
          type: 'string',
          description: 'Absolute path to Lean file with sorries to prove',
        },
        output_path: {
          type: 'string',
          description: 'Optional: path to save the solved proof when retrieved',
        },
      },
      required: ['file_path'],
    },
  },
  {
    name: 'aristotle_status',
    description: `Check the status of a submitted Aristotle project (non-blocking).

STATUSES:
- QUEUED: Waiting to start
- IN_PROGRESS: Actively working (check percentComplete)
- COMPLETE: Ready to retrieve solution
- FAILED: Could not find proof

Use this to monitor long-running proofs without blocking.`,
    inputSchema: {
      type: 'object',
      properties: {
        project_id: {
          type: 'string',
          description: 'Project ID returned from aristotle_submit',
        },
      },
      required: ['project_id'],
    },
  },
  {
    name: 'aristotle_retrieve',
    description: `Retrieve the solution for a completed Aristotle project.

Only works when status is COMPLETE. Returns the solved Lean file.`,
    inputSchema: {
      type: 'object',
      properties: {
        project_id: {
          type: 'string',
          description: 'Project ID of a COMPLETE project',
        },
        output_path: {
          type: 'string',
          description: 'Path to save the solved proof',
        },
      },
      required: ['project_id', 'output_path'],
    },
  },
  {
    name: 'aristotle_list',
    description: `List all Aristotle projects and their statuses.

Useful for:
- Finding forgotten project IDs
- Checking overall queue status
- Identifying completed proofs to retrieve`,
    inputSchema: {
      type: 'object',
      properties: {},
    },
  },
]

class AristotleMCPServer {
  private server: Server
  private client: AristotleClient | null = null

  constructor() {
    this.server = new Server(
      {
        name: 'aristotle',
        version: '0.1.0',
      },
      {
        capabilities: {
          tools: {},
        },
      }
    )

    this.setupHandlers()
  }

  private getClient(): AristotleClient {
    if (!this.client) {
      this.client = new AristotleClient()
    }
    return this.client
  }

  private setupHandlers() {
    // List available tools
    this.server.setRequestHandler(ListToolsRequestSchema, async () => ({
      tools: TOOLS,
    }))

    // Handle tool calls
    this.server.setRequestHandler(CallToolRequestSchema, async (request) => {
      const { name, arguments: args } = request.params

      try {
        switch (name) {
          case 'aristotle_prove':
            return await this.handleProve(args ?? {})
          case 'aristotle_informal':
            return await this.handleInformal(args ?? {})
          case 'aristotle_version':
            return await this.handleVersion()
          case 'aristotle_submit':
            return await this.handleSubmit(args ?? {})
          case 'aristotle_status':
            return await this.handleStatus(args ?? {})
          case 'aristotle_retrieve':
            return await this.handleRetrieve(args ?? {})
          case 'aristotle_list':
            return await this.handleList()
          default:
            throw new Error(`Unknown tool: ${name}`)
        }
      } catch (error) {
        const message = error instanceof Error ? error.message : String(error)
        return {
          content: [{ type: 'text', text: `Error: ${message}` }],
          isError: true,
        }
      }
    })
  }

  private async handleProve(args: Record<string, unknown>) {
    const filePath = args.file_path as string | undefined
    const leanContent = args.lean_content as string | undefined
    const outputPath = args.output_path as string | undefined

    if (!filePath && !leanContent) {
      throw new Error('Either file_path or lean_content is required')
    }

    const client = this.getClient()
    const result = await client.prove({
      filePath,
      content: leanContent,
      outputPath,
    })

    if (result.success) {
      let message = `Proof completed successfully!`
      if (result.projectId) {
        message += `\n\nProject ID: ${result.projectId}`
      }
      if (result.outputPath) {
        message += `\nSaved to: ${result.outputPath}`
      }
      message += `\n\n## Solution\n\`\`\`lean\n${result.solution}\n\`\`\``

      return {
        content: [{ type: 'text', text: message }],
      }
    }

    let message = `Aristotle could not complete the proof.`
    if (result.error) {
      message += `\n\nError: ${result.error}`
    }
    if (result.projectId) {
      message += `\nProject ID: ${result.projectId}`
    }
    message += `\n\n### Suggestions:\n`
    message += `- Break the goal into smaller lemmas\n`
    message += `- Provide more context or helper definitions\n`
    message += `- Check if the statement is actually provable\n`
    message += `- Try adding hints via comments\n`
    message += `\n### Logs:\n\`\`\`\n${result.logs}\n\`\`\``

    return {
      content: [{ type: 'text', text: message }],
      isError: true,
    }
  }

  private async handleInformal(args: Record<string, unknown>) {
    const problem = args.problem as string
    const contextFile = args.context_file as string | undefined

    if (!problem) {
      throw new Error('problem is required')
    }

    const client = this.getClient()
    const result = await client.proveInformal(problem, contextFile)

    if (result.success) {
      let message = `Aristotle analyzed the problem successfully!`
      if (result.projectId) {
        message += `\n\nProject ID: ${result.projectId}`
      }
      message += `\n\n## Formalization & Proof\n\`\`\`lean\n${result.solution}\n\`\`\``

      return {
        content: [{ type: 'text', text: message }],
      }
    }

    let message = `Aristotle could not solve the informal problem.`
    if (result.error) {
      message += `\n\nError: ${result.error}`
    }
    message += `\n\n### Logs:\n\`\`\`\n${result.logs}\n\`\`\``

    return {
      content: [{ type: 'text', text: message }],
      isError: true,
    }
  }

  private async handleVersion() {
    try {
      const client = this.getClient()
      const version = await client.getVersion()
      return {
        content: [
          {
            type: 'text',
            text: `Aristotle CLI version: ${version}\n\nSetup verified - ready to prove theorems!`,
          },
        ],
      }
    } catch (error) {
      const message = error instanceof Error ? error.message : String(error)
      return {
        content: [
          {
            type: 'text',
            text: `Failed to verify Aristotle setup: ${message}\n\nMake sure:\n1. ARISTOTLE_API_KEY is set\n2. uvx is installed (install via: curl -LsSf https://astral.sh/uv/install.sh | sh)\n3. You have network access to aristotle.harmonic.fun`,
          },
        ],
        isError: true,
      }
    }
  }

  private async handleSubmit(args: Record<string, unknown>) {
    const filePath = args.file_path as string
    const outputPath = args.output_path as string | undefined

    if (!filePath) {
      throw new Error('file_path is required')
    }

    const client = this.getClient()
    const result = await client.submit(filePath, outputPath)

    if (result.projectId) {
      return {
        content: [
          {
            type: 'text',
            text: `Project submitted successfully!\n\n**Project ID:** \`${result.projectId}\`\n\nUse \`aristotle_status\` to check progress.\nUse \`aristotle_retrieve\` when complete.`,
          },
        ],
      }
    }

    return {
      content: [{ type: 'text', text: `Failed to submit: ${result.error}` }],
      isError: true,
    }
  }

  private async handleStatus(args: Record<string, unknown>) {
    const projectId = args.project_id as string

    if (!projectId) {
      throw new Error('project_id is required')
    }

    const client = this.getClient()
    const result = await client.getStatus(projectId)

    if (result.error) {
      return {
        content: [{ type: 'text', text: `Error checking status: ${result.error}` }],
        isError: true,
      }
    }

    let message = `**Project:** \`${projectId}\`\n`
    message += `**Status:** ${result.status}\n`
    message += `**Progress:** ${result.percentComplete}%\n`
    if (result.description) {
      message += `**Description:** ${result.description}\n`
    }

    if (result.status === 'COMPLETE') {
      message += `\n✅ Ready to retrieve! Use \`aristotle_retrieve\` to get the solution.`
    } else if (result.status === 'FAILED') {
      message += `\n❌ Proof search failed. Consider breaking into smaller lemmas.`
    }

    return {
      content: [{ type: 'text', text: message }],
    }
  }

  private async handleRetrieve(args: Record<string, unknown>) {
    const projectId = args.project_id as string
    const outputPath = args.output_path as string

    if (!projectId || !outputPath) {
      throw new Error('project_id and output_path are required')
    }

    const client = this.getClient()
    const result = await client.getSolution(projectId, outputPath)

    if (result.success) {
      return {
        content: [
          {
            type: 'text',
            text: `Solution retrieved successfully!\n\n**Saved to:** ${outputPath}\n\n## Solution\n\`\`\`lean\n${result.solution}\n\`\`\``,
          },
        ],
      }
    }

    return {
      content: [{ type: 'text', text: `Failed to retrieve: ${result.error}` }],
      isError: true,
    }
  }

  private async handleList() {
    const client = this.getClient()
    const result = await client.listProjects()

    if (result.error) {
      return {
        content: [{ type: 'text', text: `Error listing projects: ${result.error}` }],
        isError: true,
      }
    }

    if (result.projects.length === 0) {
      return {
        content: [{ type: 'text', text: 'No projects found.' }],
      }
    }

    let message = '## Aristotle Projects\n\n'
    message += '| Project ID | Status | File | Progress |\n'
    message += '|------------|--------|------|----------|\n'

    for (const p of result.projects) {
      const progress = p.percentComplete !== undefined ? `${p.percentComplete}%` : '-'
      message += `| \`${p.projectId.slice(0, 8)}...\` | ${p.status} | ${p.fileName || '-'} | ${progress} |\n`
    }

    return {
      content: [{ type: 'text', text: message }],
    }
  }

  async run() {
    const transport = new StdioServerTransport()
    await this.server.connect(transport)
    console.error('Aristotle MCP server running on stdio')
  }
}

const server = new AristotleMCPServer()
server.run().catch(console.error)
