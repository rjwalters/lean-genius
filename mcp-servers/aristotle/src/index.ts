#!/usr/bin/env node
/**
 * MCP Server for Harmonic Aristotle Theorem Prover
 *
 * Integrates Aristotle's proof-search capabilities into the OODA loop:
 * - ORIENT: Use aristotle_analyze to understand proof difficulty
 * - DECIDE: Determine whether to attempt manually or delegate to Aristotle
 * - ACT: Use aristotle_prove to fill sorries
 * - LEARN: Analyze results and counterexamples
 */

import { Server } from '@modelcontextprotocol/sdk/server/index.js'
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js'
import {
  CallToolRequestSchema,
  ListToolsRequestSchema,
  Tool,
} from '@modelcontextprotocol/sdk/types.js'
import { AristotleClient, ProjectStatus } from './client.js'

const TOOLS: Tool[] = [
  {
    name: 'aristotle_prove',
    description: `Submit a Lean 4 file with sorries to Aristotle for proof completion.

WHEN TO USE:
- After you've structured the proof but have sorries you can't fill
- When manual proof search has stalled
- For complex lemmas requiring deep search

RETURNS:
- project_id: Use with aristotle_status to check progress
- Proofs typically take 1-30 minutes; complex ones may take hours

TIPS:
- Provide good lemma names and type signatures
- Include relevant context imports
- Break complex goals into smaller sorries`,
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
        context_files: {
          type: 'array',
          items: { type: 'string' },
          description: 'Additional Lean files to include as context (max 10)',
        },
        wait: {
          type: 'boolean',
          description: 'Wait for completion (default: false for async)',
          default: false,
        },
      },
    },
  },
  {
    name: 'aristotle_status',
    description: `Check the status of an Aristotle proof project.

Status values:
- NOT_STARTED: Queued for processing
- QUEUED: In queue
- IN_PROGRESS: Actively being solved
- COMPLETE: Solution ready - use aristotle_solution to retrieve
- FAILED: Could not find proof
- PENDING_RETRY: Temporary failure, will retry`,
    inputSchema: {
      type: 'object',
      properties: {
        project_id: {
          type: 'string',
          description: 'Project ID returned from aristotle_prove',
        },
      },
      required: ['project_id'],
    },
  },
  {
    name: 'aristotle_solution',
    description: `Retrieve the completed proof from Aristotle.

Only call after aristotle_status returns COMPLETE.

The solution will contain:
- The original file with sorries filled in
- Verified Lean 4 code that type-checks`,
    inputSchema: {
      type: 'object',
      properties: {
        project_id: {
          type: 'string',
          description: 'Project ID of completed proof',
        },
        output_path: {
          type: 'string',
          description: 'Optional: path to save the solution file',
        },
      },
      required: ['project_id'],
    },
  },
  {
    name: 'aristotle_informal',
    description: `Submit a mathematical problem in natural language for formalization and proof.

USE CASES:
- Convert textbook problems to Lean
- Explore whether a conjecture is true/false
- Get counterexamples for invalid statements

INPUT:
- Natural language description of theorem/problem
- Optional: Lean context file with relevant definitions

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
          description: 'Optional: Lean file with relevant definitions',
        },
        wait: {
          type: 'boolean',
          description: 'Wait for completion (default: false)',
          default: false,
        },
      },
      required: ['problem'],
    },
  },
  {
    name: 'aristotle_list_projects',
    description: `List your recent Aristotle proof projects.

Use to:
- Resume checking on pending proofs
- Review past proof attempts
- Clean up completed projects`,
    inputSchema: {
      type: 'object',
      properties: {
        status: {
          type: 'string',
          enum: ['NOT_STARTED', 'QUEUED', 'IN_PROGRESS', 'COMPLETE', 'FAILED'],
          description: 'Filter by status',
        },
        limit: {
          type: 'number',
          description: 'Max results (default: 10)',
          default: 10,
        },
      },
    },
  },
]

class AristotleMCPServer {
  private server: Server
  private client: AristotleClient

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

    this.client = new AristotleClient()
    this.setupHandlers()
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
            return await this.handleProve(args)
          case 'aristotle_status':
            return await this.handleStatus(args)
          case 'aristotle_solution':
            return await this.handleSolution(args)
          case 'aristotle_informal':
            return await this.handleInformal(args)
          case 'aristotle_list_projects':
            return await this.handleListProjects(args)
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
    const contextFiles = args.context_files as string[] | undefined
    const wait = args.wait as boolean | undefined

    if (!filePath && !leanContent) {
      throw new Error('Either file_path or lean_content is required')
    }

    const result = await this.client.prove({
      filePath,
      content: leanContent,
      contextFiles,
      wait: wait ?? false,
    })

    if (result.status === ProjectStatus.COMPLETE) {
      return {
        content: [
          {
            type: 'text',
            text: `Proof completed successfully!\n\nProject ID: ${result.projectId}\nSolution:\n\`\`\`lean\n${result.solution}\n\`\`\``,
          },
        ],
      }
    }

    return {
      content: [
        {
          type: 'text',
          text: `Proof submitted.\n\nProject ID: ${result.projectId}\nStatus: ${result.status}\n\nUse aristotle_status to check progress.`,
        },
      ],
    }
  }

  private async handleStatus(args: Record<string, unknown>) {
    const projectId = args.project_id as string
    if (!projectId) throw new Error('project_id is required')

    const status = await this.client.getStatus(projectId)

    let message = `Project: ${projectId}\nStatus: ${status.status}`
    if (status.progress) {
      message += `\nProgress: ${status.progress}`
    }
    if (status.status === ProjectStatus.COMPLETE) {
      message += '\n\nProof ready! Use aristotle_solution to retrieve.'
    } else if (status.status === ProjectStatus.FAILED) {
      message += '\n\nAristotle could not find a proof. Consider:'
      message += '\n- Breaking the goal into smaller lemmas'
      message += '\n- Providing more context or hints'
      message += '\n- Checking if the statement is actually provable'
    }

    return {
      content: [{ type: 'text', text: message }],
    }
  }

  private async handleSolution(args: Record<string, unknown>) {
    const projectId = args.project_id as string
    const outputPath = args.output_path as string | undefined
    if (!projectId) throw new Error('project_id is required')

    const solution = await this.client.getSolution(projectId, outputPath)

    let message = `Solution retrieved for project ${projectId}:\n\n\`\`\`lean\n${solution.content}\n\`\`\``
    if (solution.savedTo) {
      message += `\n\nSaved to: ${solution.savedTo}`
    }

    return {
      content: [{ type: 'text', text: message }],
    }
  }

  private async handleInformal(args: Record<string, unknown>) {
    const problem = args.problem as string
    const contextFile = args.context_file as string | undefined
    const wait = args.wait as boolean | undefined

    if (!problem) throw new Error('problem is required')

    const result = await this.client.proveInformal({
      problem,
      contextFile,
      wait: wait ?? false,
    })

    if (result.status === ProjectStatus.COMPLETE) {
      return {
        content: [
          {
            type: 'text',
            text: `Aristotle analyzed the problem.\n\nProject ID: ${result.projectId}\n\n${result.formalization ? `Formalization:\n\`\`\`lean\n${result.formalization}\n\`\`\`\n\n` : ''}${result.solution ? `Solution:\n\`\`\`lean\n${result.solution}\n\`\`\`\n\n` : ''}${result.counterexample ? `Counterexample found:\n${result.counterexample}` : ''}`,
          },
        ],
      }
    }

    return {
      content: [
        {
          type: 'text',
          text: `Problem submitted.\n\nProject ID: ${result.projectId}\nStatus: ${result.status}\n\nUse aristotle_status to check progress.`,
        },
      ],
    }
  }

  private async handleListProjects(args: Record<string, unknown>) {
    const status = args.status as ProjectStatus | undefined
    const limit = (args.limit as number) ?? 10

    const projects = await this.client.listProjects({ status, limit })

    if (projects.length === 0) {
      return {
        content: [{ type: 'text', text: 'No projects found.' }],
      }
    }

    const lines = projects.map(
      (p) => `- ${p.projectId}: ${p.status}${p.createdAt ? ` (${p.createdAt})` : ''}`
    )

    return {
      content: [
        {
          type: 'text',
          text: `Recent projects:\n${lines.join('\n')}`,
        },
      ],
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
