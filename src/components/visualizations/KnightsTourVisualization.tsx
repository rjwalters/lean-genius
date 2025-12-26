import { useState, useEffect, useCallback, useRef } from 'react'
import { Play, Pause, RotateCcw, ChevronRight } from 'lucide-react'
import { Button } from '@/components/ui/button'

/**
 * Tour (t) - The unique closed knight's tour with exactly 4 oblique turns.
 * Based on Knuth TAOCP Vol 4 Fascicle 8a, Fig. A-19(t)
 */
const TOUR: [number, number][] = [
  [0, 0], [2, 1], [4, 0], [6, 1], [7, 3], [6, 5], [7, 7], [5, 6],
  [3, 7], [1, 6], [0, 4], [2, 3], [1, 1], [3, 0], [4, 2], [6, 3],
  [7, 1], [5, 0], [3, 1], [1, 0], [0, 2], [1, 4], [0, 6], [2, 7],
  [3, 5], [5, 4], [7, 5], [6, 7], [4, 6], [3, 4], [5, 3], [7, 2],
  [6, 0], [4, 1], [2, 0], [0, 1], [1, 3], [2, 5], [4, 4], [3, 2],
  [5, 1], [7, 0], [6, 2], [7, 4], [6, 6], [4, 7], [2, 6], [0, 7],
  [1, 5], [0, 3], [2, 2], [4, 3], [5, 5], [3, 6], [1, 7], [0, 5],
  [2, 4], [4, 5], [5, 7], [7, 6], [6, 4], [5, 2], [3, 3], [1, 2]
]

// Positions where oblique (obtuse) turns occur - at the 4 corners
const OBLIQUE_INDICES = new Set([0, 6, 41, 47])
const OBLIQUE_SQUARES: [number, number][] = [[0, 0], [7, 7], [7, 0], [0, 7]]

interface Props {
  className?: string
  compact?: boolean
}

export function KnightsTourVisualization({ className = '', compact = false }: Props) {
  const [currentStep, setCurrentStep] = useState(0)
  const [isPlaying, setIsPlaying] = useState(false)
  const [speed, setSpeed] = useState(400)
  const animationRef = useRef<number | null>(null)
  const lastTimeRef = useRef(0)

  // Animation loop
  const animate = useCallback((timestamp: number) => {
    if (timestamp - lastTimeRef.current >= speed) {
      setCurrentStep(prev => {
        if (prev >= 64) {
          setIsPlaying(false)
          return prev
        }
        return prev + 1
      })
      lastTimeRef.current = timestamp
    }
    if (isPlaying) {
      animationRef.current = requestAnimationFrame(animate)
    }
  }, [isPlaying, speed])

  useEffect(() => {
    if (isPlaying) {
      lastTimeRef.current = performance.now()
      animationRef.current = requestAnimationFrame(animate)
    }
    return () => {
      if (animationRef.current) {
        cancelAnimationFrame(animationRef.current)
      }
    }
  }, [isPlaying, animate])

  const handlePlayPause = () => {
    if (currentStep >= 64) {
      setCurrentStep(0)
    }
    setIsPlaying(!isPlaying)
  }

  const handleStep = () => {
    setIsPlaying(false)
    if (currentStep < 64) {
      setCurrentStep(prev => prev + 1)
    }
  }

  const handleReset = () => {
    setIsPlaying(false)
    setCurrentStep(0)
  }

  // Build path data for SVG
  const pathData = TOUR.slice(0, currentStep).map(([r, c], i) => {
    const x = c * 48 + 24
    const y = r * 48 + 24
    return i === 0 ? `M ${x} ${y}` : `L ${x} ${y}`
  }).join(' ')

  // Closing path (dashed) when complete
  const closingPath = currentStep === 64 ? (() => {
    const [r1, c1] = TOUR[63]
    const [r2, c2] = TOUR[0]
    return `M ${c1 * 48 + 24} ${r1 * 48 + 24} L ${c2 * 48 + 24} ${r2 * 48 + 24}`
  })() : ''

  // Current knight position
  const knightPos = currentStep > 0 ? TOUR[currentStep - 1] : TOUR[0]
  const knightX = knightPos[1] * 48 + 24
  const knightY = knightPos[0] * 48 + 24

  // Count oblique turns so far
  const obliqueCount = [...OBLIQUE_INDICES].filter(i => i < currentStep).length

  const boardSize = compact ? 288 : 384
  const scale = boardSize / 384

  return (
    <div className={`${className}`}>
      {/* Header */}
      {!compact && (
        <div className="mb-4">
          <h3 className="text-lg font-semibold tracking-tight">
            Tour <span className="text-annotation italic">(t)</span>
          </h3>
          <p className="text-sm text-muted-foreground">
            The unique closed knight's tour with exactly 4 oblique turns
          </p>
        </div>
      )}

      <div className="flex flex-col lg:flex-row gap-6">
        {/* Board */}
        <div className="relative" style={{ width: boardSize, height: boardSize }}>
          {/* Chessboard grid */}
          <div
            className="grid grid-cols-8 absolute inset-0 border border-border rounded-sm overflow-hidden"
            style={{ width: boardSize, height: boardSize }}
          >
            {Array.from({ length: 64 }, (_, i) => {
              const row = Math.floor(i / 8)
              const col = i % 8
              const isLight = (row + col) % 2 === 0
              const isVisited = TOUR.slice(0, currentStep).some(([r, c]) => r === row && c === col)
              const isCurrent = currentStep > 0 && TOUR[currentStep - 1][0] === row && TOUR[currentStep - 1][1] === col
              const isOblique = OBLIQUE_SQUARES.some(([r, c]) => r === row && c === col)
              const isObliqueActive = isOblique && isVisited

              // Find step number for this square
              const stepNum = TOUR.findIndex(([r, c]) => r === row && c === col)
              const showNumber = stepNum !== -1 && stepNum < currentStep

              return (
                <div
                  key={i}
                  className={`
                    relative flex items-center justify-center font-mono text-xs
                    transition-all duration-300
                    ${isLight ? 'bg-[oklch(0.16_0_0)]' : 'bg-[oklch(0.12_0_0)]'}
                    ${isCurrent ? 'bg-annotation/30 ring-2 ring-annotation ring-inset' : ''}
                  `}
                >
                  {/* Oblique marker */}
                  {isOblique && (
                    <div
                      className={`
                        absolute inset-1 border-2 border-destructive rounded-sm
                        transition-opacity duration-500
                        ${isObliqueActive ? 'opacity-100' : 'opacity-20'}
                      `}
                    />
                  )}
                  {/* Step number */}
                  {showNumber && (
                    <span className={`
                      text-[10px] font-medium z-10
                      ${isCurrent ? 'text-annotation' : 'text-muted-foreground/60'}
                    `}>
                      {stepNum + 1}
                    </span>
                  )}
                </div>
              )
            })}
          </div>

          {/* SVG overlay for path */}
          <svg
            className="absolute inset-0 pointer-events-none"
            viewBox="0 0 384 384"
            style={{ width: boardSize, height: boardSize }}
          >
            {/* Path line */}
            {pathData && (
              <path
                d={pathData}
                fill="none"
                stroke="var(--color-annotation)"
                strokeWidth={2 / scale}
                strokeLinecap="round"
                strokeLinejoin="round"
                className="drop-shadow-[0_0_6px_var(--color-annotation)]"
              />
            )}
            {/* Closing line (dashed) */}
            {closingPath && (
              <path
                d={closingPath}
                fill="none"
                stroke="var(--color-annotation)"
                strokeWidth={2 / scale}
                strokeDasharray="4 4"
                opacity={0.5}
              />
            )}
            {/* Knight marker */}
            {currentStep > 0 && (
              <circle
                cx={knightX}
                cy={knightY}
                r={12 / scale}
                fill="var(--color-annotation)"
                className="drop-shadow-lg"
              />
            )}
          </svg>
        </div>

        {/* Controls panel */}
        <div className="flex-1 min-w-[200px]">
          {/* Playback controls */}
          <div className="flex gap-2 mb-4">
            <Button
              variant={isPlaying ? 'default' : 'outline'}
              size="sm"
              onClick={handlePlayPause}
              className="flex-1"
            >
              {isPlaying ? (
                <><Pause className="h-4 w-4 mr-1" /> Pause</>
              ) : (
                <><Play className="h-4 w-4 mr-1" /> Play</>
              )}
            </Button>
            <Button variant="outline" size="sm" onClick={handleStep}>
              <ChevronRight className="h-4 w-4" />
            </Button>
            <Button variant="outline" size="sm" onClick={handleReset}>
              <RotateCcw className="h-4 w-4" />
            </Button>
          </div>

          {/* Speed slider */}
          <div className="mb-4">
            <label className="text-xs font-mono text-muted-foreground uppercase tracking-wider">
              Speed
            </label>
            <input
              type="range"
              min={100}
              max={800}
              value={900 - speed}
              onChange={(e) => setSpeed(900 - parseInt(e.target.value))}
              className="w-full h-1 bg-border rounded-full appearance-none cursor-pointer
                         [&::-webkit-slider-thumb]:appearance-none
                         [&::-webkit-slider-thumb]:w-3 [&::-webkit-slider-thumb]:h-3
                         [&::-webkit-slider-thumb]:bg-annotation [&::-webkit-slider-thumb]:rounded-full
                         [&::-webkit-slider-thumb]:cursor-pointer"
            />
          </div>

          {/* Statistics */}
          <div className="space-y-2 text-sm font-mono">
            <div className="flex justify-between py-1 border-b border-border">
              <span className="text-muted-foreground">Move</span>
              <span>{currentStep} / 64</span>
            </div>
            <div className="flex justify-between py-1 border-b border-border">
              <span className="text-muted-foreground">Position</span>
              <span>
                {currentStep > 0
                  ? `${String.fromCharCode(97 + knightPos[1])}${8 - knightPos[0]}`
                  : '—'
                }
              </span>
            </div>
            <div className="flex justify-between py-1">
              <span className="text-muted-foreground">Oblique turns</span>
              <span className="text-destructive font-medium">{obliqueCount} / 4</span>
            </div>
          </div>

          {/* Legend */}
          <div className="mt-4 pt-4 border-t border-border space-y-2">
            <div className="flex items-center gap-2 text-xs">
              <div className="w-3 h-3 bg-annotation rounded-sm" />
              <span className="text-muted-foreground">Knight's path</span>
            </div>
            <div className="flex items-center gap-2 text-xs">
              <div className="w-3 h-3 border-2 border-destructive rounded-sm" />
              <span className="text-muted-foreground">Oblique turn (&gt;90°)</span>
            </div>
          </div>
        </div>
      </div>

      {/* Insight */}
      {!compact && (
        <p className="mt-6 text-sm text-muted-foreground leading-relaxed">
          Among the <span className="text-foreground font-medium">13,267,364,410,532</span> closed
          knight's tours on an 8×8 board, only <span className="text-destructive font-medium">four</span> achieve
          the minimum of 4 oblique turns—and these four are related by the symmetries of the square.
          This tour is <span className="italic">essentially unique</span>.
        </p>
      )}
    </div>
  )
}
