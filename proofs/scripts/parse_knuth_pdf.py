#!/usr/bin/env python3
"""
Parse Knuth's fasc8a.pdf to extract knight's tour coordinates.

The unique tour with exactly 4 obtuse/oblique angles is shown in Fig. A-19(t) on page 90.

Usage:
    pip install pymupdf
    python scripts/parse_knuth_pdf.py

The PDF is at: data/knuth/fasc8a.pdf

Key pages:
    - Page 90 (index 89): Fig. A-19 with tours (a)-(u) including tour (t)
    - Page 91 (index 90): More Fig. A-19 tours (p)-(x)
    - Page 92 (index 91): Discussion of angle statistics for knight's tours
    - Page 93-94: Detailed tour data grids
"""

import sys
import os
from pathlib import Path

# Get project root
SCRIPT_DIR = Path(__file__).parent
PROJECT_ROOT = SCRIPT_DIR.parent
PDF_PATH = PROJECT_ROOT / "data" / "knuth" / "fasc8a.pdf"

def check_dependencies():
    """Check if required libraries are installed."""
    try:
        import fitz  # PyMuPDF
        return True
    except ImportError:
        print("PyMuPDF not installed. Install with:")
        print("  pip install pymupdf")
        return False

def extract_page_text(page_num: int) -> str:
    """Extract text from a specific page (0-indexed)."""
    import fitz
    doc = fitz.open(PDF_PATH)
    if page_num >= len(doc):
        return f"Page {page_num} out of range (doc has {len(doc)} pages)"
    page = doc[page_num]
    text = page.get_text()
    doc.close()
    return text

def extract_page_range(start: int, end: int) -> str:
    """Extract text from a range of pages (0-indexed, inclusive)."""
    import fitz
    doc = fitz.open(PDF_PATH)
    texts = []
    for i in range(start, min(end + 1, len(doc))):
        page = doc[i]
        texts.append(f"=== PAGE {i + 1} ===\n{page.get_text()}")
    doc.close()
    return "\n\n".join(texts)

def find_figure_pages(figure_name: str) -> list:
    """Search for pages containing a figure reference."""
    import fitz
    doc = fitz.open(PDF_PATH)
    results = []
    for i, page in enumerate(doc):
        text = page.get_text()
        if figure_name.lower() in text.lower():
            results.append((i + 1, text[:500]))  # Page num (1-indexed) + preview
    doc.close()
    return results

def extract_images_from_page(page_num: int, output_dir: Path = None):
    """Extract all images from a page."""
    import fitz
    if output_dir is None:
        output_dir = PROJECT_ROOT / "data" / "knuth" / "images"
    output_dir.mkdir(parents=True, exist_ok=True)

    doc = fitz.open(PDF_PATH)
    page = doc[page_num]
    images = page.get_images()

    print(f"Page {page_num + 1} has {len(images)} images")

    for img_idx, img in enumerate(images):
        xref = img[0]
        base_image = doc.extract_image(xref)
        image_bytes = base_image["image"]
        image_ext = base_image["ext"]

        output_path = output_dir / f"page{page_num + 1}_img{img_idx + 1}.{image_ext}"
        with open(output_path, "wb") as f:
            f.write(image_bytes)
        print(f"  Saved: {output_path}")

    doc.close()
    return len(images)

def get_pdf_info():
    """Get basic info about the PDF."""
    import fitz
    doc = fitz.open(PDF_PATH)
    info = {
        "pages": len(doc),
        "title": doc.metadata.get("title", "Unknown"),
        "author": doc.metadata.get("author", "Unknown"),
    }
    doc.close()
    return info


def render_page_as_image(page_num: int, dpi: int = 300, output_dir: Path = None):
    """Render a page as a PNG image."""
    import fitz
    if output_dir is None:
        output_dir = PROJECT_ROOT / "data" / "knuth" / "pages"
    output_dir.mkdir(parents=True, exist_ok=True)

    doc = fitz.open(PDF_PATH)
    page = doc[page_num - 1]  # Convert to 0-indexed
    pix = page.get_pixmap(dpi=dpi)
    output_path = output_dir / f"page{page_num}.png"
    pix.save(str(output_path))
    doc.close()
    print(f"Saved: {output_path}")
    return output_path


def render_figure_a19_t(dpi: int = 600, output_dir: Path = None):
    """Render tour (t) from Fig. A-19 on page 90."""
    import fitz
    if output_dir is None:
        output_dir = PROJECT_ROOT / "data" / "knuth" / "pages"
    output_dir.mkdir(parents=True, exist_ok=True)

    doc = fitz.open(PDF_PATH)
    page = doc[89]  # Page 90, 0-indexed

    # Crop coordinates for tour (t) - middle column, bottom row
    # Page is 612x792 points. Fig A-19 has 4 rows x 3 cols of subfigures.
    # Row 4: (s) left, (t) middle, (u) right - labels appear below each tour
    # Tour (t) is the middle diagram - isolated crop
    x_start, y_start = 222, 450
    width, height = 108, 105

    clip = fitz.Rect(x_start, y_start, x_start + width, y_start + height)
    pix = page.get_pixmap(clip=clip, dpi=dpi)

    output_path = output_dir / "tour_t.png"
    pix.save(str(output_path))
    doc.close()
    print(f"Saved tour (t): {output_path}")
    return output_path


def is_knight_move(s1: tuple, s2: tuple) -> bool:
    """Check if s1 to s2 is a valid knight move."""
    dx = abs(s1[0] - s2[0])
    dy = abs(s1[1] - s2[1])
    return (dx == 1 and dy == 2) or (dx == 2 and dy == 1)


def validate_knight_tour(tour: list) -> tuple:
    """
    Validate a knight's tour sequence.

    Args:
        tour: List of 64 (row, col) tuples, 0-indexed

    Returns:
        (is_valid, errors) tuple
    """
    errors = []

    # Check length
    if len(tour) != 64:
        errors.append(f"Tour has {len(tour)} squares, expected 64")

    # Check all squares are unique and in range
    seen = set()
    for i, sq in enumerate(tour):
        if not (0 <= sq[0] < 8 and 0 <= sq[1] < 8):
            errors.append(f"Square {i}: {sq} out of range")
        if sq in seen:
            errors.append(f"Square {i}: {sq} is duplicate")
        seen.add(sq)

    # Check all 64 squares visited
    if len(seen) != 64:
        errors.append(f"Only {len(seen)} unique squares visited")

    # Check all moves are valid knight moves
    for i in range(len(tour)):
        s1 = tour[i]
        s2 = tour[(i + 1) % len(tour)]
        if not is_knight_move(s1, s2):
            errors.append(f"Move {i}: {s1} -> {s2} is not a valid knight move")

    return (len(errors) == 0, errors)


def count_oblique_turns(tour: list) -> int:
    """
    Count oblique (obtuse) turns in a closed knight's tour.

    An oblique turn occurs when the angle between consecutive moves is > 90°,
    i.e., when the dot product of move vectors is negative.

    Args:
        tour: List of 64 (row, col) tuples

    Returns:
        Number of oblique turns
    """
    def get_move_vector(s1, s2):
        return (s2[0] - s1[0], s2[1] - s1[1])

    def dot_product(v1, v2):
        return v1[0] * v2[0] + v1[1] * v2[1]

    n = len(tour)
    count = 0

    for i in range(n):
        # Move from tour[i-1] to tour[i]
        v1 = get_move_vector(tour[(i - 1) % n], tour[i])
        # Move from tour[i] to tour[i+1]
        v2 = get_move_vector(tour[i], tour[(i + 1) % n])

        if dot_product(v1, v2) < 0:
            count += 1

    return count


def tour_to_lean_format(tour: list) -> str:
    """Convert a tour to Lean list format."""
    squares = [f"(⟨{r}, by omega⟩, ⟨{c}, by omega⟩)" for r, c in tour]
    return "[\n  " + ",\n  ".join(squares) + "\n]"


# ============================================================================
# COMPUTATIONAL RECONSTRUCTION OF TOUR (t)
# ============================================================================
# Key insight: Tour (t) has exactly 4 oblique turns, and all must be at corners.
# So we search for tours where every non-corner has a non-oblique turn.

CORNERS = frozenset([(0, 0), (0, 7), (7, 0), (7, 7)])

def knight_neighbors(r: int, c: int) -> list:
    """Return valid knight moves from (r, c) on 8x8 board."""
    moves = [(1,2), (2,1), (2,-1), (1,-2), (-1,-2), (-2,-1), (-2,1), (-1,2)]
    neighbors = []
    for dr, dc in moves:
        nr, nc = r + dr, c + dc
        if 0 <= nr < 8 and 0 <= nc < 8:
            neighbors.append((nr, nc))
    return neighbors

def get_vec(p1: tuple, p2: tuple) -> tuple:
    """Get move vector from p1 to p2."""
    return (p2[0] - p1[0], p2[1] - p1[1])

def dot(v1: tuple, v2: tuple) -> int:
    """Dot product of two vectors."""
    return v1[0] * v2[0] + v1[1] * v2[1]

def is_oblique_turn(p_prev: tuple, p_curr: tuple, p_next: tuple) -> bool:
    """Check if the turn at p_curr is oblique (dot product < 0)."""
    v_in = get_vec(p_prev, p_curr)
    v_out = get_vec(p_curr, p_next)
    return dot(v_in, v_out) < 0

def warnsdorff_score(pos: tuple, visited: set) -> int:
    """Count unvisited neighbors (for Warnsdorff heuristic)."""
    return sum(1 for n in knight_neighbors(*pos) if n not in visited)

def find_minimal_oblique_tour(verbose: bool = False, max_nodes: int = 50_000_000) -> list:
    """
    Find THE unique tour with exactly 4 oblique turns (all at corners).

    Strategy:
    - Start from corner (0,0), first move to (2,1) to break symmetry
    - At each step, prune moves that would create oblique at non-corner
    - Use Warnsdorff heuristic to order candidates (visit constrained squares first)
    - Aggressive pruning: check if unvisited squares can still be reached
    """

    start = (0, 0)

    call_count = [0]
    found_tour = [None]

    def has_unvisited_with_no_exit(visited: set, current: tuple) -> bool:
        """Check if any unvisited square has become unreachable."""
        for r in range(8):
            for c in range(8):
                if (r, c) in visited or (r, c) == current:
                    continue
                # Count unvisited neighbors
                neighbors = knight_neighbors(r, c)
                unvisited_neighbors = sum(1 for n in neighbors if n not in visited)
                if unvisited_neighbors == 0:
                    return True  # Dead end detected
        return False

    def count_compatible_exits(pos: tuple, prev: tuple, visited: set) -> int:
        """Count exits from pos that don't create oblique (if not corner)."""
        if pos in CORNERS:
            return sum(1 for n in knight_neighbors(*pos) if n not in visited)

        v_in = get_vec(prev, pos)
        count = 0
        for next_pos in knight_neighbors(*pos):
            if next_pos in visited:
                continue
            v_out = get_vec(pos, next_pos)
            if dot(v_in, v_out) >= 0:  # Non-oblique
                count += 1
        return count

    def search(tour: list, visited: set) -> bool:
        call_count[0] += 1

        if call_count[0] > max_nodes:
            return False

        if call_count[0] % 1_000_000 == 0 and verbose:
            print(f"  ... {call_count[0] // 1_000_000}M nodes, depth {len(tour)}")

        if len(tour) == 64:
            # Check if we can close the cycle
            if is_knight_move(tour[-1], tour[0]):
                # CRITICAL: Also check turn at tour[-1] when closing!
                # Turn at tour[-1]: from tour[-2] to tour[-1] to tour[0]
                if tour[-1] not in CORNERS:
                    if is_oblique_turn(tour[-2], tour[-1], tour[0]):
                        return False  # Would create oblique at non-corner
                found_tour[0] = list(tour)
                return True
            return False

        current = tour[-1]
        candidates = []

        for next_pos in knight_neighbors(*current):
            if next_pos in visited:
                continue

            # Key pruning: reject if this creates oblique at non-corner
            if len(tour) >= 2:
                if is_oblique_turn(tour[-2], current, next_pos):
                    if current not in CORNERS:
                        continue  # Prune!

            # Warnsdorff score for ordering (lower = more constrained = try first)
            score = warnsdorff_score(next_pos, visited)

            # Extra pruning: check compatible exits from next_pos
            if len(tour) >= 1:
                compat = count_compatible_exits(next_pos, current, visited | {next_pos})
                if compat == 0 and len(tour) < 63:  # Dead end unless we're almost done
                    continue
                # Prefer positions with fewer compatible exits (more constrained)
                score = (score, compat)

            # Late-stage pruning: can we still return to start?
            if len(tour) >= 55:
                # Check if start is still reachable
                start_neighbors = knight_neighbors(0, 0)
                reachable = any(n not in visited and n != next_pos for n in start_neighbors)
                if not reachable and next_pos not in start_neighbors:
                    continue

            candidates.append((score, next_pos))

        # Sort by Warnsdorff (visit most constrained first)
        candidates.sort(key=lambda x: x[0])

        for _, next_pos in candidates:
            visited.add(next_pos)
            tour.append(next_pos)

            if search(tour, visited):
                return True

            tour.pop()
            visited.remove(next_pos)

        return False

    if verbose:
        print("Searching for minimal oblique tour...")
        print("Constraint: oblique turns only at corners")

    # Try both first moves
    for first in [(2, 1), (1, 2)]:
        if verbose:
            print(f"Trying first move: {start} -> {first}")

        tour = [start, first]
        visited = {start, first}
        call_count[0] = 0

        if search(tour, visited):
            if verbose:
                print(f"Search completed: {call_count[0]} nodes explored")
            return found_tour[0]

        if verbose:
            print(f"  No solution with this first move ({call_count[0]} nodes)")

    return None


def reconstruct_tour_t() -> list:
    """
    Reconstruct tour (t) from Knuth's Fig. A-19.

    This is THE unique closed knight's tour with exactly 4 oblique turns.
    """
    tour = find_minimal_oblique_tour(verbose=True)

    if tour:
        is_valid, errors = validate_knight_tour(tour)
        oblique = count_oblique_turns(tour)

        print(f"\nValidation: {'✓ Valid' if is_valid else '✗ Invalid'}")
        print(f"Oblique turns: {oblique}")

        if is_valid and oblique == 4:
            print("\n🎉 SUCCESS! Found the unique minimal oblique tour (t)!")
            return tour
        else:
            print(f"Errors: {errors}")
    else:
        print("No tour found - this shouldn't happen!")

    return None

def search_for_tour_coordinates():
    """Search for knight's tour coordinate patterns in the PDF."""
    import fitz
    import re

    doc = fitz.open(PDF_PATH)

    # Knight tour coordinates often appear as sequences like:
    # a1, b3, c1, ... or as numbered squares 0-63
    # Or in algebraic notation: a1-b3-c1 etc.

    tour_patterns = [
        r'[a-h][1-8][-–][a-h][1-8]',  # Algebraic moves
        r'\b[0-5]?[0-9]\s*[-–,]\s*[0-5]?[0-9]\b',  # Numbered squares
        r'Fig\.\s*A[-–]?19\s*\(?t\)?',  # The specific figure
    ]

    results = []
    for i, page in enumerate(doc):
        text = page.get_text()
        for pattern in tour_patterns:
            matches = re.findall(pattern, text, re.IGNORECASE)
            if matches:
                results.append((i + 1, pattern, matches[:10]))  # First 10 matches

    doc.close()
    return results

def main():
    if not PDF_PATH.exists():
        print(f"PDF not found at: {PDF_PATH}")
        print("Please ensure fasc8a.pdf is in data/knuth/")
        sys.exit(1)

    if not check_dependencies():
        sys.exit(1)

    import argparse
    parser = argparse.ArgumentParser(description="Parse Knuth's fasc8a.pdf")
    parser.add_argument("--info", action="store_true", help="Show PDF info")
    parser.add_argument("--page", type=int, help="Extract text from page (1-indexed)")
    parser.add_argument("--range", nargs=2, type=int, metavar=("START", "END"),
                       help="Extract pages (1-indexed, inclusive)")
    parser.add_argument("--find", type=str, help="Find pages with figure/text")
    parser.add_argument("--images", type=int, help="Extract images from page (1-indexed)")
    parser.add_argument("--search-tours", action="store_true",
                       help="Search for tour coordinate patterns")
    parser.add_argument("--render", type=int, help="Render page as PNG (1-indexed)")
    parser.add_argument("--render-tour-t", action="store_true",
                       help="Render tour (t) from Fig. A-19")
    parser.add_argument("--validate", type=str,
                       help="Validate a tour from JSON file")
    parser.add_argument("--dpi", type=int, default=300, help="DPI for rendering")
    parser.add_argument("--reconstruct", action="store_true",
                       help="Reconstruct tour (t) computationally")
    parser.add_argument("--output-lean", type=str,
                       help="Output tour in Lean format to file")

    args = parser.parse_args()

    if args.info:
        info = get_pdf_info()
        print(f"PDF: {PDF_PATH}")
        print(f"Pages: {info['pages']}")
        print(f"Title: {info['title']}")
        print(f"Author: {info['author']}")

    elif args.page:
        print(extract_page_text(args.page - 1))

    elif args.range:
        print(extract_page_range(args.range[0] - 1, args.range[1] - 1))

    elif args.find:
        results = find_figure_pages(args.find)
        if results:
            print(f"Found '{args.find}' on {len(results)} page(s):")
            for page_num, preview in results:
                print(f"\n=== Page {page_num} ===")
                print(preview[:300] + "...")
        else:
            print(f"'{args.find}' not found in PDF")

    elif args.images:
        extract_images_from_page(args.images - 1)

    elif args.search_tours:
        results = search_for_tour_coordinates()
        for page, pattern, matches in results:
            print(f"Page {page} ({pattern}): {matches}")

    elif args.render:
        render_page_as_image(args.render, dpi=args.dpi)

    elif args.render_tour_t:
        render_figure_a19_t(dpi=args.dpi)

    elif args.validate:
        import json
        with open(args.validate) as f:
            tour_data = json.load(f)
        tour = [tuple(sq) for sq in tour_data]
        is_valid, errors = validate_knight_tour(tour)
        if is_valid:
            oblique = count_oblique_turns(tour)
            print(f"✓ Valid knight's tour with {oblique} oblique turns")
            if oblique == 4:
                print("  This matches the minimum! (Unique tour from Knuth)")
                print("\nLean format:")
                print(tour_to_lean_format(tour))
        else:
            print("✗ Invalid tour:")
            for err in errors:
                print(f"  - {err}")

    elif args.reconstruct:
        tour = reconstruct_tour_t()
        if tour and args.output_lean:
            lean_code = tour_to_lean_format(tour)
            with open(args.output_lean, 'w') as f:
                f.write(lean_code)
            print(f"\nLean format written to: {args.output_lean}")
        elif tour:
            print("\nTour as coordinate list:")
            print(tour)
            print("\nLean format:")
            print(tour_to_lean_format(tour))

    else:
        parser.print_help()
        print("\n--- Quick Start ---")
        print("1. python scripts/parse_knuth_pdf.py --info")
        print("2. python scripts/parse_knuth_pdf.py --find 'obtuse'")
        print("3. python scripts/parse_knuth_pdf.py --page 90   # Fig. A-19 with tour (t)")
        print("4. python scripts/parse_knuth_pdf.py --render-tour-t --dpi 600")
        print("5. python scripts/parse_knuth_pdf.py --validate tour.json")
        print("\n--- Key Pages ---")
        print("Page 90: Fig. A-19 with tour (t) - the unique tour with 4 oblique turns")
        print("Page 92: Discussion of angle statistics")

if __name__ == "__main__":
    main()
