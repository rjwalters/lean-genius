//! Find the unique knight's tour with exactly 4 obtuse angles.
//!
//! Based on Knuth's fasc8a.pdf: Among all ~13 trillion closed knight's tours,
//! exactly 4 achieve the minimum of 4 obtuse angles (D4-equivalent = 1 unique tour).
//!
//! Strategy:
//! 1. Use backtracking to enumerate closed knight's tours
//! 2. Track obtuse angle count incrementally during construction
//! 3. Prune branches that already exceed 4 obtuse angles
//! 4. Stop when we find a tour with exactly 4 obtuse angles

use std::time::Instant;

/// Knight move offsets (dr, dc)
const KNIGHT_MOVES: [(i8, i8); 8] = [
    (1, 2), (2, 1), (2, -1), (1, -2),
    (-1, -2), (-2, -1), (-2, 1), (-1, 2),
];

/// A square on the board
type Square = (u8, u8);

/// Get all valid knight moves from a square
fn get_neighbors(r: u8, c: u8) -> Vec<Square> {
    let mut neighbors = Vec::with_capacity(8);
    for (dr, dc) in KNIGHT_MOVES {
        let nr = r as i8 + dr;
        let nc = c as i8 + dc;
        if nr >= 0 && nr < 8 && nc >= 0 && nc < 8 {
            neighbors.push((nr as u8, nc as u8));
        }
    }
    neighbors
}

/// Compute dot product of two move vectors
#[inline]
fn dot_product(v1: (i8, i8), v2: (i8, i8)) -> i16 {
    (v1.0 as i16 * v2.0 as i16) + (v1.1 as i16 * v2.1 as i16)
}

/// Check if angle between two consecutive moves is obtuse (> 90 degrees)
/// This happens when dot product is negative
#[inline]
fn is_obtuse(from1: Square, middle: Square, to: Square) -> bool {
    let v1 = (middle.0 as i8 - from1.0 as i8, middle.1 as i8 - from1.1 as i8);
    let v2 = (to.0 as i8 - middle.0 as i8, to.1 as i8 - middle.1 as i8);
    dot_product(v1, v2) < 0
}

/// Count neighbors that haven't been visited
#[inline]
fn count_unvisited_neighbors(r: u8, c: u8, visited: &[[bool; 8]; 8]) -> usize {
    get_neighbors(r, c).iter().filter(|(nr, nc)| !visited[*nr as usize][*nc as usize]).count()
}

/// Main tour finder using backtracking with pruning
struct TourFinder {
    tour: Vec<Square>,
    visited: [[bool; 8]; 8],
    obtuse_count: u32,
    target_obtuse: u32,
    tours_found: u64,
    nodes_explored: u64,
    best_tour: Option<Vec<Square>>,
    best_obtuse: u32,
}

impl TourFinder {
    fn new(target_obtuse: u32) -> Self {
        Self {
            tour: Vec::with_capacity(64),
            visited: [[false; 8]; 8],
            obtuse_count: 0,
            target_obtuse,
            tours_found: 0,
            nodes_explored: 0,
            best_tour: None,
            best_obtuse: u32::MAX,
        }
    }

    /// Check if adding a move creates an obtuse angle at the previous position
    fn would_create_obtuse(&self, next: Square) -> bool {
        if self.tour.len() < 2 {
            return false;
        }
        let prev = self.tour[self.tour.len() - 2];
        let curr = self.tour[self.tour.len() - 1];
        is_obtuse(prev, curr, next)
    }

    /// Check obtuse angle when closing the tour
    fn closing_obtuse_count(&self) -> u32 {
        if self.tour.len() != 64 {
            return 0;
        }
        let mut count = 0;

        // Check angle at position 63 (last -> first -> second)
        let last = self.tour[63];
        let first = self.tour[0];
        let second = self.tour[1];
        if is_obtuse(last, first, second) {
            count += 1;
        }

        // Check angle at position 62 (second-to-last -> last -> first)
        let second_last = self.tour[62];
        if is_obtuse(second_last, last, first) {
            count += 1;
        }

        count
    }

    /// Backtracking search
    fn search(&mut self, depth: usize) -> bool {
        self.nodes_explored += 1;

        if depth == 64 {
            // Check if tour is closed (last square can reach first)
            let last = self.tour[63];
            let first = self.tour[0];

            let neighbors = get_neighbors(last.0, last.1);
            if !neighbors.contains(&first) {
                return false; // Not a closed tour
            }

            // Count closing obtuse angles
            let closing_obtuse = self.closing_obtuse_count();
            let total_obtuse = self.obtuse_count + closing_obtuse;

            self.tours_found += 1;

            if total_obtuse < self.best_obtuse {
                self.best_obtuse = total_obtuse;
                self.best_tour = Some(self.tour.clone());
                println!("Found tour with {} obtuse angles (tours checked: {})",
                         total_obtuse, self.tours_found);

                if total_obtuse == self.target_obtuse {
                    return true; // Found target!
                }
            }

            return false;
        }

        let (r, c) = self.tour[depth - 1];
        let mut neighbors = get_neighbors(r, c);

        // Warnsdorf-style heuristic: prefer squares with fewer unvisited neighbors
        neighbors.sort_by_key(|(nr, nc)| count_unvisited_neighbors(*nr, *nc, &self.visited));

        for next in neighbors {
            if self.visited[next.0 as usize][next.1 as usize] {
                continue;
            }

            // Check if this move would create an obtuse angle
            let creates_obtuse = self.would_create_obtuse(next);

            // Prune if we'd exceed target obtuse count
            // (allowing +2 for closing angles we haven't counted yet)
            if creates_obtuse && self.obtuse_count + 1 > self.target_obtuse + 2 {
                continue;
            }

            // Make move
            self.tour.push(next);
            self.visited[next.0 as usize][next.1 as usize] = true;
            if creates_obtuse {
                self.obtuse_count += 1;
            }

            // Recurse
            if self.search(depth + 1) {
                return true;
            }

            // Unmake move
            self.tour.pop();
            self.visited[next.0 as usize][next.1 as usize] = false;
            if creates_obtuse {
                self.obtuse_count -= 1;
            }
        }

        false
    }

    /// Start search from a given square
    fn find_from(&mut self, start: Square) -> bool {
        self.tour.clear();
        self.visited = [[false; 8]; 8];
        self.obtuse_count = 0;

        self.tour.push(start);
        self.visited[start.0 as usize][start.1 as usize] = true;

        self.search(1)
    }
}

fn format_tour(tour: &[Square]) -> String {
    let mut lines = vec!["[".to_string()];
    for (i, (r, c)) in tour.iter().enumerate() {
        let comma = if i < tour.len() - 1 { "," } else { "" };
        lines.push(format!("  ({}, {}){}", r, c, comma));
    }
    lines.push("]".to_string());
    lines.join("\n")
}

fn main() {
    println!("Finding knight's tour with exactly 4 obtuse angles...\n");

    let start_time = Instant::now();
    let mut finder = TourFinder::new(4);

    // Try starting from different squares (due to symmetry, we only need a few)
    let starting_squares: Vec<Square> = vec![
        (0, 0), (0, 1), (0, 2), (0, 3),
        (1, 1), (1, 2), (1, 3),
        (2, 2), (2, 3),
        (3, 3),
    ];

    let mut found = false;
    for start in &starting_squares {
        println!("Trying start position: {:?}", start);
        if finder.find_from(*start) {
            found = true;
            break;
        }
        println!("  Explored {} nodes, found {} tours so far, best: {} obtuse",
                 finder.nodes_explored, finder.tours_found, finder.best_obtuse);
    }

    let elapsed = start_time.elapsed();

    println!("\n{}", "=".repeat(60));
    println!("Search complete in {:.2?}", elapsed);
    println!("Total nodes explored: {}", finder.nodes_explored);
    println!("Total closed tours found: {}", finder.tours_found);
    println!("{}", "=".repeat(60));

    if let Some(ref tour) = finder.best_tour {
        println!("\nBest tour found ({} obtuse angles):", finder.best_obtuse);
        println!("{}", format_tour(tour));

        // Verify the count
        let mut verify_count = 0;
        for i in 0..64 {
            let prev = tour[(i + 63) % 64];
            let curr = tour[i];
            let next = tour[(i + 1) % 64];
            if is_obtuse(prev, curr, next) {
                verify_count += 1;
            }
        }
        println!("\nVerified obtuse angle count: {}", verify_count);

        if found {
            println!("\nSUCCESS: Found tour with exactly 4 obtuse angles!");
        }
    } else {
        println!("\nNo tour found.");
    }
}
