//! Reads tracing.folded (folded stack format from tracing-flame) from stdin
//! and prints a compact text summary: inclusive time per span, sorted by total.
//!
//! Usage:
//!   cargo run --bin `summarize_trace` < tracing.folded
//!   head -n 100000 tracing.folded | cargo run --bin `summarize_trace`
//!
//! For large traces, pipe a prefix (e.g. first 100k lines) to keep output representative.

#![allow(clippy::print_stdout, clippy::print_stderr)]

use std::collections::HashMap;
use std::io::{self, BufRead};
use std::process::exit;

fn main() {
    let stdin = io::stdin();
    let mut reader = stdin.lock();
    let mut inclusive: HashMap<String, u64> = HashMap::new();
    let mut total_samples: u64 = 0;
    let mut line_count: u64 = 0;

    let mut buf = String::new();
    while reader.read_line(&mut buf).unwrap() > 0 {
        let line = buf.trim_end().to_string();
        buf.clear();

        if line.is_empty() {
            continue;
        }

        line_count += 1;

        // Folded format: "frame1; frame2; frame3 <value>"
        let value_start = line.rfind(' ').unwrap_or(0);
        let (stack, value_str) = line.split_at(value_start);
        let value: u64 = value_str.trim().parse().unwrap_or(0);
        total_samples += value;

        for frame in stack.split("; ") {
            let frame = frame.trim();
            if frame.is_empty() {
                continue;
            }
            *inclusive.entry(frame.to_string()).or_insert(0) += value;
        }
    }

    if inclusive.is_empty() {
        eprintln!("No folded lines read. Pipe tracing.folded (or a prefix) into stdin.");
        exit(1);
    }

    let mut by_total: Vec<_> = inclusive.into_iter().collect();
    by_total.sort_by(|a, b| b.1.cmp(&a.1));

    println!(
        "Trace summary (inclusive samples) — {} lines, {} total samples\n",
        line_count, total_samples
    );
    println!("{:<70} {:>12} {:>8}", "SPAN", "SAMPLES", "%");
    println!("{}", "-".repeat(92));

    for (name, samples) in by_total.iter().take(40) {
        let pct = if total_samples > 0 {
            (100.0 * *samples as f64) / total_samples as f64
        } else {
            0.0
        };
        let short = if name.len() > 68 {
            format!("{}..", &name[..66])
        } else {
            name.clone()
        };
        println!("{:<70} {:>12} {:>7.2}%", short, samples, pct);
    }
}
