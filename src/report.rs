//! Render reporting.

use std::time::{Duration, Instant};

/// Stores report state.
pub enum ReportState {
    /// No state.
    None,
    /// The state for reporting every Nth row.
    Row(u32),
    /// The last instant been reported.
    Duration(Instant),
}

/// Specifies report settings when rendering.
#[derive(Copy, Clone)]
pub enum Report {
    /// No report.
    None,
    /// Report every Nth row.
    Row(u32),
    /// Report every duration.
    Duration(Duration),
}

impl Report {
    /// Gets the start state of reporting.
    pub fn start(&self) -> ReportState {
        match self {
            Report::None => ReportState::None,
            Report::Row(_) => ReportState::Row(0),
            Report::Duration(_) => ReportState::Duration(Instant::now()),
        }
    }

    /// Update the report state and return `true` if should report.
    pub fn update(&self, state: &mut ReportState, row: u32) -> bool {
        use ReportState::*;
        match (self, state) {
            (Report::None, None) => false,
            (Report::Row(n), Row(last)) => {
                if row >= *last + n {
                    *last += n;
                    true
                } else {false}
            }
            (Report::Duration(dur), Duration(last)) => {
                let now = Instant::now();
                if now >= *last + *dur {
                    *last = now;
                    true
                } else {false}
            }
            _ => false,
        }
    }
}
