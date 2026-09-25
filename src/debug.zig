//! `2b4m debug <op>` — proof-machinery introspection. Each op is its own module
//! under `debug/`; this file is the namespace that groups them (a data-less Zig
//! struct is a module).

/// per proof, every accelerated step at its file:line:col — where trust enters
pub const taint = @import("debug/taint.zig");
/// reprint the synthetic theorem an accelerated step produced, as re-parseable 2b4m
pub const accelerant = @import("debug/accelerant.zig");
