//! `bpa debug <op>` — proof-machinery introspection. Each op is its own module
//! under `debug/`; this file is the namespace that groups them (a data-less Zig
//! struct is a module).

/// per proof, every accelerated step at its file:line:col — where trust enters
pub const taint = @import("debug/taint.zig");
