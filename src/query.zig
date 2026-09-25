//! `2b4m query <op>` — read-only proof-corpus navigation (never elaborates,
//! never checks). Each op is its own module under `query/`; this file is the
//! namespace that groups them (a data-less Zig struct is a module).

pub const outline = @import("query/outline.zig");
pub const claims = @import("query/claims.zig");
pub const theorem = @import("query/theorem.zig");
pub const whereis = @import("query/whereis.zig");
pub const search = @import("query/search.zig");
pub const uses = @import("query/uses.zig");
