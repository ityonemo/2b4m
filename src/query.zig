//! `2b4m query <op>` — read-only proof-corpus navigation. Each op is its own module under
//! `query/`; this file is the namespace that groups them (a data-less Zig struct is a module).
//!
//! All but one never elaborate and never check. The exception is `instance`, which decodes a
//! `Schema{<hash>}` and therefore MUST run the prover: a hash exists only as a product of
//! elaboration, so there is nothing to read without one.

pub const outline = @import("query/outline.zig");
pub const claims = @import("query/claims.zig");
pub const theorem = @import("query/theorem.zig");
pub const whereis = @import("query/whereis.zig");
pub const search = @import("query/search.zig");
pub const uses = @import("query/uses.zig");
pub const instance = @import("query/instance.zig");
