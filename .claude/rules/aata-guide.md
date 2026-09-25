---
paths:
  - "aata/**/*.md"
---

# Writing AATA transliterations (`aata/*.md`)

The `aata/` files are literate transliterations of Judson's *Abstract Algebra:
Theory and Applications* — the book's prose and development reproduced in order,
each stated result followed by a machine-checked ` ```2b4m ` proof. These rules
govern how those proofs are written. (For proof-label/naming conventions see
`CONVENTIONS.md` and `agents/style-guide.md`.)

## The import horizon — what a main-text proof may lean on

**Main text** (a theorem Judson proves in the running text): the proof FOLLOWS
JUDSON and is self-contained from the book's *own cumulative development*. Do
**not** import a `std/` library to alias the proof away — **unless "Judson would
already have it in hand at that point in the book."** The import horizon tracks
the book's cumulative build:

- The **sort / theory Judson is currently assuming** is fair to import — early
  Chapter 2 works over ℤ, so importing `std/integer*` for the ℤ sort + its ring
  and order is fine ("Judson has ℤ").
- Once **past** a chapter, later chapters may import that chapter's `std/` theory —
  past Chapter 3 (groups), later chapters may `import std/group` ("Judson has
  groups by then").
- But a theorem Judson **builds in-text** must be **proved in the main text**, not
  aliased from a `std/` library that packaged it. The Division Algorithm (from
  Well-Ordering), Bézout, Euclid's Lemma, the Fundamental Theorem of Arithmetic —
  Judson proves each in the running text, so each is transcribed as a real proof,
  **not** an alias.

**Rule of thumb:** import the *objects* Judson already has; prove the *theorems*
Judson develops.

## Exercises

In the **exercises** section you may use `std/` **liberally**, including that
section's library — except:

- An exercise whose result **the main text proves** (Judson often forwards a
  result, "the proof is left as an exercise," then it recurs, or the natural place
  to prove it is the running text): **prove it in place in the main text**, and in
  the exercise slot write **only a prose pointer — "(forwarded proof, see §X.Y)"**.
  Do **not** re-prove it, do **not** alias `std/`, and do **not** use a `forward`
  declaration for it. The exercise slot is pure prose referencing the main-text
  theorem.

## Accelerant discipline (pedagogy)

AATA files are *pedagogy* — the proof outline must read like Judson's argument.
Accelerants (`simplify`, `arithmetic`, `polynomial`, `assoc`, `tautology`, …) are
allowed **in general**, but **not for the steps Judson spells out**. When the book
shows a key inference step-by-step, transcribe it as explicit kernel steps so the
proof mirrors the book's reasoning. Reserve accelerants for the algebraic drudgery
the book *elides* — "clearly `a − bq − b = r − b`", ring rearrangements, normal-form
equalities: the moves a human reader also skips.

(Contrast `std/*.b4m`, where the rule is the opposite: collapse to the shortest
kernel-checked proof, accelerants everywhere — no demonstrative value needed.)

## No `hole`s in transliterations

AATA proofs are WELL-KNOWN — Judson proves them; the job is to transcribe. So do
**not** use `hole` here: a hole is unfinished work dressed up as done, and a
transliteration whose proof is left as a hole hasn't been transcribed. Finish the
proof (or, if it genuinely exceeds the kernel, defer it in prose — see below —
never as a `hole`). `hole` is for *research/exploration* (spiking a construction,
sketching a skeleton), not for a proof that is known and expected to be completed.

## When something is beyond the kernel

Where a stated result exceeds what 2b4m's first-order kernel can express, keep the
prose and mark it in place — a `**Deferred:** …` note for an exercise, or a
`// this section cannot currently be encoded [reason]` block for a stated theorem —
saying exactly what it would require. Never silently drop a result.
