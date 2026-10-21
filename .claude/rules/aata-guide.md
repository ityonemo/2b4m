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

## Fidelity: this is a TRANSLITERATION, not a paraphrase

Judson's text is GFDL, so his words may and SHOULD be carried essentially verbatim. "Near
exact transliteration, otherwise this exercise is nonsensical" (user ruling, 2026-10-21).
The transcription exception covers NAMES AND NOTATION only — rename symbols freely, but his
SENTENCES are not yours to rewrite, shorten, or reorder.

Three failure modes, all defects, all found at scale in the 2026-10-21 audit:

- **TRUNCATION** — his sentences dropped. A displayed computation collapsed to its result is
  this, not concision: he writes `r' = a - dq = a - (ar+bs)q = a - arq - bsq = a(1-rq) + b(-sq)`
  and "the identity $r' = a(1-rq) + b(-sq)$" is a defect.
- **SILENT PARAPHRASE** — his sentence rewritten in your words.
- **NARRATION** — your commentary ABOUT his argument standing in for his text ("Judson's
  chain", "what his proof turns on", "he proves this in two moves").

**Your own prose must be visibly yours.** Scaffolding a formalization needs — "three ring
facts come first", "the peel step shared by both inductions" — goes in a `>` blockquote
aside, never in the transliterated flow where a reader cannot tell it from the source.

### The four aside exceptions

A `>` aside is the only place to say "Judson …", and only for:

- **(a)** a real language limit;
- **(b)** an infeasible calculation;
- **(c)** a deliberate divergence, reading "Judson does X, we are doing Y";
- **(d)** a **divergent proof structure** — a different axiomatic strategy where reconciling
  with his would be disproportionate. Name his structure and yours.

Import-horizon reasoning ("which Judson has in hand by this point") is a defect, not an
exception. Attribution headers stay. `**Deferred:**` / `**Skipped**` blocks stay verbatim.

### The one body-prose exception

Where he leaves a proof as an exercise and you supply one, **supplying it is the point** —
the proof stays. But the body prose must read:

> Judson's text leaves this proof as an exercise:

immediately before your `**Proof.**`. That attribution is what makes the following argument
honestly yours rather than his. Deleting his "we leave the proof as an exercise" and
substituting a bare `**Proof.**` misattributes your argument to him.

### Scope

- **Numerics are NOT in scope** — his numeric worked examples and figures are not
  transliterated. Where one carries a general remark, keep the remark. Declare the omission
  rather than leaving a silent gap, and never let a header claim completeness it does not
  have.
- **A result he states FLATLY has no proof structure to transcribe** — a citation is correct
  there. A one-line `[using model(M) …]` can be the FAITHFUL rendering: his §9.2 product-law
  proof is "follows directly from the associativity of $G$ and $H$", and expanding that into
  steps would be less faithful, not more.
- **Chapter 7's cryptography exposition** may be elided wholesale with one declaration.

### Auditing fidelity

`drafts/aata-conformance/` scores each of our paragraphs against its best match among his:
coverage (fraction of HIS words we carry → truncation) and fidelity (fraction of OURS that
are his → paraphrase).

    python3 drafts/aata-conformance/extract.py judson.json
    python3 drafts/aata-conformance/compare.py judson.json cmp.json

**It has a blind spot that hid the worst defects: it scores paragraphs we WROTE, so it
cannot see paragraphs we DROPPED.** 35 of the audit's 159 defects were found only by
scanning HIS side for passages with no counterpart in ours — a missing theorem statement, a
missing definition the corpus depended on, a subsection the file's own title promised. Always
run both directions.

**And read the XML before editing.** Twice during the audit a passage that looked like ours
turned out to be his verbatim. Three agents clearing 47 flagged paragraphs as faithful was as
valuable as the defects they found.
