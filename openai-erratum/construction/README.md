# `construction/` — the assumption that swallows the paper

This directory isolates ONE axiom, because flipping it casually would make the whole exercise
worthless.

`aMarkedAlgebraicClassExistsAtSomeGoodPeriod` is Proposition 12.3 of the withdrawn
manuscript. Its proof cites Proposition 11.4, which rests on Section 11, which rests on
Sections 8–10, which rest on the weighted Floer module of Sections 4–7, which rests on the
Lagrangian of Section 3, which rests on §3.4's stabilization traces.

**The withdrawn sign error is inside this assumption.** OpenAI's `history.md` says the error
"invalidates a stabilization-trace cancellation argument"; §3.4 is where the paper uses the
stabilization traces of its reference [6]. So assuming this axiom assumes away precisely the
step that failed.

It is still stated, because without it nothing downstream can be checked at all — and what
*can* be checked is worth checking: given a marked class at one good period, does Theorem 1.1
follow? That question is answerable and the answer is yes. But the axiom must be labelled, not
buried in a list beside "the cycle class map is functorial".
