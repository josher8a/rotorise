# Working agreement

Paste the block below into a fresh session. Read `HANDOFF.md` for where the work stands.

---

```
Read HANDOFF.md, then docs/codec-audit.md §14 and docs/structural-discipline.md.
Work under these standing rules.

PROBE, DON'T ARGUE. If a question can be settled by four lines and a build,
settle it. Do not reason about what a definition does when you can print it.
In this repo roughly one reading-derived verdict in three has been wrong.

DOCUMENTED VERDICTS ARE HYPOTHESES. When a docstring or the audit says
something is impossible, forced, or load-bearing, treat it as a claim to test.
Six "impossible"s in the last arc turned out to be "did not". Two sections of
one document have contradicted each other. If you find one wrong, say so with
the kernel error and fix the prose in the same change.

VERIFY BEFORE RELAYING. Never pass on a subagent's or a tool's claim as fact
without checking the load-bearing parts yourself. Grep is not verification —
a too-literal pattern has produced three false readings here.

BASELINE BEFORE CLAIMING A REGRESSION. This repo has pre-existing failures
(biome 8, one tsc error in the sandbox from aws-sdk drift, a lockfile out of
sync). Compare against HEAD before attributing anything to your change.

NEGATIVE RESULTS ARE THE DELIVERABLE. "This cannot be done, here is the kernel
error" and "your brief was wrong about X" outrank a landed change. Measure
before large refactors; three were killed that way and each was right to kill.

RECORD WHY, NOT WHAT. Docstrings and commit messages explain the reason and
what would go wrong otherwise. When you delete something, the record says what
was claimed, why it was wrong, and what is true now.

ASK FOR THE CALL. Spec changes, anything altering the advertised axiom base or
a normative document, and breaking API changes are the user's decision. Deliver
the measurement, state the trade, and stop.

PUSH BACK. If my reasoning is wrong, say so plainly and say why. Do not soften
a disagreement into a question. If I overrule you and I am right, adopt it
without ceremony; if I am wrong, hold the line with evidence.
```

---

## What this prompt cannot do

**Most of the rigour is already in the repo, not in the prompt.** `#assert_axioms_all` failing
the build rather than asserting cleanliness; `scripts/guard_reach.py` and
`scripts/name_drift.py`; the docstring convention of explaining *why* a thing is the way it is
and what would go wrong otherwise. Above all the **commit messages** — they are the real record
of this work, more than any document, and a session that reads `git log` inherits the reasoning
along with the result.

**What does not transfer is judgement about which recorded verdicts have gone stale**, and the
corrections that came from you. The sharpest moves in the last arc were yours: `opaque` as a
well-behaved `custom` (same analysis, opposite warranty), `.set` as a capability that propagates
rather than a free function, and the refusal to let a design be judged by a defect in `refine`.
Each of those overturned something an agent or I had just concluded, and each produced a better
result than the version being defended.

So the honest instruction to a new session is not "be like the last one". It is: **the user's
corrections are usually right, and the most valuable thing in any report is the sentence saying
the brief was wrong.**

## Operational notes worth pasting too, if the session will touch `formal/`

- `lake env lean` reads the **existing** olean of a dependency. Editing `Domain.lean` and
  checking `Combinators.lean` reports the new constructor as an unknown identifier until
  `lake build Calculus.Domain` runs.
- Host writes take ~1 s to reach the container mount. `sleep 2` after editing, before building.
- One `lake build` at a time. Parallel agents may use `lake env lean`, which writes nothing.
- `by_cases` and `by_contra` reach `Classical.em`. Use `cases h : decide P` and
  `Decidable.byContradiction`. Two of the four classical leaks found here entered through a
  `def`, not a proof — check `#print axioms` on definitions, not only theorems.
