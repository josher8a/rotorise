# Handoff

**Branch `wip/map-types`. `lake build` green and warning-free, `#assert_axioms_all` and
`#lint_calculus` over 21 modules, `guard_reach.py`, `name_drift.py` and the new
`doc_counts.py --check` all exit 0.**

Delete this file once read — it is a handoff, not a document. Read the commit messages; they are
the record, and this arc's are unusually load-bearing because most of what it produced was
measurements rather than code.

---

## The one idea, because most of the arc is an instance of it

**A description must be kept in agreement with what it describes; a question cannot drift.** That
was the previous arc's finding at the analysis rows, and this arc found it one level up: the same
thing is true of *counts*, *citations* and *commit messages*, and nothing was keeping any of them
honest.

Every count defect this month was a number typed by hand. Every dangling citation was a name a
guard could not see. And two of this arc's own commit messages claimed things that were false when
written. So the work split roughly in half: three instruments that hold the documents to the tree,
and four changes that the instruments then immediately caught drifting.

The corollary that keeps paying: **a guard that is loose in a way nobody has measured is a guard
whose passes mean less than they look like.** `name_drift.py` had been passing for months while
blind to 194 citations and deaf to 11 more.

---

## What landed

Thirteen commits since `02dc06f`, though two of them are a pair that nets to nothing.

| commit | why |
| --- | --- |
| `c66d493` | `(held)`'s held set is a definition, not a premise — `hT` restated what `Codec.through` already defines, and three of four consumers never used it |
| `0aec076` | four recorded counts re-measured; §5's `Orth` table disagreed with itself about whether a 53-line theorem was in it |
| `2e13324` | the one `Orth` row that misses by strength says so in its phase cell, not with a dash |
| `83d61df` | `name_drift.py` checks single-word citations — **and its tokenizer had been swallowing real ones** |
| `9d8a263` | `doc_counts.py`: the counts ARCHITECTURE rests on are computed and `--check`ed, not typed |
| `daa211e` | `select` over `List.attach` probed and **killed**; the obstruction was a lemma that existed and was not being called |
| `152ab6b` | `(literal)`'s `ℓ ⊆ D` becomes `GroundKind.number`'s carrier (JH's call) — `LiteralD` deleted, §8's inexact row closed by deletion |
| `90794bd` | `admA`'s `legacy` row asks instead of parting into `⊤` — the last excuse of that shape |
| `eed1b58` | six sites call `mem_of_filter_eq_singleton` instead of open-coding it |
| `1516bda` | fixes a citation `eed1b58` broke, and records that I committed past a red guard |
| `8b13204` | `MapOf.insert` and `bodySemMap`, machinery for a `(dunion)` shape that was then declined |
| `bdeb8ec` | reverts it — plumbing with no consumer is what `unreferenced.lean` cannot tell from a defect |
| `36df8e7` | `(dunion)`'s discriminator is arity one (JH's call) — **and it simplified nothing, measured** |

### The three instruments, and what each is blind to

**`scripts/name_drift.py`** now checks single-word citations, with four categories skipped by
*shape* rather than by name so the list cannot rot: module names, a fixed Lean/mathlib/keyword
list, tokens of two characters or fewer, and commit hashes. That is 194 citations it could not see,
and it caught `Item` in `README.md`'s module inventory — deleted on purpose in `f3bb956`.

**Its tokenizer was the worse bug and had been wrong for months.** `BACKTICKED` required two or
more characters between backticks, so a one-character code span (`` `7` ``, `` `N` ``, `` `q` ``,
and these documents are full of them) failed to match, the scanner resumed *inside* the pairing,
and the next match was the prose between two spans, which `.strip()` turned into a plausible
identifier. The noise was harmless. The harm was that **11 real dotted citations were swallowed
into those prose runs and never checked**, one of them dangling: `lookup_rel`, deleted in
`e9ac3be`. Blind spot remaining: a count is not a name, which is why the next instrument exists.

**`scripts/doc_counts.py`** computes twelve counts and rewrites them between
`<!-- count:NAME -->` markers; `--check` exits 1 on disagreement. Two blind spots, and the second
has the same shape as the gap it closes: it measures the **tree, not the argument** — it will say
six theorems sit in the *slot* row and cannot say *slot* is the right phase for them — and two of
§5's twenty-five discharges are named in prose beneath the by-phase table rather than in a row, so
the script carries them as a hand-written list of two names. A third limit nobody adds goes
quietly missing from the total.

**`scripts/blast_radius.lean` costs neither a constructor nor a sharpened row.** The constructor
half was already recorded. The row half was measured this arc, on the `admA .legacy` change: the
four-way partition is *identical* before and after — 75 old-only, 19 both, 136 new-only, 1433
neither — and the old-only set is unchanged name for name. It has to be. The walk measures
dependence on a **name**, and sharpening a row changes a definition's body, not who depends on it.
§5 used to say this instrument costs exactly that question; it does not, and §5 is corrected.

### A guard caught drift in the commit that introduced it, three times

Worth naming because it is the case for having them, and because two of the three caught me.

- `doc_counts.py --check` failed on `Orthogonality.lean`'s length — 951 in the document, 960 in
  the tree — drift introduced by `0aec076`, the commit that *corrected* §5's table.
- It failed again on `152ab6b`, which lengthened an *alternatives*-phase proof (70 → 75).
- `name_drift.py` went red on `eed1b58`, which deleted the last occurrence of a name its own §8
  paragraph cited. **I ran the guard, did not read its exit code, and committed anyway**, in the
  commit whose message says all four pass. `1516bda` fixes it and keeps the record rather than
  amending it away: a commit message claiming green over a red tree is the same class of defect as
  a docstring describing a row it no longer matches.

---

## Pick up here

1. **`src/`'s arity-one check — JH's call.** `(dunion)`'s discriminator is arity one in the
   calculus now. `src/` is not: `EveryOptionTagged` (`src/codec.ts`) refuses only options naming
   no literal and pairs sharing a tag, so `string('A','B')` at a discriminator is legal, and
   `codec.ts:4415` records that as deliberate — *"the whole admissible set, not one value: an
   option may answer to several tags"*. One type-level check that the literal has exactly one
   value, plus that comment, which becomes false. Keying `discriminatedUnion` by tag was
   **declined**, so its list (`codec.ts:4394`) stays.
2. **`admits`' violation list — JH's call.** `admits(c,v) ↔ !isError(c.encode(v))` is false in one
   direction, because `string`/`boolean`/`binary`/`array(string)` do not validate on `encode`.
   Making `encode` use `admits` closes it at the root and is a behaviour change.
3. **Wiring `admits` into `union`'s resolver — JH's call**, and deliberately not done. It replaces
   try-and-see with a decision and retires `identifying` (45 lines, one consumer). Depends on (2).
4. **The change log's 70 dangling names** (`codec-formalization.md` §4) — a judgement about
   whether a change log carries names of deleted things, not an edit. Note that `name_drift --all`
   now reports *more* of them, because the tokenizer fix made them visible.
5. **`fa9ce05`'s commit message** cites a regex pass as a reachability measurement. Needs a
   rebase; `scripts/unreferenced.lean` is the honest instrument for next time.

**Closed this arc, do not re-open:** `select` over `List.attach` (`daa211e` — measured, and the
ten-site count in it was six); `adm (.literal .number ls)` not exact (`152ab6b`); `admA`'s `legacy`
`⊤` row (`90794bd`); the value/attribute twin merge (ARCHITECTURE §8 — the pair count is an
artifact of its transform, three passes gave 82, 69 and 72, and the dimension that decides it is
size against similarity); bundling `Lawful` into `custom` (§4a — elaborates, buys five lines,
costs ~33 sites).

---

## Landmines

**Three Claude sessions share this working tree, and there is one index.** A peer's `git commit -a`
commits your staged *and* unstaged edits under its message, and your own commit then reports
"nothing to commit, working tree clean". That happened this arc: `2e13324` carries an edit I wrote
under another session's commit message. **Before committing, check `git log -1` as well as
`git status`** — a clean tree may mean a peer already committed your work, not that your edit
vanished. Do not rewrite a peer-authored commit to reclaim authorship; verify the content and
message are accurate and leave it. For genuinely parallel work, put one session in its own
`git worktree`; otherwise agree explicitly on who owns the index.

**`lake env lean` reads the *existing* olean of a dependency.** Edit `Domain.lean`, check
`Combinators.lean`, and the new constructor is an unknown identifier until you build.

**Host writes take ~1 s to reach the container mount.** `sleep 2` after editing, before building.

**One `lake build` at a time**, and the corollary a parallel session needs: *your* build rewrites
oleans under someone else's `lake env lean`. Editing a late module and checking it with
`lake env lean` writes nothing and is the safe way to work alongside an agent.

**The TS toolchain is not on PATH and neither is `node`.** Run it in a container against the host
`node_modules`; `mcr.microsoft.com/devcontainers/typescript-node:0-20` works, `tsc --noEmit` is
**clean** there (the "one pre-existing aws-sdk error" is a host artefact), biome is at **8**.

**Python is on the host, not in `rotorise-lean-dev`.** The three guard scripts run from `formal/`
on the Mac; `python3` does not exist in the Lean container.

**`tuple` is variadic.** `tuple([x])` passes an array as one element and every reader of
`def.elements[0].def` then sees `undefined`. It cost me a false bug report.

**`by_cases` and `by_contra` reach `Classical.em`**; `simp` reaches `Classical.choice` more often
than you expect. Use `cases h : decide P` and `Decidable.byContradiction`. `Finset.card_pos`,
`Finset.mem_insert` and `Finset.mem_filter` are clean; `Finset.toList` is `Quotient.out` and is
not.

**`grep` has two blind spots and both bit this arc.** A pattern anchored on a qualified name misses
an anonymous-constructor pattern — changing `Typed.held`'s arity missed a consumer written
`| _, _, _, .held h' _ =>`, and only the build found it. And **a grep piped into `head` is not a
measurement**: a truncated pipe twice produced a false reading, once nearly asserting in a commit
message that two lemmas no longer existed. If a claim rests on a grep, run it without a limit.

---

## The thing to keep

Two findings outrank every change in the table above, and both are corrections to what the repo
believed about itself.

**§3's `(literal)` premise is load-bearing, not defective.** Four places — ARCHITECTURE §8,
`Typing.lean`, `Combinators.lean` and `codec-audit.md` §2.2 — said
`literalN_holds_what_it_cannot_write` "records a defect in §3's rule". It does not. §3's premise
line is `⊢ g : T ⇝ μ, g ground; ℓ₁ … ℓₙ ∈ T`, and at `g = number` the base's held set **is** §1's
`D`, so the rule already requires `ℓ ⊆ D` and `hD` was transcribing it faithfully. What the witness
shows is that omitting the premise breaks **(B)** — a fact about §3 worth keeping, and a better
reason to keep the witness than the one written down. It now lives on `literalNRule`, the prism
with that premise omitted, deliberately not a `Term`. `docs/codec-calculus.md` needed no change.

**The `(dunion)` narrowing simplified nothing, and the measurement is the deliverable.** JH's
rationale had two halves — "simplifies proofs" and "aligned to how I will use it". Measured over
every declaration whose name mentions the machinery: 39 declarations / 350 lines before, 40 / 353
after, the three lines being a bridge lemma, and **not one proof changed length**. Every proof over
`(dunion)` consumes only the tag set's *nonemptiness*; none consults the arity. Nothing shrank
because nothing was ever waiting on it. The second half of the rationale is real and the first is
not, and the normative note says so where the next person will look.

The general lesson both share: **the sentence saying the brief was wrong is the most valuable thing
in any report.** Three of the four briefs this arc were wrong about something load-bearing, and in
each case the correction was worth more than the change it arrived with.
