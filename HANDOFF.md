# Handoff

**Branch `wip/map-types`. `lake build` green and warning-free, `#assert_axioms_all` and
`#lint_calculus` over 21 modules, `guard_reach.py`, `name_drift.py`,
`doc_counts.py --check` and `ratchet.py` all exit 0.** Verify with the block at the end of §Landmines, by exit
code and not by eye.

Delete this file once read. The commit messages are the record; `git log` is now the only
change log there is.

---

## The one idea

**A description must be kept in agreement with what it describes; a question cannot drift.**
The previous arc found that at the analysis rows. This one found it one level up — of *counts*,
*citations* and *commit messages* — and then found the corollary that ended it:

> **Prose that records how the code came to be this way is not describing the code.** It goes
> in the commit message, where nothing has to keep it honest because nothing reads it as a
> claim about the tree.

Four documents and 430 lines of docstring went on that principle. What survived every pass was
the same three things: the § tag, the **forced choice** — why the definition could not have
been the obvious other one — and what a refutation refutes. That list is `ARCHITECTURE.md` §9
now, and it is the whole convention.

---

## What landed

Twelve commits since `954ddc2`. Three instruments, four changes, then the deletion.

| commit | why |
| --- | --- |
| `e3bd71f` | twelve sentences no guard can see, found by an adversarial read of the documents |
| `1590eaf` | a count that commit moved — **and a record that I committed past a red guard** |
| `6a90359` | `vocab_audit.py` was scoring two codecs that do not exist, which is why three documents disagreed about one denominator |
| `2798a6b` | `ARCHITECTURE.md` §8, "What the host owes" — absorbing the `src/` discipline before deleting it |
| `b163c17` | the audit, the change log and the `src/` discipline deleted; 4466 lines, 63 citations resolved |
| `fefc1f0` | `FIDELITY.md` deleted — **minus three live findings**, carried to §10 |
| `1746bde` | `VOCABULARY.md` deleted — its rules became §9, its audit went |
| `3f7708a` | README's archaeology, 224 → 208 |
| `6e66b44` | `codec-calculus.md` keeps its arguments and loses the framing that called them history |
| `a55b552`, `078c254`, `8b9844c` | the docstring sweep, 430 lines out of fourteen modules |

**Where things are now.** `docs/` is `codec-calculus.md` (normative) and `dynamo-datatypes.md`
(the reference). `formal/` is `README.md` and `ARCHITECTURE.md`. `ARCHITECTURE.md`'s sections
renumbered twice: **§8** what the host owes, **§9** the proof vocabulary and the docstring
convention, **§10** open questions, **§11** the change checklist. `EXPECTED` is 6 entries from
20. `Calculus/` is 17321 lines from 17553, net of everything this arc added to those files.

---

## Pick up here

1. **Done at `2d57420`.** `name_drift.py`'s docstring check was clearing citations with
   themselves; `occurring()` strips comments now, §9 gained the `~~oldName~~` marker at JH's
   call, and 18 stale pointers were fixed. §6 has the measurement and the shapes that lost.

2. **A question, not a task: 172 declarations are named by a document this arc deleted and by
   no surviving one.** Whether `README.md` or `ARCHITECTURE.md` should name any of them is a
   judgement about what a surviving document is for. The three-bin proposal is written and is
   with JH: **(i) 12** §2 laws and corollaries namespaced under `Lawful`/`LawfulCore`/`Carrier`/
   `Agree`/`Codec.Equiv`; **(ii) 10** where a surviving document already makes the claim in
   prose and cites nothing — the bin with content, since a claim nobody cites is a claim
   `name_drift.py` cannot see; **(iii) 150** plumbing whose name is its content.

   **This item used to say "78 theorems" and to name the wrong file, and neither survived
   reproduction.** The recipe was "diff backticked theorem citations in the current documents
   against `git show b163c17^:docs/codec-formalization.md`". The example names it gave —
   `Lawful.stable`, `Lawful.core`, `Carrier.empty`, `AdmALit_binary_exact` — are cited by
   `docs/codec-audit.md`, a *different* deleted file. And no reading reaches 78:

   | source set | orphans | minus names a `Calculus/` docstring still mentions |
   | --- | --- | --- |
   | `codec-formalization.md` (the file this item named) | 94 | 43 |
   | `codec-audit.md` (the file the examples came from) | 58 | 41 |
   | both, i.e. `name_drift.py`'s old `LOG` | 147 | 82 |
   | **all five deleted documents — the reading used** | **172** | 90 |

   Also "theorems" is wrong: `Lawful.retract` and its siblings are structure *fields*, and
   `Lawful.core` is a theorem, so the universe is declarations of both kinds. Reproduce with
   the five deleted documents — the three above plus `docs/structural-discipline.md`,
   `formal/FIDELITY.md`, `formal/VOCABULARY.md` — against `README.md`, `ARCHITECTURE.md` and
   `docs/codec-calculus.md`.

3. **`src/`'s arity-one check — JH's call.** `(dunion)`'s discriminator is arity one in the
   calculus. `EveryOptionTagged` (`src/codec.ts`) refuses only options naming no literal and
   pairs sharing a tag, so `string('A','B')` at a discriminator is legal, and `codec.ts:4415`
   records that as deliberate — *"an option may answer to several tags"*. One type-level check
   plus that comment, which becomes false. Keying `discriminatedUnion` by tag was **declined**,
   so its list stays.

4. **`admits`' violation list — JH's call.** `admits(c,v) ↔ !isError(c.encode(v))` is false in
   one direction, because `string`/`boolean`/`binary`/`array(string)` do not validate on
   `encode`. Making `encode` use `admits` closes it at the root and is a behaviour change.

5. **Wiring `admits` into `union`'s resolver — JH's call**, and deliberately not done. It
   replaces try-and-see with a decision and retires `identifying` (45 lines, one consumer).
   Depends on (4).

6. **Done at the commit after `2d57420`.** `scripts/ratchet.py` holds three per-file counts
   and fails on a rise: hand-unfolding sites (332), retirement marks (72), undocumented public
   theorems (269 of 896). The docstring-coverage *bar* §10 asked for is not buildable at 269 —
   a bar nobody can satisfy gets switched off — so all three are ratchets. Baselines in
   `scripts/ratchets.json`; `--accept` to move one, `--allow-rise` on top to weaken it.

**Closed this arc, do not re-open:** `select` over `List.attach` (`daa211e` — measured; and the
ten-site count in it was six); `adm (.literal .number ls)` not exact (`152ab6b`); `admA`'s
`legacy` `⊤` row (`90794bd`); the value/attribute twin merge (§10 — the pair count is an
artifact of its transform, three passes gave 82, 69 and 72); bundling `Lawful` into `custom`
(§4a — elaborates, buys five lines, costs ~33 sites); keying `(dunion)` by tag (§4a — the
`Body` subtype cannot be written, `Body.fields` being defined after the mutual block).

---

## Landmines

**Three Claude sessions share this working tree, and there is one index.** A peer's
`git commit -a` commits your staged *and* unstaged edits under its message, and your own commit
then reports "nothing to commit, working tree clean". `2e13324` carries an edit I wrote under
another session's commit message. **Check `git log -1` as well as `git status`.** Do not rewrite
a peer-authored commit to reclaim authorship. For parallel work, use a separate `git worktree`.

**Gate on exit codes, not on printed output.** I shipped two commits claiming all guards pass
over a red tree (`eed1b58`, `e3bd71f`) because I ran them as `…; echo "$g=$?"; done && git
commit` — `echo` always succeeds, so the chain gated on nothing. Use:

```sh
fail=0
python3 scripts/guard_reach.py >/dev/null 2>&1 || fail=1
python3 scripts/name_drift.py  >/dev/null 2>&1 || fail=1
python3 scripts/doc_counts.py --check >/dev/null 2>&1 || fail=1
python3 scripts/ratchet.py     >/dev/null 2>&1 || fail=1
docker exec rotorise-lean-dev bash -lc 'cd /workspaces/Rotorise/formal && lake build' >/dev/null 2>&1 || fail=1
echo "ALL_GREEN=$([ $fail -eq 0 ] && echo yes || echo NO)"
```

Editing *any* `Calculus/*.lean` can move a `doc_counts` count, because §5 and §8 cite file
lengths — a comments-only edit is not exempt. **And a count can move in a file you did not
edit.** §5's `orth_unreach_lines` sums the *spans* of the unreachable declarations, and a span
runs from the `theorem` line to the last non-blank line before the next declaration — so
re-wrapping one signature onto two lines moves a number the document attributes to
`Orthogonality.lean`. `7fff6e8` moved it 168 → 169 that way. When a count moves and you cannot
see why, recompute the spans against `HEAD` rather than guessing which edit did it.

**`lake env lean` reads the *existing* olean of a dependency.** Edit `Domain.lean`, check
`Combinators.lean`, and the new constructor is unknown until you build.

**Host writes take ~1 s to reach the container mount.** `sleep 2` after editing.

**One `lake build` at a time**, and *your* build rewrites oleans under someone else's
`lake env lean`. Editing a late module and checking it with `lake env lean` writes nothing.

**Python is on the host, not in `rotorise-lean-dev`.** There is no Python in that container at
all — `which python3` there exits non-zero. The six scripts run from `formal/` on the Mac.

**The TS toolchain is not on PATH and neither is `node`.** Run it in a container against the
host `node_modules`; `tsc --noEmit` is clean there, biome is at 8.

**`tuple` is variadic.** `tuple([x])` passes an array as one element and every reader of
`def.elements[0].def` then sees `undefined`.

**`by_cases` and `by_contra` reach `Classical.em`**; `simp` reaches `Classical.choice` more
often than you expect. Use `cases h : decide P` and `Decidable.byContradiction`.
`Finset.card_pos`, `mem_insert` and `mem_filter` are clean; `Finset.toList` is `Quotient.out`
and is not. Extracting an element from a `Finset` is where it turns — `Finset.card_eq_one` is an
existential, so getting the witness inside a `def` is choice.

**`grep` has two blind spots.** A pattern anchored on a qualified name misses an
anonymous-constructor pattern — changing `Typed.held`'s arity missed a consumer written
`| _, _, _, .held h' _ =>`, and only the build found it. And **a grep piped into `head` is not
a measurement**: a truncated pipe twice produced a false reading here.

---

## The thing to keep

Four results outrank every change above them.

**§3's `(literal)` premise is load-bearing, not defective.** Four places said
`literalNRule_holds_what_it_cannot_write` "records a defect in §3's rule". It does not. §3's
premise line is `⊢ g : T ⇝ μ, g ground; ℓ₁ … ℓₙ ∈ T`, and at `g = number` the base's held set
**is** §1's `D` — so the rule already requires `ℓ ⊆ D`. The witness shows that omitting the
premise breaks **(B)**, which is a fact about §3 worth keeping and a better reason to keep the
witness than the one written down.

**The `(dunion)` narrowing simplified nothing, and the measurement is the deliverable.**
39 declarations / 350 lines before, 40 / 353 after, **not one proof changing length**. Every
proof over `(dunion)` consumes only the tag set's *nonemptiness*; none consults the arity.
Nothing shrank because nothing was ever waiting on it.

**`FIDELITY.md` carried a live (R) hazard that was stated nowhere else, and deleting it unread
would have lost it.** §1's `℘⁺fin` and `⇀fin` are not in the carrier and the two omissions
cancel: `HSet` is a nonempty **list**, so `set [x,x]` encodes to `ss [s,s]` and reads back and
(R) holds — under §1's actual `℘⁺fin` the wire set would collapse and **(R) would fail on that
input**. Tightening either widening alone breaks `lawful_setCodec`. It is §10's second-to-last
bullet now, and that paragraph is the only place it exists. **A file being a dated snapshot
does not make everything in it archaeology.**

**And `codec-calculus.md`'s "history" was algebra under a label.** Sixty lines headed *"The
original argument, for the record"* turned out to be the reasons each `adm`/`admA` row parts
the way it does — the `1e+21` normalisation, `number` and every numeric literal being one base
under different predicates, `refine`'s `q` bounding the write and not the read. That document
came out at **−6 lines**, against 4466 from the other three. **Read what is under the label
before believing it.**

The lesson all four share: **the sentence saying the brief was wrong is the most valuable thing
in any report.** Every brief in this arc was wrong about something load-bearing, and in each
case the correction was worth more than the change it arrived with.
