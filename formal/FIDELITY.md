# Representation fidelity — is the model the specification?

`VOCABULARY.md` asks whether a proof *reads* in codec vocabulary. This one asks the
question that matters for an artifact meant to be **checked rather than trusted**:

> Could a competent reviewer who knows `docs/codec-calculus.md`, but not this codebase,
> verify a single theorem in isolation — and would they be verifying the specification?

Two failure modes, and the second is the one people forget. A claim can be **false**, and
`docs/codec-formalization.md` §4 logs six of those the mechanization has caught. A claim
can also be **true but unlocatable** — correct, provable, and impossible for a reviewer to
line up against the rule it is supposed to represent. For this artifact's purpose those
are the same defect, and this file measures both.

---

## §1 How this was produced, and how much to trust each line

Two independent audits, deliberately given opposite directions and no sight of each
other: **spec → model** (does every normative element have an exact counterpart?) and
**model → spec** (does the model assert anything the specification does not license, and
can a reviewer find it?). Convergence between two blind readings is the only real
evidence here; a finding both reached independently is marked **[both]**.

Every finding carries its verification status, and this matters more than the finding:

- **[checked]** — re-derived at the cited lines, in this session, by me.
- **[reported]** — one audit's reading, cited but not independently re-derived.

Neither audit compiled anything, and neither verified a *proof*. Everything below is
about statements, definitions and their relation to the specification. Where a claim
needed the toolchain to settle, it is marked as such and the result recorded.

## §2 The findings

### Defects in the specification

**D1 — §5 defines union admission two incompatible ways. [both] [checked]**
`codec-calculus.md:698` says an option admits `t` when "the `κ`/name filter passes **and**
`eᵢ(t)` is defined". §4 says objects decide "by names, not attempts", and
`OptionSem.byNames` (`Combinators.lean:1289`) tests `keysOk` alone, never consulting
`c.e`. These are different semantics: under the Sums clause an object whose names fit but
whose field encode fails would not admit and a sibling could answer; under `byNames` it
admits, wins the singleton filter, and the union returns `none`. **The union's `dom(e)`
differs.** The model's reading is the defensible one — it is what makes the name device
decidable at the declaration — so the Sums clause needs the exception written into it.

Sharpened by the second audit: `κ` is **never consulted by the denotation** anywhere. It
lives only in `Discharge.lean` as a declaration-time discharger. Sharpened again, from a third
direction the audits had no access to: **the implementation follows the specification's reading
and not the model's.** `union`'s matcher filters by `κ` — `carries` on the value side, `writes` on
the stored side — and only then attempts the survivors, which is §5's "the `κ`/name filter passes
**and** `eᵢ(t)` is defined" exactly. Under `byAttempt`, `union([string, number])` **violates (U)**,
because `number.encode('-1')` succeeds — encoding does not validate, so definedness alone separates
almost no two ground options. So `byAttempt` is not merely missing a conjunct the discharger
re-derives; it is the reading under which a union this library ships and recommends is unsound.
`checkUniqueAdmission` (`src/testing.ts`) states admission the specification's way for that reason,
and `codec-formalization.md` §4 records what it found once it did. And the loss is *why*
`uAtCan_of_separated` needs a lawfulness premise it would otherwise not — the discharger
re-derives by read-side (W) what the missing member filter would have given free.

**D2 — `(D)` is a premise of `(union)` that nothing checks. [both] [checked] [fixed]**
The rule figure at `codec-calculus.md:490` carries `(D)` and `(K)`. `Typed.union`
(`Typing.lean:145`) carries only `TypedListμ`. `(K)`'s relocation to `Obligations`' `UAtCan`
is deliberate and documented; **`(D)` is simply absent**, and `DDisj` (`Discharge.lean:874`)
exists only as the subject of a counterexample.

Direction matters, and the second audit got it right: `Typed ⊋ ⊢`, so `soundness` is
*safely* stronger and the "not derivable" rows refute against the larger relation. But
`typed_union_string_boolean` (`Refutations.lean:189`) asserts **derivability**, and the
identity `Typed = ⊢` asserted at `Typing.lean:8` — which every §6/§7 row leans on — is
false as stated. Since §5 itself concludes (D) discharges nothing, the honest resolutions
are to demote it to a remark or to add it to the rule. Normative in the doc, absent in the
model, unremarked in the defect log is the worst of the three.

**Resolved by adding it to the rule** (§5 item 2). `DIncomp` (`Typing.lean`) is §5's
incomparability, pairwise over the option held sets, and `Typed.union` now carries it.
Two things made this the cheaper of the two resolutions than it looked: the rule had
exactly **one** construction site in the whole development (`typed_union_string_boolean`)
and five inversion sites, and (D) is fuel-free and reads off the index the rule already
computes — so it fits `Typing.lean`'s stated syntactic/fuel-free policy without argument.
No theorem consumes it, which is correct and is now stated where a reviewer will look:
§5 says no condition on held sets can discharge (U), and `DDisj` next to
`not_uAtCan_literal_held` is why. `Typed = ⊢` is now true as asserted.

**D3 — §5's `adm` cannot pass through `legacy` on the read side. [checked] [witnessed, logged]**
`codec-calculus.md:514` says `legacy` passes `adm` through. It cannot: `extendRead`
(`Combinators.lean:289`) widens `p` by `r`, which is exactly the direction `adm` bounds.
**The model already corrects this** — `admA` (`Discharge.lean:139`) has no `legacy` case —
but the correction is not in `codec-formalization.md` §4, so the document still asserts
the false row. A defect of the same species as the six logged, and the only one currently
unwitnessed by a theorem. Second half: the doc has one `adm`, the model needs two, and
they genuinely disagree at `legacy` and at `literalN`. §5 should split it.

**Witnessed, logged, and now amended** (§5 items 8 and 10). `not_admA_legacy`:
`legacy(literal("A"), r)` with `r` reading an `N` reads `⟨N, "1"⟩` to `"A"`, and
`admA(literal("A"))` refuses it — so a passthrough `admA` makes `admA_sound` false.
`codec-formalization.md` §4 carries the entry, including the `literalN` half.

**`codec-calculus.md` §5 now states the two functions**, at the user's call, as a table over
`Term` with both partings argued: `legacy` passes `adm` and not `admA` because a migration
exists to accept attributes the current codec refuses, and a numeric `literal` has no `admA`
because distinct numerals read to the same double. The readable-side discharger row and the
`(D)` paragraph's closing sentence now say `admA`.

Writing the table found a third thing neither audit had, and neither had this finding: the old
passthrough list was `refine`, `optional`, `fallback` and `legacy`, and **two of those are not
terms**. `optional` and `fallback` are §4's fields; `adm : Term → …` cannot have a case for
them. It is the C3 stratification error again, this time inside the specification's own
auxiliary table, and what exposed it was writing the table out against `Term`'s constructors —
where a case for a field cannot be written down. **A prose table has no arity to violate**,
which is exactly why transcribing one into a total function is worth the trouble.

**D4 — §2's (MP) exemption is localized in the doc and global in the model. [checked]**
`codec-calculus.md:78`: a term *containing* a `legacy` inherits the exemption "on exactly
the attributes the migration rereads, **and on no others**". `MPOk` (`Soundness.lean:65`)
is `False` at any `legacy`, so `soundness` delivers no (MP) claim at all for such a term.
The sentence that makes `legacy` a migration rather than a licence has no counterpart.

**D5 — `numeric(T)` denotes `refine(number, T)`, which §3 says is a different term. [reported, now checked] [logged]**
`codec-calculus.md:178`: "`p` … **does not verify membership in `T`** … a claim and a check
are different terms." `numericCodec` (`Combinators.lean:196`) gates `q` on both halves.
This is a spec self-contradiction — `:617` calls the checked reading normative — resolved
in §5's favour silently.

**Re-derived, and sharper than reported.** §5's reading is not merely the one the model
picked; it is the only one available. Under §3's reading `p` returns values outside `T`,
which is `Carrier.ranP` failing and with it `typed_p_mem` and the honesty of the `: T`
index.

**And there was a third side the audit never looked at: the implementation.**
`numeric<T>()` in `src/codec.ts` decoded with `Number(ok) as T` — no check at all, a type
assertion over `number`. Three artifacts, three readings, of a term whose stated purpose
was to be a fourth thing.

**Resolved by removing `(numeric)`**, at the user's call, from the rule figure, from
`Term`, and from the implementation. `numericCodec_eq_restrict` (commit `eb3fac9`) was
proved first: `numeric(q)` and `refine(number, q)` are the same codec on all four fields,
so nothing expressible was lost. Enumerated members go to `literal(0, 1, …)`, which is
`literal‑N` and checks both directions; an arbitrary subset goes to `refine`; a caller's
own narrowing goes to `held`. The general lesson is in `codec-formalization.md` §4: an
unchecked read cast cannot be a term of a calculus whose judgement carries a held set.

**D6 — `(held)`'s iso premise is stronger than the proof consumes. [reported]**
The doc demands total cancellation on the carriers; `IsoCancels` (`Codec.lean:102`)
restricts both to `(c.e ·).isSome`, and `soundness_both` closes on the restricted form.
The same shape as §4's "too weak *and* unnecessary" finding, run the other way.

**D7 — §1's `℘⁺fin` and `⇀fin` are not in the carrier, and the two omissions cancel. [reported]**
`Attr.ss []` is well-formed and `M`/`Item` admit duplicate keys; `Domain.lean:8` records
the list-for-set choice as being about *order* only. The second audit found the coupling:
`HSet` is a nonempty **list**, so `set [x,x]` encodes to `ss [s,s]` and reads back — (R)
holds. Under §1's actual `℘⁺fin` the wire set would collapse and (R) would fail on that
input. **The two widenings are load-bearing on each other and the coupling is stated
nowhere**; tightening either alone breaks `lawful_setCodec`. The project has already paid
for this class of error once (`HeldSet.lean:14`, `HOpaque` admitting `set []`).

### Claims that are true but unlocatable

**U1 — `ident` is mechanized, faithful, and dead. [both] [checked] [fixed]**
`ident`/`identList` (`Discharge.lean:74`) reproduce §5's table row for row and appear in
**no theorem statement and no proof** — only three `example`s. `κ`, `adm` and `admA` each
have a soundness lemma pinning them to the denotation; `ident` has none, so **nothing
forces the model's `ident` to be §5's `ident`.** Worse: §5's (K) is
`κ disjoint ∨ (ident ∧ ident ∧ adm disjoint)`; `SepV` (`Discharge.lean:583`) is
`κ disjoint ∨ adm disjoint` — both `ident` conjuncts dropped. It is sound because `adm`
defaults to `true`, so `adm`-disjointness is unsatisfiable between non-`ident` terms —
and that argument appears nowhere in the model.

**That argument is now in the model** (§5 item 4), and `ident` is used rather than
deleted. `ident_of_adm`: if `adm` refuses a single value, the term is `ident` — the
pinning `ident` can have, since unlike `κ`/`adm`/`admA` it has no denotational content
to tie. `admDisj_ident` then recovers §5's two dropped conjuncts from `SepV`'s `adm`
clause, given that each option admits *something*.

Writing it turned up a finding neither audit had: **that side condition cannot be
dropped, and the witness is derivable.** `dunion(d)` with no options is derivable —
`(dunion)`'s premises are quantified over the option list, so an empty list satisfies
them vacuously — and its `adm` is `false` everywhere, so it is `adm`-disjoint from
`string`, which is not `ident`. So `SepV` is **strictly weaker** than §5's (K) at a
derivable pair (`sepV_string_dunion_nil`). Weaker is the safe direction — `SepV` is a
premise of `uAtCan_of_separated`, so the theorem discharges strictly more — but the two
conditions are not the same condition, which is exactly the kind of thing that should
not have been living in prose.

**U2 — §5's discharger table speaks two languages. [checked] [fixed]**
Two rows are about `UAtCan fuel opts` (`uAtCan_of_separated`, `uAtCan_of_disjoint`), two
about `List OptionSem` (`uniqueAdmission_byTag`, `uniqueAdmission_of_kinds`). A reviewer
checking the table changes vocabulary halfway across it, and `(dunion)`'s (U) is visible
only *inside* `lawful_dunionCodec`. Also a dangling reference: `Combinators.lean:1361`
cites `uniqueAdmission_of_disjoint`, which does not exist.

**Three of the four now speak one language** (§5 item 5), and the fourth has a reason
rather than an excuse. `(dunion)`'s row is `uAtCan_dunion`, at term level, with
`denote_dunion` — an `rfl` — pinning its option list to the one the denotation is
actually built from; its premises are exactly `Typed.dunion`'s two side conditions, and
`Obligations.dunion` says the obligation list has no (U) entry to receive them.

`(opaque)`'s row cannot follow, and the audit had not noticed why: `denote` gives
`opaque` the **fuel-free** `opaqCodecω`, which budgets each input by its own depth and
is not `altCodec` over any single list of options. There is no term-level list to state
`UniqueAdmission` about. So `uAtCan_opaque` is about `opaqCodec` at a fuel — premise-free,
since `lawful_opaqCodec` discharges the one hypothesis — and says so where it is stated.
That is a fact about `opaque`, not a gap in the table.

Two things came out of writing it. The eight-option list `opaque` sums was spelled twice
(`opaqCodec` and `opaq_onKinds`) and about to be spelled a third time; it is now
`opaqOptions`, taking the recursive codec as an argument, so `opaqCodec` is one line and
the three statements about the list cite it. And the dangling reference is gone —
`uniqueAdmission_opaque` is what it should have said.

**U3 — `≡` is not transitive, and nothing says so. [checked] [fixed]**
`Codec.Equiv` (`Equations.lean:36`) is faithful to §6 — agreeing everywhere both are
defined. `Equiv.refl` and `Equiv.symm` are proved; **`trans` is absent and false**: take
three codecs agreeing on `T` and `μ` where the middle one's `e` is nowhere defined.
§6 is presented as an equational theory, and `codec-formalization.md`'s conformance
standard asks a port to exhibit `Codec.Equiv` — a relation that does not chain.

**Now said, three places** (§5 item 3): `not_equiv_trans` in `Refutations.lean`, a
docstring where a reader looks for `trans` (beside `Codec.Equiv.symm`), and a sentence in
C3 telling a port not to certify through an intermediate. The witness came out stronger
than the sketch above: all three codecs are `Lawful` **and** on their `Carrier`, and the
held set is nonempty, so the failure survives every hypothesis §2 imposes on a pair. It
needs only the licence §2 grants out loud — `e` does what it likes off `T` — plus the
fact that `Carrier` bounds `dom(e)` by `T` and not the converse.

Left open, and said so in the source: whether `≡` chains when both ends are `denoteω` of
*derivable* terms. The middle codec holds `null` and writes nothing, which no derivable
term does, so this refutation does not decide the restricted question.

**U4 — §6's "Hold" table is advertised complete; two of eleven rows are not. [reported — half of it wrong]**
Commutativity is proved for the adjacent transposition only (`equiv_altCodec_swap`);
wrapper member preservation for three of five wrappers. `README.md` is honest about the
first; `codec-formalization.md:287` ("Complete — twenty of twenty") is not. The second
audit adds that the remaining two are not merely unproved but **unstatable** in the
current model: `FieldSem` carries no `μ` field, while §4 insists a field carries a member.

**That second half is wrong, and checking it was worth more than the finding.**
`FieldSem` has `FieldSem.codec`, which is exactly where the model puts a field's member,
so both rows are statable and are now stated — `optional_μ` and `fallback_μ`, each `rfl`.
The row is five of five. What the audit had actually found was `Equations.lean` saying
their half of the row was "the stratification of §4 and not a statement about `Codec.μ`
at all" — an evasion, since §4 says in as many words that a field carries a member like
anything else. The docstring now says so and proves the rows.

The first half stands and is now stated honestly in `codec-formalization.md`:
commutativity is the adjacent transposition, which generates every permutation without
the `List.Perm` lift being written down. That row also carries the `≡`-is-not-transitive
caveat from U3, which bounds what a table of rewrites licenses at all.

**U5 — the guard covers a fraction of what the documents advertise. [checked, settled, and now closed]**
`Calculus/Axioms.lean` put 17 constants through `#assert_axioms`; the documents cite 99
theorem names as results. Unguarded and doc-claimed: every §6 row, six of nine
refutations, all four ω-twins, two of the four dischargers, `κ_sound`/`adm_sound`/
`admA_sound`, `denoteω_eq`, and **`opaq_T_identity`** — the one row
`codec-formalization.md` calls "Closed for `opaque`", behind seven `omega` calls in
`HeldSet.lean`, and `omega` is a known `Classical.choice` route.

**This one I settled rather than reported.** `#print axioms` on `opaq_T_identity` and the
ten other unguarded doc-claimed results: **all clean** — `propext`, `Quot.sound`, the
`Double` axioms, no `Classical.choice`. So there is no leak today. There is also no
process: that was eleven hand-checks standing in for a build error, which is exactly the
gap `Axioms.lean` was written to close.

**Closed.** Those eleven are now `#assert_axioms` lines (§5 item 1), grouped by what each
group would cost if it leaked: the three devices that pin §5's declaration-time table to
the denotation, the three ω-twins that all travel along `denoteω_eq`, and the `opaque`
and numeral rows. The guard went green first try, which is the expected result — the
point was never to find a leak, it was to stop the eleven hand-checks from having to be
redone by the next reader. Coverage 17 → **28 of 99**, and 52 of 130 once items 3–5 and 8–11 and the `(number)` gate added theorems of their own; the denominator moved again when §6's audit began citing the theorems it had read.

A measurement artefact worth naming, since this file's own rule is that the script wins:
`fidelity_audit.py` reads `FIDELITY.md` as one of its document sources, so *citing* a
theorem here marks it cited. Writing this audit raised the denominator from 93 to 99 by
itself. The ratio is honest — a name this file holds up as a result is a name the
documents advertise — but the denominator is not independent of the auditor.

### Corrections to this project's own artifacts

**C1 — `vocab_audit.py` had two blind spots, both flattering. [checked, and fixed]**
It carried a silent `Lawful.{s}` fallback that scored ✓ where `VOCABULARY.md` §2's naming
scheme is not followed, and it did not recognise `opaqCodec`'s eighteen per-constructor
unfoldings (`opaqCodec_e_str`, `opaqCodec_p_s`, …) as inversion. So `VOCABULARY.md`'s
headline — "the observation half is 12% done … `opaque` is the only block with a
measurable residue" — was **measuring a naming gap for its own largest cited offender.**

Fixed: the matrix now counts an inversion *family*, and prints the dot-form lemmas rather
than absorbing them. The convention turned out to be wrong rather than the code —
`Lawful.through` reads "`through` preserves `Lawful`" and is the better name for a
namespaced construction — so `VOCABULARY.md` §2 now sanctions both forms and says when
each applies. Corrected coverage: **25/48**, not the 21/48 previously claimed.

**C2 — stale prose, some of it mine. [checked] [fixed]**
`Equations.lean:105` quotes a specification sentence **deleted in this arc's own
`nullable` commit**. `Denote.lean:10` says "at fuel 0 every term denotes `Codec.empty`";
`denote 0 t` sets `μ := μSyn t` (`Denote.lean:89`), which is the entire point of
`denote_μ`. `Denoteω.lean:20` names a file that does not exist. Five more at
`Continuity.lean:50,64`, `Domain.lean:20`, `Discharge.lean:22`, `README.md:144`.

**All eight fixed**, and two of the eight were not quite what the audit said:

- `Equations.lean`'s quotation is half live. §3 *does* still call `nullable(c)`
  "structurally the two-option union" — that sentence was not deleted. What was deleted
  is what followed it, the "coincide under honesty" clause the section refutes. The
  prose now quotes the live half as live and the dead half as former.
- `Discharge.lean:22` was accurate when the audit was written and is stale now, because
  §5 item 2 moved (D) into `Typed.union` this session. It points at `DIncomp` and at
  `DDisj`'s role as the withdrawn strengthening.

`README.md` had four stale numbers rather than one — the guard's 17, the observation
half's "16 of 48" (C1's own correction had not reached it), the "0–3 against 6–9"
density claim, and two entries in "What remains" that are done (§6's rows, and
`typed_TSub` tying the judgement's `T` to the denotation). `VOCABULARY.md`'s density
table had drifted by a few lines per block and is re-synced to the script.

## §3 The review surface, measured

```sh
python3 scripts/fidelity_audit.py          # --names to list the offenders
```

At HEAD: 739 declarations, 543 theorems, 196 definitions.

| | |
| --- | ---: |
| theorem names the documents cite as results | 133 |
| …put through `#assert_axioms` | **63** |
| §-tag coverage (declarations naming a spec section) | **24%** |
| docstring coverage, theorems | 60% |
| docstring coverage, definitions | 72% |
| **theorem statements naming an undocumented definition** | **60%** |
| …and themselves undocumented | 125 |

The last row is the one that matters. A statement naming an undocumented definition
cannot be read against the specification without a detour — and this counts the
*statement*, never the proof. A reviewer is entitled to skip a proof; they are not
entitled to skip a statement.

Per-module §-tags are worst exactly where the volume is: `Combinators.lean` 11%,
`Term.lean` 0%, `Denoteω.lean` 3%. `Opaque.lean` was 1% and is now 25%, and `Lists.lean` 2%
and now 21% — both from the §6 audit below, which is what that audit turned out to be *for*. The 55 undocumented definitions include `Typed`,
`Term`, `denote`, `setCodec`, `arrayCodec`, `objectCodec`. **No line of source says which
§3 rule `setCodec` denotes** — that mapping exists only in `README.md` prose.

**A level mismatch inside §6 — closed** (§5 item 7). It was: `Equations.lean` had **0 of 36**
statements mentioning `denote`/`denoteω`/`Typed` while `Refutations.lean` had 17 of 18, so the
"Hold" rows were stated about combinators and the "Do not hold" rows about terms. Checking a
Hold row against the specification needed an eight-entry translation — `through→held`,
`restrict→refine`, `extendRead→legacy`, `orNull→nullable`, `altCodec→union`,
`dunionCodec→discriminatedUnion`, `opaqCodec→opaque`, `objectCodecCore→object` — five of which
share no substring with the term they translate, and it was written down nowhere.

It is now written down as theorems: ten `denoteω_*` bridges, each `rfl`, because `denoteω`
dispatches straight onto the combinator. Nothing is *proved* by them except the
correspondence, which is exactly what was missing. Every Hold row then gets a term-level twin
one line long, so both halves of §6 read in one language. **21 of 55** statements now name
`denoteω`, up from 0 of 36.

Two things the bridges made visible that the prose had not. `Equations.lean` did not import
`Denoteω` at all — the file stating §6's equations could not mention the denotation those
equations are about, which is the mechanical reason the mismatch persisted rather than an
oversight anyone chose. And `opaque`'s bridge is to `opaqCodecω` rather than to a fueled
codec, which is the same fact §5's discharger table records when it gives `(opaque)` a reason
instead of a term-level row — one cause, two symptoms, previously written up separately.

## §4 What both audits agreed on, unprompted

**No new codec-level construction is warranted.** Both re-ran the argument of
`VOCABULARY.md` §4 against fresh readings and both reached it independently:
`carriedCodec` absorbs four of six products, `setCodec` is genuinely not an instance (its
attribute side is a choice among three wire constructors, not one prism), `dunionCodec` is
already `altCodec`. **Every gap either audit found is a naming gap or a fidelity gap.**

That is worth recording because it is the negative result the whole arc has been testing
for, and it now has three independent confirmations.

## §5 The plan, ranked

| # | item | why it is first |
| --- | --- | --- |
| 1 | ~~The eleven `#assert_axioms` lines — the hand-checks of U5, made mechanical~~ **done**: 28 of 99 guarded, green first try | cheapest, and it is the guard's own principle; `opaq_T_identity` guards seven `omega` calls behind a row the docs call closed |
| 2 | ~~`(D)` into `Typed.union`, or name the divergence in `Typing.lean`'s list~~ **done**: `DIncomp`, into the rule | the difference between "`Typed` is §3–§5's judgement" being true and false; the list records five smaller divergences and omits this one |
| 3 | ~~Attempt `Equiv.trans`, fail, record `not_equiv_trans`~~ **done**, lawful and on-carrier throughout | three lines; a non-transitive `≡` presented as an equational theory is exactly the species §4's log is made of |
| 4 | ~~`ident_sound`, or delete `ident` and say `adm` carries the exemption~~ **done**: `ident_of_adm` / `admDisj_ident`, plus the derivable pair where `SepV` and (K) part | a normative table transcribed and unconstrained is the definition of an unlocatable claim |
| 5 | ~~`uAtCan_dunion`, `uAtCan_opaque` — the four discharger rows in one vocabulary~~ **done**: three in one vocabulary, and `opaque` has a reason | two one-line theorems; converts two unlocatable rows to checkable, and retires the dangling reference |
| 6 | A §-tag ratchet in `fidelity_audit.py`, failing the build when coverage drops | 18% today, 1% in `Opaque.lean`; `Axioms.lean`'s principle applied to traceability |
| 7 | ~~Restate §6's eleven "Hold" rows at term level~~ **done**: ten `rfl` bridges and a twin per row; 0 of 36 → 21 of 55 | retired the unwritten translation table and made both halves of §6 one language |
| 8 | ~~The documentation corrections: D3, D5, U4, C2's eight stale comments~~ **done**; U4's second half was wrong and the row is five of five | cheap, and D3 is the only defect of the seven with no machine-checked witness |
| 9 | ~~`Codec.Ker` and `Can` in `Codec.lean`~~ **done**: and `η ⊆ ker p` with them | `≈c` is §2's central device and had no name; `Can` sat in §6's file where §2 and §5 could not cite it |
| 10 | ~~D3's amendment to `codec-calculus.md` §5~~ **done**: the `adm`/`admA` split, and a stratification error found while writing it | normative, so it waited for the call; the model had been right and unrecorded since `admA` was written |
| 11 | ~~`(literal-N)`'s `ℓ ⊆ D`~~ **done**: §3's premise, `Typed.literalN`'s `hD`, and the shipped `literal(NaN)` that settled it | the rule figure had said `∈ D` all along and the paragraph under it called `D` unchecked — the worst of the three states a premise can be in |

Item 9 turned out to carry more than its description. Naming `≈c` was three lines and an
`Equivalence`; what it unlocked was §1's store concession, which had been prose in
`Domain.lean` since `Numeral.Stored` was written. `SurvivesStore c η` is `η ⊆ ker p`,
`Lawful.retract_through_store` is **(R)** with the store in the middle — the law production
actually runs, and the one the shipped `decimal` broke — and `decimal` now has both halves of
its answer: `survivesStore_decimalCodec` says the narrowed held set discharges the premise,
`not_survivesStore_decimalWF` says the un-narrowed one cannot, and `ker_decimalCodec` says
why the question is that sharp (its kernel is equality, so `η` has to be the identity where
it can be handed anything). The narrowing was a fix with a measurement behind it; it is now a
fix with a certificate behind it too.

Item 11 is the one to reread if the arc is ever summarised. The premise was **already in the rule
figure** — `ℓ₁ … ℓₙ ∈ D`, written down, normative, and printed above the line. What was wrong was
the paragraph beneath it, which called `D` "an unchecked precondition" and named `5e-324` as the
example of it going unchecked. Neither audit flagged it, because both were reading the figure. A
premise stated in a rule and disowned in the prose underneath is worth less than no premise at all:
it reads as checked to everyone who stops at the figure, and as optional to everyone who does not.

What found it was not a proof either. It was a design question — *would normalizing `literal-N` be
simpler?* — and the first move was to ask the shipped constructor what it did at the ends of the
range. It wrote `{ N: 'NaN' }`. The answer to the question turned out to matter less than the
measurement taken on the way to it.

**And the entry recording all that contained a fresh error of its own**, which is why it is worth
rereading twice. Having added `ℓ ⊆ D`, I argued the read side needed no gate: membership in `ℓ` is
checked in both directions, `ℓ ⊆ D`, so the premise covers it. The user refused the argument — *it
has to pass through the same checks as `decimal` and `number`* — and `literal(0, 1, 2)` read
`⟨N, ""⟩` as `0`, `literal(0, 16)` read `⟨N, "0x10"⟩` as `16`. Reading an `N` as a value is wider
than membership in `ℓ`, so the check passes on attributes §1 has no point for.

No §2 law catches it — (C) and (R) both hold — which is the part worth keeping. What it breaks is
**§1**, and therefore **C1**: the embedding into `𝔸` is partial, the implementation's attribute type
is wider, and every term that reads an `N` is the one that must notice. Two of the three did.
`codec-formalization.md` §4 carries the entry. The principle I had and misapplied is written down
one section later in that same document — *an unchecked direction is sound exactly as far as
something outside the codec enforces it* — and for a read there is nothing outside the codec at all.

Three corrections in this arc have now come from the same move: the user declining to accept a
justification. That is a higher hit rate than any audit in this file.

Also worth recording, since it is the pairing that made the docstring: `Ker` is an
equivalence and `Codec.Equiv` is not (`not_equiv_trans`, item 3). They are one symbol apart
in the specification's prose and they differ exactly where a reviewer would assume they do
not. Stating them in the same file is cheaper than the remark that would otherwise be owed.

Item 3 of `VOCABULARY.md`'s plan — `pointCodec = carriedCodec`, which would hand inversion
to the ten ground codecs — remains open and is now ranked below all of these. It is
density; these are fidelity.

### A postscript, from applying §6's own conclusion

§6 below ends with *unaudited is not the predictor; unaudited **and duplicated** is.* The next
thing looked at was chosen by that rule rather than by coverage, and it paid immediately.

`docs/codec-formalization.md` §6 has a row called **"`T` as an identity"**. Read against the
theorem it cites, it is **two claims wearing one name**:

- **(A)** the denotation's `T` is the judgement's — `(denoteω t).T = T`. This is what §3 means
  by "`Uν` *is* `opaque`'s held set" and what `opaq_T_identity` proves.
- **(B)** the held set is what the codec can write — `T = dom(e)`, the claim that makes `: T`
  an honest index rather than an upper bound.

The row asserted (A) and then explained why it is "*false* for `union` without full (U)" — and
that explanation is about (B). (A) is not false at `union`; it is **definitional** there, since
both sides are the same union of the options' sets (`altCodec_T`, `Iff.rfl`). (B) is the one
that fails, and now has its witness: `not_TIsDomE_unionLiteralString`, in `union(literal("A"), string)`,
where `"A"` is held and nothing is written because both options admit.

The row is now two rows. What kept the conflation alive is worth naming, because it is the
same mechanism as `(literal-N)`'s: **a claim and its justification drifted apart while both
stayed true of *something*.** Each half was correct about a different proposition, so neither
audit reading the row alone could catch it — it takes reading the row against the theorem.

And the cost of closing (A) generally is now measured rather than estimated. `typed_TSub` only
*projects* the denotation's witness; the converse must **construct** it, which needs a converse
to `align_TSub` that builds `align`'s output and the object case's presence data. That is why
it is open, and it is a bigger job than the row's "still open for the other constructors"
suggests.

## §6 What neither audit checked — now read

Neither audit compiled anything, and neither verified a proof. Four regions went unread:
`Lists.lean` against §5's Traversal Lemma, `Opaque.lean`'s unfoldings and depth lemmas,
`Denoteω`/`Soundnessω`'s transport, and `Continuity.lean`. The §3 measurements are mechanical
and reproducible; the §2 findings are readings, and are marked with which of them was
re-derived.

**All four have now been read, and the verdict is: no defects.** That is worth stating first,
because the prediction going in was the opposite one.

| region | verdict |
| --- | --- |
| `Lists.lean` vs §5's Lemma (traversal) | **faithful.** All five clauses have counterparts and each says what the Lemma says: `traverse_eq_some` (the lift, positions preserved), `traverse_isSome_of_all` (defined where every entry is), `traverse_roundTrip` (R), `traverse_isSome` (C), `traverse_rel` (`≼`), `traverse_length`. The keyed clause is `traverse_fst` and `lookup_rel` |
| `Opaque.lean`'s unfoldings and depth | **complete and exhaustive.** Eight `opaqCodec_e_*` and ten `opaqCodec_p_*` — total over `Value`'s and `Attr`'s constructors respectively — and `opaq_onKinds` pins all eight options to eight distinct kinds as a `Forall₂`, so the "one option per kind" claim `uniqueAdmission_of_kinds` consumes is total rather than sampled |
| `Denoteω`/`Soundnessω` transport | **faithful.** `denoteω_eq` is a total case analysis over `Term`, already under `#assert_axioms` |
| `Continuity.lean` | **faithful**, and the best-documented file in the development — it states the obligation `partial_function` cannot discharge, gives the witness at combinator and term level, and names the honest reading of its own counterexample |

Two things came out of reading them, and neither is a defect:

- **`Lists.lean` is §5's Traversal Lemma and nothing in it said so.** One `§` in 440 lines,
  and that one was an aside about `Classical.choice`. Five typing rules rest on that Lemma and
  a reviewer had no way to line up nine theorems against a paragraph of prose. The file now
  opens with the clause-by-clause table and the theorems carry §5 tags; coverage 2% → 21%.
  This is U-class exactly — true, provable, and unlocatable — and it is the largest single
  instance of it left.
- **One stale sentence in `Opaque.lean`'s header**: "the eight unfoldings, one per kind",
  which is true of `e` and false of `p`. The read side has ten, because §1's three wire sets
  are one *kind* and three *members*. The asymmetry is load-bearing — kind-disjointness is
  what (U) needs — so the header now says which side is which and why.

**And the prediction was wrong, which is the entry worth keeping.** Going in, the argument for
reading these first was that this arc's defects had all come from unaudited transcriptions —
`HOpaque.set`'s missing `vs ≠ []`, `admA`'s absent `legacy` case, §5's `adm` table — so the
region with zero audit coverage was where the next one was most likely to be. It was not. The
four unread files are, if anything, *better* than the audited ones: `Continuity.lean` is the
most careful prose in the development and `Lists.lean`'s theorems are exactly the Lemma's
clauses with nothing missing.

The reason is visible in hindsight and is worth carrying forward. Every defect this arc found
sat where **two artifacts had to agree** — a doc against the model, the model against the
implementation, a rule figure against the paragraph beneath it. These four files have no
counterpart to disagree with: `Lists.lean` is plumbing, `Continuity.lean` is a refutation of a
claim about tooling. **Unaudited is not the predictor; unaudited *and* duplicated is.** The
remaining places where two artifacts state the same thing are where the next defect is.
