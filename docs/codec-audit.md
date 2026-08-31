# Audit: what the five representation repairs left behind

*Opened 2026-08-31, branch `wip/map-types`. All eight scans reported. Items are struck
through as they land in the tree.*

~~**The single most consequential finding is §9: five live bugs in the shipped TypeScript,
four of them C1 violations concentrated in one file, including two that §4 records as
already fixed.**~~ **Landed.** All five are closed in the tree — the four C1 violations by
gating both halves of `native`'s `N` and refusing an empty stored set, the fifth by making
`literal()` a construction-time refusal. `Carries('N')` moved out of `codec.ts` and into
`attribute.ts` on the way, which is why one file could close four bugs in another: the
predicate is a property of the carrier, and there is now one of it. See §9.7.
Everything else in this file is hygiene by comparison.

## Why this exists

Five representations were retyped in one arc: `M`'s payload, the object field table,
`℘⁺fin`, a literal's alternatives, and `Carries(N)`. Each replaced a *gate* — a `Bool` side
condition or a rule premise — with a *type* that makes the condition structural. Each also
left residue: machinery that existed only to repair the old representation, and prose
written when the old representation was current.

A green build hides both. Dead code compiles, and **prose does not typecheck** — the two
drift findings before this audit were caught by luck.

**§14 states the strategy the arc was actually following, its one exception, and the larger
principle (§13) that turned out to matter more.** Read that first if you are deciding what to do
next rather than auditing what was done. Hence parallel read-only scans, each
timeboxed. This file is their output and the disposition of each item.

## 1. Actionable queue

**Priority, set by `codec-formalization.md` §1–§2: the Lean spec first.** The model is not a test
suite for the target and does not observe it; a target is certified afterwards by exhibiting a
homomorphism. So a `src/` item is worth doing when it closes a claim the model currently
*certifies as false* — which is what §9 was — and is otherwise deferred behind the model. Item 15
is deferred on those grounds: it is a real bug, and the model does not yet say anything about
depth, so fixing the target first would be fixing a target against an uncertified spec.

**Item 17 is maximal priority.** It is the largest item, it is pure spec, and
`codec-formalization.md` §2 already disclaims the thing it deletes: *"Fuel is a termination
device, not a cost measure."* Roughly 1400 lines that the motivating document says are not model
content.

| # | site | problem | deletes | radius |
| --- | --- | --- | --- | --- |
| ~~1~~ | ~~`Domain.lean:9-13`~~ **Landed.** | File header **inverted on four clauses**: wire sets and maps "are lists", the numeral carrier "stays unrestricted on purpose", set-ness lives in `ker p` "not in the carrier". Self-contradicted 290 lines later in the same file. Rewritten to what the file now does, including the narrower true statement of the kernel's restriction — it rejects a `Finset` over the datatype being declared, not a `Finset` in a constructor. | — | **landed** |
| ~~2~~ | ~~`codec-formalization.md` §6~~ **Landed.** | Two §6 summary rows, at `:2135` and `:2138` after the file moved. Both rewritten: the numeral carrier is `WFNumeral` and `⟨N, "abc"⟩` is unrepresentable; the wire sets are `NEFinset` not `Finset`, and non-emptiness is not gated at all — `neSetImage` carries it. | — | **landed** |
| ~~3~~ | ~~`codec-calculus.md:87-88`, `:167-172`, `:559-560`~~ **Landed.** | The **specification's** justification for the `ker p` quotient listed *three* reasons, the first being set orderings. Now two — `η` normalising `N`, `drop` discarding names — at all three sites, and `:559` says which two rather than comparing to a loss that no longer exists. | a bullet + follow-on | **landed** |
| ~~4~~ | ~~`WireOrder.lean`~~ **Landed — deleted.** | **17 of 19 declarations dead** (independently found by two scans); header argues for a design the code abandoned. Only `Axioms.lean` imports it, for the axiom scan. The `Classical.choice` warning about `LinearOrder String` is a real hazard and must be relocated, not lost. | ~247 lines | small |
| ~~5~~ | ~~`Domain.lean:344`~~ **Landed — deleted.** | `Item := List (Name × Attr)`, docstring calls it "an `M` without its wrapper" — the exact shape five sites removed, beside the repaired `Attr.m`. **Dead**: grep finds only the declaration. | the declaration | none |
| ~~6~~ | ~~`Typing.lean:165-167`~~ **Landed.** | `literalOK` did two jobs: `Numeral.WF` on `.num` (content, stays) and `\| _ => false` for containers, which is just *"this value has a ground base"* — a claim about the field's carrier. `Term.literal (v : GroundValue)` makes `literalMember` total. Landed exactly as scoped: `hμ` and `μ` gone, `literalOK` → `literalD` with only the `.num` case, both laws argument-free, `literalMember` deleted, `literalCodec`'s `Codec.empty` case and `Exactness`'s container case gone. | **all of `hμ`**, the container half of `hok`, the `hok` arg of two laws, a case in `Exactness` | small (11 sites) |
| 17 | `Denote.lean:95` +4 modules | **`denote` does not need fuel.** A structural, fuel-free `denote` compiles against the real `Term` (§13.1). The obstructions were `List.map` and a higher-order `fieldSemOf`, both incidental. Puts `Denoteω` (314), `Soundnessω` (77), `Continuity` (123) and `Opaque.lean`'s budget apparatus (854, 148 `depth` uses) in question, plus `fuel` in `Soundness` (191), `Discharge` (159), `Exactness` (40). §13. | ~1400 lines | **largest in this file** — spike first |
| ~~18~~ | ~~`codec-formalization.md`, ~45 names~~ **Half landed: the check exists and the current-state documents pass.** | **A name-drift scan the repo did not have.** `fidelity_audit.py` and `vocab_audit.py` measure the mechanization; neither checked that a backticked name in a document still exists in `Calculus/`. `scripts/name_drift.py` now does, and fails non-zero. The three current-state documents in `formal/` had **seven** broken citations, all fixed. What remains is `codec-formalization.md`'s ~45, nearly all in §4, where the supersession rule applies and a name records what was reasoned with — a judgment about §4, not an edit. | — | **check landed**; §4 open |
| 15 | `src/codec.ts` | **DEFERRED — target work behind the spec.** **Nothing checks the 32-level nesting bound**, so the library writes items DynamoDB rejects — a C1 violation of the `⟨N,"5e-324"⟩` shape, and the fifth after §9 closed five. `opaque` and `native` are where it bites: both walk arbitrary user data. §12.3. | — | small (library); the model's side is a scope decision |
| 16 | `Typing.lean:207-210` | `dunion` keyed by tag (`MapOf Term`, discriminator **injected** not read back) deletes `htags` and `hdisj` with no coherence gate — §2.2's stated reason was wrong. Blocked on one measurement: whether `discriminatedUnion` has a multi-tag variant. §12.2. | 2 premises | medium, and a C2/C3 change |
| ~~6b~~ | ~~`Term.lean:27-35`~~ **Landed.** | **`literal`, `literalS` and `literalN` are one rule.** Raised by JH while item 6 was landing, and right: all three are *a nonempty finite set of values at one ground base*. Landed as the base-indexed form of §11.1 — `literal (k : GroundKind) (ls : NEFinset k.Carrier)` — after §11.4/§11.5 settled that the cheaper union route costs either `Classical.choice` or two reintroduced gates. | 2 constructors, 5 codec definitions → 4, 3 lawful theorems → 1, 2 carrier theorems → 1 (one of them 26 lines), 4 `admA` row lemmas → 3 | **landed** |
| ~~7~~ | ~~`Combinators.lean`, 43 sites~~ **Landed.** | `objectCodecCore` took `kn : Name → Bool` free; the only instantiation is `keepB rest sems`, and `rc?` is likewise always `rcOf rest`. Three hypotheses across five signatures all said *the filter never discards a declared name*. All three are gone, the private `lawfulCore_objectCore`/`lawful_objectCore` layer with them — it existed only to be instantiated by the public pair. §4.4 records what the parameter was actually costing, which was not the five signatures. | 2 theorems, 3 hypotheses × 5 signatures, 23 lines net | **landed** |
| ~~8~~ | ~~36 declarations~~ **Landed, in two passes.** | Transitively dead plumbing. The estimate was ~61 and the delivered figure is **36**; §4.1 records what the other ~25 turned out to be, because the miss was systematic rather than random. | 36 decls, 302 lines | **landed** |
| ~~9~~ | ~~`codec-calculus.md:249-251`, `:301-302`, `:938-944`, `:1034`~~ **Landed.** | §3 presented both number rules as `refine` over an **ungated base** (those bases cannot exist); the base table said "doubles"/"numerals"; §5's traversal Lemma had a "keyed lists … first occurrence first" clause naming nothing; `:1034` called a wire set "the lifted list". All four rewritten, and the literal rows collapsed to the one indexed rule. | one clause | **landed** |
| ~~10~~ | ~~`Lists.lean:13-22`~~ **Landed.** | Header advertised "three groups" incl. `List.lookup` on association lists, "the pivot is `lookup_cons`" — a group deleted, and contradicted at `:81` in the same file. The three groups are now the ones that are there, and the deleted one is named as deleted with a pointer to the note that explains it. | — | **landed** |
| ~~11~~ | ~~`Discharge.lean:529`~~ **Landed — the option was not needed; two remain, both justified.** | The one `set_option maxHeartbeats` of three with **no justifying comment**. Re-measure — it may not be needed after the representation changes. | possibly the option | trivial |
| ~~12~~ | ~~`Combinators.lean:3507`~~ **Landed — `keepB_of_entryWrite`.** | `keepB_of_encEntry` still carries the name of a deleted definition. Rename. | — | trivial |
| ~~13~~ | ~~`Refutations.lean:443`~~ **Landed — inlined.** | `abbrev decimalWF : Codec := wfDecimalCodec` — the leftover half of a unification I did; its two `rfl` lemmas are free either way. | alias + 2 lemmas | trivial |
| ~~14~~ | ~~`Exactness.lean`; `codec-formalization.md:694`; `codec-calculus.md:1129`~~ **Landed.** | "`Numeral` is `String`" no longer explained why the numeric witness is axiom-free (it is `WFNumeral`'s decidable predicate, at two sites); a superseded §4 entry named `rawNumberCodec`, `literalSCodec`, `literalNCodec`, `inLS` and `inLN`, all five deleted, and now carries a supersession note; §7 labelled `set` "quotiented", now "unordered". | — | **landed** |

## 2. Closed questions — verified impossible, do not re-test

### 2.1 `union` / `dunion` option lists: the defect is real and unfixable

**Asked again, and now closed by the kernel rather than by argument.** The payload cannot be a
set for two independent reasons, both probed:

* `NEFinset Term` needs `DecidableEq Term`, which cannot exist — `Term.custom` carries functions
  on `Value`, so deciding two `custom` terms equal decides function equality on an infinite
  domain (§11.5).
* `Multiset Term` needs no `DecidableEq` and is *exactly* what §2.1 measured — order
  unobservable (`altCodec_e_swap`), multiplicity observable (`select_dup_none`) — so it would
  change nothing about the semantics and remove the over-specification. **The kernel rejects
  it**: `arg #1 of 'T.union' contains a non valid occurrence of the datatypes being declared`.
  A quotient in a nested inductive position is not a legal occurrence.

So `union` stays list-shaped. One thing worth adding, because it narrows what the defect *is*:
`dincomp_dup` makes `DIncomp` irreflexive, so a duplicate option is never **derivable**. The
list's multiplicity is observable only at terms the judgement refuses, which is a smaller defect
than "multiplicity is observable" alone suggests.

Four theorems compiled to settle it:

```lean
altCodec_e_swap, altCodec_p_swap   -- order unobservable, extensionally
select_dup_none                    -- multiplicity IS observable
dincomp_dup                        -- DIncomp is irreflexive
```

**Order is unobservable at full extensional strength**, not merely up to `≡`. That matters:
`Codec.Equiv` is deliberately weak (`e`/`p` agree only where both are defined, and it is not
transitive), so `equiv_altCodec_swap` alone could not have settled it. But `select` reads the
list only through `filter … = [o]`, and a singleton is permutation-stable, so the `e` and `p`
*functions* are literally equal under a swap; `T` and `unanimous` are permutation-invariant;
adjacent swaps generate every permutation.

**Multiplicity is observable** — `select_dup_none` is the mechanism behind `not_ExactV_union`,
so dedup would change behaviour and `Finset` is semantically wrong even where constructible.

Together: `List` admits *n!* terms per denotation, so the shape **is** wrong; but the fitting
type is `Multiset Term`, barred by the quotient-under-an-inductive rule `Domain.lean`'s header
already cites, and `Finset Term` is barred twice (element type under declaration, *and* no
`DecidableEq Term` — `held`'s `f`/`g`, `custom`'s pair, `refine`'s `q`, `legacy`'s `r`). No
concrete key type, so the key-set-plus-function factoring does not apply.

Four hats: `Term.union`, `Term.dunion`, `List OptionSem`, `dunionCodec`'s list. Two notes:

- `dunion` is the **cleanest instance**: `htags` + `hdisj` make duplicates unreachable, so its
  list is a true set with no compensating observable at all.
- `DIncomp` is irreflexive, so `union [.string, .string]` is **not even `Typed`**. (D) is the
  only thing between the judgement and the duplicate-option defect — load-bearing in the real
  sense, not a candidate for weakening.

**Disposition:** a header note at `Term.lean`, analogous to the old `Value.set` remark.

### 2.2 Gates that are content and must stay

| gate | site | why |
| --- | --- | --- |
| `hD : ∀ d ∈ ℓ, Numeral.WF d.toDec` | `Typing.lean:176` | Typing it needs `NEFinset {d // WF d.toDec}`, which changes what `ℓ` *is* and **silently deletes** the (B) defect `literalN_holds_what_it_cannot_write` exhibits rather than proving it absent. |
| `hsm : setMember μ₀ = some μS` | `Typing.lean:179` | Says the element's member is `S`/`N`/`B`, which selects `encSet`'s branch. `Term.set` holds a `Term` — no carrier to subtype. |
| `hfb` (six signatures) | `Combinators.lean:3323` +5 | `FieldSem.fb (c) (v : {v // (c.e v).isSome})` *is* admissible and strikes all six — but cannot reach the syntax, since `Field.fallback` has no `denote` and no fuel. `fieldSemOf` would supply the proof: same obligation, moved. Net ≈ 0. |
| `htags`, `hdisj` | `Typing.lean:207-210` | ~~`tagsOf` *computes* the set from the term, so storing them duplicates derived data and needs a coherence gate of its own.~~ **This reason is wrong as stated** — see §12. It holds only if each option *keeps* its own discriminator literal; a `dunion` keyed by tag that **injects** the discriminator has one source of truth and no coherence gate. The real costs are different ones. |
| `hnd : ks.Nodup` | `Combinators.lean:3691` | `Finset Kind` *is* available, but `ks` is bound positionally to `os` by `List.Forall₂`, so order is load-bearing and `Nodup` cannot be separated from the pairing. |
| `Obligations` / `MPOk` | `Soundness.lean:55-104` | All four remaining premises are semantic relations. `MPOk (.legacy _ _) = False` reads typeable, but needs a second mutual `Term` family plus an embedding — structural duplication for a one-line gate. |

### 2.3 Collections already correctly typed

**Including their cardinality, which is unbounded on purpose.** `dynamo-datatypes.md:132` and
`:185`: *"There is no limit on the number of values in a list or a map"*, and the same for a set.
`L = List 𝔸`, `M = Name ⇀fin 𝔸` and `℘⁺fin(α)` carry no cardinality refinement, and that is
exact rather than loose — the only thing bounding breadth is the 400 KB item size, which is a
property of the item and not of any attribute. The bound that *does* exist on `L`/`M` is depth,
and it is a separate constraint that nothing enforces (§12.3).

Confirmed with the theorem that settles each: `Attr.l` / `Value.arr` (the reference says lists
are ordered and heterogeneous); `Term.tuple`, `align`/`slots`/`tupleCodec`, `HTuple`/`HProd`
(position *is* the semantics — `align_eq_zip`, `slots_length`); `HUnion`/`DIncomp` and the
`TypedList*` families (permutation-invariant in themselves, but bound positionally to `opts`,
so `List` is *forced* by the correspondence); the `denoteω*`/`κList`/`admList` folds (`||`,
`&&`). `FieldSem`/`RestSem` are not collections; their table is already `MapOf FieldSem`.

## 3. Corrections to my own record

Both caught by putting my claim into a scan's prompt as something to check, not as context.

**The rule in §4 is too narrow.** I wrote that a gate is typeable when it constrains a
collection's *shape*, content when it constrains *what the elements are*. Queue item 6 is
element-level and typeable anyway, because what is too wide is the **carrier of a
non-recursive field** — the same move `Attr.n : WFNumeral` was. As stated, the rule would
have told me to skip it. It needs the third clause.

**My `union` inference was wrong.** I argued that duplicates being observable made `List`
right. Duplicates rule out `Finset`; they say nothing about order, which is separately
unobservable. Correct conclusion: the shape is wrong and the fitting type is barred (§2.1).

## 4. Residue sweep

978 top-level declarations scanned across 19 files. 663 have no in-code reference — **not a
defect count**, this development is mostly leaf results. 153 of those are also absent from all
three documents, carry no attribute, and match no result-naming pattern. 86 theorems have a
trivial proof. **0** pairs of definitions share a body — *and that check did not cover
theorems, which is how `lawful_dead`/`carrier_dead` survived it: they are `Lawful.empty` and
`Carrier.empty` generalised over a `μ` nothing instantiates, and `carrier_dead`'s proof is
byte-identical to `Carrier.empty`'s.*

*Scan of record, taken when the audit opened. The tree is now 17 files and 960 declarations —
`WireOrder.lean`, `Denoteω.lean` and `Soundnessω.lean` are gone (items 4 and 17) and §4.1 has
landed. The reference figures above are not re-derivable against the current tree, and the
trap list at the end of §4.1 is why they should not be trusted to three digits even against
the tree they were taken from.*

### 4.1 ~~Plumbing, safe to delete (~61)~~ — landed, and the count was wrong

**36 declarations and 302 lines are gone; the build is green, warning-free and
`#assert_axioms_all` still passes.** The first pass took 32; the second pass, prompted by JH
asking whether anything else was being held up by a load-bearing verdict, took four more and
is recorded at the end of this section. What the first pass took:

- **The payload-traversal cluster** (11), `Combinators.lean` — `strPayloads`/`numPayloads`/
  `binPayloads`, their six laws, and the two `traverse_ctor_*` lemmas that fell with them.
  The section header said "Payload facts for the quotiented product" and the section after it
  says why they are gone: on `Finset` the laws are the element codec's own, lifted by
  `setImage_inv`.
- **`entrywise_e`/`entrywise_p` and the three `attr_*_of_member`** (5), `Combinators.lean` —
  the first two proved `:= carried_e` / `:= carried_p`. `carried_e`/`carried_p` were in the
  first deletion batch and had to be put back: they are consumed through dot notation
  (`(carried_e.mp h)`), which the reference scan could not see. See the traps below.
- **A duplicate section header over an empty section**, `Combinators.lean` — a
  `/-! ## The traversal toolkit -/` block, 11 lines of prose about `traverse_eq_some` and
  "the four laws below", followed by a `section Traverse` containing a `variable` line and
  nothing else. The toolkit it describes is in `Lists.lean`, where the same paragraph appears
  and is true.
- **Two `fbNames` corollaries** (2), `Combinators.lean` — one-line restatements of
  `mem_fbNames`, no docstring, no users.
- **`Opaque.lean`** (11) — `traverse_congr`, whose own docstring says "needed everywhere
  below" and which nothing now needs; the two `depthL_pos` lemmas; three `opaqCodecω_*`
  bridges, one of them documented as "the bridge `denote` will use once `opaque` stops
  carrying [a fuel]" — `denote` stopped, and used something else; and **the `opaq_p_*L` leaf
  family**, which is the most interesting of the five. Its three wire-set list lemmas were
  superseded by `opaq_p_wire_depth`: `decSet` fixes a wire set's depth at 2 outright, so the
  three-way traversal the list representation needed is not needed at all. A `℘⁺fin` dividend
  nobody had collected.
- **`Discharge.lean`** (2) — `traverse_input_isSome` and `filter_map_singleton`, general list
  utilities whose consumers went in earlier arcs.

#### What the other ~29 turned out to be, and why the estimate was wrong

The estimate came from "has no in-code reference". §4's own opening paragraph says why that
is not a defect count — *this development is mostly leaf results* — and the ~61 figure did not
apply its own caveat. Two clusters account for nearly all of the gap.

**The `adapt`/`restrict` bridging family: claimed 10, delivered 0.** `Codec.adapt`,
`partialId` and `wfDecimalCodec` have live consumers in `Exactness.lean` and
`Refutations.lean`. The three that really are unreferenced — `through_p_adapt`,
`restrict_p_adapt`, `decimalCodec_p_restrict` — are each the *read* half of a write/read pair
whose write half is cited in prose, under a docstring that says "the four theorems below are
the whole of it". The claim being checked is that the two constructions agree **as pairs**.
Deleting the read halves would leave a claim about half a codec, which is not the claim.

**`Discharge.lean`: claimed 21, delivered 2.** The other nineteen are results. The
boolean-literal cluster the audit filed as "a self-contained example" establishes that §3's
two `literal` rules are not special — a literal over any ground base is a derivable
`refine`, and a union of two discharges by the same shared-base argument. `typed_dunion_nil`
is the "and it is derivable" half of a stated claim; `typed_tRel`/`dDisj_tRel` are what make
the (D) counterexample a union (D) actually admits; the `adm_custom`/`admA_literal*` rows are
the §5 table, checked. Every one carries a docstring saying what it establishes. That is the
marker: **a declaration with no consumers is not dead if it is the output.**

Smaller misreads of the same kind: `Codec.lean`'s §2 law corollaries (the API a port checks),
`Continuity.lean`'s refutation witnesses, `Soundness.lean`'s six-row ground-term lawfulness
table (three rows are consumed, three are not, and a table is the unit), and the equation
tables in `Denote.lean` and `Equations.lean`.

#### Three traps for the next scan

1. **Dot notation.** `h.core` elaborates to `Lawful.core`, `(h.agree hp he).member_eq` to
   `Agree.member_eq`, `carried_e.mp` to `carried_e`. A scan keyed on the full declaration name
   sees none of these, and the first deletion batch broke the build on exactly this. Match a
   dotted declaration on its **final segment** as well, and match dotted tokens on every
   prefix, not only every suffix.
2. **Closed cliques.** `Codec.adapt` has a reference — from the four `*_adapt` theorems that
   exist only to relate it to `through` and `restrict`. Per-declaration reference counts cannot
   distinguish a live definition from a mutually-citing island. Iterate to a fixpoint.
3. **Macro bodies.** `term_depth_wf` keeps five `Term.depth_*` lemmas alive from inside a
   `macro` declaration, whose name is a string literal and which a decl-header regex will skip
   entirely — attributing its body to whatever declaration precedes it, and marking the whole
   group dead.
4. **Non-ASCII identifiers.** This development names things `μSyn`, `Lawful.μNone`,
   `TypedListμ`, `denoteμs`, `opaqCodecω`, `κ`. An identifier pattern built from
   `[A-Za-z0-9_']` splits `LawfulCore.μNone` into two tokens and reports it unreferenced —
   it is passed bare at `Soundness.lean:479`. Tokenize with a Unicode letter class. Fixing
   this alone moved 13 declarations from "dead" to live.

The build is the only oracle here. Every batch above was applied and built before the next one
was written, and one of them had to be partly reverted.

#### Second pass: the keeps, probed

The first pass kept about forty declarations on the argument "this is a documented result".
That argument was worth nothing on its own — the docstring is written by the same hand as the
theorem — so each keep was re-checked against corpora *outside* its own file. Almost all are
**uncited anywhere but their own docstring**, which convicts nobody (most genuine results here
are too) but does mean the original test was doing no work. Four more declarations went:

- **`lawful_dead` and `carrier_dead`** — `Lawful.empty` and `Carrier.empty` generalised over a
  `μ` nothing instantiates; `carrier_dead`'s proof is byte-identical to `Carrier.empty`'s.
- **`MapOf.at_isSome`** — the one lemma in the `MapOf.at_*` group with no docstring, subsumed
  by `at_eq_some`.
- **`Term.depth_lt_rest`** — the fourth `object` position, where `term_depth_wf` handles the
  rest case inline instead. The first pass declined to probe this one; declining was the error.

**Three suspicions did not survive contact, and the reasons are reusable.**

*A counterexample's premises are part of the counterexample.* `Refutations.lean`'s
`lawful_cA`/`cB`/`cMid` and `carrier_cA`/`cB`/`cMid` establish that the witnesses to
`¬ Transitive Codec.Equiv` are legitimate codecs — without them the refutation could be
cheating with an unlawful pair. `lazy_e_eq`/`lazy_p_eq` are what make `not_equiv_lazy`
interesting rather than vacuous: §6's row is *"the pair is the same and the `μ` is not"*, and
the first half is those two theorems. `typed_tRel`/`dDisj_tRel` in `Discharge.lean` are the
same shape. None is reachable from the headline theorem's proof term; all are load-bearing to
its meaning. This category accounts for most of the unreferenced mass in `Refutations.lean`,
`Discharge.lean` and `Exactness.lean`.

*A translation table is a unit when its rows are not derivable by name.* `Denote.lean`'s
`Bridge` section says so outright — the §6 correspondence needed "an eight-entry translation,
five entries of which share no substring with the term they translate, written down nowhere".
`denote_held = through` is the table's reason for existing; deleting the eight unreferenced
rows would leave a reader looking up `held` and finding nothing.

*And one left standing with the doubt recorded.* `Soundness.lean`'s seven ground-term
lawfulness rows (`lawful_string` … `lawful_literal`) are complete over the ground terms and
four are consumed, but each is one line (`simp only [denote]; exact lawful_stringCodec`) and
each row's name names its target — the opposite of `Denote.lean`'s case. Deleting the three
unused rows leaves an incomplete table; deleting all seven costs three edits at
`uAtCan_string_null`, `uAtCan_string_boolean` and `uAtCan_literal_literal` and saves seven
lines. **Examined, left alone, not re-litigated without a new reason.**

### 4.3 The check that should have existed: `scripts/name_drift.py`

Items 1, 2, 3, 9, 10 and 14 were six separate instances of one failure — a document naming a
declaration the tree no longer has, or describing a representation two repairs out of date.
Every one was found by a human reading, which is the same way the two drift findings before
this audit were found. **`Axioms.lean` exists because "the axiom base is clean" is worth more
as a build error than as a sentence; the same argument applies to "the documents name what
exists", and nothing was enforcing it.**

`scripts/name_drift.py` enforces it. Every backticked token that looks like a Lean name — has
a `_` or a `.`, no spaces — is checked against every identifier *occurring anywhere* in
`Calculus/*.lean`, which is deliberately loose: one use in one proof clears a citation, so the
residue is small enough to read. Structure projections clear component-wise. Deliberate
citations — a mathlib name given as future work, `FIDELITY.md`'s dated snapshot of the deleted
ω layer — live in an `EXPECTED` table with a reason each, **and a stale entry there fails the
check too**, so the suppression list cannot rot into a place where defects hide.

The current-state documents pass. Seven citations were broken when it first ran, five of them
naming declarations this branch deleted:

| document | broken citation | now |
| --- | --- | --- |
| `README.md` | `decimal_writes_wf`/`decimal_reads_wf` | `decimal_writes_stored`/`decimal_reads_stored` |
| `README.md` | `set_nil_outside_opaque` | gone with the non-emptiness premise; row rewritten to `not_TIsDomE_unionLiteralString` |
| `README.md` (×2) | `denote_not_fuel_monotone` | `stage_not_monotone`, and the surrounding claim that `lazy` carries `Unit → Term` was false too |
| `FIDELITY.md` | `denote_dunion` | `denote_dunion_tags` |
| `FIDELITY.md` | `not_survivesStore_decimalWF` | `not_survivesStore_wfDecimalCodec` |
| `VOCABULARY.md` | `recordCodec_eq` | `recordCodec_e_eq`/`recordCodec_p_eq` — `record` is not definitionally the traversal, so it gets a directional pair rather than one identity |

The `README.md` fuel row is the one worth noting: item 17 removed fuel from `denote` three
commits before this audit opened, `Continuity.lean`'s own prose was rewritten for it at the
time, and the map of the development still described the old design in two places. That is
exactly the failure mode the check catches and a reviewer does not.

### 4.4 Item 7: what a free parameter costs, and where

`objectCodecCore` took two parameters — `rc? : Option Codec` and `kn : Name → Bool` — that the
object rule always supplies together, as `rcOf rest` and `keepB rest sems`. The queue entry
scoped the defect as three hypotheses on five signatures. That was right about the hypotheses
and wrong about where the cost fell.

**What went.** The three hypotheses (`hkeep`, `hknE`, `hknDecl`), from
`carrier_objectCodecCore`, `object_retract`, `object_canon` and both halves of the private
core layer. That layer — `lawfulCore_objectCore` and `lawful_objectCore`, both `private`, both
taking five hypotheses — turned out to exist for no reason except to be instantiated by
`lawful_objectCodec`/`lawfulCore_objectCodec` one line later, so it is deleted and inlined.
`carrier_objectCodecCore` is now `carrier_objectCodec`.

**Where the cost actually was.** Not in the five signatures, which a reader skips. In
`Soundness.lean`, the `object` case of `carrier_denote` carried a ten-line `have hkeep` that
re-proved `keepB_of_declared` by hand, in full, because the hypothesis asked for it and the
lemma discharging it was not in scope at that altitude. **A free parameter with one
instantiation does not cost you the parameter; it costs you a re-proof at every call site that
cannot see the discharge.** One call site here, ten lines, and it is the kind of duplication
that no reference count and no `simp` set will show you.

`keepB_of_entryWrite` and `keepB_of_declared` were queued for deletion along with the
hypotheses. They are not deleted — they are used three times between the specialized laws, and
they are the *content* of what the hypotheses were asking for. They moved up the file instead,
above the theorems that now discharge with them, next to `rcOf_forall`, which does the same job
for the other half of `rest`.

**What did not go, and the probe that settled it.** `objRead`, `objWrite` and
`objectCodecCore` still take `rc?` and `kn`. After the laws were specialized no proof outside
that block mentions `kn` at all, so the block is self-contained — but collapsing it deletes no
declaration and lengthens `objRead_eq`'s statement by four occurrences of `keepB rest sems`.
A parameter is where a payload function's argument belongs; the defect was hypotheses on laws.
Measured, left.

### 4.2 Scaffolding

- ~~**Exactly 3 `set_option maxHeartbeats`**~~ **Two, both in `Exactness.lean`, both
  justified** — item 11 deleted the third, which was the one with no justifying comment, by
  re-measuring rather than by argument.
- **0 `sorry`, 0 `admit`, 0 commented-out code.** All 25 `admit` greps are prose.
- **2 `attribute [local simp]` blocks in `Opaque.lean`, byte-identical, 160 lines apart** —
  nothing stale, but one shared section would do.
- **52 bare `simp` in `Finset`-touching proofs — and the premise of that check does not hold
  here, which is good news.** `#assert_axioms_all` walks the namespace and fails the build if
  any constant exceeds the sanctioned axioms, so a bare `simp` routing through
  `Classical.choice` is a **build error, not a silent widening**. The residual risk is
  fragility under a mathlib bump, not unsoundness.

## 5. Prior art

The most consequential scan. Summary: **the domain is novel, the machinery mostly is not.**

### 5.1 Closest work

1. **PulseParse / EverCBOR / EverCDDL** — Ramananandro, Ebner, Martínez, Swamy, [arXiv
   2505.17335](https://arxiv.org/abs/2505.17335) (2025). *The closest existing artifact.* CBOR
   is a tagged coproduct with maps, arrays and byte strings plus a deterministic fragment;
   they prove that fragment non-malleable, formalize the CDDL schema language, and — the part
   that matters — *"identify well-formedness conditions on CDDL definitions that ensure that
   they yield unambiguous, non-malleable formats"*, mechanically checked, then generate
   parsers **and** serializers. That is our (U) plus its dischargers, one year early.
2. **Narcissus** — Delaware, Suriyakarn, Pit-Claudel, Ye, Chlipala, ICFP 2019.
   [ACM](https://dl.acm.org/doi/10.1145/3341686) · [preprint](https://arxiv.org/pdf/1803.04870).
   A format is a **relation**, not a function pair — see §5.4.
3. **EverParse / LowParse** — USENIX Security 2019.
   [paper](https://www.usenix.org/conference/usenixsecurity19/presentation/delignat-lavaud).
   Laws: safety, inverse-ness, and **non-malleability**.
4. **A Verified Protocol Buffer Compiler** — Ye & Delaware, CPP 2019.
   [ACM](https://dl.acm.org/doi/10.1145/3293880.3294105). Confronts "the same source data can
   be encoded in infinitely many ways" — a direct hit on our `η`.
5. Ancestry: Kennedy, *Pickler Combinators* (JFP 2004) is our combinator inventory minus the
   proofs; Rendel & Ostermann, *Invertible Syntax Descriptions* (2010); Danielsson, *Every Bit
   Counts* (JFP 2012); Tan & Morrisett, *Bidirectional Grammars for Machine Code* (JAR 2017),
   explicitly partial both ways; Zaliva et al., *Verified ASN.1 stack* — where formalizing
   revealed the **standard** was wrong (DER booleans admit several encodings), precedent for
   measuring `η` against a real table.

### 5.2 What to call `(T, μ, e, p)`

Not a lens — `p` does not take the old source, so PutPut is not merely unproved but
meaningless, and asking for it is the first thing a reader will do. Not a Galois connection —
no order on values, and (C) is a definedness side condition, not an adjunction. A **prism** is
the right intuition and the wrong laws (a prism's `build` is total). The accurate name is a
**partial embedding–projection pair**: (R) is `p ∘ e = id` on `T`, and (MP) is the `e ∘ p ⊑ id`
direction with the domain order replaced by "agrees with". Shortest honest sentence: *partial
isomorphisms relaxed to hold only up to store normalization on the attribute side.* (C) as a
definedness condition is standard — Narcissus states encoder correctness the same way.

### 5.3 (U) is reinvention

Named at least four ways: **unambiguity / non-malleability** (EverCDDL, LowParse); **unique
decodability** (Danielsson states our attribute half verbatim); **disjointness for untagged
union elimination** — a live line: Rehman, Huang, Xie, Oliveira, *Union Types with Disjoint
Switches*, ECOOP 2022 ([PDF](https://xnning.github.io/papers/ecoop22switches.pdf)), and Backes,
Hriţcu, Maffei (J. Comp. Security 2014) on **static reasoning about type disjointness with
refinement predicates** — which is our shared-base-refinement discharger; and **predict-set
disjointness** on the parsing side. The concept has a name; take *unambiguity*, with
disjointness as the discharge technique. What was *not* found is a packaged decidable family of
dischargers for a document-store attribute domain — engineering novelty, not conceptual.

### 5.4 The exactness apparatus

Two halves with different answers. **"Exact, not merely sound" is known**: this is
completeness in abstract interpretation — Cousot, *Completeness in Static Analysis by Abstract
Interpretation* ([arXiv 2211.09572](https://arxiv.org/abs/2211.09572)), whose framing
("completeness is usually forgone from the start") is our axis; and the modern refinement,
**local completeness** (Bruni, Giacobazzi, Gori, Ranzato), is precisely "complete on the parts
that matter, and here is the exact place it is not". Two `Bool`s over-approximating
`dom e`/`dom p`, exact on 16 of 23 forms, is a *locally complete* analysis. Cite it or a
reviewer will. **The witnessed escape hatch: no prior art found** — claim it, framed as
*locally complete domain analysis with certified incompleteness witnesses*, and do not oversell
it; it is proof engineering, not new science.

### 5.5 DynamoDB — this heading is empty, and that is the strongest claim

All AWS formal-methods output is protocol or policy, never the data type mapping: the
DynamoDB ATC'22 paper (TLA+ on **replication**), Newcombe et al. CACM 2015, the S3 ShardStore
SOSP'21 paper (crash consistency), Physalia NSDI'20, Cedar (Dafny model of an authorizer).
Nobody has formalized DynamoDB's attribute domain, or any document store's data type mapping.
Adjacent but not prior art: *Foundations of JSON Schema* (WWW 2016) and the NoSQL
schema-inference literature are validation semantics, not proved codecs.

### 5.6 Criticisms worth acting on

Requested explicitly, and the sharpest ones continue this session's own arc:

1. **(W) wants to be a type index, not a law.** If `Codec` were indexed by its stored member —
   `Codec μ` — (W) is discharged structurally for every combinator and vanishes as an
   obligation. This is exactly the side-conditions-into-types move, applied to the one law it
   was not applied to.
2. **(U) wants to be a field, not a hypothesis.** If a discharger *value* sat in the `union`
   constructor, the arc completes there too. The λ_u experience is that untagged unions with
   overlap are a pit and the fix is to make disjointness a typing requirement.
3. **The exactness apparatus may be a symptom.** We need a decidable over-approximation of
   `dom e` *because* `e` is partial on `T`. If `T` carried enough structure that encode were
   **total** on it — precisely what the five repairs did for unorderedness, key-uniqueness,
   non-emptiness and numeral well-formedness — then `Adm` on the value side and its exactness
   theorems would be unnecessary. Worth asking honestly how many of the 7 non-exact forms are
   non-exact because *the value type is still too loose*. If most are, the right move is to
   keep the apparatus only on the attribute side, where partiality is forced by the medium.
4. **A relational format would collapse three laws into two.** With `fmt : V → Set 𝔸`
   (Narcissus), normalization becomes part of the *specification*: "decode inverts `fmt`" and
   "encode refines `fmt`" replace (R)+(C)+(MP), and `η` stops being a separate relation
   compared against `ker p`. Leading refactor candidate.
5. **Hand-written combinators with hand-proved laws is what Narcissus exists to argue
   against**, and ~700 theorems for 23 term forms is evidence for their position, not ours.
6. **The escape hatch has no bound.** It prevents silent widening but not loud widening, and
   nothing stops it reaching 23 excuses and a vacuous claim. Consider a theorem about the
   excuse set itself.
7. **The axiom guard is hygiene, not novelty** — and note our own record that `omega` can pull
   `Classical.choice`, which is why it is load-bearing.

### 5.7 To adopt

**Differential testing against the shipped TypeScript**, the way Cedar and ShardStore do it:
generate random terms and values from the deep embedding, run the Lean-evaluated reference and
the TS implementation, diff. This is the realistic answer to certifying the port — extraction
to TypeScript is not credible. **QuickChick-style derived generators** with soundness *and*
completeness proofs against an inductive relation would turn `Adm`/`AdmA` into a test oracle
for free and feed the above. **Read next:** arXiv 2505.17335, then Narcissus §3–4.

## 6. Carrier refinements: the axis is closed

**Zero defects *on this axis*** — the axis being "which members of `𝔸` carry a subtype". §12
records the constraint this framing let through: a limit that cannot be a carrier refinement is
still a limit, and depth is one nothing enforces anywhere.

The authoritative list is C1's own table at `codec-formalization.md:1871-1876`
— exactly four members carry a refinement, `N` (grammar / 38 digits / magnitude) and
`SS`/`NS`/`BS` (non-empty), and **all four are now enforced**. Every remaining constraint in
`dynamo-datatypes.md` is either a resource limit §1 deliberately omits or a schema-position
limit about tables, indexes and keys that the model does not have.

| ref | constraint | verdict |
| --- | --- | --- |
| `:27` | attribute names ≥1 char, <64 KB | **OUT-OF-SCOPE-BY-SPEC.** §1's `M` row is `Name ⇀fin 𝔸` with no refinement and C1's table omits `M`. The non-emptiness half *is* kernel-admissible (`{s : String // s ≠ ""}`), but `Name` is a collection element type and function domain, not the carrier of a non-recursive field in the `Attr.n` sense — coercions and instances at ~35 map sites in the largest file, for no spec mandate. Highest cost of any candidate. **Not worth doing.** |
| `:80`, `:103` | string/binary min length zero *"unless a key"* | **NOT-TYPEABLE.** A contextual permission; a subtype cannot express "unless it is a key" without a key concept the model lacks. Would also cost a witness (`Refutations.lean:203` uses `.str ""`). |
| `:83-84`, `:106-107` | partition key ≤2048 B, sort key ≤1024 B | **OUT-OF-SCOPE**, un-typeable in principle — constrains a position in a table schema, not membership in `𝔸`. |
| `:80`, `:103` | item size ≤400 KB | **NOT-TYPEABLE.** A global aggregate over the recursive structure; enforcing it refines `Attr.l`'s list and `Attr.m`'s function — the recursive occurrence, which the kernel rejects. A subtype on `Item` alone is admissible and vacuous. **Not checkable per attribute either** — it is a property of the *item*, so unlike depth it cannot be a codec's obligation. See §12.3. (Cited `:132`/`:185` here until JH pointed out those lines say the opposite; corrected below and in §2.3.) |
| `:132`, `:185` | **no** limit on the number of values in a list, map or set | **NOT A CONSTRAINT — and the model is already right.** *"There is no limit on the number of values in a list or a map, as long as the item containing the values fits within the DynamoDB item size limit."* `L = List 𝔸`, `M = Name ⇀fin 𝔸` and `℘⁺fin` carry no cardinality bound, which is exact. Recorded so nobody tightens it later. |
| `:130` | nesting ≤32 levels | **NOT TYPEABLE AS A SUBTYPE** — `{as : List Attr // Attr.depthL as ≤ 31}` nests `Attr` under its own declaration, which the kernel rejects, exactly as for item size. An *indexed family* `Attr : Nat → Type` is a different move and the kernel takes it; §12.4 has the probe and the price. ~~And typing it would destroy live theorems: the ω-codecs' totality argument depends on depth being unbounded.~~ **That second reason is wrong.** `Opaque.lean:17-20` supplies *each input its own budget* — `Value.depth` on the write side, `Attr.depth` on the read side — and a cap on the carrier makes those budgets bounded, not ill-typed. The un-typeability is the whole of it. **But see §12: un-typeable is not un-checkable, and nothing checks it.** |
| `:63-65` | ≤38 significant digits, magnitude range | **ALREADY ENFORCED** — `WFNumeral`. |
| `:134`, `:183`, `:187` | sets non-empty, unique, unordered, homogeneous | **ALREADY ENFORCED** — `NEFinset`. |
| `:20-39` | table/index names, reserved words, `#`/`:` | **OUT-OF-SCOPE** — no table, index or expression language in the calculus. |

**Sharpened rule.** The `WFNumeral` move generalises to *concrete, non-recursive field
carriers* only. Depth and item size are the canonical inadmissible case: they refine the
recursive occurrence itself, and no restatement turns them into a subtype. The reference's
size limits are resource limits and §1 excludes them on purpose — treating them as `𝔸`
membership would itself be the defect.

## 7. The exactness hatch: one promotion, one wrong reason

Ranked most to least retirable. Static reading only, so the promotion is *"looks provable,
record-shaped"*, not checked.

**`nameAdmission` — the object half looks promotable.** The excuse survives (its `tuple`
witness `not_ExactV_tuple` still holds), but `ExactV (.object …)` now looks provable. Object
encode demands exactly two things (`objectCodecCore_e_inv`): `valPresentB sems keys = true`,
and `funImage (fun k => (entryCodec …).bind (·.e (f k))) = some g`. Both are decidable over a
`Finset Name` plus a function — *exactly* the shape of the `record` row that was already
repaired, which closes via `funImage_isSome_iff`. Crucially the `fb` stand-ins
(`fbNames`/`fbValue`) and `keepB` live only in `objRead`, so they constrain `p`, not `e`; on
the write side `valPresentAt` treats `.fb` like `.req` and is a plain `decide`. To land it:
rewrite `Adm`'s `.object` row, fill the `.object` case of `Adm_exact`, flip `Analysable`, and
**delete the `nameAdmission → .object` row from `Excuse.covers`** or `excuse_shapes` and
`analysable_excused` break. The attribute side stays excused.

**`payloadShape` — the stated reason is now wrong; the excuse survives for two different
reasons.** It says *"`asWireSet` demands payload homogeneity: a fact about attributes, not
values"*. Homogeneity of values and non-emptiness are structural now, so that sentence is
stale. `not_ExactV_set` still holds, and it is not about homogeneity at all: `collapse` sends
both elements to one string, so both admit while `setImage`'s `Nodup` check refuses. The two
real obstructions, neither visible to any `Bool` on terms:

1. **Collision.** `setImage` requires the images be `Nodup`; element-wise admission cannot see
   a collision *between* two elements.
2. **Wire-kind agreement.** `encSet` picks one kind by trying `sC`, then `nC`, then `bC` for
   *all* elements. A `.custom` codec may send different `.str` inputs to different `Attr`
   constructors, so all three passes fail while every element individually writes. This is the
   surviving residue of the old "homogeneity" reason — genuinely about attributes, but stated
   as if it were the whole story when the witness proves otherwise.

Correct reason: *a set codec must write its elements to **distinct** payloads of a **single**
wire kind; element-wise admission sees neither the collision nor the kind disagreement.* Fix
at `Exactness.lean:281-282` and in `Analysable`'s bullet list; `Adm`'s `.set` comment is
already right, and `not_ExactV_set`'s own docstring already states the corrected reason.

**`opaqueDepth`, `uniqueAdmission`, `nullOwnership`, `valueUnderRead` — reasons accurate,
witnesses hold, not retirable.** Two imprecisions worth fixing:

- `not_ExactV_opaq`'s docstring — **my own sentence** — claims that after the set repair the
  numeral gate is "the only place" `⊤` over-claims. But the constructor's named reason is
  *depth recursion*, and what the witness exhibits is the *`refuse` policy* having no number
  option. Those are two different over-claims; the witness is a policy witness, not a depth
  witness.
- Pre-existing, not from this batch: `Excuse.covers` files `.dunion` under `uniqueAdmission`,
  while `Analysable`'s bullet gives `dunion` a *different* reason ("the tag is checked, the
  matched option's own admission is not").

**Net for `Analysable`/`AnalysableA`:** exactly one promotion available, `.object` on the value
side. `AnalysableA` gets none — the object read still goes through `fbNames`/`fbValue`/`keepB`.

## 9. TypeScript conformance — five live bugs

The model exists to certify `src/`. The five tightenings were used as a checklist against it.
`src/codec.ts` (4023 lines) is the library, `src/attribute.ts` the domain, `src/native.ts` the
AWS-SDK-compatible marshaller.

### 9.1 Correspondence (C2/C3) — total, with two holes

The mapping is already tabulated at `codec-formalization.md:1929-1981`: 24 `CodecDef['kind']`s
against 22 `Term` constructors, stratified `TermDef`/`FieldDef`/`RestDef` with a type-level
assertion that fails the build on an unclassified kind. Checked term by term against
`Term.lean:21-71` — **all present**.

- **GAP** — `literal<const T extends string | number>` (`codec.ts:871`). Lean's arity-one
  `literal` takes any `Value`, so `literal (Value.bool true)`, `literal Value.null` and
  `literal (Value.bytes …)` are model terms with no TS constructor.
- **GAP, still open** — `native` files itself under `def: { kind: 'opaque' }`, so the C3 table
  counts it as `.opaq`. **It is not the same pair**: it writes `NS`, reads `NS`, and honours
  `convertEmptyValues`, none of which `opaque`'s `(T, μ, e, p)` does. One kind, two different
  codecs — and **every bug below hid in the half the table does not describe.** The four C1
  violations are fixed, so the two pairs no longer disagree about what an `N` *carries*; they
  still disagree about everything else, and the table still describes only one of them.

### 9.2 The five tightenings

| # | tightening | verdict |
| --- | --- | --- |
| 1 | `M` unordered, unique-keyed | **OK** — `record`/`object` walk key-by-key; a JS object cannot carry a duplicate and no branch reads enumeration order. |
| 2 | object field tables a set | **OK** — `spec` is a `Record<string, AnyCodec>` flattened once; keys unique by construction. |
| 3 | sets non-empty by type | **OK** in `codec.ts` (all four refuse, and the comment names (C) as the reason). ~~**BUG** in `native.ts`~~ — **fixed**: all three of `SS`/`NS`/`BS` now refuse an empty stored set on read, through one `nonEmpty` helper carrying the (C) argument. |
| 4 | literal alternatives non-empty, repeat-free | ~~**BUG**~~ — non-emptiness **fixed**, see 9.3. Repeat-freedom is still not checked. |
| 5 | `Numeral.WF` on both halves | **OK** in `codec.ts` — `isNumeral` at `992-1006` explicitly cites `Numeral.WF`; both halves gated for `number` for `number`, `decimal`, numeric `literal` and `opaque`. **§4's two named defects are closed there.** ~~**BUG** in `native.ts`~~ — **fixed**, see 9.4. |

### 9.3 ~~`literal()` with no alternatives admits everything~~ — fixed

`codec.ts:874-879` takes `...allowed: readonly T[]`, so **zero** arguments typecheck; and
`admits` at `937-942` is `allowed.length && !allowed.includes(...)`, whose short-circuit makes
an empty `allowed` admit **every** value. So `literal()` compiles and is a codec that encodes
any string as `S` and decodes any `S`. The model has no such term — that is exactly what
`NEFinset` now forbids — so the construction has no denotation, *and* it is silently the wrong
codec: the caller asked for an enum and got `string`.

Also **GAP**: no repeated-alternative check, so `literal('a','a')` is accepted where the
model's `NEFinset` cannot express it. Semantically benign, but C3's "the constructor denotes
this term" stops being injective.

The rest of the family is right: mixed-kind refusal, `ℓ ⊆ D` at construction, a genuine
read-side numeral gate.

**Fixed** by a construction-time `CodecError` beside the other two refusals, and by deleting the
`allowed.length &&` guard rather than correcting it — a truthiness guard in front of a membership
test *inverts* the test exactly when the set is empty, where `∀ x. x ∉ ∅` should refuse
everything. Not a type, and the reason is worth recording: `literal(...Object.values(Status))` is
an honest call that spreads a plain array, which a `(first, ...rest)` signature refuses. The type
cannot carry `ℓ ≠ ∅` without breaking the caller who most wants it, so the construction site
does. The repeated-alternative GAP is untouched.

### 9.4 ~~`native.ts` — four C1 violations~~ — all four fixed

- **`native.ts:78-95`** gates the write on `Number.isFinite` plus `MAX_SAFE_INTEGER`, then
  `carrying('N', value.toString())`. `5e-324` is finite and inside the safe range, so it
  **writes `⟨N, "5e-324"⟩`** — outside `Numerals`. This is precisely the defect §4 records
  `opaque` having had, one file over, still live.
- **`native.ts:226-230`** `fromNativeNumber` is `Number(digits)` with no `isNumeral`. So
  **`{N:''}` reads as `0`** — §4's other named defect, still reachable in this repo through
  `native`. Also `{N:'0x10'}` → `16`, and `{N:'abc'}` → `NaN` returned.
- **`native.ts:265-269`** `NS` decode maps `fromNativeNumber` with neither a numeral check nor
  an emptiness check: `{NS:[]}` and `{NS:['abc']}` both decode.
- **`native.ts:270-271`** as in 9.2 row 3.

**Fixed, and it is a deliberate divergence from the SDK rather than a repair of the port.**
`convertToAttr` checks a finite double on the way in and `convertToNative` checks *nothing* on
the way out; `Carries('N')` is neither. So the port now gates both halves on `isNumeral` and
refuses the three empty stored sets, which means it refuses four things the real SDK accepts —
each one an attribute DynamoDB itself rejects or never wrote. `native.spec.ts` records this as a
`describe` that asserts **both** sides: that the SDK really does the permissive thing, and that
this refuses it. `native.Deviations` (`readNumber`/`writeNumber`) is the way back for a team
migrating a table that already holds such rows, and there is a test that it reproduces the SDK
byte for byte.

One gate suffices on `native`'s read side where `number` needs two: `number`'s second gate
catches a stored numeral that rounds *out* of range on the way into a double, and this reader
hands a wide value back as a `bigint` of the very digits stored, a narrow one from inside the
safe range. Nothing it returns can fail to be writable again.

### 9.5 The C1 embedding verifies — but §5's term list is incomplete

`AttributeValue = ExactlyOne<AttributeCarries>` (`attribute.ts:21-45`) is the unrefined host
`𝔸`. The inhabitants with no image in the model's `𝔸` are exactly:

1. `{N: s}` for `s` failing the grammar, 38 digits, or magnitude — `{N:''}`, `{N:'NaN'}`,
   `{N:'0x10'}`, `{N:'5e-324'}`, `{N:'1e400'}`;
2. `{SS: []}`; 3. `{NS: []}` and `{NS: [s,…]}` with any `s` failing (1); 4. `{BS: []}`.

That is the whole surface, and it is closed because `AttributeCarries` has exactly ten keys and
the other six carry host types the model carries unrefined. **§5's claim that the list is short
and closed verifies.** What does not verify is §5's *term* list: it names `decimal`, `number`,
`literal`, `set`, `opaque` as the terms touching a refined member — and omits `native`, which
touches `N` on both sides, `SS`/`BS` on the read side and `NS` on both, and gated none of them.
It gates all of them now; the list is still wrong, and that is §9.6's remaining item.

### 9.6 Fixes, in order

1. ~~**Route `native.ts`'s number write and read through `codec.ts`'s `isNumeral`, and add the
   emptiness check to its `SS`/`BS`/`NS` decode.**~~ **Landed** — though not by routing through
   `codec.ts`; see §9.7.
2. ~~Make `literal()`'s empty case a `CodecError`, beside the mixed-kind refusal.~~ **Landed.**
3. **Open.** Add `native` to §5's term list, or give it its own term and stop filing it as
   `opaque`. The second is the honest one and it is a model change, not a `src/` change: `native`
   is a fourth pair over `unknown` whose `μ` is nine members wide, and the C3 table currently
   claims `opaque`'s row describes it. §9.1's surviving GAP is the same item.

### 9.7 Where `Carries('N')` lives now

`isNumeral` and `isStoredNumeral` moved from `codec.ts` into `attribute.ts`, exported. §9.6's
first item was written as "route `native` through `codec.ts`'s `isNumeral`", and that is the
wrong direction: `native.ts` is a sibling entry point, deliberately dependency-free, and it
should not import a codec module to learn what an attribute carries.

The predicate is not a property of any codec. It is `Carries('N')` — a property of the *carrier*,
which is what the `Attr.n : WFNumeral` change made exact on the Lean side. `attribute.ts` is the
unrefined host `𝔸` (§9.5), so it is where the refinement belongs, and `codec.ts` and `native.ts`
now import the same one. That is why one file's fix closed four bugs in another: before, there
were two answers to "what does an `N` carry", and only one of them was written down.

The cost is that `isNumeral` is public API (`Rotorise.ts` re-exports `./attribute`). That is
defensible — a caller checking a string before a write is asking a real question — but it was not
a decision the fix needed, and it can be walked back with an internal module if it becomes one.

## 10. EverCDDL, read

Read from the arXiv HTML (§2 PulseParse, §3 EverCBOR, §4 EverCDDL). Quotes are from that
text; where a gloss is inference rather than the paper's own words it is marked.

### 10.1 Their (U) is the *definedness of a compilation pass*, not a premise

**Theorem 4.4.** *"Given a CDDL type `t`, if `elab(t)` is defined, and `p` is the parser
specification associated with `t`, then `p` is injective."*

That is our (U), and the factoring is better than ours. They do not carry a side condition on
the rule and then supply dischargers; they run an **elaborator**, a partial function on
schemas, and *its definedness is the well-formedness check*. `EverCDDL` is "a tool that checks
that a CDDL definition is well-formed, and then produces verified parsers and serializers for
it" — so the user never discharges anything. Theorem 4.3 is the bridge: the elaborated type
has "equivalent validation semantics to the original".

This sharpens the criticism in §5.6.2. (U) does not merely want to be a *field* of the `union`
constructor; it wants to be the **output of a checker** — an `elab : Term → Option Term'` whose
definedness implies the property, with our existing dischargers as its cases. `UAtAct` in
`Obligations` becomes `elab t = some t'` and stops being a semantic obligation the caller
proves.

### 10.2 Their serializer's *type* carries the round trip — this is (R) as a type

```
serializer p = (x: t) → (b: seq U8.t { p b == Some (x, length b) })
```

The refinement is in the codomain, so **(R) holds by construction and is not a law**. Our
analogue is available and constructible, because a Lean structure field may mention an earlier
one:

```lean
structure Codec where
  p : Attr → Option Value
  e : (v : Value) → Option {a : Attr // p a = some v}   -- (R) is the type
```

That would make (R) — the *first* law, not a side condition — structural for every combinator,
which is the largest remaining instance of this session's move. **But it is not obviously
right, and the tension is worth stating rather than resolving:** it fuses definitions with
proofs, so each combinator's `e` produces the retract witness inline instead of once in
`lawfulCore_*`; `Codec.Equiv`, `Codec.Approx` and the `Continuity` results all compare `e`s
whose types would now differ; and Narcissus deliberately went the *other* way, separating a
relational spec from its correctness. It is the same work relocated, and readability is the
thing being traded. Worth a spike, not a commitment.

### 10.3 Non-malleability: they prove it, we deliberately fail it — and `ker p` is the measure

Their property, §2.1: *"if `p(b1) = Some (v, n1)` and `p(b2) = Some (v, n2)` … then `n1 = n2`
and `b1` and `b2` coincide on their first `n1` bytes"* — two inputs decoding to one value must
be equal.

Our analogue would be: `p a₁ = some v → p a₂ = some v → a₁ ≈ a₂`. **We do not have this theorem
and should not: our `ker p` is deliberately not equality**, and §2's two surviving reasons —
`η` normalising an `N`, `drop` discarding names — are exactly its failures. Their CBOR result
holds only of the *deterministic fragment*; DynamoDB has no deterministic fragment, because the
store itself rewrites numerals.

So the honest move is to name the property in their vocabulary and state where it fails:
`SurvivesStore` (`η ⊆ ker p`) is precisely the condition under which the failure is harmless,
and `ker_decimalCodec` / `not_survivesStore_decimalWF` are already the two halves. This costs
nothing and buys legibility to the verified-formats community.

### 10.4 EverCBOR keeps the representation we abandoned — and is right to

Their raw map type, §3.2:

```
Map: (len: raw_u64) → (v: nlist (raw_data & raw_data) len.value) → raw_data
```

A **list of pairs with "no duplicate checking in raw form"**, with key uniqueness as a `valid`
predicate (§3.3: "no two entries have equivalent map keys"), plus **Theorem 3.2**, a
lexicographic byte order on keys, because deterministic CBOR sorts map entries.

That is the representation this arc spent five sites removing, plus the canonical order
`WireOrder.lean` was built for. **The reason they need it and we do not is the layer**: their
`raw_data` models *bytes before parsing*, which genuinely is an ordered sequence that can
repeat a key. DynamoDB's `𝔸` is *post-parse* — the SDK hands over a map, not a byte string —
so our carrier can be exact and no order is forced.

This retro-justifies the arc and simultaneously explains why `WireOrder.lean` is dead (§1 item
4): the module was importing a wire-level obligation into an API-level domain. **The design
axis is whether the domain is the wire or the API**, not whether typing is better than gating.
Worth recording, because it is the answer to "why does the closest prior art not do what we
just did".

### 10.5 Three of their four well-formedness conditions we get free

| their condition (§4.1, Thms 4.1–4.4) | ours |
| --- | --- |
| "all alternatives must be disjoint" (map-group choice) | **(U)** — the one that survives |
| Kleene star: "if `∗a1,∗a2,a3` appears, then `a1` and `a2` must be disjoint and `a1` and `a3` must be disjoint" | free — our `tuple` + tail assigns **positionally** via `align`; there is no boundary to locate |
| map concatenation: "if `g1,g2` appears, then the footprints of `g1` and `g2` must be disjoint" | free — `object` + `rest` dispatches on `k ∈ keys` via `entryCodec`, so the declared and open groups are disjoint by construction |
| "deterministic map form" `g ::= ℓ ⇒ t \| ℓ : t \| ∗(tk ⇒ tv) \| g1 // g2 \| ?g \| g1,g2` | n/a — no group grammar; the field table *is* a `MapOf FieldSem` |

**This reduces the reinvention claim in §5.3.** Three of the four are *ambiguity conditions
forced by having to find boundaries in a byte stream*. Only the choice condition is
domain-independent, and that is the one we have. Our (U) is not "EverCDDL's well-formedness
conditions, rediscovered"; it is the single condition of theirs that survives the change of
layer — and the other three being discharged by our representation is a point in the
representation's favour.

### 10.6 One caveat on the extraction

The gloss *"this implies the elaborated parser's domain is exactly the set of valid CBOR items
for that type"* attached to Theorem 4.4 was the extraction's inference, not a quoted theorem.
Injectivity is not exactness of a domain, so **the §5.4 conclusion stands as written**: the
"exact, not merely sound" domain result is still ours, and the reference for it is local
completeness in Cousot's sense, not this paper. Confirm against the PDF before citing.

## 11. The literal family collapses to one rule

Raised mid-item-6, and it subsumes it.

**The specification already has one rule.** §3 of `codec-calculus.md:230` reads

```
⊢ g : T ⇝ μ,  g ground    ℓ₁ … ℓₙ ∈ T,  n ≥ 1,  pairwise distinct
───────────────────────────────────────────────────────────────── (literal)
⊢ literal(ℓ₁ … ℓₙ) : {ℓ₁ … ℓₙ} ⇝ μ
```

One rule, n-ary, with `g ground` as a premise. The model has three constructors, and this is not
a case of the model being more precise than the spec — every part of that premise line is now
expressible as a type. `g ground` is a `GroundKind` index; `n ≥ 1, pairwise distinct` is
`NEFinset`, which the model already uses for `literalS` and `literalN`; `ℓᵢ ∈ T` at the indexed
carrier is what makes the set homogeneous. So the collapse is not a new design — it is **the
model finally transcribing the rule it has**, which is the same argument the five landed repairs
made one representation at a time.

Three constructors —

```lean
| literal  (v : GroundValue)        -- after item 6
| literalS (ls : NEFinset String)
| literalN (ls : NEFinset Double)
```

— are three readings of one thing: **a nonempty finite set of values, all at one ground base.**
`literalS` is that at `String`, `literalN` at `Double`, and item 6's `literal` is that at
cardinality one, which is why item 6 is the prerequisite rather than a competitor: it is what
turns arity-one from "a `Value`, if it happens to be ground" into "a ground base and a value".

### 11.1 The form that keeps the payload a `Finset`

```lean
inductive GroundKind where | string | number | boolean | binary | null
def GroundKind.Carrier : GroundKind → Type
  | .string => String | .number => Double | .boolean => Bool
  | .binary => Bytes  | .null   => Unit
def GroundKind.member : GroundKind → Member          -- total, as item 6's is

| literal (k : GroundKind) (ls : NEFinset k.Carrier)
```

`literalS ls` is `literal .string ls`; `literalN ls` is `literal .number ls`; item 6's
`literal (.str s)` is `literal .string {s}`. Three properties stop being premises and become
the type's: **non-emptiness** (already `NEFinset`'s), **homogeneity** (all elements share a
base because they share a carrier), and **the member** (`k.member`, a function of the index —
item 6's deletion of `hμ`, now for the whole family). `NEFinset Unit` at `.null` is a
singleton, so `literal .null` cannot say anything but the one thing it means.

What stays a premise is `hD`: `∀ d ∈ ls, Numeral.WF d.toDec` at `k = .number`, as a `Bool` over
the dependent pair. **It must stay** — §2.2's first row is the reason. Typing it into the
element carrier silently deletes `literalN_holds_what_it_cannot_write`, the witness that (B)
fails without it, rather than proving the defect absent.

### 11.2 The version to refuse

`literal (ls : NEFinset GroundValue)` — no index, one flat set. Tempting, and wrong: a set may
mix `.str` with `.num`, so the member is no longer a function of the payload and the rule needs
`hhomog : all elements share a base`. That is `hμ` returning under a new name, one commit after
item 6 deleted it. The index is what makes homogeneity unsayable-otherwise.

### 11.3 Cost of the indexed route, honestly

`Term` gains a dependent field, so every `cases w` in `Discharge`/`Exactness` becomes `cases k`
first — tractable (the carrier reduces once `k` is a constructor) but it is the dependent
elimination the object-field work already paid for once. `literalS`/`literalN` are named **266
times** across twelve modules, `Discharge` alone 118. `tagsOfField` reads `literalS` for
`discriminatedUnion`'s tags and `Refutations` builds the §2.1 union witnesses out of it, so both
need the new spelling before anything compiles.

This is a day, not an hour — and §11.4 settles that it is the *fallback* day's work rather than
the first choice, with §11.5 naming the one measurement that decides between them. Either way it
is the last of the five representation repairs' family: the four that landed each replaced one
gate with one type, and this replaces *constructors* with the thing they differ in.

### 11.4 The other answer, which the record already gave — and it is the right one

`codec-formalization.md:632` got here first, and answered differently: retire `literalS`/`literalN`
and let **the n-ary form be surface syntax for the union**, "which the `⋃` rows on `adm`/`admA`
made lossless". No new constructor at all — strictly cheaper than §11.1 if it holds.

It may well hold *denotationally*. §2.1's defect is about duplicate options and order:
`altCodec_e_swap`/`altCodec_p_swap` make order unobservable, and `select_dup_none` makes
multiplicity observable — but a `Finset`'s elements are distinct, so a union of distinct singleton
literals dodges the one thing that is observable. Taken as a claim about `adm`/`admA` I have no
reason to doubt it.

I raised two objections to it and **both were wrong.** `Calculus/LiteralArity1.lean` was written
to settle them and does, by proof rather than by argument — that file is the evidence, and it
changes the recommendation from §11.1 to this one.

1. **`tagsOf` needs no homogeneity proof.** I claimed the union route would have to recognise *a
   union whose every option is a singleton string literal* and prove homogeneity while rebuilding
   the `Finset String`. It does not: a non-conforming option contributes `∅`, which is exactly
   what `tagsOfField`'s existing `| _ => ∅` already does. Heterogeneity is an empty contribution,
   not an error — and the error it should be is `(dunion)`'s `htags` premise, where it already
   lives. `mem_tagStringsOf_union` is that, one level deep and non-recursive, like the definition
   it would replace.
2. **The union's separation premises discharge once, centrally, not per use site.** (D) is
   *incomparability*, not disjointness — `DIncomp`'s own docstring says disjointness would reject
   working unions — and two distinct singletons contain each other in neither order:
   `dincomp_map_literal_str`, from `Nodup` alone. (U) is the interesting one, because §5's table
   says it is impossible: `admA_literalN_blind` sends a numeric literal's read side to `⊤`, so two
   numeric options never separate *in the table*. They separate in the **pair** —
   `numberCodec.restrict` at disjoint predicates — which is all `uniqueAdmission_of_sharedBase`
   needs. `uAtCan_of_literalN_disjoint` already made that argument for a union of `literalN`s and
   never used the n-ary constructor to make it, only the shared base; `uAtCan_map_literal_num` is
   the same proof with `ℓ` as list data instead.

So both rules are **derivable**: `typed_literalsS` and `typed_literalsN` conclude exactly what
`Typed.literalS` and `Typed.literalN` conclude, from `Typed.literal` and `Typed.union`, with
`(literal-N)`'s `ℓ ⊆ D` still a premise and not absorbed into a carrier (§2.2's warning honoured).
The two constructors are not rules. They are a union of arity-one literals with a rule's clothes on.

### 11.5 The cost that only appeared by building it

`Term.union`'s payload is a `List Term`. `literalS`'s is a `NEFinset String`. Bridging them is
`Finset.toList`, which is `Multiset.toList`, which is `Quotient.out` — **`Classical.choice`**.

This is not a guess. The first draft of `LiteralArity1.lean` stated the two derivations over
`NEFinset` and `#assert_axioms_all` rejected five theorems for exactly that reason:

```
Calculus.typed_literalsN: [Classical.choice],  Calculus.typed_literalsS: [Classical.choice],
Calculus.tagStringsOf_literalsS: [Classical.choice], Calculus.toList_ne_nil: [Classical.choice],
Calculus.tagStringsOf_fold: [Classical.choice]
```

Restated over `(l : List α)` with `hnd : l.Nodup` and `hne : l ≠ []`, all of it is choice-free and
the module passes the scan. But look at what those two premises are: **`hnd` and `hne` are exactly
the gates the `℘⁺fin` repair deleted from `literalS` on this branch.** So the absorption, routed
through `union`, offers a choice:

* keep `Term.union` list-shaped and let the n-ary literal be a `List` with `Nodup` and
  non-emptiness spelled out — which reintroduces two of the five gates this arc removed; or
* convert the `Finset` at the boundary and take `Classical.choice` into the axiom base — which
  voids what `formal/` advertises, and is not a trade anyone should make for two constructors.

There was a third door, and it is shut. `Term.union`'s payload is a list because §2.1 found
multiplicity *observable* (`select_dup_none`) and order *not* (`altCodec_e_swap`) — so an
unordered, repeat-free payload is what `select`'s exactly-one-admitting semantics wants anyway,
and `NEFinset Term` would make the bridge the identity with no choice in it.

`NEFinset Term` needs `DecidableEq Term`. **`Term` cannot have one.**

```lean
| custom (ce : Value → Option Attr) (cp : Attr → Option Value)
```

Deciding `custom ce cp = custom ce' cp'` decides equality of functions on `Value`, which is
infinite. This is not a gap in `deriving` — `deriving instance DecidableEq for Term` does fail,
but the point is that no hand-written instance exists either. So `union` stays list-shaped, and
the two bullets above are the whole choice: **choice, or two gates back.**

### 11.6 Where this left the recommendation — and what landing it cost

**Back to §11.1, now for a proved reason rather than a hedge.** The base-indexed
`literal (k : GroundKind) (ls : NEFinset k.Carrier)` is the only route that keeps the payload a
`Finset`: no `Classical.choice`, no `Nodup`/non-emptiness premises coming back, at the price of a
dependent field and the 266 sites. The union route would have been cheaper and is not available,
because `Term.custom` makes `DecidableEq Term` impossible and `Finset.toList` makes the bridge
non-constructive.

That is a better answer than the one this section opened with, and it is not the one I would have
reached by reading. Both of the objections I wrote down were wrong; the obstruction that actually
decides it was found by the axiom scan on a draft, and closed by a three-line probe.

`LiteralArity1.lean` stays regardless of the route. It is the proof that the two constructors
carry no derivable judgement of their own — the fact both routes rest on, and one neither should
have to re-establish. It is also the thing to check the indexed rewrite against: whatever
`literal (k) (ls)` ends up concluding, `typed_literalsS`/`typed_literalsN` say what it has to
imply.

### 11.7 Landed — and where the estimate was wrong

The indexed form is in the tree. What the collapse actually bought, beyond deleting two
constructors:

* **Five codec definitions became four, and they are the right four.** `literalSCodec`,
  `literalNCodec`, `inLS`, `inLN` and the old arity-one `literalCodec` are now `baseCodec`,
  `inL`, `HLit` and one `literalCodec`. The codec **is** `(baseCodec k).restrict (inL k ls)`
  rather than a hand-written pair that agreed with one, so `literalCodec_e_restrict` and
  `_p_restrict` are `rfl` where the string versions needed a `funext` and a case split.
* **`carrier_literalNCodec` was twenty-six lines and is now shared.** It unfolded
  `Double.ofDec`, split on `Numeral.WF`, then on membership — all of it because the codec only
  *agreed* with a restriction. `carrier_literalCodec` is `Carrier.congr` over
  `carrier_restrict`, one line for all five bases, and the only content left is `hLit_of_inL`.
* **Three `lawful_*` theorems became one, with no hypothesis.** `Lawful` never mentions `T`, so
  the restriction of a lawful pair is lawful whatever `ℓ` is.
* **`adm`'s literal row is `inL`** — the codec's own prism, not a second definition of it. Its
  soundness case went from three cases (a `simp_all`, a `Double.ofDec` split, and a five-way
  arity-one split) to `exact (restrict_e.mp he).1`.
* **`typed_TSub`'s literal case is `exact hv`.** The denotation's held set and the rule's are the
  same expression, `HLit k ls`, at every base.
* **§5's `literal-S`/`literal-N` asymmetry is now one line of `admALit`.** It was never a
  difference between two rules; it is a difference between two *bases* of one, and the definition
  says so where two constructors used to imply otherwise.

Where the estimate in §11.3 was wrong, in both directions. It said 266 sites; the real count of
*edits* was far smaller, because most of those mentions were `literalS`/`literalN` in positions a
mechanical rename covers. But it under-priced the dependent field in exactly one way that cost
real time: **`simp [Adm]` and `simp [AdmA]` blow up at a dependent row.** `Exactness`'s two big
tables are mutual definitions with ~20 rows each, and generating their equation lemmas across a
pattern whose second field's *type mentions the first* exhausts the heartbeat budget — in proofs
that used to close in one step. The fix is the same one the numeric sites already use: name the
row (`Adm_literal`, `AdmA_literal`, both `@[simp]`) and never unfold the table at a literal.

Two smaller costs worth recording, because neither was predicted:

* `GroundKind.Carrier` must be **reducible**. An indexed `DecidableEq k.Carrier` instance works
  and is *noncomputable* — `Double`'s equality is one of §1's axioms — which then spreads
  `noncomputable` to every `def` that names a literal. Reducible carriers let membership resolve
  through `String.decEq` and friends instead.
* At `binary` (`List UInt8`) and `null` (`Unit`), even the named row was not enough for
  `AdmA_exact`: `NEFinset k.Carrier` at a constructor `k` is the same *type* as `NEFinset Bytes`
  but not the same *expression*, and `simp` re-derives that on every rewrite.
  `AdmALit_binary_exact` and `AdmALit_null_exact` state those two bases with the carrier written
  out, which does the reduction once at elaboration.

Green across all 20 modules, warning-free, `#assert_axioms_all` passing, `maxHeartbeats` still at
three — none of the timeouts above were fixed by raising the budget.

## 12. Three questions asked from outside the queue

Raised by JH after §11 landed. One is closed by the kernel, one corrects a §2.2 row, and one is
a **live defect in the shipped library** that this file's own structure hid.

### 12.1 Should `union` take a `NEFinset`? — No, and now for a kernel reason

Answered in §2.1. Two payloads were tried, not argued: `NEFinset Term` needs `DecidableEq Term`,
which `Term.custom` makes impossible; `Multiset Term` needs no such instance and matches exactly
what §2.1 measured, and the **kernel rejects it** as a non-valid occurrence of `Term` in its own
declaration. A quotient cannot sit in a nested inductive position.

### 12.2 Should `dunion` be a map from labels to codecs? — The obstruction I recorded is not real

`dunion (d : Name) (opts : List Term)` carries `htags` (every option names at least one tag) and
`hdisj` (their tag sets are pairwise disjoint). §2.2 filed both as content, on the grounds that
`tagsOf` *computes* the tags from the option, so storing them would duplicate derived data and
need a coherence gate. **That is only true while each option keeps its own discriminator field.**

`dunion (d : Name) (opts : MapOf Term)` — a `Finset String` of tags with a function on it, the
same shape `object`'s field table now has — with `dunion` **injecting** the discriminator into
each variant instead of reading it back, has one source of truth. Then `htags` is "a key exists",
which the type says, and `hdisj` is "keys are unique in a `Finset`", which the type also says.
Both premises go, and no coherence gate replaces them.

The real costs are two, and neither is the one I wrote down:

1. **A variant answering to several tags.** `discriminatedUnion` allows a variant whose
   discriminator is `literal .string {A, B}`. Keyed by tag, that variant appears under two keys —
   duplicating its codec — or the map's values are keyed by `NEFinset String`, which puts
   disjointness back as a premise. This is the actual reason the shape resists, and it is a
   question about what the *implementation* allows, not about derived data.
2. **C2/C3.** `codec.ts`'s `discriminatedUnion` demands each option declare the discriminator as
   a bare `literal` — it reads the tag off the option. A model where `dunion` injects it instead
   describes a different constructor, so the correspondence table stops holding at the one term
   whose whole mechanism is the tag.

Worth measuring before either: whether `discriminatedUnion` has a use with a multi-tag variant.
If not, cost 1 evaporates and only the C2/C3 divergence remains — which is an argument for
changing `codec.ts` too, not for keeping two premises.

### 12.3 Documents nest ≤32 levels — and nothing checks it

**Corrected by JH after the first draft: 32 is a depth bound and nothing else.** The three limits
are separate, and only one of them is a candidate for a codec to enforce:

| limit | what it constrains | where it can be checked |
| --- | --- | --- |
| nesting ≤ 32 | depth — how many dereferences a path takes (`a.b.c…`), per attribute | **at `encode`, locally** — this is the gap |
| element count | **nothing.** `dynamo-datatypes.md:132`, `:185`: *"There is no limit on the number of values in a list or a map"* — nor in a set | n/a; the model is already exact |
| item size ≤ 400 KB | the cumulative size of every attribute name and value in one row | only at the *item* level, never inside one attribute's codec |

So breadth is unbounded and the model saying so is correct, not loose. A `List 𝔸` of ten thousand
elements is a legal attribute; a 33-deep one is not, at any size.

`dynamo-datatypes.md:130`: *"The document types are list and map. These data types can be nested
within each other, to represent complex data structures up to 32 levels deep."*

§6 has this as **NOT-TYPEABLE** and the first half of that verdict is right: the subtype
`{as : List Attr // Attr.depthL as ≤ 31}` puts `Attr` under its own declaration and the kernel
refuses it, exactly as for item size. The second half — *"the ω-codecs' totality argument depends
on depth being unbounded"* — is wrong, and §6 is corrected: `Opaque.lean:17-20` gives **each
input its own budget** (`Value.depth`, `Attr.depth`), and a bound on the carrier makes those
budgets bounded rather than ill-typed.

**The part neither §6 nor §9 covers.** §6 asks "can this be a carrier refinement?", answers no,
and then declares the axis closed on the grounds that everything remaining is *"either a resource
limit §1 deliberately omits or a schema-position limit about tables, indexes and keys"*. Depth is
**neither**. It is a structural membership condition on `𝔸`: a 33-deep document is refused
whatever its size, and there is no table or key in the statement. So the dichotomy that closed §6
does not cover it, and being un-typeable never made it un-checkable — `Numerals` was *typed* and
`src/` still had to gate on both halves, in three terms plus `native`.

`grep` for a depth or nesting check across `src/codec.ts`: **nothing.** So:

* **`src/` will write a 33-deep item and DynamoDB will reject the row.** This is a C1 violation of
  precisely the `⟨N, "5e-324"⟩` shape — an attribute the store has no point for, reachable with
  no cast — and it is the fifth, found after §9 declared five and closed them. §9 did not look
  because §6 had already filed depth as out of scope.
* **The model over-approximates `𝔸` — in depth, and only in depth.** `Attr.l` and `Attr.m` admit
  arbitrary *nesting*, so `ran(e) ⊆ 𝔸` holds against the model's `𝔸` and not the store's. Their
  *breadth* is unbounded in both, which is right. Unlike the numeral case this cannot be repaired
  in the carrier, so the honest options are a **derived** bound (`Attr.depth a ≤ 32` as a theorem
  about derivable terms, or an `Obligations` entry) or an explicit scope note in §1 saying `𝔸` is
  the unbounded closure with depth checked outside it.

The library fix is independent of that choice and should not wait for it: a depth check on
`encode` at the top level, or a `checkDepth` in `rotorise/testing` beside `checkAgainst`. It is a
*depth* walk — no counting, no sizing — which is what makes it cheap and local. `opaque` and
`native` are where it bites hardest: both walk arbitrary user data, and `native` is the one people
point at a table they did not design.

The 400 KB limit is the one to leave alone at the codec level, and for a reason rather than a
shrug: an attribute codec sees one attribute, and item size is a sum over all of them plus their
names. It is checkable where an *item* is assembled and nowhere else, which is a different
obligation from `ran(e) ⊆ 𝔸` and belongs to whatever writes the item.

**What this says about the audit itself.** §6's heading is "the axis is closed", and it *is* —
for the axis it defines. The defect got through because a constraint that fails one test
(can it be a type?) was recorded as disposed of, rather than handed to the test it would have
failed next (does anything enforce it?). §9 existed to ask exactly that question and never
received this constraint.

### 12.4 Bounding the nesting *would* simplify what I called load-bearing — and the price is `List`

JH's follow-on, and it is right in kind. The `∀ n, Value.depth v ≤ n → …` shape in
`HeldSet.lean:58-61` is described there as *"what lets the induction go through"*, and
`Opaque.lean` names the depth budget **148 times**. That machinery exists for one reason: the
budget is a **measure** on an unbounded carrier rather than a **type**. Bound the carrier and the
measure becomes an index — which is the same move as all five landed representation repairs, and
would take `opaqCodec`'s input-side fuel and its stabilization lemmas with it.

So the question is whether the bound is reachable. Two probes:

```lean
inductive A : Nat → Type where
  | l {n} (v : List (A n)) : A (n+1)      -- kernel: invalid nested inductive datatype 'List',
                                          -- nested inductive parameters cannot contain local variables
```

Rejected — the same class of refusal as `Multiset Term` in §12.1. But:

```lean
mutual
inductive A : Nat → Type where
  | l {n} (v : AL n) : A (n+1)
  | m {n} (keys : Finset Name) (f : {k // k ∈ keys} → A n) : A (n+1)
inductive AL : Nat → Type where
  | nil {n} | cons {n} (a : A n) (as : AL n) : AL n
end
```

**Legal.** So the bound *is* reachable, and §6's "NOT-TYPEABLE" is too strong: what is
un-typeable is a *subtype* of the unbounded carrier. An indexed family is a different move and
the kernel takes it — with `Finset Name` and the function-valued map field surviving intact.

The price is precise, and it is the wrong way round for this branch:

* **`Attr.l` stops being `List Attr`.** The only way past the nested-`List` refusal is a bespoke
  index-carrying list. §2.3 certifies `Attr.l`/`Value.arr` as *already correctly typed* on the
  reference's own words — lists are ordered and heterogeneous, so `List` is exact — and a
  hand-rolled `AL n` is the same shape as the five containers this arc replaced, reintroduced to
  encode a bound.
* **Every theorem mentioning `Attr` or `Value` gains an index.** That is most of 731.
* **It buys no correctness.** The bound in the carrier does nothing about item 15: `src/` still
  needs a runtime depth check, because the defect is that the *library* writes a 33-deep row.

And the scope of the win is narrower than it first looks. `denote`'s fuel is **Term**-level — it
decrements on subterms — so a carrier bound does not touch it, and `Denoteω`, `Soundnessω` and
`Continuity` (514 lines between them) are all Term-level too. What is in scope is exactly
`Opaque.lean` (854 lines, 148 depth mentions) and `HeldSet.lean`'s opaque held-set lemmas (22).
Those recurse on the *input's* depth, which is the only place a carrier index would be an index.

**Verdict: a spike, not an item, and bigger than 6b was.** The honest statement of the trade is
that it converts a 170-use measure into a type — genuinely the winning move — at the cost of
undoing the one container the audit certifies as exact and reindexing the model. Worth measuring
`Opaque.lean` against an indexed carrier in a scratch file before anyone commits to it. What it
must not do is wait for item 15, which is a library bug with a local fix.

*(§6's `:130` row now says "not typeable **as a subtype**", which is what the kernel actually
refused. That is the third correction to that row.)*

## 13. `denote` does not need fuel — and this is the largest finding in the file

JH pushed on §12.4: *"you are scared of load-bearing where we can have stronger pieces. trust
yourself, this is deterministic."* The push was right, and it landed somewhere much better than
the depth bound.

### 13.1 The probe

This compiles, against the real `Term`, with no `decreasing_by` and no fuel:

```lean
mutual
noncomputable def den : Term → Codec
  | .set elem => setCodec (den elem)
  | .tuple elems tail => tupleCodec (denL elems) (denO tail)
  | .object fields f rest => objectCodec ⟨fields, fun k => denField (f k)⟩ (denRest rest)
  | .union opts => altCodec (denOpts opts) (unanimous (denμs opts))
  | .dunion d opts => dunionCodec d (denTagged d opts)
  | …                                             -- the other fifteen rows unchanged
noncomputable def denField : Field → FieldSem
  | .req t => .req (den t) | .optional t => .opt (den t) | .fallback t v => .fb (den t) v
noncomputable def denRest : Rest → RestSem
  | .drop => .drop | .refuse => .refuse | .codec t => .codec (den t)
noncomputable def denL : List Term → List Codec
  | [] => [] | t :: ts => den t :: denL ts
  -- …and one companion each for `Option Term`, options, members, tagged options
end
```

Kept at `scratchpad/denote-structural-probe.lean`.

### 13.2 What was actually blocking it — neither of the two things I assumed

I reasoned twice from the wrong frame and the compiler corrected both.

**Not `sizeOf`.** My first guess was that the map field defeats termination because `sizeOf`
cannot see into a function: `sizeOf (Value.map keys f) = 1 + sizeOf keys + sizeOf f` and
`sizeOf f = 0`, both confirmed by `simp`, so `sizeOf (f k) < sizeOf (Value.map keys f)` is
unprovable. True — and irrelevant. **`Value.depth` in `Opaque.lean:50` already recurses at
`f k`** with no fuel and no `decreasing_by`, because a function field makes `Value` reflexive and
*structural* recursion goes through it. `sizeOf` only becomes the measure once something else
forces well-founded recursion, which is what my first probe accidentally did by using
`List.map` in the array case.

**Not the `Finset`-plus-function representation.** The five repairs did not buy their types at
the cost of fuel. The two real obstructions in the current `denote` are both incidental:

1. `elems.map (denote fuel)` and `opts.map fun t' => … (denote fuel t')` — recursion under
   `List.map`. A list companion fixes it, which is exactly what `μSyn`/`μSynList` in the same
   file already do.
2. `fieldSemOf (denote fuel) (f k)` and `restSemOf (denote fuel) rest` — `denote fuel` passed
   **unapplied**, as a function value. Structural recursion cannot do that. But `fieldSemOf`
   applies its argument to *exactly the subterm* in all three rows (`.req t => .req (den t)`),
   so it is fully invertible: make it a mutual companion and the higher-order argument
   disappears.

### 13.3 What it costs to keep the fuel

| module | lines | why it exists |
| --- | --- | --- |
| `Denoteω` | 314 | *is* the fuel-free denotation — the thing `den` above just is |
| `Continuity` | 123 | relates fueled to fuel-free; contains one real finding (see below) |
| `Soundnessω` | 77 | the same, for soundness |
| `Opaque.lean` | 854 | `opaqCodecω`'s per-input depth budgets and stabilization, 148 `depth` uses |

Plus `fuel` threaded through `Soundness` (191 mentions), `Discharge` (159), `Exactness` (40), and
the `fuel = 0` base case of every induction — `lawful_dead`, `carrier_dead`, `Obligations 0 = True`.

An earlier probe in this session also showed an `opaqE`-shaped `Value → Option Attr` compiles
structurally, with a mutual list companion and a dependent `if h : ∀ k, (enc (f k)).isSome`. So
`opaque`'s budget apparatus is avoidable on the same grounds, and the §12.4 depth-bound question
is **moot**: nothing here needs a bound on nesting.

### 13.4 What must survive, and what I have not shown

`Continuity.lean`'s content is a *finding*, not scaffolding: union's admission is anti-monotone,
so a genuinely recursive union has no fixpoint semantics in any system. That is why `Term.lazy`
carries a plain `Term` rather than a thunk, and it has to survive as a statement whatever happens
to the fuel around it.

**Shown:** the definition typechecks and terminates structurally, against the real `Term`.
**Not shown:** that the proofs port. They should get *simpler* — no fuel induction, no `fuel = 0`
base case, `denote_μ`'s two-case induction collapses — but "simpler" is a prediction and this
file's record on predictions is poor. The honest scope is: one spike that ports `Soundness.lean`
to `den` and reports what actually happened, before anything is deleted.

### 13.5 Queue position

This subsumes item 4 (`WireOrder` dead), most of §4.1's dead-plumbing list, and §12.4. It is
larger than 6b by a wide margin and it is the only item in the file that would make the model
*smaller* rather than more exact. It does not touch item 15, which is still a live library bug
with a local fix.

**And the pattern is worth naming.** Every "this is load-bearing" verdict I wrote this session
that JH pushed on has been wrong: §11.4's two objections, §6's depth row three times over, and now
the assumption that fuel was forced. The ones that held — `DecidableEq Term`, `Multiset Term`,
`Finset.toList` — held because a probe settled them in under a minute. The rule that falls out:
**in a deterministic system, a claim about what is possible is worth one probe, and an argument
about it is worth nothing.**

## 14. The strategy, stated — and the one place it is wrong

Asked directly: *is replacing logic guards with structural impossibility our best strategy?*
Mostly yes, and this file has the evidence for a sharper version in three parts. Two of them are
the answer; the third is that the biggest win of the arc is **not** this strategy at all.

> **The standing rule now lives in `docs/structural-discipline.md`.** It argues the same
> preference from a stronger premise than this section does — **portability**: a Lean *type* can
> be mirrored by a host *type* and the mirror is checked by a compiler, where a Lean *gate* must
> be re-implemented as a host *check* and nothing checks that you did. §9's five bugs are the
> evidence, and they sort perfectly: zero bugs in the two tightenings TypeScript carries
> structurally, four in the two it had to gate, one in the one it cannot express. This section is
> the audit-local version; that file is the discipline.

### 14.1 Where it works: gates about the shape of a payload the library owns

Every landed repair is this, and the pattern is exact — the gate said something about *data the
library holds*, decidable at construction:

| gate | became | deleted |
| --- | --- | --- |
| `hnd` on `M`'s payload | `Finset Name` + a function on it | the premise, and `Lists.lean`'s whole association-list section |
| `hnd` on the field table | the same, one level up | the premise, the `TypedFields` inductive, −293 lines |
| `hne`, `hnd` on wire sets | `NEFinset α` | both premises, at three members |
| `hne`, `hnd` on `ℓ` | `NEFinset` again | both, twice |
| unrestricted `N` carrier | `Attr.n : WFNumeral` | made `Carries(N)` exact; `numberCodec` *became* the base it refined |
| `hok`'s container half, `hμ` | `GroundValue`, then a `GroundKind` index | `hμ`, the container gate, the `hok` argument of two laws, a case in `Exactness` |
| three literal constructors | one, indexed by the base | 2 constructors, a 26-line carrier proof, 2 of 3 `lawful_*` |

The test that predicts success: **can the condition be decided from the constructor's own
arguments, at construction, with no reference to a value being encoded?** Non-emptiness,
uniqueness, unorderedness, "has a ground base", "which base" — all yes. That is the whole
qualifying set, and it is now empty.

### 14.2 Where it actively harms: when the gate is the only witness that a defect exists

**§2.2's first row is the counter-example, and it is the one claim in this file that survived
every push.** `Typed.literalN`'s `hD : ∀ d ∈ ℓ, Numeral.WF d.toDec` could be typed —
`NEFinset {d // WF d.toDec}` is perfectly admissible. Doing it would **delete
`literalN_holds_what_it_cannot_write`**, the theorem exhibiting a literal that is *held* and
unwritable, which is (B) failing.

That is not conservatism. A typed `hD` makes the bad term unconstructible, so the model can no
longer *exhibit* the defect — and exhibiting it is what `Refutations.lean` is for. The difference
between "this cannot be said" and "this can be said and here is why it is wrong" is the
difference between a model that hides a defect and one that documents it. §4's numeral repair is
the live example of the risk: the defect did not vanish, it **changed shape** — from "writes a
non-attribute" to `T ⊄ dom(e)` — and it was only visible afterwards because a witness still
existed to relocate.

The `℘⁺fin` repair paid this cost for real and it is recorded: typing it destroyed the only
`Double`-free witness that `opaque`'s exactness row over-claims, so `not_ExactV_opaq` and
`excuse_witnessed` now take a `(d : Double)` they did not need.

**So the rule has a second clause: a gate that is load-bearing for a refutation stays.** Not
because typing it is impossible, but because typing it would make the model claim more than it
can prove — by making the counterexample unsayable rather than false.

### 14.3 The bigger principle, which is not this one

Add up §14.1: seven repairs, on the order of fifty lines of premises and a few hundred lines of
machinery that existed to repair the old representations.

Now §13: a structural `denote` puts **~1400 lines** in question — `Denoteω` (314),
`Continuity` (123), `Soundnessω` (77), `Opaque.lean`'s budget apparatus (854, 148 `depth` uses) —
plus `fuel` threaded through `Soundness` (191 mentions), `Discharge` (159) and `Exactness` (40).

And it is a **different move**. Fuel is not a guard; nothing is being made unrepresentable.
`fuel`, `Value.depth` and `Attr.depth` are *measures standing in for a recursion the checker
could not see*, and the repair is to let it see the recursion. Call it **measure → structure**,
against §14.1's **gate → type**. On this codebase the second is worth an order of magnitude more
than the first, and it was invisible for the whole arc because nobody asked the checker.

### 14.4 The predictable tax, in one place

Both moves push work into the elaborator, and it lands somewhere specific: **the moment a type
carries an index or a quotient, the kernel and `simp` stop being free.**

* A dependent field makes `simp [Adm]` exhaust the heartbeat budget across the row (§11.7); the
  fix is to name the row, never to raise the budget.
* A `Finset` payload cannot reach a `List`-shaped constructor without `Finset.toList`, which is
  `Classical.choice` (§11.5).
* A quotient cannot sit in a nested inductive position — `Multiset Term` is refused by the kernel
  (§12.1), and so is `List (A n)` in an indexed family (§12.4).
* `DecidableEq` is not always available at all: `Term.custom` carries functions on `Value`.

None of these is a reason not to do it. They are where to look first when it goes wrong, and each
one cost a probe of under a minute to establish.

### 14.5 So, confirmed — with the clauses

1. Replace a gate with a type when the condition is decidable from the constructor's own
   arguments at construction. **The qualifying set is now empty**; §14.1's table is the whole of
   it.
2. **Keep** a gate that a refutation depends on. Typing it deletes the witness, and a model that
   cannot state its defects is worse than one that gates them.
3. **Prefer measure → structure over gate → type** where both are available. It is where the mass
   is, and §13 is the open item.
4. Settle every "can this be done" with a probe, not an argument. Every verdict in this file
   reached by argument and later challenged was wrong; every one reached by probe held.
