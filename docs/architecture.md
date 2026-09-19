# Architecture of the Lean development

What this system is. Read this before changing anything under `Calculus/`.

This file carries no count, no line number and no measurement. A count is short lived: it belongs
in the commit that measured it, in `defects.md` where it pins an issue, or in the output of a
guard. What is here is the structure, the invariants, the models and the mechanics of an
operation, which are the things that stay true across passes.

This file cites no section number, in this document or any other, so that a renumbering cannot
make it wrong. It names declarations and files instead.

A backtick here means a Lean name that `Calculus/` defines. A host identifier is written as a
path, as a call, or in prose.

| For | Read |
| --- | --- |
| The rules, normatively | `formal/docs/blueprint/src/content.tex` |
| Future states, and what decides each | `docs/roadmap.md` |
| Known, suspected and partially mitigated issues | `docs/defects.md` |
| What changed and why | `git log` |
| Module table and how to build | `formal/README.md` |

---

## The epistemic structure

This repository is two developments and one bridge between them.

`src/` is a published TypeScript library. `Calculus/` is a Lean model of part of that library.
The bridge is a generator in `src/codec/lean.ts` that emits Lean theorems from encodes the library
actually performed, and the Lean kernel decides whether the model agrees.

The three carry different warranties, and keeping them apart is the whole discipline.

- **The model proves.** A theorem in `Calculus/` is checked by the kernel against an advertised
  axiom base.
- **The bridge checks agreement.** A vector is a proposition about one operation the library ran.
  Elaboration is what verifies it. Comparing the generator against output the generator produced
  verifies nothing, because a stale generator agrees with its own stale output.
- **A written premise is neither.** Where the model discharges an obligation the host cannot
  check, the guarantee is a sentence on both sides and no instrument is looking.

The asymmetry that governs the analyses: **a missing analysis row is sound and says nothing.**
An approximation that answers "everything" is always correct and never useful, so the failure mode
here is silence rather than error, and silence does not fail a build.

---

## The layering, and the one property the build enforces

The import graph of `Calculus/` is an almost-linear spine: `Domain`, then `Codec`, then the
combinator algebra as `Prisms`, `Products`, `Objects`, `Sums`, `Carriers`, `Lawful` and
`Frontier`, and `Term`, then `Denote`, `Typing`, `Soundness`, then the analyses `Discharge`,
`HeldSet`, `Nesting` and `Equations`, then `ExactV`, `ExactA` and `Separation`, then
`Orthogonality`, with `Axioms` as the sink. `Malleability` is the one analysis off the spine.

**The layering is a convenience. One property of it is checked.** `Axioms.lean` walks the
environment, and the environment is what `Axioms.lean` imports, which is a hand-maintained list. A
module nothing on that list reaches is silently unguarded. `scripts/guard_reach.py` fails when any
module under `Calculus/` sits outside the transitive closure of the guard's imports.

So a new module under `Calculus/` must be reachable from `Axioms.lean`. `Axioms.lean` cannot
import the aggregator instead, because the aggregator imports the guard, and inverting that would
let the default build run with no guard at all.

Nothing else about the graph is enforced. A cycle is caught by Lean; an upward dependency in bad
taste is caught by nobody.

---

## The term family, and what a stratum owes

`Term`, `Body` and `ObjectSlot` are inductives in one `mutual` block. **The point of the split
is negative: no `Term` position accepts an `ObjectSlot`.** A slot is not a term, so a nonsensical
term is a type error rather than a rule somebody must remember to refuse.

`Body` bundles the object payload — the declared key set, the slot at each key, and the one open
block — into one thing. Two consequences are the reason to do it again:

- Every table over terms gets a one-argument object row that delegates to a `Body` companion.
  Threading the payload's parts by hand is what made them agree by convention rather than by type.
- A `Finset Name` together with a function off the membership subtype makes the no-duplicate-keys
  premise disappear. Both a repeated name and two orderings of one object stop being
  representable. `ObjectSlot` sits in the function's codomain, which is strictly positive.

`ObjectSlot` carries the current-schema rule only. A required slot remains required on both
current-schema sides. `LegacyRead` carries one current `Term` and one optional alternate reader.
Structural operations, including `meet` and union certification, operate on `Term`. The operations
cannot observe or propagate an alternate reader.

`Body`'s projections `Body.fields`, `Body.at` and `Body.wild` are written by hand, because a
`mutual` block admits no `structure`. Rows needing all three match on the constructor, which keeps
the equation compiler's reductions available.

**A stratum owes a companion in each of these places.** Miss one and the failure is not a build
error but a silent "everything": the analysis stays sound and stops saying anything.

| Companion | For `Body` | Why it is owed |
| --- | --- | --- |
| a depth clause | `Body.depth` | the termination measure must see through it |
| a denotation clause | `bodySem` | `denote` must dispatch with no case split at the use site |
| a spec projection | `Body.spec` | `select` counts an object option by its names, not its contents |
| an admission row, per side | `AdmBody` and `AdmABody` | exactness is per row; a stratum with no row cannot be exact |
| a premise carrier | `ObligationsBody` | semantic side conditions are structural, not global |
| an emitter clause | the object row of `src/codec/lean.ts` | the bridge writes terms in this language, and a constructor it cannot spell breaks it |

The spec projection is owed only by a stratum that holds names. A policy answers to no name.
Every other row is owed unconditionally.

The spec projection separates a name's presence from what the name holds. The split is
Rémy's, from the 1989 record and variant extension of ML. A field type carries presence
beside the value type, so an analysis keeps exact negative information about a name.
`keysOk` reads the one current-schema presence fact. `literalsOk` and `literalsOkA` read the
value constraints. No reader reads a codec.

The emitter clause is owed for the same reason as the rest: the bridge is part of the
correspondence, and a stratum whose shape the emitter cannot spell produces committed vector
output that typechecks against nothing.

---

## Where a side condition goes

The first thing to settle when adding a rule. `Typed` keeps the syntactic, fuel-free premises
only.

| A premise that is | goes in | consumed by |
| --- | --- | --- |
| decidable from the term | `Typed`, as `DIncomp` is for a union | the judgement itself |
| about what a codec does — its write half, its read half, an iso, a resolution | `Obligations`, as `UAtAct` and `IsoCancels` are | both soundness theorems |

`Term` has no alternate reader. Therefore `soundness` proves all four laws for every typed term.
`LegacyRead` packages a separate alternate reader and its conditions at the codec layer.

Choosing wrong is not a build error. A semantic premise in `Typed` makes the judgement
undecidable; a syntactic premise in `Obligations` becomes a burden every caller carries.

---

## Termination

`Term.depth` exists because `Typed` is a `Prop`-valued mutual family with no recursor over
derivations, so proofs recurse on the term. The built-in size measure cannot serve: the object
payload's field table is a function, and that measure is blind to functions. `Term.depth` takes a
supremum over the key set where a list would fold.

What matters is that the measure is **derived from the term**, so it appears in no statement, no
`Obligations` and no rule. That is the whole difference between it and a fuel parameter.

`term_depth_wf` is the shared tactic for a term recursion. Anything new recursing on a term takes
it, and an inequality the block does not offer goes beside `Term.depth` rather than inline.

---

## The four recurring design moves

These are the architecture, more than the module list is.

### A premise becomes an index

Repeatedly a typing-rule side condition turns out to be expressible in the type of the
constructor, at which point violating it stops being possible rather than being refused.
`SetBase` is the set of bases that survive the element premise, so the member is a total function
of the index and the refusal is a type error. `GroundKind` makes a literal's carrier concrete and
its equality decidable, so `ℓ ⊆ T` is the carrier rather than a premise beside it. `NEFinset`
makes nonemptiness, pairwise distinctness and homogeneity properties of the type wherever a wire
set is written.

**The criterion.** A premise becomes structural when its satisfying set is finitely enumerable at
declaration time, or when it is a property of one argument expressible in that argument's own
type. It does not when the premise relates one argument to other arguments' behaviour at a shared
input.

That last clause is the boundary, and **unique admission is the case on the wrong side of it**:
it is not a property of an option but a property of a set of options at an input the set as a
whole resolves. Indices make per-thing properties structural, and this is not one.

**The discriminated union is the case that left the term language rather than crossing into it.**
A dissection is a `union` of object members whose pairwise structural meet is empty: two members
differ at a required literal name with disjoint alternatives, or the name intervals they declare
cannot be satisfied at once. Structural admission is what reads that, on both halves of the pair.
An object option is admitted when the names the item carries lie in the interval its spec declares,
and every present name whose field is a literal carries one of that literal's alternatives. `OrthS`
is the phase of `Orth` that certifies the first case, and a sub-selection of a certified union
stays certified, because the certificate is `Pairwise` and `uAtAct_sublist` carries (U) under it. A
tag table keyed by the discriminating literals is an index the host builds over such a union, and
no term carries it.

**The criterion is necessary and not sufficient.** A move can pass it and still not pay, when the
bundling it invites re-threads the parts a stratum exists to bundle, or when it crosses a stated
decision about where a law belongs. Measure the site count too.

### A row asks its codec instead of describing it

A row can describe the set it stands for, or call the codec and ask. **Prefer asking.** A
description must be kept in agreement with what it describes; a question cannot drift.

Every excuse this pattern retired was a correct observation reaching a wrong conclusion, and the
shape recurs: *no syntactic set names this* is a reason to stop being syntactic, not a reason to
give up. The denotation of a numeric literal **is** the literal codec by reduction, so the row
that asks is the domain of the read half exactly.

The price is that a row becomes `noncomputable` when its codec is, which costs nothing here
because the numeric equality is already a field of an axiomatized interface.

An alternate reader is deliberately outside the term rows. `LegacyRead.denote` tries the current
reader first and then the alternate reader. No structural analysis reads the alternate reader.

### One codec, stated once for both sides of the pair

A constructor is a prism — `Ctor`, with the laws `out_into` and `into_out` — and those two are the
round-trip and completeness clauses at a constructor, so the prism half of every lawfulness proof
is discharged once.

Two shapes sit over the prisms. `pointCodec` is the degenerate case, one payload type on both
sides, and the point codecs share one lawfulness proof through it. `carriedCodec` is the
load-bearing one: a payload pair between two prisms, the shape underneath every product. **The
model states a codec once for both sides**, so the doubling in this development is in the analyses
rather than in the algebra. Its two inversions `carried_e` and `carried_p` are what every
product's proof goes through.

The prism inventory is partial on both sides on purpose. The gaps are the constructions that are
not one payload between one pair: the numeric constructor, where the numeral gate stops the
projection being onto its image, and the wire sets. `setCodec` is the one deliberate non-instance,
because its attribute side is a choice among wire constructors rather than one prism, and its
inversion names all of those families.

**The rule reaches inversions, not only constructions.** An inversion stated on one side only
makes every proof on the other side unfold the definition by hand, which means unfolding the
matcher for a whole table and paying for every row at every rewrite. A one-sided inversion is a
defect of this rule, not a gap in coverage.

### The guards exist because prose does not typecheck

Every instrument here was built after a description drifted from what it described: an axiom claim
in prose, an attribute asserting a behaviour that had stopped being true, a citation of a deleted
name, a regex passed off as a reachability measurement, a grep passed off as a refactor estimate.
None was added speculatively.

---

## The analyses, and why two generations stand

Every discharger is one appeal to `uniqueAdmission_of_disjoint`, which takes two families of
allowed values, one per side, and asks only that each be pairwise disjoint. Kinds, members, tags
and admissible sets are ways of building those families rather than four separate conditions.

`ExactV.lean` holds `Adm` and `ExactA.lean` holds `AdmA`, exact at every constructor, with no
hypothesis and no escape hatch. Its value-side separation predicate is one clause, because the
joint predicate absorbs what a kind table used to carry. The attribute-side predicate is also one
clause. An alternate reader cannot add a structural exception because `LegacyRead` is outside
`Term`.

**Retiring the older generation is refused by theorem, and the reason is counter-intuitive.**
`select` counts an object option by the names a map carries, never by what they hold. So at an
object the joint predicate is not an over-approximation of option admission; it is strictly
tighter, and disjointness of a tighter predicate does not imply disjointness of admission.
Therefore **the object row answering "everything" is load-bearing rather than slack**: it is
exactly the over-approximation that turns row disjointness into admission disjointness. Restate
the discharger on the sharper predicate and the pair does separate while `select` still attempts
both options, so the uniqueness property genuinely fails. The premise gets stronger and the
theorem becomes false. `not_uAtCan_of_sepJ` is that statement, and the witness is two objects with
the same names and different field terms, both derivable and both lawful.

**The direction has a standard name.** Both facts are one principle, the abstract
interpretation of Cousot and Cousot, 1977. A coarse test that over-approximates a precise
one transfers disjointness downward. A tighter test does not. The object row answering
everything over-approximates option admission, which is why the row is load-bearing.
Structural admission over-approximates `Adm`, which is `admitOptV_of_Adm`, and that is what
lets a certificate proved over specs bind a union whose options carry codecs.

On the value side the object row is the whole of the obstruction: `admitV_Adm_nonObject` and
`admitA_AdmA_nonObject` hold from exactness alone for every term whose spec projection is absent,
which is every term but an object.

**The outer carrier has a separate read-side fact.** An alternate reader can read an attribute
outside the current term's member. `legacyRead_reads_n` records a string core that reads a numeric
attribute through its alternate reader. The structural classifier has no row for the outer
carrier.

The repair the object row invites — ask what the resolver consults rather than what the row says
— is made in `Orthogonality.lean`. `OrthSV` and `OrthSA` are occupancy conjoined with option
admission, `admitOptV_eq` identifies that second conjunct with option admission itself, and
`uAtCan_of_separated` is the discharger stated on what `select` actually decides by.

### The classifier, and what it is the specification of

`Orthogonality.lean` is a decidable certificate for a fragment of the uniqueness property. It
over-approximates each term's occupancy per side with `occV` and `occA` and certifies a pair whose
occupancies are disjoint, by `decide`.

**Its value is that it is the specification of the library's only declaration-time guard, and a
checked one.** The `union` combinator in `src/` refuses a pair of options no value can choose
between, which is the same question `Orth` answers. The bridge is the separation class in
`src/codec/lean.ts`: one theorem per pair the library refuses, asserting that `Orth` does not
certify it, generated and elaborated by `formal/scripts/gate.sh`.

**`Orth` is sufficient and not necessary,** so exactly one direction is a law: the library never
refuses a pair the model certifies. A decline by `Orth` is not a refutation, and the pairs the
library accepts while `Orth` declines all land in a documented exemption — a literal, which
identifies its own values; an object option, chosen by names; or an option whose kind is unknown.
Asserting the converse would manufacture findings.

`Separated` is what names the separation guarantee over the option list, with
`separated_of_orth` as the classifier's bridge into it.

---

## The instruments, and what each is blind to

The blind spot is the part that matters. The check is the part anyone can read off the script.

**The axiom assertion** in `Axioms.lean` makes the advertised base a build error rather than a
claim in prose. The base admits `Classical.choice`, in part because mathlib resolves membership in a
`Finset` through an instance whose injectivity field is proved classically, so no theorem here
carries a constructive warranty that this guard checks. It walks imported modules only, which is why the reachability guard exists. Its
filter admits theorems, so **a definition that acquires an axiom is not checked at all** — run the
axiom query on definitions, not only on theorems.

**The environment linters** over the `Calculus` namespace have no sanctioned hit today: the list is
empty, and the mechanism stays, because a hit this tree keeps owes a row and a reason beside it. The
docstring linter is excluded rather than sanctioned, because whether the docstring convention reaches
helper definitions is a judgement and not a defect, and an exclusion is visible where a mass sanction
would not be.

**`scripts/guard_reach.py`** is textual and necessary-only. It says the declarations are in the
environment the guard walks. It says nothing about whether the elaborator is correct or whether
the advertised base is the base the documents claim.

**`scripts/name_drift.py`** holds every backticked Lean-looking name in the current-state
documents to occurring somewhere in `Calculus/`, with a table carrying a reason per deliberate
exception, and failing when an entry there stops being cited so the table cannot rot quietly. Its
source set strips comments and docstrings, so a citation has to be answered by code rather than by
its own evidence.

Its blind spots are the shape of the whole problem. **A count is not a name**: it cannot see a
claim about how many declarations share a tactic being false while every name exists. It clears a
dotted name component-wise. **An entry fails when it stops being cited and cannot fail when its
reason goes stale**, which is the same asymmetry the docstring convention has, and the reason both
are conventions rather than guards. And it cannot see a name that stops being *the right one*: a
declaration that still exists while ceasing to be the one a passage cites is invisible. Renaming
is checked; re-pointing is not.

**`scripts/ratchet.py`** holds per-file counts to the state they were in and fails when one rises.
It exists because the bars this development wanted could not be bars: a coverage bar set at a
number nobody can satisfy is a bar that gets switched off, where a ratchet asks nothing on the day
it lands. Baselines live beside the script rather than in it, so a change to one is worth reading.
**A ratchet accepts the state it was born in, so it cannot see a defect older than itself** — it
guards the derivative, not the value. Lowering a baseline is the only move that should be routine.

**`scripts/docstring_anchor.py`** checks that no docstring in the library sits above a declaration
that is not its own. The host's documentation convention binds the *last* docstring before a
declaration, so where two blocks close and open with nothing between them, every block but the
last describes nothing a reader can reach: it renders in no tooltip, no link resolves to it, and no
other check here reads it. That is the shape a scripted deletion leaves behind — the declaration
goes and its prose drifts down onto whatever follows. **Nothing else can see it**: the type checker
and the formatter read no comment, the name guard reads the model's side, and the suite passes
either way. Its blind spot is that the signature is structural rather than semantic. It finds two
blocks with nothing between them; whether a stranded block is deliberate two-part prose is a
judgement, so such a block carries a marker and the guard takes it at its word.

**Grep is the instrument that is left, and it has two blind spots of its own.** A grep piped into a pager is not
a measurement, and the same pipe hides an exit code as readily as a line — reading a status
through a pager reports the pager's success. And an edit anchor that is not unique is not an
anchor: anchor a scripted edit on a whole block that occurs once, and read the line delta before
writing, because a diff of the wrong size is visible in one number and invisible in a review. The
second real blind spot is the anonymous-constructor pattern: a positional match names neither the
qualified constructor nor the case, so when costing a constructor change, grep the bare dotted
form too and expect the arity to be implicit.

### The bridge, and the claims that cannot reach the kernel

**Regeneration is not verification.** What verifies the bridge is elaboration, which is why the
gate runs the committed samples and the full refusal cross product through Lean rather than
trusting a byte comparison. **Refusal vectors are the other half of the same blind spot**: a
positive vector is an agreement about what the library wrote, so a value the library refuses
produces no vector at all — the half of the pair where the two sides could disagree unobserved.

**No vector asserts a decoded value.** Every emitted theorem is about the write half or about a
refusal, and the read-side differential compares a decision rather than the value that came back.
So the kernel has never been shown that the read half returns a particular value, and the two laws
most of this library's shipped defects lived in are the two the bridge cannot state. `veq`, sound
by `veq_sound`, is what would make them statable.

**The terms the emitter refuses are exactly the terms whose laws a caller owes.** The constructors
carrying a caller's function, and a refinement holding a host predicate, are unemittable because
nothing translates a closure into a Lean term, and emitting a different predicate would compile
and prove the wrong theorem. That refusal is right. Its consequence is that the bridge is blind
precisely where the model discharges an obligation the host cannot check either, so for those
terms the guarantee is a written premise on both sides.

**A red bridge check that returns immediately has read nothing.** The bridge shares a build cache,
and a racing run fails at once over an unchanged tree. Judge that check by its duration before
judging it by its exit code.

The bridge checks generated lines by kernel typechecking rather than by evaluation, because the
denotation is `noncomputable` where the numeric host is an axiom. Evaluation and decision by
compilation are both unavailable, and that is not a toolchain gap to route around.

### The host's instruments

**The type checker's error count is a lower bound, not a measure.** Retyping a position
under-reports the sites: a cast standing on the position leaves the checker nothing to say, a test
whose subject rides on a type it does not name keeps passing while the fact it pins stops being
checked, and a comparison at the wrong level of nesting reports nothing. The sharpest case is a
deletion rather than a retyping — collapsing an option builder to the term-only form typechecks
cleanly, because the member's type already admits the absent case, and fails a row of tests. The
suite is what closes the gap.

**The type-level snapshot proves negatives and sees only what a spec asserts.** It records an
instantiation count and a resolved type per assertion, so a change that moves neither moved
nothing any assertion covers. What it cannot say is anything about a type no spec names, and the
population it covers is a choice somebody made rather than the surface.

**A strictness flag that is off reports nothing**, and that is a blindness no tool can announce
because nobody asked it anything. Asking, with no file changed, is what turns an unasked question
into an answer.

---

## What is deliberately not modelled

Each of these is a decision with a price, not a gap, and each has a witness.

**Recursion under a union.** A union resolves by *unique* admission, and admission derived from
whether the write half succeeds means that growing a recursive result grows admission, grows the
filtered option list, and collapses the answer. Unique admission quantifies over the other
options: a negative condition, anti-monotone in exactly the argument a fixpoint must grow.
`altCodec_not_monotone` is the obligation any fixpoint construction would have to discharge and
cannot, and `stage_not_monotone` shows the same collapse between adjacent stages. The low-stage
answer is over-defined, not under-defined.

**The refutation is specific to counting.** Confluent resolution, where several options may admit
provided they agree, is proved monotone and continuous by `selectF_mono` and
`selectF_continuous_list`, and is **not adopted**. Order-independence stops being unconditional
and holds only given the obligation, and a specification whose commutativity is conditional is a
worse specification. That is a specification call, not a mechanization call.

**The nesting bound.** `Nesting.lean` is the one place the attribute algebra is larger in the
model than in the store, deliberately. The list and map constructors nest without limit by
construction, so a derivable term can write an attribute the store refuses, and
`not_storable_of_typed` is the witness: a well-typed term, a value on its held set, an encoding
outside `Attr.Storable`. The model must be able to **state** this, because a target certified
against a specification that cannot say it is certified against a weaker claim than its users
read. The honest repair is not a carrier refinement, because the witness violates no premise: the
rules do not mention depth. The indexed-family alternative is accepted by the kernel only in
mutual form, so every list position needs a hand-rolled companion indexed alongside it, which is
the price. `Attr.Storable` counts the two nesting constructors and is a different function from
`Attr.depth`, which is a termination measure. Do not unify them.

**An element-level adapter or read widening under a set**, given up by indexing the set by its
element base. A restriction of the elements is not lost: `setCodec_restrict` proves that a
restriction of the elements and a restriction of the set write the same attribute on the nose,
with `liftQ` carrying the predicate through. What is lost has no set-level spelling, because a
set-level adapter would need an injective image rather than the classical one, and a set-level
read widening widens the whole attribute rather than each member.

**The n-ary literal is a union of singletons.** A literal carries one value, and several
alternatives are a `union` of singleton literals whose members are separated because the values
differ. `LiteralArity1.lean` is the derivation, including the uniqueness property on both sides
through `uniqueAdmission_of_sharedBase`. The route was refused while a literal held a set: the
bridge from a `Finset` of alternatives to the list `Term.union` takes is `Finset.toList`, which
reaches `Classical.choice`. One value leaves no such set, so there is no bridge to cross. The host
keeps the n-ary call as a builder that writes the union, because the hand-written union costs the
type checker in proportion to the number of alternatives where the call is flat.

**A number with no closed terms.** The host's number is axiomatized rather than modelled, because
rounding is not a theorem of this calculus. The price is paid in distinct places that close
differently, and `docs/defects.md` records them as an issue with what is mitigated and what
remains. The architectural point is the discipline: each is met by somebody doing something
reasonable and finding it impossible, so **establish which impossibility it is before recording it
as permanent.** Apparent walls here have turned out to be something else, and the one that was
something else closed.

**Non-malleability.** `Malleability.lean` records that this development deliberately fails it, and
why the relational-format proposal that would have entailed it is refuted by `fmt_forced`: `Fmt`
is the fibre of the read half, so a relational presentation is the same model addressed by fibre,
and a fibre cannot be shrunk to buy the agreement clause without losing completeness.

---

## What the host owes

The model's structural guarantees are not self-enforcing in an implementation. A type here is a
question the host still has to answer.

**The rule: prefer making a bad state unrepresentable over guarding against it.**

For every structural guarantee the model makes, a host is in exactly one of three positions.

| the host | owes | why that is the whole debt |
| --- | --- | --- |
| **(a)** carries it structurally | **nothing** — verify by types and move on | the host type is doing the work; there is no gate to own and nothing to test that the type does not already say |
| **(b)** must gate | a **named** gate, in the module that owns the carrier, and a test asserting **both** sides | one owner: a gate mirroring a carrier refinement belongs to the module that *is* the unrefined carrier, or a sibling entry point writes a second answer to the same question. And a test checking only our behaviour cannot tell a deliberate divergence from a reference implementation apart from a regression |
| **(c)** cannot express it | a construction-time **refusal**, a test that pins it, and a written **reason** | the reason is what stops the next reader from "fixing" the signature, and **the test is the half that goes missing** |

**A (c) refusal is not finished until a test reaches it past a cast.** A brand is not a proof and
a cast defeats a brand, so the caller the refusal exists for is exactly the caller the type cannot
see, and that caller is the one a test must impersonate. A refusal whose deletion leaves the suite
green was load-bearing for the type and unobserved for behaviour.

**The three cases are not a permanent assignment.** A host that had to gate can later carry the
guarantee structurally, and when it does the gate stops refusing anything and its remaining
content is its message. **What such a gate owes on the way out is that message, moved where a
refused caller reads it.** A constraint's own diagnostic names the offending type; it does not say
what to write instead. A gate deleted without moving its sentence loses the only part of it the
type did not already carry.

**The exception that keeps a gate.** Keep it only where the refutation depending on it **cannot be
restated outside the term language**. If the thing refuted is a rule rather than one of our
constructors, a standalone transcription carries it and the gate can go — `literalNRule` is such a
transcription, deliberately not a `Term`. Where the claim is about one of our own rows, no
transcription recovers it and the gate pays.

**A measure has no host counterpart, so it is pure overhead.** No line of the library has a fuel
parameter. A measure standing in for a recursion the checker could not see corresponds to nothing
in an implementation. The discipline is a hierarchy: turning a measure into structure costs the
correspondence nothing and is worth the most; turning a gate into a type is worth less and is
available where the condition is decidable from a constructor's own arguments and the host can
mirror it or pay honestly; keeping the gate is for the exception above.

**Targets differ, and that is a fact about certification.** The same structure ports with
different fidelity. A nonempty finite set is not expressible for a variadic in TypeScript and is a
newtype with a private constructor in Rust. An indexed literal is a discriminated union of literal
types in one and an enum with a payload per variant in the other, which *is* the indexed family.
A checked numeral wants a nominal newtype in both, and where a language has no nominal typing the
branded-type trick is the closest thing and a cast defeats it.

**Sometimes the host has the sharper instrument.** Two byte arrays holding the same bytes are the
same value in the model, which has no reference identity to distinguish them. A host that does
have one answers a binary literal's read side with the declared array rather than a copy: that is
how the host spells "the value the model means" where the model needs no spelling. A target with
value semantics for byte arrays owes nothing here, and one without owes the identity.

**Where the two sides disagree, the emitter is where it gets written down.** A tag is stored as a
string or as a numeral, and the model reads a discriminator as the literal it is at either base —
a decimal literal holds its numeral as text, so the two bases are two spellings of one tag rather
than two tag types. There the two sides agree, and a discriminator at either base emits.

**The one refusal left is the numeric base**, and it is not a disagreement about what a tag is.
The model can state no tag there at all, for the reason `docs/defects.md` records as an issue: the
numeric host is an axiom with no closed terms. The emitter refuses such a union rather than
emitting a vector about a selection the model cannot express, and its message says so in the
caller's vocabulary. That refusal is the record, and it is the shape every gap of this kind takes
— the reader is total, and what bounds it is which terms have closed forms.

**A core union requires its discriminator.** The model selects only an input that carries the
required discriminator. A caller that accepts an old input wraps the whole union in one outer
`LegacyRead` carrier. The alternate reader owns that migration after core selection refuses.
`Body.spec` contains no migration field.

**A host obligation that no host code reads is found by whatever has to serialise the host's own
definition, or it is not found.** A term the host builds must determine the codec the host runs.
Where a definition record kept only what each reader needed, a channel the model carries was
dropped and nothing failed, because the half that was missing was the half nothing read.

**A codec carrying a `Term` is case (a) reached by deletion.** Keeping two descriptions of a codec
— the model's language and a record that grew a row at a time — made states reachable in the host
that are unrepresentable in the model. One description means those states stop being reachable
rather than being checked for, which is what (a) buys. Such a flip has to be one commit, because
the denotation dispatches on one type: a union of the two types on the field compiles just as well
half-migrated, so nothing in the checker says when the transition has finished, and a reverse
conversion at the construction site is a second conversion written in order to be deleted. What
says when it is finished is a table asserting the conversion is the identity, one row per
constructor — which no checker can answer, and which asserts nothing once it is complete.

**Test machinery drives the generators; it does not hold them.** A hand-written codec states its
own generator and shrinker, because how a codec generates is a fact about that codec rather than
about testing, and `custom` takes the pair and the two generators together as data — they go into
the term, which is the codec's whole definition. What lives in the testing entry point is the
machinery that *drives* them: the derivers that walk a term to build a generator, the shrinker, and
the law checkers. **The term is the only source.** Where a generator was a projection of the term
that the derivers read before the term was consulted, one fact travelled two paths and could
disagree with itself; now a caller that wants to share a generator names it rather than reading it
back off a codec.

**So a guarantee that must be a gate in one target may be structural in another.** The three cases
are re-answered per target at the time that target is certified, not in advance, and not as a
reason to shape the model around one language. The model's job is to make the guarantee structural
in the model. How much each target carries is that target's certification.

---

## The proof vocabulary, and what a docstring is for

**The rule.** A definition is unfolded once, in its own inversion lemma. Every proof downstream
cites the lemma. Each construction gets two, proved in one step, and they are the only place that
construction's option chain is ever taken apart: one for what the construction writes, one for
what it reads.

**The naming scheme is normative**, so the next proof inherits it.

| form | means |
| --- | --- |
| `X_e` and `X_p` | inversion — what `X` writes, what `X` reads |
| `X_eq` | `X` **is** an instance of a named construction, on the nose |
| `lawfulCore_X`, `lawful_X`, `carrier_X` | the three obligations, in that order |
| `Lawful.X` and `LawfulCore.X` | the same where the construction is itself namespaced |
| `f_sound` | a syntactic function agrees with the denotation |
| `equiv_X` | a rewriting row |
| `not_X` | a refutation, or a repaired discharger |
| `onKind_X` | `X` is pinned to a kind |

**What a docstring is for.** The source explains the code; the history is in `git log`. Keep the
rule or clause tag, so a reviewer can check a theorem in isolation. Keep the forced choice: why
the definition could not have been the obvious other one. Keep what a refutation is a refutation
of. Move out how a finding was made, what it cost, which audit missed it, and any argument another
document already states. Prefer a name that makes the sentence unnecessary.

**A name the sources do not define is marked rather than backticked, and this is normative.**
Usually it is retired, because a docstring recording what a forced choice cost has to name the
thing that lost. To the name guard a deliberately dead name and a renamed one are the same token
absent from the sources, and the difference is the tense of the sentence, which no parser reads.
The mark carries it. An unmarked backticked name is a claim that it is live and the guard holds
you to it; a marked one is a claim that it is dead, and a mark on a name still in the sources
fails as a false retirement. Occasionally the name never existed, and the mark says the same
useful thing there.

Two further conventions, both load-bearing. **The core lemma is not a second proof**: the weaker
obligation and the stronger one share their clauses and differ only where the content differs,
with a projection making the weaker a corollary rather than a parallel development. **An identity
stated in prose gets cashed as an equation**, so that every lemma carries across by rewriting
rather than by restatement.

**Length is not the metric; sites are.** A theorem whose content *is* a rule-by-rule dispatch
belongs at the top of the length table, one line per typing rule, and compressing it would cost
the reader the correspondence with the rules. Inline comments are exempt from the naming
convention: they are proof waypoints, which is the one thing a name cannot supply.

---

## If you change something

- New module under `Calculus/` → make it reachable from `Axioms.lean`, and baseline its counts,
  because a new module has no prior state to be judged against.
- New stratum in the term family → every companion in the table above, counted per side.
- New rule → put each term premise in exactly one of `Typed` and `Obligations`.
- New term recursion → `term_depth_wf`, and any new inequality beside `Term.depth`.
- New analysis row → prefer asking the codec over describing the set, then prove its exactness
  clause, because a missing row is silent and silence is sound.
- Sharpening a row that answers "everything" at a container → find what relied on the slack
  before you sharpen it. Nothing measures transitive dependents any more, so the cost is a grep
  with the two blind spots above, read against what the analyses say the slack is carrying.
- Citing a Lean name in a current-state document → the name guard must exit 0.
- Reaching for a count in a document → do not. No guard holds a document to a number any
  more, so a count in prose is unguarded by construction. It belongs in the commit that
  measured it, in `defects.md` where it pins an issue, or in a guard's output.
- Deleting a declaration → resolve every path and every name the deletion leaves cited, because
  no guard resolves a cited path and the name guard clears a citation that any file in its source
  set happens to mention. `git log -S` on the name is what says whether it was ever declared.
- Touching a normative document, the advertised axiom base, or the library's behaviour → that is
  the owner's decision. Deliver the measurement and stop.
- Committing anything → run the gate, and gate on its **exit code**. Printing an exit code is not
  checking it.

### On the host side, per structural guarantee

- Which of the three cases is this host in? Answer that before writing the gate, not after.
- **(a)** Name the host type that carries it. No gate, no test.
- **(b)** The gate lives in the module that owns the carrier, not in the first caller. One owner.
  The test asserts both sides wherever the behaviour diverges from a reference implementation.
- **(c)** Construction-time refusal, a test that reaches it past a cast, and a written reason.
- Does a refutation depend on this being a gate *in the model*? Only then keep it, and only if the
  refutation cannot be restated outside the term language.
- Is it a measure rather than a guard? Then it has no host counterpart and is overhead.
- **Un-typeable never means un-checkable.** A constraint that fails "can it be a type?" is not
  disposed of. It is handed to the next question: does anything enforce it? Filing it as closed on
  the first answer is a recorded failure mode of this project's own auditing.
