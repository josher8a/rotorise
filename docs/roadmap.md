# Roadmap

What this system would be in the future. One entry per future state, with what decides whether the
state arrives.

An entry here is a state the system does not have. A statement of what the system *is* belongs in
the architecture. An issue belongs in `defects.md`.

An entry carries no measurement. A count is short lived: it belongs in the commit that measured it,
in `defects.md` where it pins an issue, or in the gate's output. A figure appears here only where
the figure is itself the threshold that decides the entry.

Each entry names declarations and files. It points at no section number, because a section number
moves and a declaration name does not.

---

## The term language is founded on a pre-term, so an undischargeable union has no inhabitant

**The future state.** `Scoped.Term` becomes a subtype of a pre-term, carrying its own well-formedness:
`{t : PreTerm // wf t = true}`, where `wf` recurses after the `SFlat` rather than inside it. A
union whose options are not shown compatible then has no inhabitant, so such a union is a type
error rather than a runtime refusal.

**The ruling today is no, and it is JH's.** The model's `Scoped.Closed.Obligations` already carries the
compatibility of a union, and `Scoped.Closed.sound` takes it as a premise. The library refuses such a union
at construction. The re-founding buys the model a stronger statement about itself and buys the
library nothing it lacks.

**Two other shapes do not elaborate, and both were run rather than argued.** A witness indexed by
the option list it constrains is induction-induction, and the elaborator answers `unknown
identifier` on the type being defined. A field whose type is computed from the term is
induction-recursion, and the elaborator answers `invalid mutual block: either all elements of the
block must be inductive/structure declarations, or they must all be definitions`. The subtype shape
elaborates and is axiom-free, so the obstruction is not expressibility but cost.

**The obligation is a `Prop` today.** The compatibility of a union sits in `TOp.obl`, beside the
judgement, and a term that does not meet it is still a term.

**The cost is structural.** Every operation of `Scoped.Term` becomes a smart constructor carrying a
proof obligation, and every match on a term goes through the subtype's first projection.
`Scoped.Term` is the vocabulary of most of `Calculus/`, so the re-founding reaches every signature that names it. The
commit that probed this holds the site count; the count moves with the tree and the shape of the
cost does not.

**What decides it.** A statement the model owes about itself that `Typed` cannot make. Until such a
statement exists, the re-founding pays the whole term language for a guarantee two other layers
already give.

**What names the guarantee instead today.** `Closed.PairwiseCompat`, one `Prop` over the option
list. `Closed.pairwiseCompat_of_compatPair` discharges it through the decision, and
`Closed.pairwiseCompat_of_separated` with `Closed.separated_of_certAllC` through the certificate.

---

## A reader can tell what every public theorem says from its name and one line

**The future state.** Every public theorem in `Calculus/` carries a docstring, so a reader who knows
the specification can tell what the theorem says without reading its proof.

**A coverage bar is the wrong instrument, and that is settled.** A bar over the coverage this tree
has would be switched off or exempted into meaninglessness, and the fraction it would have to name
is the fraction it exists to reject. `scripts/ratchet.py` holds the count of undocumented public
theorems and fails when it rises. A ratchet costs nothing to satisfy on the day it lands, which is
why it is what runs.

**What decides it.** The ratchet reaching **zero**. That is the one figure this entry carries,
because it is the threshold and not a measurement: the state arrives when no public theorem is
undocumented, one pass at a time, and no threshold in between is worth setting. The current count is
the gate's output, not this file's.

---

## A cofinite set at a ground kind is a ground constructor

**The future state.** A ground kind carries a cofinite set of its values: each value of the kind
but a finite set. The test keeps a cofinite set apart from a literal that the set
excludes, and from a value of another kind.

**What the tree carries today.** A finite set at a ground kind is a union of literal ground
symbols, and a literal is the singleton. `refine` carries a closure, `Pred.closure`, and the
decision reads through a refinement, because a refinement accepts a part of what its inner term
accepts. So no declaration compares two predicates, and a cofinite set has no representation.

**Why the state is wanted.** A name is a string, so a cofinite set at the string kind excludes a
finite set of names. A closure states the same set, and the test reads through the closure. So
`Scoped.disjoint` answers `false` for the string literal `"a"` beside a string that excludes `"a"`.

**What a change costs.** The cofinite set is a new ground constructor, so `Ground.apart` and each
primitive row gain a case. The generated artifacts are stated over the term language, and the gate
elaborates each artifact. So a change to the constructor set lands checked wherever the change
reaches an artifact.

**What decides it.** A pair that the library writes, which the test refuses only because a
cofinite set sits in a closure.

---

## The disjointness test answers at an adapter, at the top, and at a closure over a finite set

**The future state.** A closure over an unbounded carrier is the one leaf that answers nothing.
Every other position answers the test:

- An adapter answers through its obligation. A theorem states when a `held` admits some value,
  from its inner term and its outer, under `Obl1`. The theorem reads no property of the host
  function beyond the obligation, so the set of the adapter stays unnamed.
- `opaque` is total on both sides, so `opaque` is disjoint from a partner exactly where the
  partner admits no value.
- A closure beside a finite admissible set applies its function to each alternative of the set.
  The answer is exact.

**What the tree carries today.** Over the free fragment `Scoped.Frag` the test is exact
(`Scoped.disjoint_exact`). The positions this entry names lie outside the fragment: `Scoped.disjoint`
reads a raw `held`, a `legacy` and `opaq` as disjoint from the bottom alone. A `refine` reads through
its inner term. So a closure over `boolean` that refuses every value is not disjoint
from the literal `false`. The certificate reaches a `held` through its views (`Closed.viewsDisjoint`),
and not through the test. `Closed.opaq_total` and `Closed.opaqA_total` state that `opaque` admits
every value and every attribute. No theorem states when a `held` admits some value.

**What decides it.** A union that the library refuses where one option is a raw `held`, `opaque`,
or a closure over a finite carrier, and where a caller needs the union.

---

## One decision of inhabitation settles both sides

**The future state.** A declaration decides whether a term admits any value. A theorem derives
the emptiness of the read side from the emptiness of the value side.

**Why one decision suffices.** A term that admits a value writes an attribute, and the retraction
law reads the attribute back. A term that accepts an attribute reads a value, and the definedness
of reads writes the value. So the two projections of a term are inhabited together. Applied to the
product of two domain idempotents, the value projections are disjoint exactly when the attribute
projections are. The premises are the retraction and the definedness of reads, which are fields
of `LawfulCore`, so a term with an alternate reader still meets them.

**What the tree carries today.** On the value side, over the free fragment, the decision exists:
`Scoped.inhabited_iff` says that a closed codec admits a value exactly where `Scoped.disjoint` does not
separate the codec from itself. No theorem derives the emptiness of the read side from the value
side, and outside the fragment no declaration decides inhabitation. `Closed.AdmA` is a computable
`Bool` at one attribute, the domain of the read of the meaning.

**The exception is an adapter.** The certificate reads an adapter through its two views, and
the future state keeps the views there.

**What decides it.** A pass that needs the attribute side of a pair where the tree proves only
the value side.

---

## A run of restrictions, and a run of adapters, has one normal form

**The future state.** A function reduces a term to a carrier under an alternating word. A run of
restrictions meets to one restriction, and a run of adapters composes to one adapter. A
restriction and an adapter do not collapse, because no law relates them: a refinement outside an
adapter tests the value of the caller, and the same refinement inside tests the carrier.

**Why the state is wanted.** The restrictions around one carrier form a meet-semilattice, so a run
of them has one normal form, and the order inside the run carries no information. The adapters
form a monoid, so the order inside a run carries everything. A run carried as written costs the
certificate. A string refined by two closures that hold together nowhere admits no value, and
`Scoped.disjoint` does not find the pair disjoint from a string.

**What the tree carries today.** The equations of a run hold up to `Codec.Equiv`:
`equiv_restrict_meet` meets two restrictions, `equiv_through_comp` composes two adapters, and
`Scoped.equiv_held_comp` composes two nested `held`s under a closure restriction outside them. No
function reduces a run. `not_equiv_trans` shows that `Codec.Equiv` does not chain, so the
equations do not compose into a normal form one step at a time.

**What decides it.** A pair that the test misses because a run is spelled as written, in a term
that the library builds.

---

## A restriction outside an adapter meets into the held side

**The future state.** Which values an adapter owns is a restriction on the values of the caller.
A restriction written outside a `held` meets into the outer of the `held`, because both restrict
the values of the caller. Then the caller view of the `held` names the values that the `held`
owns.

**What the tree carries today.** A `held` carries its held side as its outer, and the caller view
of a `held` is its outer. The host's `decimal` over literals records the string literals of its
texts there. A `refine` outside a `held` stays a separate layer, and no equation in the tree
states the meet.

**What decides it.** A union that the views refuse because a restriction sits outside a `held`
rather than in its outer.

---

## Admission and the certificate are one relation

**The future state.** One relation answers two questions: whether a value inhabits an option, and
whether any value inhabits two options.

**Why the state is wanted.** A certificate that separates what admission cannot tell apart is
unsound: two incompatible options then admit one value, and the order of the options decides the
attribute. A pair that admission tells apart and the certificate does not is waste, because the
union is refused where the codec works. Two functions kept in agreement by hand drift, and
nothing reports the drift.

**What the tree carries today.** The meaning of a closed codec holds its own domains, and
`Closed.AdmA` is the domain of its read. The certificate is a separate function, `Scoped.disjoint`,
sound for the domains of the meaning (`Scoped.disjoint_sound`). Over the free fragment
`Scoped.Frag` it is exact (`Scoped.disjoint_exact`): there the certificate answers `true` exactly
where the two meanings share no value. Outside the fragment (a refinement, a fill, a `held`, a
`legacy`, the top) it is sound and not complete.

**What decides it.** A pass that adds a constructor, and so owes a row in both functions.

---

## The certificate is parametric in the universe

**The future state.** The separation rows and the certificate take a universe signature as a
parameter, as the disjointness test does. JSON then separates a union by the same certificate as
DynamoDB.

**What the tree carries today.** `Scoped.disjoint`, its soundness and its exactness
(`Scoped.disjoint_exact`), and `Scoped.compatPair` are generic. A universe supplies its leaves, its
shape classes and the laws `Scoped.Laws` that the decision reads, and JSON supplies each. `Closed.viewsDisjoint`, `certAllC`, `Closed.Separates` and
`Closed.pairwiseCompat_of_separated` read the closed codecs of DynamoDB, and JSON has none of them.

**What decides it.** A second universe that needs a union of separated options.

---

## The compatibility decision knows a canonical bound below the top

**The future state.** The decision accepts an adapter beside a term where one canonical codec
other than the top bounds both at a component that shares an input.

**What the tree carries today.** `Scoped.compatPair` knows two bounds: the top, which bounds two
terms below the top, and one adapter word, which bounds two `held`s
of one side and one word. A canonical codec below the top that bounds an adapter and a term is
neither bound. So the decision refuses such a pair at each component that shares an input on one
half. `compat_of_common_bound` proves in the model that two restrictions of one canonical codec
are compatible.

**What decides it.** A union that a caller needs, of an adapter and a term below one canonical
codec, which the library refuses today.

---

## The development carries its own constructive `Finset` layer

Mathlib resolves `k ∈ (s : Finset α)` through `Finset.instSetLike`, whose injectivity field
is proved classically, so every statement that mentions membership in a key set carries
`Classical.choice`. No proof in `Calculus/` appeals to choice, and none needs it.

**The layer alone does not drop the axiom, and that is measured rather than expected.** The
`Finset` route is one of several. Core Lean's own string lemmas reach `Classical.propDecidable`
through the UTF-8 decoding proofs, and theorems in several modules reach choice that way; cut
`Finset.instSetLike` out of the citation graph and those theorems still reach it. One arithmetic
simp lemma is a third route. `scripts/classical_gateways.txt` holds the set, and the gate fails
on a route that is not in it. So this entry delivers a constructive membership layer, and a
constructive *base* is a further state that needs the other routes closed as well.

The state this entry names is a membership and decision layer of this development's own, over
`Multiset.Mem` rather than the coercion to `Set`, with the mathlib lemmas the tree uses restated or
bridged against it. `MapOf` in `Alg/Maps.lean` is where it starts, because the key set is a
`Finset String` and `MapOf.at` is the first declaration that decides membership.

**What decides it.** Two local instances, membership and its decision, were measured against the
whole tree and moved a small fraction of the declarations that reach the axiom. So the entry arrives
only with the restated lemmas, not with an instance. It arrives sooner if mathlib makes the set-like
route constructive upstream, and the entry closes with no work here if that happens.

---

## A derived key is a codec of the item, and a key parses back to its components

**The future state.** The model states a key spec as a codec. Each component of the spec is a codec
of one attribute, a tag is a literal, and a transform is an adapter. The key is the word of the
components, printed with the separator into one `S` attribute. The print is injective where no
component prints the separator, and the parse of a key gives back its components. A variant that has
no key, the `null` arm of a discriminated spec, is the codec that writes no attribute, so the index
is sparse by construction. The row of an entry is the attributes of the item and the keys that the
attributes derive, and a key that disagrees with its attributes is a row that the entry does not
read.

**Why the state is wanted.** Derived keys are the most used part of the library. `fromEntry(entry)`
today deletes the key attributes and reads nothing, so a service reads a row with a cast to the
entry type, and the boundary parses no key. Two items with one key overwrite each other in silence
where a component prints the separator. With a parse, `fromEntry(entry)` is a decode at the
boundary, and a component that can print the separator is a refusal at construction.

**What the tree carries today.** `key(name, attributes)`, `toEntry(item)` and `fromEntry(entry)` in
`src/Rotorise.ts` build and strip key strings. The model states the key as a codec from a list of
segments to a string, `DerivedKey.keyCodec`, lawful on the lists that have a segment and hold no
separator (`DerivedKey.keyCodec_lawful`). A segment that holds the separator gives two lists one key
(`DerivedKey.rawWrite_not_lawful`). No vector ties the run-time builder to the model yet.
`item(codec)`, `at(codec, path)` and `extract(codec, pattern)` give the codec of an item, of a path,
and of the options of a union that a pattern names.

**What decides it.** A pair of items of one entry that derive one key, or a row whose key disagrees
with its attributes, in a table that a service writes.

---

## A partial key is a prefix, and a query by the prefix selects exactly the items that agree on it

**The future state.** The components of a key spec are ordered, and a partial key is the print of a
prefix of the components. `begins_with(key, prefix)` on the partial key selects an item exactly
where the item agrees with the prefix, on each component that the prefix holds. The model states the
condition: each component prints no separator, and the partial key ends with a separator where the
prefix stops between two components, so that `A#1` does not select `A#10`. A range condition on a
sort key is sound where the print of each component preserves the order of its values. The library
refuses a partial key or a range for which the condition fails, and does not build a key that
selects more than the prefix states.

**Why the state is wanted.** Services query by partial keys at many sites, through
`key(name, attributes, { depth })` and `key(name, attributes, { allowPartial: true })`. The boundary
is an option today, `key(name, attributes, { enforceBoundary: true })`, and a partial key without it
can select items outside the prefix. Services also build prefix strings by hand, such as a tag
followed by a separator, because the spec form cannot state a prefix that holds only a tag.

**What the tree carries today.** The run-time key builder in `src/Rotorise.ts` reads the three
options, and the type of its result reads the same options. The model states the prefix law: a
partial key with a trailing separator is a prefix of a key exactly where the key extends its
segments (`DerivedKey.prefix_iff`), and without the separator it selects more
(`DerivedKey.prefix_without_separator`). The run-time rule of
`key(name, attributes, { enforceBoundary: true })` counts segments, so a transform that prints one
segment makes it append a separator to a full key (`DerivedKey.hostBuild_ne_build`).

**What decides it.** A query by a derived partial key that returns an item outside its prefix, or a
hand-built prefix in a service that the derived form cannot state.

---

## A table entry is built from the item codec, and the spec form is a spelling of the construction

**The future state.** An entry has two forms. The spec form stays: `tableEntry<Entity>()(schema)`,
with arrays of attribute names, transforms, discriminated specs and `null` arms. A constructive form
is a free function over the codec of the item, as `item(codec)` is a free function: the entry is
a reading of one codec, not a second declaration. The function builds each key from the codec of the
item: a component reads a path of the codec, a tag is a literal, a transform is an adapter, and a
discriminated spec is one key for each option of the union. The type of each key is the template
literal that the construction gives, and the type of each component is the decoded type of the codec at its path. The spec form denotes the construction,
so the two forms have one semantics and one type. The footprint of each key, the attributes that it
reads, is one fact. `keyUpdates(changed)`, the refusal of a change that moves the item, and the type
of a key read that fact.

**Why the state is wanted.** The spec form finds its type by trial at the type level: the validation
and processing types of `src/Rotorise.ts` test each shape of a spec in turn. Services cast around
the result: `as never` at `toEntry(item)` and at `key(name, attributes)`, a helper that strips the
readonly mark from a shared spec, and a key updater written again by hand with a cast of `key`,
because the type cannot relate the name of a key to the row. The codec already carries the decoded
type of each path, so a construction from the codec gives the type in one step.

**What the tree carries today.** The spec form takes a `{ codec }` option, and no service passes
one. `keyUpdates(changed)` exists with its refusal of a change that moves the item, and services
write their own updater instead. The key types of `src/Rotorise.ts` state the footprint at the type
level.

**What decides it.** The services' entries, written in the constructive form, typecheck with no
cast. The vector bridge puts the keys of the free function to the model of a derived key, as it puts
the codec to the model of a codec. Each spec entry gives the same keys and the same types as its
construction, on the entries that the services declare.

---

## An entry costs the checker and the run time no more than the spec form costs today

**The future state.** After the two forms above, the type of an entry and the build of a key are
measured on the entries of the services. The checker time and the instantiations of the largest
service, and the run time of `key(name, attributes)` and `toEntry(item)`, are no worse than the spec
form at the base. Where a form is worse, a pass makes it cheaper before the form ships.

**What decides it.** The measurement at the base, taken before the constructive form lands. That
figure is the threshold.
