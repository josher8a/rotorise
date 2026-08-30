# Codec calculus — formalization goal, scope, and conformance

Companion to [`codec-calculus.md`](./codec-calculus.md). That document is the **specification**:
what a codec is, what laws it obeys, and what side conditions its constructions carry. This one
answers three questions about the machine-checked model in [`../formal/`](../formal/):

- **What is it for** — and why it is not "tests for the TypeScript".
- **What it proves**, exactly, and what it does not.
- **What an implementation must exhibit to be certified against it** — in any language, in this
  codebase or another.

The short version: the calculus defines what a *correct* codec is, once. The formalization proves
that definition is coherent and that the algebra's constructions preserve it. A target
implementation is certified by exhibiting a homomorphism into the model — not by re-deriving the
laws.

---

## §1 Why formalize at all

A codec is a pair `(e, p)` that has to round-trip through a store nobody controls, under schema
evolution, forever. The failure modes are not crashes; they are **silent** — a value that reads
back subtly different, an attribute two union options both claim, a migration that re-encodes a
variant no tag selects. Tests find these only if you thought of the case.

The specification's job is to name the properties that make those failures impossible. The
formalization's job is to check that the specification is not lying — that the properties are
mutually satisfiable, that each construction really preserves them, and that the side conditions
stated as sufficient actually are.

That last one is not hypothetical. Mechanizing §5 refuted **three** of the discharger claims the
specification made (§4 below). Each was a small concrete counterexample, and each had been read by
humans and believed. That is the return on this work.

The traffic is not one-way. Two of §4's entries are defects the model found in the **implementation**
rather than in the document: a `numeric` that narrowed a read without checking it, and a decoder that
returned a value its own encoder refuses. Both had shipped.

And it keeps flowing. §4's last entry is a defect found by a *harness written from the model* — (U)
stated as a property test, over inputs no value-driven test can produce — in a union the library
accepts, decodes from, and cannot encode into. The model does not have to observe the runtime to
find things in it; it only has to say what to look for.

## §2 What the formalization is not

**It is not a test suite for the TypeScript.** Nothing in `formal/` observes the shipping
implementation. `denote` is a second implementation of the calculus that happens to be verified;
that the runtime agrees with it is a separate obligation, and currently an unmet one (§6).

**It is not a proof that the calculus is the *right* specification.** It proves the specification
is internally sound. Whether (R), (C), (W) and (MP) are the properties DynamoDB persistence
actually needs is an engineering judgement, argued in `codec-calculus.md` §2 and §7, not a theorem.

**It is not a performance or resource model.** Fuel is a termination device, not a cost measure.

## §3 What is proved

Everything below is machine-checked, `sorry`-free, on `propext`, `Quot.sound`, and the `Double`
axioms of §1 — no `Classical.choice`, no `sorryAx`. `#print axioms` on any named theorem shows the
whole trusted base, and `formal/Calculus/Axioms.lean` makes that sentence a **build error rather
than a claim**: `#assert_axioms_all` walks the `Calculus` namespace and fails on anything
unsanctioned. This matters more since mathlib arrived, because mathlib proves a great
deal classically — a single `by_contra`, or an appeal to a lemma such as `List.filter_eq_nil_iff`,
silently widens the base of everything downstream. Both leaks happened while the guard was being
written, which is the argument for having it.

The guard was itself opt-in until recently: 125 hand-written `#assert_axioms` lines naming 125
theorems, in a namespace of 1199. That is the wrong default for a guard, because it holds exactly
where someone remembered to invoke it and is silent everywhere else — and it *was* silent: one of
the 1074 unnamed theorems, `not_equiv_tupleTail_tuple`, had acquired `Classical.choice` from
`simp`'s classical push-neg and no one had noticed. The universal form found it on its first run.
A theorem is now guarded **because it exists**; there is no list to keep in step and nothing for
`scripts/fidelity_audit.py` to police beyond the presence of the guard itself.

### The theorem

For every derivable judgement `⊢ c : T ⇝ μ`, the denoted pair satisfies §2's laws:

| Statement                          | Content                                                                         |
| ---------------------------------- | ------------------------------------------------------------------------------- |
| `soundness_core`                   | **(R)**, **(C)**, **(W)** — unconditionally, `legacy` included                  |
| `soundness`                        | all four laws including **(MP)** in the strong form `e(p(a)) ≼ a`, where the derivation is legacy-free (`MPOk`) |
| `typed_μSyn`, `denote_μ`           | the `⇝ μ` index is the member the denotation actually stores                    |
| `typed_e_mem`, `typed_p_mem`       | the `: T` index bounds what the pair writes and reads — §3's `e : T ⇀ 𝔸`, `p : 𝔸 ⇀ T` |

Both indices of `⊢ c : T ⇝ μ` are therefore claims about the denotation, not decoration.

Each has a fuel-free twin on `denoteω` — `soundnessω`, `soundness_coreω`, `typed_e_memω`,
`typed_p_memω`, `typed_μSynω` (`Calculus/Soundnessω.lean`). Same content, no `fuel` in the
statement; see §7 for why that took a change to the model rather than a change of tool.

### Two named residues

The theorem is honest about where it stops, and both stopping points are in the specification:

- **(MP) is off on the attributes a `legacy` re-reads.** Deliberate — changing what is stored *is*
  the migration. The consequence is stated in §6 of the specification and holds in the model: a
  `legacy` attribute cannot be an index key.
- **(U) — unique admission — is a premise at canonical inputs** (`UAtCan`), not a conclusion. It
  quantifies over all inputs and is undecidable at the declaration in general.

### One law the specification states and the model can now run

**(R), with the store in the middle.** §2 composes `e` and `p` directly; in use there is a
DynamoDB between them, and it is not the identity on attributes. §1 answers that by narrowing
`decimal`'s held set to `Numeral.Stored`, and the argument for the narrowing was prose: a codec
survives the round trip exactly when the store's normalisation `η` **lies inside `ker p`**.

`Codec.Ker` is that relation — §2's `≈c`, which had no name in the model — `SurvivesStore` is the
inclusion, and `Lawful.retract_through_store` is what they buy. `decimal` now has both halves:
`survivesStore_decimalCodec` (the narrowed held set discharges the premise, because a
normalisation fixes its own normal forms) and `not_survivesStore_decimalWF` (the codec that
gated on `WF` instead does not, and `"1.500"` is the witness). `ker_decimalCodec` is why the
question is that sharp: `decimal`'s kernel is equality, so `η` must be the identity wherever the
codec can be handed an attribute at all.

This is the one place the calculus reaches past itself, and it is worth saying which direction
the evidence ran. The defect was found by putting values in a real table (§4); the narrowing was
the fix; this is the certificate that the fix is not merely sufficient but forced.

### The dischargers of (U)

Decidable conditions, each sufficient for (U) on the unions it covers, all proved:

| Discharger                    | Statement                | Decides                       |
| ----------------------------- | ------------------------ | ----------------------------- |
| disjoint kinds, or disjoint `adm` | `uAtCan_of_separated` | the writable side             |
| distinct members, or disjoint `admA` | `uAtCan_of_separated` | the readable side          |
| tag disjointness              | `uniqueAdmission_byTag`  | `discriminatedUnion`, outright |
| kind disjointness             | `uniqueAdmission_of_kinds` | `opaque`'s fixpoint, outright |

with `κ_sound`, `adm_sound`, `admA_sound` connecting the syntactic functions to the denotation, and
`uAtCan_string_boolean` / `uAtCan_literal_literal` witnessing that the premises are jointly
satisfiable — a discharger whose premises cannot all hold discharges nothing.

## §4 What the mechanization changed in the specification

Three claims in §5's discharger tables were unsound as written. Each is now corrected in
`codec-calculus.md`, with the counterexample machine-checked in `formal/Calculus/Discharge.lean`.
The 12 findings after the table are the rest of the log — defects in the specification, defects in
the shipped implementation, and corrections that ran the other way into the model. Every amendment
they call for has been made; **this file is where the history lives, and `codec-calculus.md` states
only what is true now.**

| Was claimed                                            | Counterexample                                                        | Now |
| ------------------------------------------------------ | --------------------------------------------------------------------- | --- |
| **(K)**: `κ` disjoint ∨ `ident(cᵢ)` ∨ `ident(cⱼ)`      | `union(literal("A"), string)` — (K) passes, both admit `"A"`           | (K) needs `adm` disjoint on **both** sides (`not_uAtCan_literal_string`) |
| the same, with `ident` on both sides                   | `union(array(literal "A"), array(literal "B"))` — both admit `[]`      | `ident` propagates through containers; disjointness does not (`not_uAtCan_array_literals`) |
| **(D)** as disjointness "would be sound"               | `union(literal("A"), held(literal("A"), f, g))` — held sets `{"A"}`/`{"B"}`, both read `S "A"` | (D) is well-formedness on `T`, never a discharger of (U) (`not_uAtCan_literal_held`) |

The shared error is worth stating once, because it will recur in any port: **held sets are sets of
values; (U)'s readable side quantifies over attributes; `held` relabels between them.** No condition
on held sets alone can decide the readable side.

### One the domain had and the calculus did not

§1 gives the value language a `null` and the attribute domain a `NULL` member; §3's
`(opaque)` lists the `NULL` point among the eight options it dispatches on. But **no term
denoted it** — the calculus could describe a value that is `null` and an attribute that is
`⟨NULL, ∗⟩`, and could not describe a codec for them. A schema could say "this attribute is
a string" or "this attribute is optional", and could not say "this attribute is exactly
`NULL`" — a tombstone, or a payload-free option of a discriminated union.

`(null)` is now a ground rule, `⊢ null : {null} ⇝ NULL`, mechanized like the other points
and discharged like them: `κ(null) = {null}` is disjoint from every other ground kind and
`NULL` is a member no other ground term names, so `uAtCan_string_null` settles
`union(string, null)` at the declaration. The omission was found by asking whether
`nullable(c)` could be written as `union(c, null)` — it could not, because the right-hand
side was not a term.

### One about an identity rather than a discharger

§3's paragraph on null-honesty said `nullable(c)` and `union(c, ⟨NULL⟩-point)` "coincide under
honesty, which is why the precedence is harmless". Mechanizing it showed the sentence wrong in
**both** directions, and the correction is sharper than the claim:

| | was claimed | holds |
| --- | --- | --- |
| `≡` (§6) | under null-honesty | **with no premise at all** — `equiv_orNull_altCodec` |
| `=` (same codec) | under null-honesty | only when the base does not touch the null point — `orNull_eq_altCodec` |

Honesty constrains which *attribute* a value is written to; it says nothing about whether `c`
writes `null` at all. Where the base does handle null both options admit, (U) fails, and the union
is undefined exactly where the wrapper answers (`orNull_ne_altCodec`, at `nullable(nullable(c))`).

The first reading of that was that the precedence is therefore **load-bearing**. It is not, and
the correction is worth recording as its own step, because it was reached by someone pushing back
on the justification rather than by the proof assistant. `orNull_eq_self` closes the dichotomy:
where the base *does* handle null, `nullable(c) = c`. So `nullable` is either the union or the
identity — `nullable(opaque) = opaque`, `nullable(nullable(c)) = nullable(c)` — and the precedence
buys nothing a schema would want. §3 now states the dichotomy, and says `nullable` earns its place
as surface syntax rather than as expressiveness.

### One that ran the other way

This one turned up while closing §6's `T` row, and it is worth separating because the arrow
points the opposite direction: the **model** was wrong and the specification was right.
`HOpaque`'s `set` clause had been transcribed without `vs ≠ []`, so `Uν` admitted the empty set.
All three of the specification's readings exclude it — §1's `SS`/`NS`/`BS` are `℘⁺fin`; §3's
fixpoint `union(…, set(opaque), …)` inherits `(set)`'s non-emptiness; and §3's prose ("the values
whose member is recoverable from the value alone") excludes it for the sharpest reason of all, since
an empty set has no payloads and so `SS`, `NS` and `BS` are indistinguishable. `Typing.lean` now
carries the premise, and `set_nil_outside_opaque` is the witness: no fuel ever held `set []` and
none ever wrote it.

The direction matters for how much it cost. `typed_TSub` proves *denotation ⊆ judgement*, so the
surplus sat on the judgement's side, no law depended on it, and `soundness` was never affected —
only the advertised precision of the `: T` index. Which is exactly the claim §6 could not check
while fuel was in the way.

### One where the hedge was about the wrong thing

`union` associativity is the only conditional row in §6's "Hold" table: it is stated to hold
"where both sides satisfy (D) and (K) — and only on inputs satisfying (U)". Mechanizing it shows
the row needs **none** of those conditions. `equiv_altCodec_assoc` proves it outright.

This is not a defect in either document, but it is worth recording, because the reason is a
property of `≡` that is easy to lose sight of. `≡` requires `e` and `p` to agree only *where both
are defined*. At exactly the input §6 warns about, the nested option is ambiguous: the left side's
inner union fails and its outer union resolves anyway, while the right side sees three admitting
options and refuses. One side defined, the other not — so `≡` asks nothing.

The behaviour §6 describes is real; `≡` simply cannot see it.
`not_eq_altCodec_assoc` exhibits it — at `"A"`, with `string` outside and two copies of
`literal("A")` nested inside, the left encodes and the right refuses. So the conditions are
needed for **interchangeability**, and not for `≡`. Any port that rewrites across the two forms
is relying on the former, which the calculus does not give it.

### One neither document could have found, because it is about the store

§2 composes a codec's `e` and `p` directly. In use there is a **store** between them, and it is not
the identity on attributes. DynamoDB normalises every `N` it accepts — measured against a real
table in `src/codec.dynamodb.spec.ts`, not assumed:

| written | returned | | written | returned |
| --- | --- | --- | --- | --- |
| `1.500` | `1.5` | | `-0` | `0` |
| `007` | `7` | | `0.0` | `0` |
| `+1` | `1` | | `1.0` | `1` |
| `1e5` | `100000` | | `.5` | `0.5` |
| `1E+2` | `100` | | `1.` | `1` |

It **trims but does not round**: 39 significant digits, magnitude past `9.9…e125` or below
`1e-130`, `NaN` and `Infinity` are all hard `ValidationException`s. Nothing is silently truncated.
What is silent is the normalisation, and that is the half that costs correctness.

Write `η` for the store's normalisation. A codec survives the round trip through the store exactly
when **`η` lies inside `ker p`** — `≈c` of §2, the relation the calculus already has for "a
different attribute that reads to the same value". So:

- `number` satisfies it for free. `p "1.500"` and `p "1.5"` are the same double, and `η` is
  invisible to it.
- `decimal` cannot. Its `p` is the identity on the digits, so `ker p` is equality, and `η` would
  have to be the identity too.

`decimal` is the codec for money, and money is conventionally written `'10.50'`. That string was
being written, stored as `10.5`, and read back as `10.5` — a round trip failing **across storage**,
where neither the type system nor an in-memory law suite can see it. The implementation knew: its
docstring said "`decode ∘ encode` is identity only in normal form", and a test in
`codec.listing.spec.ts` pinned the failure as expected behaviour, with the comment "the codec cannot
prevent this; it is the service normalising `N`".

It can. It prevents it by never handing the service something to normalise. §1's `Numerals` stays
what the service accepts; `Numeral.Stored` is what it returns unchanged, and `(decimal)` now
concludes `⊢ decimal : Stored ⇝ N`. `decimal` rejects a denormalised numeral on write rather than
rewriting it, because rewriting is how you lose track of which value was meant — and it rejects on
read too, since gating only the write is the one configuration that breaks **(C)**.

Three things worth keeping from this one:

1. **A pinned defect is still a defect.** The expectation had been written down, tested, and
   documented, which made it look settled. What made it moveable was asking which law it broke.
2. **The calculus was not wrong, it was silent.** `lawful_decimalCodec` is true, and so is the
   docstring saying the round trip fails. They are about different compositions, and nothing in
   either document named the thing between them.
3. **`ker p` was already the right vocabulary.** §2 had `≈c` for exactly this shape of question —
   an attribute that differs but reads the same — and it turned out to state the store's condition
   without needing anything new.

`number` is closed in the implementation, which refuses `NaN`, `Infinity` and anything outside
`D`, on both halves. **It is now closed in the model too**, and the route there is worth recording
in full, because two estimates of it were made and both were wrong in different directions.

The gate is what the first attempt said it was, and it needed no new axiom: `e` on
`Numeral.WF (toDec d)`, and `p` on the **round-tripped** value rather than the stored digits, since
`ofDec` of a numeral at the top of the range can round *up* past it and would otherwise read back a
double `e` refuses. `Typed.number` concludes the same set, so the judgement now says `D` where the
rule always did.

**What the second estimate got right.** The bound does not stay in `(number)`. It is forced outward
twice, and both steps are *correct* rather than incidental:

1. **§3's `Uν`.** `opaque`'s number option *is* `numberCodec`, so `HOpaque.num` carries the same
   premise — a double `opaque` cannot write is not one of "the values whose type is recoverable from
   the value alone", because there is no `N` for it to be recoverable from. The same species as
   `HOpaque.set`'s `vs ≠ []` above, and it is now in the rule.
2. **`(literal-N)`.** `literalNCodec`'s laws were proved as a prism over `number`, so a literal
   outside `D` is writable where `number` is not. §3's rule wants `ℓ ⊆ D`: `literal(1e999)` should
   not be derivable, and still is.

**What it got wrong, and this is the correction.** It read `Uν` as the expensive half — "reaches
`Opaque.lean`'s depth machinery and `opaq_T_identity` with it". It reaches them and they do not
move: four local proof repairs in `Opaque.lean` (two unfoldings that stopped being `simp`, two
depth cases that needed the gate split), one line in `HeldSet.lean`, one in `Soundness.lean`.
`opaq_T_identity` is unchanged and still green under `#assert_axioms`. Adding a premise to an
inductive that every proof already destructs is cheap; the estimate priced it as a rework.

The cost it did not see at all was in the half it called simple. **`literalNCodec` had to be
reproved from scratch**, both `Lawful` and `Carrier`, because the prism over `number` is not
weakened by the gate — it is gone. `restrict numberCodec (inLN ls)` and `literalNCodec ls` are
different codecs the moment `number` gates and `literal-N` does not, so `Lawful.congr` has nothing
to transport. The laws never needed the prism (**(R)** here is `Double.roundtrip` and a membership
test, which is what the prism was carrying second-hand), but nothing said so until the route was
removed. **A proof route is not a proof, and the two are easiest to confuse where the route has
always worked.**

`ℓ ⊆ D` was left open, because adding a premise to a rule changes the specification. The model
carried the cost instead — `literalN_sub_number`, `not_literalN_sub_number`,
`literalN_writes_off_numerals` — all **conditional on a double outside `D` existing**, deliberately,
since `Double` is axiomatized with the shortest-text round trip and nothing else and asserting an
IEEE-754 fact would widen the trusted base to settle a question the specification can answer for
itself.

**The implementation answered it.** Asked whether normalizing `literal-N` would simplify anything,
the first thing measured was what the shipped constructor does with the ends of the range:

```
literal(NaN).encode(NaN)     → { N: 'NaN' }
literal(1e400).encode(1e400) → { N: 'Infinity' }
```

Both reachable with no cast, `tsc` clean, and both rejected by DynamoDB on arrival. So the
conditional was not hypothetical, and the term that had no premise was writing attributes outside
§1's `𝔸` in the field. `number` had refused all of this since the numeral domain was tightened;
`literal` is the other term that writes an `N` from a double and it had been left behind — the
`(number)` pass predicted exactly this and could not close it alone.

**`ℓ ⊆ D` is now §3's premise**, at the user's call, and the set is the one `(number)` already gates
on: what DynamoDB *accepts*. `Typed.literalN` carries `hD` beside `hne` and `hnd`, which is where it
belongs — a decidable fact about data the term owns, checked once at the declaration. The
implementation refuses at the constructor for the same reason and in the same place as the
mixed-kind refusal. `not_typed_literalN_nonD` is the premise biting — `literal(d)` on a
double outside `D` has no derivation at all — and `typed_literalN_sub_number` is what it buys back:
**every derivable numeric literal refines `number` again**, which is the containment the gate had
broken.

Two things are worth keeping from how the decision was reached. The rule figure had said
`ℓ₁ … ℓₙ ∈ D` **all along** — the amendment was not to the rule but to the paragraph under it, which
called `D` "an unchecked precondition" and gave `5e-324` as the example of it going unchecked. A
premise stated in a rule and disowned in the prose beneath it is worth less than no premise at all,
because it reads as checked to everyone who stops at the figure.

### One the premise was claimed to cover, and did not

Writing the entry above, I argued that `(literal-N)` needed no read gate: membership in `ℓ` is
checked in both directions, `ℓ ⊆ D`, so the premise discharges the half it does not mention. The
user did not accept it — *it has to pass through the same checks as `decimal` and `number`* — and
the measurement took one minute:

```
literal(0, 1, 2).decode({ N: '' })    → 0        number.decode({ N: '' })     → refused
literal(0, 16).decode({ N: '0x10' })  → 16       number.decode({ N: '0x10' }) → refused
```

`Number` reads `''`, whitespace, `0x10`, `0b11`, `0o7`. Membership in `ℓ` does not filter those —
it only rejects the ones whose numeric value happens to miss the set — so an attribute DynamoDB
could never have written decoded to a value the type calls legitimate.

**No law in §2 catches it.** (C) holds: `0` re-encodes to `⟨N, "0"⟩` without complaint. So does (R).
What it breaks is **§1**: `Carries(N)` is `Numerals` and `""` is not one, so `p` was defined on
something that is not an attribute. That is C1's obligation, seen from the inside — the embedding
into `𝔸` is *partial*, the implementation's attribute type is wider than `𝔸`, and every term that
reads an `N` is the one that has to notice. `decimal` and `number` both did. `literal` is the third
and it did not, which is why "the same checks" was the right instinct and the derivation was not.

The general form is already written down one section later, in the worked case for `refine`: **an
unchecked direction is sound exactly as far as something outside the codec enforces it.** For
`(literal-N)`'s write side that something is real — `ℓ` is frozen at construction, so the premise
genuinely discharges it. For the read side there is nothing, because stored data is outside every
invariant this library owns. I had the principle and applied it to the wrong half.

One part of the derivation survives, and it is worth separating out because it is the same shape and
it is *sound*: `number` needs a second read gate on the round-tripped value, since
`Number('9.9…E+125')` rounds up to `1e126`. `(literal-N)` does not — the rounded value is outside
`D`, and `ℓ ⊆ D`, so membership refuses it. That argument is about a value landing in a set fixed at
construction, not about an attribute, which is exactly the distinction the failed one blurred. It is
pinned by a test rather than believed.

One thing fell out that neither estimate anticipated. §1 says `number` satisfies `η ⊆ ker p` "for
free" because `p "1.500"` and `p "1.5"` are the same double, and with `Codec.Ker` in the model that
sentence is now `survivesStore_numberCodec`: `number`'s `p` factors through `Double.ofDec`, so any
normalisation preserving the double a numeral reads to lies inside its kernel. Set against
`ker_decimalCodec` — whose kernel is *equality*, so the same inclusion forces `η` to be the identity
— the two theorems are §1's entire argument for narrowing one held set and leaving the other alone.

### One the model found in the implementation

The empty set, and it is the plainest kind of defect the exercise can find: a law the model proves,
failing in the code.

`HSet` carries `vs ≠ []` — §1's `SS`/`NS`/`BS` are `℘⁺fin`, and `set_nil_outside_opaque` says no fuel
ever held `set []` — so `carrier_setCodec` and `(C)` hold: whatever `p` returns, `e` can write.
`set`'s implementation refused the empty set on **encode**, with a good message, and returned it on
**decode**: `every([])` is `[]`, and `new Set([])` is a value the same codec will not write.
`opaque`'s `SS`/`NS`/`BS` case did the same.

So an item carrying an empty `SS` could be read and not written back — the failure lands in a
read-modify-write, some distance from the decode that caused it. DynamoDB never stores an empty set,
so the item did not come from DynamoDB; it came from a migration, another writer, or a fixture, which
is exactly the traffic a decoder exists to be suspicious of.

Both directions now refuse it. The general form is worth naming, since it is cheap to check across a
port: **a codec whose `e` and `p` disagree about what it holds has no `T`.** `(C)` is the law that
says so, and it is the one an encoder-side-only validation always breaks.

### One the specification says twice, two different ways

§5's auxiliary tables give the calculus one `adm` — the set an `ident` term checks against —
and list `refine`, `optional`, `fallback` and `legacy` as passing it through. The value side
can. **The attribute side cannot, and `legacy` is the term that makes it impossible.**
`extendRead` widens `p` by the migration `r`, which is exactly the direction `adm` bounds:
a migration exists to accept attributes the current codec would refuse.

The model has always had two auxiliaries, `adm` and `admA`, and `admA` has no `legacy` case —
so the model was already right and the document was already wrong, with nothing recording it.
`not_admA_legacy` is now the witness: `legacy(literal("A"), r)` with `r` reading an `N` reads
`⟨N, "1"⟩` to `"A"`, and `admA(literal("A"))` refuses `⟨N, "1"⟩`. A passthrough `admA` would
make `admA_sound` false.

The two also part at `literalN`, for a different reason: the read side goes through the
axiomatized `Double.ofDec`, so no syntactic set bounds it and `admA(literal‑N)` is `⊤`.

**The amendment is made.** §5 now carries the two functions as a table, term by term, with both
partings argued rather than asserted — `legacy` because a passthrough `admA` is *unsound* and not
merely coarse, `literal-N` because distinct numerals read to the same double so no set of values
bounds a set of attributes. The readable-side discharger row and the closing sentence of the `(D)`
discussion say `admA` where they used to say `adm`; a condition on values cannot decide a question
about attributes, which is the confusion that paragraph refuses twice already.

**A third correction came with it, and it was not in the finding.** The old passthrough list was
`refine`, `optional`, `fallback` and `legacy`. Two of those four are not terms at all: `optional`
and `fallback` are **fields** (§4), and `adm` is a function on terms, so nothing can pass through
them. That is the same level confusion the C3 mapping found in `CodecDef['kind']` — a flat list
read as one stratum when the specification is normative that there are three — arriving this time
inside the specification's own auxiliary table. It went unnoticed by two audits and by the finding
that opened this entry, and what exposed it was writing the table out against `Term`'s
constructors, where a case for a field cannot be written down.

The `⊤` default earned a remark too, since §5 states **(K)** with two `ident` conjuncts the model's
`SepV` drops. Disjointness of two `⊤` sets is unsatisfiable, so it already implies each side carries
a real set — `ident_of_adm` and `admDisj_ident` — but only where each option admits *something*, and
`discriminatedUnion(d)` with no options is derivable and admits nothing (`sepV_string_dunion_nil`).
§5 keeps the conjuncts and now says why: a stated premise is easier to check than a recovered one.

### One found by asking whether the calculus can express the last one

The previous entry ends with a question worth asking of any defect a formalization missed: *can the
calculus say it at all?* For `⟨N, "">` the answer is that it says it in the **signature** — `p` is
typed `𝔸 ⇀ T`, and `⟨N, "">` is not in `𝔸` — so no law is violated because in the calculus there is
nothing to violate. C1 in §5 now carries the obligation that replaces the missing law, and with it
the audit list it implies: **four members carry a refinement**, `N`, `SS`, `NS` and `BS`, and the
question for a port is which of its terms read one.

Running that list on this library found one more, and this one **is** expressible — by the strongest
law in §2:

```
opaque('refuse').decode({ N: '1' })          → refused
opaque('refuse').decode({ NS: ['1','2'] })   → Set(['1','2'])  of string
                        re-encoded           → { SS: ['1','2'] }
opaque('lossy').decode({ NS: ['1','2'] })    → the same
```

**`NS` in, `SS` out.** That is **(MP)** — `member(e(p(a))) ≠ member(a)` — and it is the exact failure
`opaque`'s `N` refusal exists to prevent, one member over. §2 makes the argument in as many words:
"a codec reading `⟨N, "1.5"⟩` to a string and writing `⟨S, "1.5"⟩` satisfies both — the *value*
survives — while silently changing the stored type, so a numeric sort key stops ordering and a typed
index rejects the write. This is why `opaque` refuses `N` by default." The `NS` path does not apply
that rule, and it does not consult the number policy either: `'lossy'` reads `⟨N, "1"⟩` as `1` and
still reads `⟨NS, …⟩` as strings.

**The model has never had this.** `setCodec`'s `p` on `.ns` reads each entry through the element's
`p`, which for `opaque` is `opaqCodec` itself — `Codec.empty` under `lossy = false`, so the set read
fails and `NS` is refused exactly as `N` is; under `lossy = true` the entries are numbers and
re-encode to `NS`. Both policies are right in the model and wrong in the implementation, which makes
this the fourth defect the mechanization has found in shipped code and the first found by reading
the *conformance obligation* rather than a rule.

The write side makes it sharper than a missing check. **`opaque` has no `NS` write path at all** — a
numeric `Set` is refused outright, on the same "NS decodes as strings" grounds — so there is no
value in its language that writes back to `NS`. The read is not merely careless about the member; it
reads an attribute nothing it can produce will restore. Only two resolutions are consistent with §2:
refuse to read `NS`, as it already refuses to read `N` under `'refuse'`, or read it as numbers and
write `NS` back.

The behaviour was deliberate and argued in the source — `opaque.Decode` documented `NS` reading
back as `Set<string>` because "nothing without a schema can say which of them a JS number holds
faithfully", with `native.Decode`'s `Set<number | bigint>` named as the guess it refuses to make.
That reasoning is sound about the **value** and silent about the **member**, which is the shape of
the whole finding.

**Resolved, and the resolution is a one-line principle: a codec is a pair, so a member it cannot
write is a member it cannot read.** `opaque` now refuses `NS` on both sides, and its `Decode` type
says so.

The principle is not a policy. It is a corollary of §2, and it is now proved
(`Calculus.Lawful.no_read_without_write`): **(MP)** holds the two halves of a pair together, so if
`e` never produces member `m`, no attribute carrying `m` can be in `dom(p)` — reading one would
guarantee the member change (MP) exists to refuse. Note which law does the work. (C) is *satisfied*
in the failing case: the value round-trips and only the stored type changes. (W) says nothing,
because `opaque`'s `μ` is `⊤`. **(MP) is the only law that sees it**, which is the sharpest
illustration available of §2's remark that (MP) binds hardest exactly where `μ = ⊤`.

**And the read side of `N` was loose in the same term, which the same pass caught.**
`opaque('lossy')` decoded `⟨N, "abc"⟩` to `NaN` and `⟨N, "1e400"⟩` to `Infinity` — values its own
`encode` refuses, which is **(C)** failing outright. `Number` reads far more than an `N` carries:
`""` and whitespace are `0`, `"0x10"` is `16`. It now reads through the same two gates `number`
does, the second on the round-tripped value.

That one is worth a paragraph of its own, because **the harness that catches it already existed and
had never been pointed at this codec.** `checkDecodesAreWritable` generates *attributes* rather than
values for exactly this reason, and it fails on the pre-fix codec within eighty cases, on the
mutation "an N with a leading zero" — `⟨N, "0-1"⟩` decodes to `NaN`. It had been run on `Pet`, on
`Listing`, on planted counterexamples, and never on `opaque`, the term with the widest read in the
library. `codec.unknown.spec.ts` now runs it under both number policies. Two defects this session
were of that shape — a harness that exists, is proven to catch the failure, and was pointed
somewhere else — which makes *coverage of the harnesses themselves* a better next move than another
harness.

**The write half of the same audit was a correction, and is fixed.** `opaque('lossy')` wrote
`⟨N, "5e-324"⟩`, `⟨N, "1e+200"⟩` and `⟨N, "1e-200"⟩`: it gated on `Number.isFinite`, which is not
`Carries('N')`. `5e-324` is `codec-calculus.md` §3's own example of the bound going unchecked, and
it was still being written by the third term that writes an `N` after `number` and `literal` had
both been closed. It now reads through the same numeral gate as they do, everywhere a number can
nest. Nothing was deliberate about that one; it was simply the last place nobody had looked.

### One where §3 and §5 disagreed, and the term did not survive it

§3 said of `numeric(T)` that `p` "returns the double it read and **does not verify membership
in `T`**", that `refine(number, T)` is "the same held set *with* the check", and that "a claim
and a check are different terms". §5's soundness proof said the opposite in the same breath:
"the normative reading is `number`'s restricted to attributes landing in `T`, and every law
restricts with it; the implementation elides the restriction."

Only one of those readings is available. Under §3's, `p` returns values outside `T`, which is
`Carrier.ranP` failing and with it `typed_p_mem` and any claim the `: T` index makes. So the
model took §5's reading, and `numericCodec` gated on both halves.

Then the third side turned up, in the implementation. `numeric<T>()` in `src/codec.ts` decoded
with `Number(ok) as T` — **no check at all**, a type assertion over `number`. So the TypeScript
and the mechanized codec were never the same construction, and C3 conformance would have failed
on it. Three artifacts, three readings, of a term whose whole purpose was to be a fourth thing.

**`(numeric)` is removed** — from the rule figure, from `Term`, and from the implementation.
The certificate came first: `numericCodec_eq_restrict` (commit `eb3fac9`) proved `numeric(q)`
and `refine(number, q)` equal on all four fields, so nothing expressible was lost, and
`denote_numeric_eq` said it at term level. What replaces it is what always did the work: a
narrowing that checks is `refine`, and a narrowing that is the caller's business is `held`.

The general lesson is worth more than the term. **An unchecked read cast cannot be a term of a
calculus whose judgement carries a held set.** `: T` is either a claim the laws enforce or it is
decoration, and `(numeric)` was a rule for saying `T` while asking not to be held to it. §3 was
candid that this was a precondition rather than a check; what it did not notice is that the
calculus has no room for the distinction.

### One that only (U) could see, and only from the write side

**A union this library builds, decodes from, and cannot encode into.** `union([held(decimal,
dateAdapter), string])` — a timestamp or a raw string — is accepted at the declaration, reads
back correctly from both `N` and `S`, and throws on **every** `Date` handed to `encode`:

```
union.encode(new Date(0))
  → CodecError: held and string both admit this value; these options cannot be told apart
```

Found by `checkUniqueAdmission` on its first pass over the shapes the library supports, and then
measured directly rather than argued: `union.decode({N:'0'})` is a `Date`, `union.decode({S:'hi'})`
is `'hi'`, and no value of the first option can be written.

The cause is one asymmetry in `κ`. `writes(held(decimal, …))` is `'N'` — a `held`'s stored member
is its **inner** codec's, so the read side has a `κ` and the two options separate. `carries(held(
decimal, …))` is `undefined`, because the adapter's carrier is a caller's type and §1's `Value` has
no point for a `Date`; `shapeOf(new Date())` is `undefined` for the same reason, so the filter
cannot even be applied to the value. With no `κ` on the write side, admission falls back to the
attempt — and `string.encode(new Date())` **succeeds**, because encoding does not validate. Two
options admit, and the union correctly reports ambiguity rather than choosing.

**Neither of this library's two guards is wrong, and that is the finding.** The declaration-time
scan refuses `array(string)` beside `array(number)` because they share a `carries`; it skips an
option whose `carries` is unknown, and it must, or it would refuse `union([held(…), object({…})])`,
which works, because names decide there. The run-time filter exempts exactly the same options for
exactly the same reason. So the two guards are complementary everywhere except on the options where
both are vacuous, and there nothing is left to notice.

Why no other harness could reach it: the failing input is a value of the *first* option, and every
value-driven property test round-trips values the union already accepted. `checkRoundTrip` never
sees it because the union refuses to encode; `checkDecodesAreWritable` never sees it because it
starts from an item `encode` produced. (U) is the only law stated over an input a *single option*
can write, which is why it is the one that reaches here.

**Recorded, not repaired.** The fix is a choice between two normative positions — refuse the
declaration where two options are both `κ`-free, or give `held` a write-side `κ` by embedding its
carrier — and §1's `Value` is what would have to change for the second. `codec.uniqueadmission.spec.ts`
carries the measurement as four assertions.

### The unified rule, mechanized — and why arity one was what made it affordable

§3's `(literal)` was unified as a rule first and mechanized second, on the reading that one
constructor would need `ℓ : List Value` plus a homogeneity premise the two typed constructors get
for free. That reading was right about `List Value` and wrong about the conclusion, because it did
not consider arity one.

**The measurement that changed it.** There are *zero* multi-element literals in the source. All 41
concrete uses are singletons; the other 80 sites are the list machinery — `literalSCodec ls`,
`Typed.literalS ls`, membership lemmas — carried by 80 sites and exercised by no witness. At arity
one the homogeneity premise never arises (one value has nothing to be homogeneous with), `hne` and
`hnd` are vacuous, and the list machinery simplifies rather than moves.

  Term.literal (v : Value)
  literalCodec  — dispatch on the value's kind to its ground base, `restrict`ed at equality
  literalOK     — §3's `ℓ ⊆ T`: `WF` at `number`, trivial elsewhere, false for a container
  Typed.literal — one premise where the two old rules carried three

**And the constructor still earns its place**, which is the part I had backwards. At arity one
`literal(v)` and `refine(g, · = v)` denote the same pair, so the obvious move is to delete it. But
`adm` is the same either way and **`admA` is not**: `ℓ` is data the term owns, so it can be tested
against the *stored attribute*, where `refine`'s `q` is a value predicate and cannot be pushed
there. `admA_literal_str` and `admA_literal_bool` against the `refine` row are that difference —
the same `literal-S`/`literal-N` asymmetry, now deciding a design question rather than explaining
one. `admA_literal_num_blind` is the one base where it still cannot, §1's `N` carrying text where
the value is a double.

**What is not done.** `literalS`/`literalN` remain, with all their witnesses; the new constructor
was added alongside so the build stayed green at every step. Retiring them is mechanical — 41
concrete sites — and the n-ary form becomes surface syntax for the union, which the `⋃` rows on
`adm`/`admA` made lossless.

`κ_sound`'s literal case is the one place the shape bit: it is the only single-kind rule whose kind
comes from *data*, so the `single_kind` macro cannot serve and the codec has to be reduced at the
literal's value before the tested value is split.

### One rule where §3 had been writing two

`(literal-S)` and `(literal-N)` differed in exactly one thing: which set `ℓ` had to lie in, and
therefore which member the term stored. Everything else — `n ≥ 1`, pairwise distinctness, the held
set, the shape of the pair — was written twice. §3 said so itself, that `literal` "is the one ground
term with two rules, because it is the only one whose member follows from its values rather than
from its name," and then did not take the next step.

The unified rule reads both off a base:

    ⊢ g : T ⇝ μ,  g ground    ℓ₁ … ℓₙ ∈ T,  n ≥ 1,  pairwise distinct
    ───────────────────────────────────────────────────────────────── (literal)
    ⊢ literal(ℓ₁ … ℓₙ) : {ℓ₁ … ℓₙ} ⇝ μ

which covers `S` and `N` as before and covers `BOOL`, `B` and `NULL` with nothing added. `ℓ ⊆ D` is
no longer a premise anyone states: a numeric literal's base *is* `number`, and `ℓ ⊆ T` is the rule.
The base is fixed by `ℓ`'s kind, `string` being the base for strings — `decimal` is what to write
when strings are wanted stored as `N`, and it is not reachable as a literal base, which matches what
`(literal-S)` always did.

**The model keeps two constructors, and the metalanguage is the reason.** One constructor needs
`ℓ : List Value` plus a premise that the values share a kind; `literalS (ls : List String)` and
`literalN (ls : List Double)` get that premise from the *type*, so homogeneity is Lean's to check
rather than something carried through every rule, every `cases`, and every witness — 270 sites.
That is a mechanization choice of the same kind `Typing.lean` already documents for the list
judgements, and it is recorded there.

Nothing §3 admits is unreachable in the model, only differently spelled: a boolean literal is
`refine(boolean, ∈ ℓ)`, and `uAtCan_of_refine_disjoint_of_typed` shows such unions discharge
identically. The factorizations proved a commit earlier —
`literalSCodec = restrict stringCodec (inLS ls)`, `literalNCodec = restrict rawNumberCodec (inLN
ls)` — are what make the two constructors visibly the one rule at two bases.

### One where a term was nearly removed for a reason that was not true

The user proposed deleting `(refine)`, on the grounds that it cannot state stability across a
round trip through an altered attribute. Two checks, both against the model:

- `Lawful.restrict` proves all four laws of `refine` from its base's.
- `refine`'s `p` factors through `c.p`, so `SurvivesStore c η → SurvivesStore (c.restrict q) η`
  — every alteration the base tolerates, the refinement tolerates identically. It cannot fail
  there without the base failing first.

So the stated reason does not hold. But the instinct behind it did, and it was one table row away:
**§5 sent `refine` straight through on both admissible sets**, so `q` narrowed the held set and was
invisible to every discharger. `union(refine(number, positive), refine(number, negative))` has `κ`
`{number}` on both sides and `adm` `⊤` on both — nothing separates it, and it falls to (U) per
input despite the two predicates being disjoint by construction.

`adm (refine(c, q)) = adm c ∩ q` fixes it, and is sound for the reason the passthrough was too
weak: `refine`'s `e` is defined only where `q` holds. `admA` cannot follow — `q` tests the value a
read *produces*, and no syntactic set of attributes bounds that — which makes this the mirror of
the `held` row, one-sided the other way. `sepV_refine_disjoint` is the witness.

**And the readable side, which the table cannot reach.** `admA` cannot carry `q` — it tests the
value a read *produces*, and no syntactic set of attributes bounds that — so from the tables alone
the readable side looks undischargeable. It is not. Two refinements of **one base** read an
attribute to the same value, so at most one predicate accepts it, and the readable side separates
for exactly the reason the writable one does. `uAtCan_of_refine_disjoint` is that discharger, and
it settles both sides outright.

What made it reachable is that `uniqueAdmission_of_disjoint` takes the two families as *arbitrary
predicates*. Nothing in it has to be syntactic, so the attribute family can be
`∃ v, base.p a = some v ∧ q v` — a semantic set — and disjointness is just the base reading `a` to
one value. The condition is relational, about options sharing a base rather than about any one
option's admissible set, which is why it is a discharger and not a table row.

**One consequence, and it is a correction to §5's `ident` table rather than a side effect.**
`ident_of_adm` says a term whose `adm` ever refuses is `ident`. With `q` in `adm`, a refinement over
a non-`ident` base refuses — so `refine` must *hold* `ident` rather than propagate it. That is also
the truth of the matter: `refine` checks `q` on the way in and on the way out, which is what
deciding your own membership means, and §3 already argues exactly this when it says a `p` returning
the value it read without verifying `q` would break (C).

**A correction of my own, recorded because it shaped the recommendation.** I argued that removing
`refine` would leave narrowing with nowhere to go but `custom`. That is false, and the user said so:
`e` and `p` are *partial*, so refusal is the error channel, and any constructor can use it — which
is what C4 already tells a port to do, "in the shape of `refine`'s". `refine` is not the only way to
refuse; it is the calculus giving refusal a rule so the caller does not have to discharge the laws
by hand.

### One the specification could state and never did

Asked what an *ideal* codec is — the guess being a bijection, with prisms as the exception — §2
turned out to have every piece of the answer and never to have assembled it.

`Can(c)`, `Ker`, `Lawful.e_injective` and `retract` were all present. What was missing is five
lines: `Lawful.can_roundTrip`, the statement that `e ∘ p = id` **on `Can(c)`**. With `retract` it
says `e` and `p` are mutually inverse between `dom(e)` and `Can(c)` — a bijection on the nose, no
quotient, no partiality.

Which relocates the whole of §2. The four laws are not four constraints on a pair; they are a
bijection plus **two extensions of it**, in the only two directions a bijection can be extended:
`dom(p)` grows past `Can(c)` (the quotient, governed by (C) and `≈c`), and `dom(e)`/`dom(p)` fall
short of `T`/`𝔸` (the partiality). `e ∘ p ≠ id` — the sentence §2 leads with — is the first
extension seen from outside, not a weakening of the iso, because on `Can(c)` the equation holds.

The guess was half right and the half it missed is the interesting one. Partiality is the prism,
and §2 always named it. The quotient is the other extension, it is the one `Quotient Lenses` is
cited for, and it is the reason neither reference alone is the right one for this calculus.

Worth recording as method, not just as content: the gap was invisible from inside the formalization
because nothing *needed* the theorem — every proof that could have used it used `retract` directly.
It took a question about what the object ideally is.

### One where the abstraction was still one level too high

The entry below unified §5's two *outright* dischargers as one theorem at two projections. The user
read the leftover friction as evidence the abstraction was wrong rather than incomplete, and it was:
three things kept not fitting, and all three had the same cause.

**The projection did not belong in the lemma.** `filter_eq_singleton_of_labels` took a projection
`key : α → Option ι` and label sets `Ss : List (ι → Prop)`. Strip both and what remains is the
actual content — *disjoint subsets of the carrier*:

    filter_eq_singleton_of_disjoint
      Forall₂ (fun o S => ∀ y, adm o y = true → S y) os Ss →
      Pairwise (fun S T => ∀ y, S y → ¬ T y) Ss → …

The label form is now this plus a pullback, which is a *construction*, not a condition.

**One label type for two sides was the second mistake.** `OptionSem.Labelled` shares an `L` between
the value side and the attribute side. Tags share one (`String`), kinds share one (`Kind`) — but
`κ`/`μ` do not, and that mismatch is exactly why §5's first two rows resisted every attempt to join
them, and why the previous entry had to reach for a *product of projections* to make them fit.
`uniqueAdmission_of_disjoint` takes the two families separately, and the mismatch disappears.

**The pairwise disjunction was the third.** `SepV` offers a disjoint kind *or* a disjoint admissible
set, per pair. Asked per option, the two constraints just intersect: `SVof t v` is "`κ` allows the
kind and `adm` allows the value". Disjointness of intersections follows from disjointness in either
factor, so `SepV`/`SepA` are precisely what makes the families pairwise disjoint.

**What it bought.** `uAtCan_of_separated` was sixty lines containing the same fourteen-line exclusion
argument twice — once through `admitV_kind`/`admitV_adm`, once through
`admitA_member`/`admitA_admA`. It is now a single appeal to `uniqueAdmission_of_disjoint` with five
short goals, and neither side has an argument of its own. Unfolding tics 259 → 255.

The methodological point is worth keeping. The refactor before this one worked and left friction;
the friction was not the cost of abstracting, it was the abstraction naming the wrong things. A
projection and a shared label type are *presentations* of separation. Disjoint sets are separation.

### One where four dischargers were one theorem

§5's discharger table lists four conditions, and the two marked *outright* — tag disjointness for
`(dunion)`, kind disjointness for `opaque` — had a hand-written proof each:
`uniqueAdmission_byTag` with its own filter lemma (`tag_filter_singleton`, 16 lines), and
`uniqueAdmission_of_kinds` through `filter_eq_singleton_of_keys`. Same shape, twice.

**The observation was the user's**, and it starts from something the model states outright:

    dunionCodec d os = altCodec (os.map fun o => .byTag d o.1 o.2) (some .M)

`(dunion)` *is* `(union)`. The only difference is which `OptionSem` builder wraps each option —
`byAttempt` attempts the codec, `byTag d` reads the discriminator. So the uniqueness criterion is a
**projection of the input**, and the two outright dischargers are that same criterion at two
different projections: a tag for `(dunion)`, a kind for `opaque`.

**The generalisation.** Label each side of the pair by a partial projection, give each option the
set of labels it answers to, require those sets pairwise disjoint:

    OptionSem.Labelled πV πA o S   -- admission is bounded by the option's label set
    uniqueAdmission_of_labels      -- disjoint sets ⟹ (U), on both sides

`uniqueAdmission_of_kinds` is that at `Value.kind`/`Attr.kind` with singleton sets, where `Nodup` is
disjointness of singletons; `uniqueAdmission_byTag` is that at `tagOfV`/`tagOfA` with the tag sets.
The same generalisation one level down turns `filter_eq_singleton_of_keys` — 25 lines of hand
induction — into a six-line instance of `filter_eq_singleton_of_labels`, and makes
`tag_filter_singleton` redundant outright; it is deleted, its content being the tag instance.

Two lemmas moved on the way, which is §1 of `VOCABULARY` rather than this refactor's convenience:
`byTag_admitA`/`byTag_admitV` were in `Discharge.lean`, three modules downstream of the definition
they invert. They now sit beside `OptionSem.byTag`, and both the general lemma and
`uniqueAdmission_byTag` cite them instead of unfolding by hand.

**What it measures.** Theorem docstrings 61% → 62%, definitions 72% → 73%, and the unfolding-tic
count **unchanged at 261** — new abstraction paid for by deleted hand-proof, which is the outcome
this kind of change should have and usually does not.

**What it opens.** With the dischargers written as projections, the table stops being a list and
becomes a question: *which other projections separate?* §5's first two rows are the same condition
run on one side each — `μ`/`admA` on attributes, `κ`/`adm` on values — which is now visibly why
they must be combined while the last two need not be.

### One premise that turned out to be a missing guard

§3 gave `(nullable)` two side premises — null-honesty, in both directions — and §5's theorem
counted them among the four it levied. They are gone, and nothing replaced them.

**What they were doing.** `orNull` writes `null ↦ ⟨NULL, ∗⟩` and reads it back, with the `NULL`
branch taking precedence over `c`. That precedence is the whole problem: if `c` also touches the
null point, the wrapper's branch shadows it, and a subterm moving a sentinel onto `null` round-trips
to `null` instead of the sentinel. The premises forbade the collision by fiat.

**What they should have been.** §3 already recorded the dichotomy — `nullable(c)` is
`union(c, ⟨NULL⟩-point)` where `c` does not touch the point, and *equal to `c`* where it does
(`orNull_eq_altCodec`, `orNull_eq_self`). Both halves were theorems *about* a wrapper whose
definition ignored them. Making the dichotomy the definition removes the collision instead of
forbidding it:

    Codec.ownsNull c = (c.e null).isSome || (c.p null).isSome
    Codec.withNull  c = if c.ownsNull then c's pair else c.orNull

and then **null-honesty is a consequence** (`nullHonest_of_not_ownsNull`). Under the guard, a lawful
`c` cannot write `⟨NULL, ∗⟩` — (R) would make it read the point back, so `ownsNull` would hold — and
cannot read to `null` — (C) would make it write the point, likewise. Both hypotheses are refuted
rather than assumed, and `Obligations` at `.nullable` is now just the subterm's.

**The guard is joint, and that is not a detail.** Asked per side, `c` could decline to write `null`
while still reading `⟨NULL, ∗⟩`; the null point's two ends would belong to different options, and
(R) would break with each side, taken alone, looking unambiguous. `orNull_eq_altCodec` already had
the right hypothesis — `c.e .null = none` **and** `c.p .null = none` — which is what made the fix
findable.

**What it cost.** `T` and `μ` had to stay outside the guard: `(nullable)` concludes `T + 𝟙 ⇝ ⊤`
whichever branch runs, and a first attempt that guarded the whole codec broke `denote_μ` and
`typed_TSub` immediately. Only the pair moves. Five sites in `Soundness`, one in `Denoteω`, one in
`κ_sound`, two in `Equations`; nothing in `Opaque`, `Continuity` or `Discharge`'s dischargers.

**And §6's idempotence stopped being an equation.** `nullable(nullable(c)) ≡ nullable(c)` used to
need null-honesty to hold *of `nullable(c)` itself* before it was lawful. Now the wrapper's own
point makes `ownsNull` true, so the second insertion finds it present and returns the pair
untouched: `withNull_ownsNull` is a two-line proof and `withNull_idem_e`/`_p` follow from it. An
equation became a property of insertion.

**What it says about the term.** `nullable` is sugar — idempotent insertion of the null option into
a pair that may already have it. §3 used to justify keeping it primitive by "compatibility and the
`κ = ⊤` cases", where `union(c, null)` has no discharger. After (K) became a discharger rather than
a premise, no discharger means an obligation, not a refusal, so that half of the justification is
gone. Compatibility is what is left, and that is a packaging decision.

### One where the obligation was quantified over inputs the union refuses

§5 stated **(U)** as `∀ input. ∣{i : cᵢ admits it}∣ = 1`, and the model transcribed it faithfully:
`UniqueAdmission` asks, of *every* canonical pair of *every* option, that the option admitting it
admit it alone. The transcription was faithful and the rule was too strong, and the model is where
it shows — because `altCodec` is the one artifact that says what the union actually does.

**`altCodec` declines what it cannot resolve.** `e` is `match os.filter (·.admitV v) with | [o] =>
o.c.e v | _ => none`. Where two options both admit, the union is *undefined*, and every law is
quantified over `dom`. So an ambiguity at an input the union refuses is unreachable by (R), (C),
(W) or `≼` — and (U) was demanding it be absent anyway.

The three consumers say the same thing. `lawfulCore_altCodec` and `lawful_altCodec` use `hU`
exactly three times, and every use instantiates it at an option obtained from a *singleton filter*:
`retract` needs the attribute side unique at an `a` the union wrote, `canon` and `agree` need the
value side unique at a `t` the union read to. Nothing asks about an option's canonicals in general.

**What it cost.** `union(array(literal("A")), array(literal("B")))` — and its `record` twin, and
`union(array(string), tuple(string, rest(number)))`. Each collides at one input: the empty array,
the empty map, and (for the last) nowhere at all once both sides are compared, since the options
agree there. `adm` does not propagate through a container (§5), so the collision is the empty case
and nothing else. The union declines to write it, every other value round-trips through the one
option that wrote it — and the soundness theorem covered none of them, because `UniqueAdmission`
was refuted by a canonical pair the union never uses.

**The repair.** `UniqueBothWays`: resolving one side of the pair resolves the other, through the
same option. `UAtAct` is it at the union's own options, and it is what `(union)`'s `Obligations`
now carries. `UAtCan` stays, as the strong form the dischargers produce, and
`uAtAct_of_uAtCan` is the bridge — so every discharger in `Discharge.lean` discharges exactly as
before, `(dunion)` and `opaque` included, with no proof changed.

Nothing is admitted that was not derivable, and no law is weakened: the theorem now covers strictly
more terms because the obligation stopped asking about inputs the semantics refuses.

**The two are separated by a theorem, not by the argument above.** `uAtAct_array_literals` proves
`UAtAct` of the very union `not_uAtCan_array_literals` refutes `UAtCan` of. What carries it is that
a `literal`'s two halves test one set — `literalS_p_none` and its dual — so an element the
neighbouring option declines to *write* is one it declines to *read*, and the traversal inherits
that positionwise. Which is precisely what `held` breaks, so the argument is about literals and not
about containers in general: `not_uAtCan_literal_held` is unaffected, as it must be.

**How it was found.** By measuring before changing. The user's proposal was to weaken (U) to
*agreement* — where two options both admit, let them through if they answer the same. That is sound,
and it is a change to `altCodec`, which 11 files and 153 sites depend on. Counting those first is
what surfaced the cheaper and more accurate diagnosis: the semantics was already right, and it was
the obligation that over-quantified. Agreement would additionally let the union *write* the empty
case; that remains open, and is a change to the denotation rather than to a premise.

### One where `held` was opaque on the wrong number of sides

The entry above records `adm`/`admA` splitting because `legacy` widens `p`. The split had a second
consequence nobody drew, and it runs the other way: **`held`'s opacity is one-sided, and §5's table
priced it as total.**

`held(c, f, g)` denotes `Codec.through`, whose two halves are not symmetric. `f` sits in front of
`e`, so what the term will write is a question about a caller's function and `adm` is rightly `⊤`.
`g` sits *behind* `p` and is total — `through_p` says `(c.through f g).p a = some v ↔ ∃ w, c.p a =
some w ∧ v = g w` — so `dom(p)` is the subterm's exactly. The adapter changes which value comes out
and never which attributes go in. The model had proved this from the beginning (`Combinators.lean`
even says it in prose: "`held` and `legacy` are transparent on the side they do not touch"), and
`admA` still sent `held` to the `_ => true` catch-all, alongside `custom` and `lazy`, whose reads
really are unknowable.

So the table had `legacy` and `held` sharing a `⊤` for opposite reasons — one because it reads
*more* than its subterm, the other in spite of reading exactly what its subterm reads.

**What it costs.** A discharge, and it is not a corner case:
`union(literal("A"), held(literal("B"), f, g))` separates on the readable side for every `f` and
`g` — the footprints are `{S "A"}` and `{S "B"}` — and §5 could not say so, because it had thrown
the footprint away at the wrapper. The member disjunct does not help; both options are `⇝ S`.
`sepA_literal_heldLiteral` is the witness.

The row is precise rather than permissive, which is the part worth checking:
`not_sepA_literal_heldLiteral` shows that with the *same* inner literal both disjuncts still fail,
so `not_uAtCan_literal_held` — §5's standing `held` counterexample, and the reason (D) is
incomparability rather than disjointness — survives untouched. The wrapper never decides. The
subterm does, and reading through the wrapper is what lets the question be put to it.

**How it was found.** Not by a proof and not by a sweep. The user asked whether
`union(literal("A"), held(literal("B"), f, g))` decides, given that
`union(literal("A"), held(literal("A"), f, g))` does not — a question about two terms differing in
one leaf. Nothing in either document distinguished them, and the model's own `through_p` did. That
is the same shape as every other entry here: two artifacts that had to agree, and one of them
knowing something the other had stopped asking.

### One where the opacity was the residue of a refactor nobody finished

§5 lists `lazy` alongside `custom` and `opaque` as unanalysable, and `κ`, `ident`, `adm` and `admA`
all four sent it to the catch-all. **`lazy` is the most transparent wrapper in the language.**

`denote fuel (.lazy t) = { denote fuel t with μ := none }`. The pair *is* the subterm's — not
adapted like `held`'s, not widened like `legacy`'s, not extended like `nullable`'s. Only the member
is erased, which is what `(lazy)` concluding `⊤` means. Every one of the four tables was throwing
away a footprint that was sitting definitionally in front of it, and the four soundness cases after
the repair are each a one-line appeal to the subterm's own — `exact adm_sound fuel t' he` and its
three siblings — which is the evidence that nothing had to be argued at all.

**Why it was there.** The doc's `lazy` carried `Unit → Term`, a real thunk, and for *that*
constructor the opacity is correct: you cannot analyse a closure. `Denoteω.lean` records the change
— the closure "defeated the termination checker without adding a constructible term" — and
`Term.lean` argues it at length. The constructor was replaced; the analysis rows it justified were
not. So this is not a defect in the specification's reasoning but in its bookkeeping: a premise was
withdrawn and four conclusions drawn from it stayed.

**What it costs.** Every discharge through a `lazy`. `sep_lazy_literal` and `sepA_lazy_literal`
separate a `lazy` literal from a plain one on both sides; `kappa_lazy_lazy` reaches a doubly-nested
scalar; `ident_lazy` makes a `lazy` option `adm`-informative at all. While the row was `⊤`, wrapping
any option in `lazy` silently destroyed its separability — and because a `⊤` is sound, nothing ever
failed.

**How it was found.** The user asked why `lazy` was on the unanalysable list, and observed it should
be analysable "at least if all the internal content is exact". The instinct was right and the hedge
was unnecessary: the propagation is unconditional, because `e` and `p` are the subterm's
definitionally rather than up to any obligation on the subterm. This is the seventh instance of the
shape the other entries record, found the same way as the `held` one — a question about a term,
against a model that already knew the answer.

**What it says about the catch-all.** The six earlier instances were each argued as an oversight.
This one could not have been noticed by re-reading the tables, because the table's own stated reason
was coherent; it was wrong only against a constructor definition three files away. That is the case
for the rows being exhaustive and the reasons being written down next to them — which they now are,
and which is what made this entry findable at all.

### One where "unanalysable" turned out to be three different things

The entry above repaired `lazy`. The question that followed it — whether `held` is really
unanalysable, and whether its iso obligation would buy the analysis if it were — dissolved the
category. **Only `opaq` was ever unanalysable.**

`held` and `custom` were on the list because they carry Lean functions, and a function is not
something a reader can look inside. But `adm` is not a reader. It is a function with the term in
hand, and the term carries `f`, `ce` and `cp` *as data*. It can apply them.

- `held`: `(c.through f g).e v = c.e (f v)` by `Iff.rfl`. The writable set is the subterm's pulled
  back along `f`, exactly. No iso obligation is needed — that premise is about `T` and
  roundtripping, not about the domain, so the analysis was available for free and the obligation
  did not have to be spent.
- `custom`: `denote` sets `e := ce` and `p := cp`. Both rows are `isSome` of the function the term
  carries, and `custom`'s `T` is *defined* as `dom(ce)`. These are the only rows in either table
  that are exact against the denotation in both directions (`adm_custom_exact`).
- `opaq`: genuinely unanalysable, and for a reason none of the others shared. `opaqCodecω`'s domain
  is a recursion over the *input's* depth, so there is no set the syntax names.

Three senses had been running together under one word: (i) the term does not carry the information
— true of nothing; (ii) the domain cannot be computed without running the codec — true only of
`opaq`; (iii) a reader cannot see through it — true of `held` and `custom`, and not a property of
the calculus at all. §5's table was built on (iii), which is a fact about tables rather than terms.

**What it costs.** `held`'s writable side, entirely. `sepV_literal_heldLiteral` separates a `held`
literal from a plain one whenever `f` does not send the one value to the other, and
`not_sepV_literal_heldLiteral` is its exact converse — separation fails precisely when the adapter
relabels. That "precisely" is new: the old row could not distinguish an adapter that relabels from
one that does not, because it had discarded `f` unexamined.

**And it settles a design question.** These three rows are why bundling each row with a *soundness*
proof — the obvious construction, and the one first proposed — cannot work. `⊤` is sound for every
term, so `admV := fun _ => true` discharges a soundness obligation with `rfl`. Every one of the
seven gaps in this log was an imprecision, not an unsoundness; not one of them would have been
caught. What catches them is the converse direction, which is what `adm_custom_exact` states and
what the remaining rows should be measured against.

### Three where the recursion was on the wrong object, and what stating the converse found

The entries above are seven imprecisions found one at a time. This one is the measurement that
should have found them all, and the three further defects it turned up.

**The statement.** `κ`, `ident`, `adm`, `admA` are over-approximations, so `⊤` is sound for every
term and no soundness obligation can catch a loose row — `fun _ => true` discharges it with `rfl`.
The converse is what bites: `Adm t v = true ↔ v ∈ dom(e)`. `formal/Calculus/Exactness.lean` states
it and proves it for sixteen of the twenty-three constructors.

Stating it turned up three things the per-table form hid.

1. **Exactness belongs to the row, not to `adm`.** `adm .string` is `⊤`; it is `κ` that carries the
   kind. Neither is exact alone and their conjunction is. Four hand-maintained recursions were
   computing one predicate between them, and no single one of them could be held to anything.
2. **The conjunction does not survive `held`.** `f` may change a value's kind, so `κ (held t f g)`
   must be `none`, leaving no `κ` to pair the subterm's `adm` with. The kind gate has to be absorbed
   into the row: `Adm (.held t f _) v = Adm t (f v)`. So the (κ, adm) factorisation is not preserved
   by the term formers — which is the argument for treating the row as the unit that no amount of
   staring at the tables would have produced.
3. **The list rows recursed on the wrong thing.** `array`, `record` and `union` took `⋀`/`⋁` of
   `adm` alone, where exactness needs `⋀`/`⋁` of the joint predicate. One defect with three faces.

**The container defect, in detail**, because §5's justification for it is instructive. §5 argues
`adm(array(c))` must be `⊤` because it would have to contain the empty array whatever `c` is. That
argument is *true* and it justifies far less than it was asked to: the exact row still admits `[]`
(`Adm_array_nil`, and `not_uAtCan_array_literals` survives on exactly that basis), while refusing
`[.str "B"]` at `array(literal "A")` (`Adm_array_sharp`) at any nesting depth
(`Adm_array_nested`). A sound reason was carrying a much stronger conclusion than it supports —
the same shape as the `nullable` refusal two entries up, which was also true and also stipulated
where it could have been derived.

**The hatch, and why it is seven rather than one.** `Analysable` names the rows with no exactness
proof, and each has a reason rather than a shrug: `opaq` (domain recurses on the *input's* depth);
`union` (`select` admits only when **exactly one** option does, so `⋁` is exact precisely under
(U) — a semantic obligation, not a syntactic row); `dunion` (the tag is checked, the matched
option's admission is not); `set` (`asWireSet` demands payload homogeneity); `object` and `tuple`
(name admission, alignment); and `nullable`.

`nullable` is the subtle one and it has a witness. `ownsNull` is `(e null).isSome || (p null).isSome`
— a disjunction over **both** halves. So a `legacy` whose migration reads the null point makes the
guard fire, `withNull` adds nothing, and the wrapper's `e` still refuses `null` — while any row of
the shape `Adm t v ∨ v = null` claims it. `not_ExactV_nullable` is that term.

**What this settles about the construction.** The obvious repair — bundle each row with a soundness
proof so a row cannot exist without one — cannot work, and this is the file that proves why: every
defect in this log is an imprecision, and soundness is blind to all of them. Bundling with the
*converse* is a different matter, and points 1 and 2 above are the argument for it: the obligation
is joint across the four tables, and `held` shows it cannot be factored back into them.

### Where the bundling idea ends up, and what it can and cannot buy

The construction first proposed for all of this was to bundle each analysis row with a proof, so
that a row could not exist without one. Two rounds of measurement changed what goes in the bundle
and what the bundle is for, and both changes are worth recording because the first instinct was
right and the first *reason* was not.

**Soundness cannot be the obligation.** `⊤` is sound for every term, so `admV := fun _ => true`
discharges a soundness field with `rfl`. Every defect in this log is an imprecision. A
soundness-bundled row would have caught none of the ten.

**The forcing was already there, three times over.** `Adm`, `Analysable` and `Adm_exact` are
separate exhaustive recursions, so a new `Term` constructor breaks all three. Re-wrapping them in a
structure adds locality and atomicity, but not the property; that property is exhaustiveness, and
`κ` had it from the beginning while the three tables with catch-alls accumulated seven gaps between
them.

**What was still soft was the hatch.** `Analysable`'s `false` rows are where a vague row can hide:
the list could grow by one identifier, and the reasons lived only in a docstring nobody is obliged
to write. So the reasons are a type. `Excuse` has five constructors and no `other`; `Excuse.covers`
says which term shapes each may be invoked for; and `analysable_excused` — exhaustive over `Term` —
says every declining row either names a covering excuse or inherits the refusal from a subterm.
Filing `array` under `opaqueDepth` is a type error. `excuse_shapes` runs the other way: a covered
shape really does decline, so the hatch cannot be used as a shortcut past a provable obligation.

`covers` has a catch-all, and it is the one place in this development where a catch-all is correct.
The polarity is the reason: it answers **`false`** — *no excuse covers this shape* — so a new `Term`
constructor lands in "not excusable", which forces `Analysable` to call it analysable, which forces
`Adm_exact` to prove it. Every other catch-all here failed by silently saying yes.

**And the hatch rows still needed soundness — which is where the discarded obligation belongs.**
`Adm_exact` binds the sixteen analysable rows in both directions. The other seven had, for a while,
*no* obligation whatever: nothing stopped one being written `fun _ => false`, which would have been
an outright **unsoundness** rather than the imprecision every other defect in this log has been.
Soundness is useless as the obligation for a row that has an exactness proof, because exactness
implies it; it is exactly the right obligation for a row that does not. `Adm_sound` supplies it for
all twenty-three. A hatch row may be loose; it may not be wrong.

That is the correction to the correction. The first instinct — bundle each row with a soundness
proof — was not wrong about soundness being *needed*; it was wrong about where. Applied uniformly it
is vacuous on the rows that matter and it was absent on the rows where it was the only thing
available.

**Every excuse is earned.** `Excuse` said which rows may decline; nothing said the declining was
*warranted*, so a constructor could name a shape that is secretly provable and the hatch would
absorb a row that ought to carry a proof. `excuse_witnessed` makes each excuse owe a counterexample:
a term of a shape it covers on which exactness genuinely fails. For a shape that is exact there is
none to be had, and both `excuse_witnessed` and `excuse_shapes` reject the attempt independently.

Four of the five witnesses had to be rebuilt around the axiom base, which is worth recording. The
obvious `uniqueAdmission` witness is a union of `string` and `number` at a numeral outside `D` — and
it is **not constructible**: `Double` is axiomatized with `toDec`, `ofDec`, `roundtrip` and `decEq`
only, and is not even known to be inhabited, so no `.num` value can be built. The replacement is
better than the original: `union(string, string)`, where `select` writes nothing because *two*
options admit. That is (U) failing in its purest form, and it needs no arithmetic at all. `opaq`'s
witness moved for the same reason — `opaq false` refuses every numeral, but the empty set is refused
too and costs nothing.

The obligation is that an excuse names a real phenomenon, **not** that it is tight on every term of
that shape — the stronger reading is false, and `union []` is the counterexample: covered by
`uniqueAdmission`, and perfectly exact, there being no option to admit. Widening `covers` to a shape
that is always exact is caught; widening it to one that is *sometimes* exact is not, and that is the
residual softness.

**What none of it can buy.** No construction inside the kernel prevents someone writing a weak
specification: an `Excuse` constructor can always be added with a witness of its own. What the construction does is make the weak choice *expensive and visible* — a named reason,
of a declared shape, in a file a reviewer reads — and make the strong choice cheap, since sixteen
rows already carry their proof. That is the honest limit, and it is the argument for spending the
effort on exactness rather than on ceremony around soundness.

### Why the migration is not a rename

With `Adm` proved exact on sixteen rows and sound on all twenty-three, the obvious next step is to
retire `κ`, `ident`, `adm` and `admA` in its favour. That is **not** a mechanical substitution, and
the three reasons are worth stating because each is a real gap rather than an inconvenience.

**There was no attribute side.** `Adm` is the value half. `admA` has 63 call sites and `SepA` is
defined on it, and nothing existed to migrate them onto. `AdmA` now supplies the definition and
`AdmA_sound` the soundness, so the half exists — but it carries one obligation where `Adm` carries
two: **exactness for the attribute rows is still unproved.** Until it is, the pair is not
interchangeable with the tables it would replace.

The mirror is not symmetric either, and the asymmetries are §1's. `number`, `literalN` and a numeric
`literal` reach their domains through `Double.ofDec`; the row can *call* it, so these are sharper
than §5's `⊤`, at the cost of being noncomputable. `refine` cannot narrow a read at all — `q` tests
the value a read produces and no syntactic set of attributes bounds that. `legacy` is `⊤` because
`extendRead` widens `p` past the subterm's set. Three rows differing in kind, not degree.

**`SepV` uses `κ` structurally, not as a predicate.** Its first disjunct is
`∃ kx ky, κ x = some kx ∧ κ y = some ky ∧ ∀ k ∈ kx, k ∉ ky` — it needs the *kind list*, and `Adm`
folds the kind gate in and discards it. The disjunct is arguably subsumed (disjoint kinds give
disjoint `Adm` wherever the rows are exact), but subsumption is a theorem about the hatch rows too,
not a substitution.

**`ident` has no counterpart.** `ident_of_adm` is what pins `ident` to anything at all, and with an
exact `Adm` the notion may well be derivable or unnecessary — but "may well be" is the work, not the
result.

So the sequence is: exactness for `AdmA`, then `SepV`/`SepA` re-derived on the pair, then the call
sites. The last of those is mechanical. The first two are not, and doing them in the other order
would replace four checked recursions with two unchecked ones.

**Step one is done.** `AdmA_exact` proves fourteen of the twenty-three attribute rows exact — two
fewer than the value side, and the two are `refine` and `legacy`, the pair whose asymmetry is why §5
needed `adm` and `admA` rather than one function. The numeric rows are the surprise: they reach
`dom(p)` through `Double.ofDec`, which is axiomatized, and are exact anyway, because a row may
*call* an axiomatized function even where no finite set of numerals describes its domain. §5 wrote
`⊤` there and did not have to.

The excuses gained two constructors — `valueUnderRead` and `widenedRead` — which cover nothing on
the value side. That forced `excuse_witnessed` into its proper form: the covering is a *hypothesis*,
so an excuse must be witnessed **on the side it is used on**, and neither side answers for the
other's reasons. All seven attribute-side excuses are witnessed. Claiming `valueUnderRead` for
`refine` on the value side — where it is provably exact — is rejected by both `excuse_shapes` and
`excuse_witnessed`.

Both halves now carry the same five obligations: exactness where claimed, soundness everywhere, a
covering reason for each declining row, no excuse over an exact row, and a counterexample behind
every excuse.

**Step two is done, and the two sides did not re-derive the same way.** `Adm_le_adm` and
`AdmA_le_admA` show the joint predicate is at least as tight as the rows it replaces, and
`sepJV_of_sepV` / `sepJA_of_sepA` carry every discharge §5 already has — nothing is lost.

But `SepJV` collapses to a **single clause** and `SepJA` does not. On the value side `Adm` folds the
kind gate into its own rows, and `Adm_kind` proves it lands where `κ` says, so the kind disjunct is
subsumed by the admissible-set one. On the attribute side the member disjunct survives, and the
reason is `setMember`: one value kind maps to three attribute members, and `AdmA`'s `set` row admits
all three whatever its element term is. `set(string)` and `set(number)` differ in `μSyn` and are
indistinguishable to `AdmA` — `sepJA_needs_member` is that pair.

So §5's two-disjunct shape was right on one side and redundant on the other, and nothing in the
tables could have said which.

**Step three answers `ident`, and the answer changes what the migration is.** `ident` is **not** a
function of `Adm` — nor of `adm`. `string` and `refine(string, ⊤)` denote the same pair, have the
same `Adm`, the same `adm`, and differ in `ident`. It is a fact about how a term is *written*, not
about which values it admits, and no predicate on values recovers it
(`ident_not_determined_by_Adm`).

That is not a gap, because nothing consumes it: none of the seventeen `uAtCan_*` theorems mentions
`ident` in its statement. What it carries is §5's **(K)** — stated as
`κ(cᵢ) ∩ κ(cⱼ) = ∅ ∨ ident(cᵢ) ∨ ident(cⱼ)`, found unsound, replaced by `SepV`. `ident_of_adm` pins
it and the two refutations record why the withdrawn form was wrong.

And `admitV_of_sepJV` / `admitA_of_sepJA` are what "nothing is lost" actually means, now proved
rather than asserted. `SepJV` is a *weaker* statement than `SepV` — the joint predicate is tighter,
so disjointness is easier to satisfy — but `Adm_sound` connects it straight to the denotation: where
`x` writes, `y` refuses. The discharge never needed the extra strength.

**So the migration is not a rename.** The pair supersedes `κ`/`adm`/`admA` *for the discharge*, and
the seventeen refutations plus the two counterexamples that retired (K) are the record of what §5
got wrong; deleting those would delete the record.

That much stands. What did **not** stand was the next sentence, which said `ident` should be left
alone because it carries something the pair lacks. It carries something *nothing* justifies, and the
only reason to think otherwise was that it had never been asked.

`Decides` is the semantic notion §5's prose describes: two values of the same kind, one written and
one refused, so the kind does not settle admission and an admission is evidence. Against it, `ident`
errs in **both** directions. `refine(string, ⊤)` is `ident` and decides nothing — `q` is checked on
both halves and always passes, and `ident` never looks at `q`. An `object` with a required field
refuses the empty map and writes a populated one, which is deciding by any reading, and `ident`
calls it `false`.

Worse, the `refine` row is an artifact rather than a claim: `ident (refine t q) = true`
unconditionally is exactly what makes `ident_of_adm` go through, because `adm (refine t q)` can
refuse on `q` alone while `ident t` is `false`. The row exists to satisfy the pinning lemma.

`ident` cannot be made exact — whether an arbitrary `q : Value → Bool` narrows anything is not a
syntactic question — but it can be honest about which side it errs on, and it is not. Nothing live
depends on it: no `uAtCan_*` consumes it and `admDisj_ident` derives it rather than assuming it. The
lesson is the one every other entry in this log records, applied to the one table that had been
exempted from it: a row nobody can fail is a row nobody has checked.

## §5 Certifying an implementation

The calculus is portable by design: nothing in it is TypeScript, and nothing is Rotorise. An
implementation in any language is certified by connecting its codecs to the model. There are two
routes, and the difference between them is the whole point of having an algebra.

### Route A — direct (sound, does not scale)

For each codec you ship, prove your `(T, μ, e, p)` satisfies §2's four laws. This is legitimate and
needs none of the calculus. It also means re-proving four laws for every codec you ever write, and
gives you nothing when you compose two of them.

Use this only for a genuinely primitive codec that no combinator builds — the equivalent of the
specification's `custom`, whose typing rule demands exactly this and for exactly this reason.

### Route B — structural (what the calculus is for)

Show your *combinators* correspond to the calculus's terms. Then soundness transfers to every codec
anyone can build with them, including ones not yet written.

Five obligations. `C1`–`C3` are the port; `C4`–`C5` are per-codec and mostly discharged by the
dischargers of §3.

**C1 — Embed the domain.** Exhibit maps from your value and attribute types into §1's `Value` and
`Attr`, injective on the sets you claim to hold. §1's `Value` is partitioned exactly as `Kind` is;
if your value language has a shape §1 lacks, the calculus does not cover it and this is where you
find out.

**The attribute map is partial, and pretending otherwise is how a defect gets in.** This obligation
used to ask for *total* maps, which no host language can supply: §1's `𝔸` is a coproduct over
`Carries(m)`, and four of the ten members carry a **refinement** rather than a host type —

| member | `Carries(m)` | what a host type does not enforce |
| --- | --- | --- |
| `N` | `Numerals` | the grammar, 38 significant digits, magnitude `1e-130 … 9.9…e125` |
| `SS` | `℘⁺fin(String)` | non-empty |
| `NS` | `℘⁺fin(Numerals)` | non-empty, **and** every entry a numeral |
| `BS` | `℘⁺fin(Bytes)` | non-empty |

— so `{ N: '' }`, `{ N: '5e-324' }` and `{ SS: [] }` are values of the implementation's attribute
type with **no image in `𝔸`**. The embedding is therefore partial, and the obligation that replaces
totality has two halves, because a pair has two directions:

> **`ran(e) ⊆ dom(⌈·⌉)`** — a term may write only attributes the embedding sends somewhere.
> **`dom(p) ⊆ dom(⌈·⌉)`** — and may read only those.
>
> Every term that touches a refined member is the term that has to check it, on the side it
> touches it.

Neither is a law of §2, and neither can be. §2 types the pair `e : T ⇀ 𝔸` and `p : 𝔸 ⇀ T`, so in
the calculus the question never arises: there are no non-attributes to be written to or defined on.
**The calculus expresses this in the signature of the pair, where nothing has to prove it because
nothing can violate it** — which is precisely why a port can violate it and see nothing fail. (R),
(C), (W) and (MP) all held while `literal(0, 1, 2)` read `⟨N, ""⟩` as `0`, and all four held while
`literal(NaN)` wrote `⟨N, "NaN"⟩`.

Those two defects are one obligation seen from its two ends, which is the argument for stating it
this way rather than as a warning about numerals. The list is short and closed — four members — so
for a port the audit is mechanical: *which of my terms touch one, and on which side*. In this
repository the terms are `decimal`, `number`, `literal`, `set` and `opaque`, and running the audit
found two more gaps, both in `opaque` and both in §4: it wrote `⟨N, "5e-324"⟩` because it checked
`Number.isFinite` rather than the numeral domain, and it reads `NS` it can never write back.

**C2 — Extract the pair.** For each codec `c` in your library, name its `(T, μ, e, p)`: the values
it claims to hold, the member it stores them in, and its encode and decode read through the C1
embedding. `μ` must be your real stored member, not a wish — `(W)` is what makes index keys stable
under refactoring, and it is the law a wrong `μ` breaks silently.

**C3 — Match the terms.** For each constructor your library offers, name the `Term` it denotes, and
show the two pairs agree: `Codec.Equiv (yourCodec …) (denote fuel t)` for sufficient fuel — §6's
`≡`, so agreement is required only where both are defined. Constructors with no corresponding
`Term` are outside the certificate; say so explicitly rather than assuming they inherit anything.

Show it for *your* codec against the term, not through an intermediate: `≡` is reflexive and
symmetric but **not transitive** (`Calculus.not_equiv_trans`), because a pair that is nowhere
defined agrees with everything. Two hops through a partial codec certify nothing.

Watch the stratification here (§4 of the specification). `optional` and `fallback` are **fields**,
not codecs. If your library lets `optional(c)` appear where a codec is expected, C3 fails at that
constructor and the fix is in your library, not in the mapping.

#### The mapping, for this repository

C3 asks for the `Term` each constructor denotes, and for the constructors that have none to be named
rather than assumed. Here it is, and the shape of the table is the answer to a question that had not
been asked: **a definition language for codecs has three levels in it, because §4 does.**

`CodecDef['kind']` is flat — twenty-four names in one union — while §4 puts a **codec**, a **field**
and a **rest policy** at three different levels and is normative about it. This library did enforce
the separation, with branded markers and a `NotAboutAbsence` guard at each site that could go wrong,
but the level a kind belongs to was written down nowhere, so the flat list read as twenty-four
constructors of which three had no term. They are not missing terms. They are not codecs.

**§3's terms** — twenty-one kinds, denoting twenty-two `Term` constructors:

| `CodecDef['kind']` | `Term` | | `CodecDef['kind']` | `Term` |
| --- | --- | --- | --- | --- |
| `string` | `.string` | | `attributes` | `.object` |
| `decimal` | `.decimal` | | `tagged` | `.dunion` |
| `number` | `.number` | | `untagged` | `.union` |
| `boolean` | `.boolean` | | `refine` | `.refine` |
| `binary` | `.binary` | | `nullable` | `.nullable` |
| `null` | `.null` | | `legacy` | `.legacy` |
| `literal` | `.literalS` / `.literalN`, by the values | | `held` | `.held` |
| `set` | `.set` | | `lazy` | `.lazy` |
| `array` | `.array` | | `opaque` | `.opaq` |
| `tuple` | `.tuple` (with `tail`) | | `custom` | `.custom` |
| `record` | `.record` | | | |

**§4's fields** — a *position* in an item, not a codec:

| `CodecDef['kind']` | denotes |
| --- | --- |
| `optional` | `Field.optional` |
| `fallback` | `Field.fallback` |

**§4's rest policy** — likewise a position:

| `CodecDef['kind']` | denotes |
| --- | --- |
| `restOf` | `Rest.codec` |

`Rest.drop` and `Rest.refuse` have no `CodecDef` and want none: they are the *absence* of a rest
codec, which the definition records by having no `rest` entry.

**The mapping is total in both directions.** Every kind denotes something, and every `Term`
constructor has a codec. It was not total until recently, and both gaps are worth naming because
they were the same mistake pointing opposite ways:

- `branch` was a kind with no term, because it was not a construction — a pseudo-codec manufactured
  while walking a path, whose `encode` and `decode` both threw. Removed; the walk carries the
  disagreement now.
- `null` was a term with no kind. §1 gives the value language a `null` and the attribute domain a
  `NULL`, §3's `(opaque)` dispatches on the `NULL` point, and no constructor denoted it, so a schema
  could not say "this attribute is exactly `NULL`". Added as `nullValue`.

The three strata are now named in the source (`TermDef`, `FieldDef`, `RestDef`), and a type-level
assertion fails the build if a kind is added that no stratum claims. That is `#assert_axioms`'s move
in a different language: a classification the specification makes normatively, turned into a build
error rather than something a reader is asked to re-derive. It was checked by adding an unclassified
kind and watching the build stop.

**What this table is not.** Naming the term is C3's first half; showing the pairs agree is the
second, and that is still a paper obligation — there is no `Codec.Equiv` check between a codec and
its term's denotation, because there is no denotation in TypeScript to check against. Until there
is, this table says the mapping exists and is total, not that it is correct.

#### A worked case: what C3 establishes for `refine`, and what it does not

`(refine)` carries no premise. `restrict` gates **both** halves — `e v = if q v then c.e v else none`,
`p a = (c.p a).bind (if q · then · else none)` — and is lawful for any decidable `q`, which is why
`Obligations` has no `refine` case at all. It is a total, law-preserving construction.

This library's `refine` gates only the read. `encode` is `inner.encode`, unchecked, because its
argument is already typed `Narrow` and TypeScript is what says so; `decode` runs the predicate,
because a stored value was never type-checked. The two codecs therefore differ in **definedness**:
the implementation's `e` is defined on values `restrict` refuses.

**C3 passes anyway**, and it is worth being precise about why. `≡` requires `e` and `p` to agree
only where both are defined, and the place they differ is exactly where `restrict`'s gate is shut —
so the agreement clause has no input to disagree on. `Codec.Equiv (refine …) (restrict c q)` holds.

That is `≡`'s tolerance doing the work, not the implementation's correctness. The same tolerance
makes §6's associativity row hold unconditionally while the two forms are not interchangeable
(`not_eq_altCodec_assoc`), and it is what `not_equiv_trans` bounds. **`≡` cannot see a domain
difference, and here the domain difference is the obligation.** So C3 is passed and something is
still owed:

> `refine` is sound **iff** `is` honestly decides `Narrow`. Given that, TypeScript discharges the
> write gate at every call site; nothing discharges the read gate, because stored data is outside
> the type system.

That obligation belongs on the C4 list, beside `held`'s iso and `custom`'s laws — it is a condition
on a component the library does not own. What it is *not* is a premise for `(refine)` in the
calculus: the rule is sound without one, so adding it would be adding a premise that discharges
nothing, which is the defect §4 already records twice — for `(D)` and for `ident`.

The general shape is worth keeping, because any port will meet it. **An unchecked direction is
sound exactly as far as something outside the codec enforces it.** For `refine`'s encode that
something is the type system, which is real but is not the calculus. For `literal` there is no such
enforcement — a union widens the field's type — so `literal` checks both directions, and its
admissible set is data this library owns, which gives the check an authority a caller's predicate
cannot have.

**C4 — Discharge the side conditions.** `Obligations fuel t` collects the specification's semantic
premises — `legacy`'s `ran(r) ⊆ dom(e)` and coherence, `fallback`'s writable stand-in, `held`'s iso
on the carriers, `custom`'s laws — together with any obligation your *own* constructors add on top
of the term they denote, in the shape of `refine`'s above. These are obligations on *your* values,
and they are the premises the proof failed without. A port that skips them has not weakened the
certificate; it has voided it.

`nullable`'s null-honesty was a fifth until the wrapper's guard made it derivable, and the porting
lesson is in *how* it left: a premise that constrains the library's own construction can be designed
out, where one that constrains a caller's function cannot. If your `nullable` adds the null point
unconditionally rather than only when the base lacks it, you still owe both honesty conditions.

**C5 — Discharge (U) for each union.** Use `uAtCan_of_separated` where the syntax decides it. Where
it does not, (U) remains a per-input obligation the semantics enforces by failing, which is safe for
every law except **(R)** at a canonical attribute — the one residue the theorem names.

**Then**: `soundness` and `soundness_core` apply to every term you can build, and their conclusions
transfer back through C1–C3 to your implementation.

### The certification checklist

```
[ ] C1  value and attribute embeddings, injective on the claimed carriers
[ ]     dom(p) ⊆ dom(embedding) — every term reading N, SS, NS or BS checks the refinement
[ ] C2  (T, μ, e, p) named for every codec; μ is the real stored member
[ ] C3  every constructor mapped to a Term, with Codec.Equiv demonstrated
[ ]     constructors with no Term listed explicitly as out of scope
[ ]     optional / fallback are fields, unusable in codec position
[ ] C4  Obligations discharged per term built
[ ] C5  UAtCan discharged per union, or the residue accepted and documented
[ ] --  legacy-containing derivations marked: (MP) off, no index keys
```

### Certifying without a proof assistant

A port that will not adopt Lean can still take the specification seriously, and should. The four
laws are directly property-testable, and the counterexamples of §4 show that bounded exhaustive
checking finds real defects in this domain:

| Law    | As a property test                                                       |
| ------ | ------------------------------------------------------------------------ |
| **R**  | `e v = some a  ⟹  p a = some v`                                          |
| **C**  | `p a = some v  ⟹  e v` is defined                                        |
| **W**  | `μ = some m ∧ e v = some a  ⟹  member a = m`                             |
| **MP** | `p a = some v ∧ e v = some a'  ⟹  a' ≼ a` (skip where `legacy` is in scope) |
| **U**  | for each union input: exactly one option admits it, per side — `checkUniqueAdmission` |

This is a weaker certificate — it checks the terms you generate, not all of them — but it is the
right first move, and it is where the §4 defects would have surfaced fastest.

**(U) needs a generator of neither.** Its inputs are **canonical pairs** — a value one option can
write, and the attribute it writes it to — so it generates per *option* and asks the other options
what they make of the result. `checkUniqueAdmission` in `src/testing.ts` does that for every union
reachable from a codec, reading admission off the **definition** and never off the union's own
matcher: a test that asked `union` which option it picked would be checking the implementation
against itself. Admission is `κ` **and** the attempt, as `codec-calculus.md` §5 states it and as
`FIDELITY.md` D1 records the model's `OptionSem.byAttempt` failing to — and the difference is not
cosmetic, because `union([string, number])` violates (U) under the model's reading and satisfies it
under the specification's. It found the defect §4's last entry records on its first pass.

**One warning from doing it.** The obvious harness generates *values* and round-trips them, which
tests **(R)** and nothing else. `decode` then only ever sees attributes `encode` produced, and the
attribute that breaks **(C)** is by definition one `encode` would never make. All three defects §4
records against this implementation lived in that gap, and none was reachable from a generated
value: the empty set, the denormalised numeral, the unchecked narrowing.

So (C) needs a generator of *attributes*. `checkDecodesAreWritable` in `src/testing.ts` builds one
by taking each encoded item and applying one **named** deviation at a time at every position in it —
an empty set, a denormalised `N`, an `N` past the magnitude, a member swapped for another, an
absent attribute. The names matter: a counterexample says which shape found it, and each shape is a
class of defect this project has actually had rather than a random perturbation. The harness is
itself checked against planted versions of two of the three, so that passing means something.

## §6 Scope: what is not proved

Stated plainly, because a certificate that hides its edges is worth less than one that names them.

| Gap                                    | Status                                                                                      |
| -------------------------------------- | -------------------------------------------------------------------------------------------- |
| **Implementation conformance**          | Partly mechanized. **(C)** is a property test over generated *attributes* (`checkDecodesAreWritable`), which is where all three of §4's implementation defects lived; **(R)** and the member laws are `checkRoundTrip` and `checkMembersStable`. C1–C3 themselves — the embedding, the pair, and the `Term` each constructor denotes — remain a paper obligation, and **(U)** is unchecked. Still the largest remaining risk. |
| **(U) in general**                      | A premise. The dischargers cover the decidable cases; the rest fails per input at runtime.  |
| **Recursive `union`**                   | Unmodelled — and not for convenience. `union`'s unique admission is *anti-monotone* in its options, so a union whose options are genuinely recursive has no fixpoint semantics at all (§7, `Continuity.lean`). `Term.lazy` carries `Unit → Term`, which defeats the termination checker without adding a single term, so every term in the model is finite. `lazy` under `union` is therefore not merely awkward to model; it is outside the model, and (U) is why. |
| **(MP) under `legacy`**                 | Off, by design, on re-read attributes.                                                      |
| **(A) the denotation's `T` is the judgement's** | `(denoteω t).T = T` for a derivable `⊢ t : T ⇝ μ`, which is what §3 means by "`Uν` *is* `opaque`'s held set". **Closed for `opaque`** (`opaq_T_identity`), and `typed_TSub` is one half of it in general. Open for the other constructors: the missing half must *construct* the denotation's witness, where `typed_TSub` only projects it — a converse to `align_TSub` that builds `align`'s output, and the object case's presence data. Not false anywhere, and **definitional at `union`** (`altCodec_T`): both sides are the same union of the options' sets. |
| **(B) the held set is what can be written** | `T = dom(e)` — the claim that makes `: T` an honest index rather than an upper bound. `Carrier.domE` gives `dom(e) ⊆ T` for every derivable term. The converse is **false for `union` without full (U)** (`not_TIsDomE_unionLiteralString`): in `union(literal("A"), string)`, `"A"` is in the held set and the union writes nothing for it, because both options admit. That is the residue `uAtCan_of_separated` names, seen from the held set rather than from **(R)**. |
| **§1's numeral domain**                 | **Modelled.** `Numeral.WF` (Domain.lean) carries §1's three clauses — grammar, ≤ 38 significant digits, magnitude `0` or `1e-130 … 9.9…e125` — and `decimal` gates on it, so it no longer holds every string. `decimal_writes_wf`/`decimal_reads_wf` are the report. The *carrier* is still unrestricted (`Attr.n "abc"` remains representable), which is the honest split: §1 says which strings DynamoDB accepts in an `N`, and the calculus's job is that its codecs write only those. Two narrowings are noted at the definition: a bare integer part is required, and significance is counted between first and last nonzero digit. |
| **§6's equations**                      | **Twenty of twenty, with one row narrower than the table reads — and now stated in one language.** Every Hold row has a term-level twin (`equiv_denoteω_*`), reached through ten `rfl` bridges that write down the combinator-to-term translation the model had only implied. The "do not hold" table is settled: eight machine-checked, and `optional(optional(c))` enforced by the syntax, since no `Field` constructor takes a `Field`. All eleven "Hold" rows are proved, but `union`'s commutativity is proved for the **adjacent transposition** (`equiv_altCodec_swap`), which generates every permutation without the lift to `List.Perm` being written down. Wrapper member preservation is five of five — three codec wrappers, and the two field wrappers through `FieldSem.codec`, which §4 of the specification says is where a field's member lives. `union` associativity, the table's only *conditional* row, holds **without** its conditions — see §4. And `≡` itself is reflexive and symmetric but **not transitive** (`not_equiv_trans`), which bounds what a table of rewrites licenses. |
| **`Double`**                            | Axiomatized with exactly the shortest-text round trip `(number)` consumes. IEEE-754 facts are not this calculus's theorems. |
| **Set-ness**                            | Wire sets and maps are lists; the quotient lives in `ker p`, where §2 puts it, not in the carrier. |

## §7 Tooling rationale

Recorded because the choice shapes what the model can say, and because the next port will face it.

### Where the cost went

Three buckets. **The plumbing** — roughly 1,300 of `Combinators.lean`'s 4,620 lines were
traversal, lookup and filter machinery. This is now **retired**: mathlib supplies most of it, and
the residue it does not supply lives in `Calculus/Lists.lean`, apart from the codec content. The
traversal toolkit in particular collapsed onto one observation — a successful traversal *is* the
pointwise relation `List.Forall₂ (f · = some ·)` (`traverse_eq_some`) — after which each of its
laws is that relation reversed, forgotten or composed, and mathlib's `Forall₂` API does the work
that four twenty-line `Option` case analyses used to. **Fuel** — the calculus
is partial by design (`lazy` exists to break recursion), Lean 4 wants structural recursion, so
partiality is encoded as fuel and fuel then infects every statement, every obligation, and the `T`
identity of §6. **Genuinely hard content** — the object codec's name dispatch, `opt` widening,
fallback stand-ins and drop filter are intricate in any system.

### Fuel is not the assistant's fault

This was recorded here for a while as a Lean tax, with Isabelle/HOL's `partial_function` as the
escape. That is wrong, and `formal/Calculus/Continuity.lean` proves it.

Every least-fixpoint construction — `partial_function`, HOLCF, a hand-rolled `⨆` over the fuel
stages — is a fixpoint over a ccpo, and it discharges a **monotonicity obligation on the
functional**: unfolding one more step may only add information. `union` does not satisfy it.
`altCodec` resolves a union by *unique* admission, and `OptionSem.byAttempt` derives admission from
`(c.e v).isSome` — definedness of the option's own encoder. So as the recursive results grow,
admission grows, the filtered option list grows from `[o]` to `[o, o']`, and the union's answer
collapses from `some` to `none`. (U) quantifies over the *other* options: it is a negative
condition, anti-monotone in exactly the argument a fixpoint must grow.

Two theorems:

| Theorem                     | Content                                                                                   |
| --------------------------- | ------------------------------------------------------------------------------------------- |
| `altCodec_not_monotone`     | The cause, on the combinator alone: one option grows in the information order (`Codec.Approx`, the minimal requirement *any* ccpo must meet) and the union's `e` shrinks. This is the `mono` obligation a `partial_function` denotation would have to discharge, and it is false. |
| `denote_not_fuel_monotone`  | The bite, on a closed term: `union(literal("A"), lazy(string))` encodes `"A"` at fuel 2 and nothing at fuel 3. The fuel stages are not a chain, so `⨆ fuel, denote fuel t` is not a definition either. |

Note the direction of failure: the low-fuel answer is **over**-defined, not under-defined. Fuel 2
answers `some` because it has not yet seen the second option — it is not a sound approximation of
the truth from below, it is a different and wrong one. The relational route closes the same way:
`¬∃ another option admits` is a negative recursive occurrence, so admission is not (co)inductively
definable either.

The obstruction is therefore in the calculus, not in the proof assistant. Porting to Isabelle/HOL
would replace the fuel parameter with a failed `mono` proof at the `union` case. What fuel is
actually standing in for is the finiteness of `Term` — which suggests the cheaper repair, below.

### The observation that matters

All three of §4's discharger refutations are **finite counterexamples**: a handful of concrete values each. None
needed a proof assistant. Bounded exhaustive checking over the existing implementation would have
found all three quickly. The proof assistant earned its keep on the *positive* theorem — soundness
of the algebra — which is what cannot be established by testing at all.

The corollary for planning held up: the nine refutations went quickly once `≡` and `denoteω` were in
place, and every one turned on a *held-set* separation rather than an `e`/`p` disagreement — `≡`
tolerates a shrinking domain but never a differing `T`, so that is where the cheap witness lives.
**Reach for a counterexample finder before a proof, on any new side condition.**

### Which assistant

| Option              | Assessment                                                                                             |
| ------------------- | ------------------------------------------------------------------------------------------------------ |
| **Lean + mathlib**  | Chosen, and now **adopted**. It retired the plumbing as predicted; it did not remove the fuel encoding, but nothing does — see above. The one cost not anticipated: mathlib's classical proofs make the §3 axiom base easy to widen by accident, which is why `Calculus/Axioms.lean` now guards it. |
| **Isabelle/HOL**    | `sledgehammer` is the real and un-rebutted win: `Combinators.lean` is 4,620 lines of first-order list/option reasoning, which is exactly its diet. The other two claims do not survive. `partial_function` does **not** remove fuel here — it fails its `mono` obligation at `union`. And `nitpick` is weakest where it is most needed: `Term` carries function-typed fields (`held`'s `f`/`g`, `custom`'s pair, `refine`'s `q`), finite model finding degrades badly on those, and the §6 rows most in need of one sat precisely on `held`/`custom`/`refine` (they are now refuted by hand — see `Refutations.lean` — which is the outcome that would have tested the claim). A switch would also forfeit §3's axiom-base claim — Isabelle/HOL is classical with Hilbert choice, unconditionally. |
| **Rocq/Coq**        | No clear win over Lean. Same dependent-pattern-match friction, same partiality problem.                |
| **Agda**            | Better sized types, worse automation. Net loss here.                                                   |

Honest conclusion: **stay.** The premise that made Isabelle/HOL look like the better default was
that it would buy a fuel-free denotation; it would not, and no system would. What is left is
`sledgehammer` against a finished, `sorry`-free development — not enough, and it is bought partly
with the axiom base.

The cheaper repair was in the model, and it is **done** — in Lean, in three steps:

1. **`Term.lazy` is finite** — `lazy (t : Term)`, not `lazy (γ : Unit → Term)`. The thunk added no
   constructible term and existed only to defeat the termination checker.
2. **`opaque` budgets each input by its own depth** (`Calculus/Opaque.lean`). `opaqCodec` was the
   one case whose regress is not on the term — it rebuilds itself under `set`/`array`/`record` —
   and it is also the one union that *is* continuous, because its eight options are kind-disjoint
   so at most one ever admits. `opaqCodecω` supplies `Value.depth v` writing and `Attr.depth a`
   reading; `opaq_e_agree`/`opaq_p_agree` prove the answer never changes past those budgets, and
   `opaq_e_depth`/`opaq_p_depth` license the transport between them that `retract` and `canon`
   need. `lawful_opaqCodecω` and `carrier_opaqCodecω` follow.
3. **`denoteω : Term → Codec`** (`Calculus/Denoteω.lean`) is structural — no fuel parameter at
   all. With `denote`'s `opaq` case now fuel-independent too, `denote` *stabilizes*, and
   `denoteω_eq : termDepth t ≤ n → denoteω t = denote n t` makes the two denotations equal (as
   codecs, not merely pointwise) at sufficient fuel.

So the fuel-free statements are transports, not reproofs — the existing ~7,500 `sorry`-free lines
were not rewritten. `Calculus/Soundnessω.lean` states the theorem the way §5 always meant it:

```
soundnessω : Typed t T μ → Obligationsω t → MPOkω t → Lawful (denoteω t)
```

with `soundness_coreω`, `carrier_denoteω`, `typed_e_memω`, `typed_p_memω` and `typed_μSynω`
alongside. Axiom base unchanged throughout: `propext`, `Quot.sound`, and the `Double` axioms of
§1 — no `Classical.choice`.

Worth noting which constructors this leaves alone: `dunion` never consults the recursive result to
decide admission, and `opaque`'s options are kind-disjoint, so both look continuous and could carry
a genuine fixpoint semantics if recursive codecs were ever wanted. Neither is proved here. It is the
*general* `union`, whose options may overlap, that is not — and that is a fact about (U), portable
to any system and any port.

## §8 Priorities

1. **Mechanize conformance** (§6, row 1) — C1–C3 for the TypeScript. The largest gap between "the
   calculus is sound" and "what ships is correct".
2. ~~**Refute §6's "do not hold" table**~~ — **done**, and the "Hold" table with it: twenty of
   twenty, with commutativity proved for the adjacent transposition and the `List.Perm` lift not
   written down, and with `≡` itself shown non-transitive (`not_equiv_trans`), which bounds what a
   table of rewrites licenses. See §6's row.
3. ~~**Tighten §1's numeral domain**~~ — **done** (§6), then tightened again: `decimal` holds
   `Numeral.Stored`, the form the store hands back, and not §1's `Numerals`, which is what it
   accepts. The two differ, and the difference was a round trip failing across storage. And
   again, at the other end: `number` now holds `D` rather than every double, `Uν` carries the
   same premise, `(literal-N)` carries it as `hD`, and `η ⊆ ker p` is `SurvivesStore` rather
   than prose. `D` is checked everywhere an `N` is written from a double, which it had never
   been — the last gap was `literal(NaN)` writing `{ N: 'NaN' }` in the shipped library.
4. ~~**De-fuel the denotation**~~ — **done** (§7), and with it `T` **as an identity** for
   `opaque`. What remains of that row is the other constructors, where the honest answer differs by
   rule: containers and wrappers should go through much as `opaque` did, but `union` needs (U) in
   full, not merely at canonical inputs, and is false without it.
5. **The remaining §6 equations.**

---

## Sources

The specification and its citations: [`codec-calculus.md`](./codec-calculus.md).
The model, its module map and its running remaining-work list: [`../formal/README.md`](../formal/README.md).
