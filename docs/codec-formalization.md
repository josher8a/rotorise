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
than a claim**: `#assert_axioms` collects what each headline theorem actually depends on and fails
on anything unsanctioned. This matters more since mathlib arrived, because mathlib proves a great
deal classically — a single `by_contra`, or an appeal to a lemma such as `List.filter_eq_nil_iff`,
silently widens the base of everything downstream. Both leaks happened while the guard was being
written, which is the argument for having it.

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
Five further findings follow the table — five defects and one correction that ran the other way,
into the model. The last two are open against `codec-calculus.md`: the text has not been changed
yet, and the entries say what the amendment should be.

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

`ℓ ⊆ D` is left open, because adding a premise to a rule changes the specification. What the model
now carries instead is the cost, stated: `literalN_sub_number` (with the premise, `literal-N`
refines `number` again — the premise is the whole of what the prism needed),
`not_literalN_sub_number` and `literalN_writes_off_numerals` (without it, a derivable term writes an
attribute outside §1's `Numerals` at a value `number` refuses), and `typed_literalN_any` (the
derivation that would be refused, with no hypothesis on `d` at all).

Those three are **conditional on a double outside `D` existing**, and deliberately so. `Double` is
axiomatized with the shortest-text round trip and nothing else; whether IEEE-754 has a value
DynamoDB will not store is a fact about IEEE, and asserting it would widen the trusted base to
settle a question the specification can answer for itself. So the refutations read: *if* there is
such a double, this is what the missing premise costs — and if there is not, the premise costs
nothing to add. That is the whole decision, and it is a one-line change to §3 either way.

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
§5 should split its `adm` row into a value side and an attribute side and say where each
stops — the model's `adm`/`admA` is the shape it wants.

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

**C1 — Embed the domain.** Exhibit total maps from your value and attribute types into §1's `Value`
and `Attr`, injective on the sets you claim to hold. §1's `Value` is partitioned exactly as `Kind`
is; if your value language has a shape §1 lacks, the calculus does not cover it and this is where
you find out.

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
premises — `legacy`'s `ran(r) ⊆ dom(e)` and coherence, `nullable`'s null-honesty, `fallback`'s
writable stand-in, `held`'s iso on the carriers, `custom`'s laws — together with any obligation
your *own* constructors add on top of the term they denote, in the shape of `refine`'s above. These are obligations on *your*
values, and they are the four premises the proof failed without. A port that skips them has not
weakened the certificate; it has voided it.

**C5 — Discharge (U) for each union.** Use `uAtCan_of_separated` where the syntax decides it. Where
it does not, (U) remains a per-input obligation the semantics enforces by failing, which is safe for
every law except **(R)** at a canonical attribute — the one residue the theorem names.

**Then**: `soundness` and `soundness_core` apply to every term you can build, and their conclusions
transfer back through C1–C3 to your implementation.

### The certification checklist

```
[ ] C1  value and attribute embeddings, injective on the claimed carriers
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
| **`T` as an identity**                  | **Closed for `opaque`** — `opaq_T_identity` proves `(opaqCodecω ν).T = Uν` exactly, the case this row said bites hardest. Still open for the other constructors, and *false* for `union` without full (U): `T` is the union of the options' sets, but `e` refuses wherever two of them admit, so the surplus is real. The general blocker is gone — the "fuel exceeds depth" hypothesis is now `Value.depth`/`termDepth`. |
| **§1's numeral domain**                 | **Modelled.** `Numeral.WF` (Domain.lean) carries §1's three clauses — grammar, ≤ 38 significant digits, magnitude `0` or `1e-130 … 9.9…e125` — and `decimal` gates on it, so it no longer holds every string. `decimal_writes_wf`/`decimal_reads_wf` are the report. The *carrier* is still unrestricted (`Attr.n "abc"` remains representable), which is the honest split: §1 says which strings DynamoDB accepts in an `N`, and the calculus's job is that its codecs write only those. Two narrowings are noted at the definition: a bare integer part is required, and significance is counted between first and last nonzero digit. |
| **§6's equations**                      | **Twenty of twenty, with one row narrower than the table reads.** The "do not hold" table is settled: eight machine-checked, and `optional(optional(c))` enforced by the syntax, since no `Field` constructor takes a `Field`. All eleven "Hold" rows are proved, but `union`'s commutativity is proved for the **adjacent transposition** (`equiv_altCodec_swap`), which generates every permutation without the lift to `List.Perm` being written down. Wrapper member preservation is five of five — three codec wrappers, and the two field wrappers through `FieldSem.codec`, which §4 of the specification says is where a field's member lives. `union` associativity, the table's only *conditional* row, holds **without** its conditions — see §4. And `≡` itself is reflexive and symmetric but **not transitive** (`not_equiv_trans`), which bounds what a table of rewrites licenses. |
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
   same premise, and `η ⊆ ker p` is `SurvivesStore` rather than prose. **One thing is left and
   it is not a proof:** whether §3's `(literal-N)` gains `ℓ ⊆ D`. The cost of not adding it is
   stated in `Refutations.lean` and in §4; the decision is normative.
4. ~~**De-fuel the denotation**~~ — **done** (§7), and with it `T` **as an identity** for
   `opaque`. What remains of that row is the other constructors, where the honest answer differs by
   rule: containers and wrappers should go through much as `opaque` did, but `union` needs (U) in
   full, not merely at canonical inputs, and is false without it.
5. **The remaining §6 equations.**

---

## Sources

The specification and its citations: [`codec-calculus.md`](./codec-calculus.md).
The model, its module map and its running remaining-work list: [`../formal/README.md`](../formal/README.md).
