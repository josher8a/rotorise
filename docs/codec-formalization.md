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
whole trusted base.

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

### The dischargers of (U)

Decidable conditions, each sufficient for (U) on the unions it covers, all proved:

| Discharger                    | Statement                | Decides                       |
| ----------------------------- | ------------------------ | ----------------------------- |
| disjoint kinds, or disjoint `adm` | `uAtCan_of_separated` | the writable side             |
| distinct members, or disjoint `admA` | `uAtCan_of_separated` | the readable side          |
| tag disjointness              | `uniqueAdmission_byTag`  | `discriminatedUnion`, outright |
| kind disjointness             | inside `lawful_opaqCodec` | `opaque`'s fixpoint, outright |

with `κ_sound`, `adm_sound`, `admA_sound` connecting the syntactic functions to the denotation, and
`uAtCan_string_boolean` / `uAtCan_literal_literal` witnessing that the premises are jointly
satisfiable — a discharger whose premises cannot all hold discharges nothing.

## §4 What the mechanization changed in the specification

Three claims in §5's discharger tables were unsound as written. Each is now corrected in
`codec-calculus.md`, with the counterexample machine-checked in `formal/Calculus/Discharge.lean`.

| Was claimed                                            | Counterexample                                                        | Now |
| ------------------------------------------------------ | --------------------------------------------------------------------- | --- |
| **(K)**: `κ` disjoint ∨ `ident(cᵢ)` ∨ `ident(cⱼ)`      | `union(literal("A"), string)` — (K) passes, both admit `"A"`           | (K) needs `adm` disjoint on **both** sides (`not_uAtCan_literal_string`) |
| the same, with `ident` on both sides                   | `union(array(literal "A"), array(literal "B"))` — both admit `[]`      | `ident` propagates through containers; disjointness does not (`not_uAtCan_array_literals`) |
| **(D)** as disjointness "would be sound"               | `union(literal("A"), held(literal("A"), f, g))` — held sets `{"A"}`/`{"B"}`, both read `S "A"` | (D) is well-formedness on `T`, never a discharger of (U) (`not_uAtCan_literal_held`) |

The shared error is worth stating once, because it will recur in any port: **held sets are sets of
values; (U)'s readable side quantifies over attributes; `held` relabels between them.** No condition
on held sets alone can decide the readable side.

### One that ran the other way

A fourth defect turned up while closing §6's `T` row, and it is worth separating because the arrow
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

Watch the stratification here (§4 of the specification). `optional` and `fallback` are **fields**,
not codecs. If your library lets `optional(c)` appear where a codec is expected, C3 fails at that
constructor and the fix is in your library, not in the mapping.

**C4 — Discharge the side conditions.** `Obligations fuel t` collects the specification's semantic
premises — `legacy`'s `ran(r) ⊆ dom(e)` and coherence, `nullable`'s null-honesty, `fallback`'s
writable stand-in, `held`'s iso on the carriers, `custom`'s laws. These are obligations on *your*
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
| **U**  | for each union input: exactly one option admits it, per side              |

This is a weaker certificate — it checks the terms you generate, not all of them — but it is the
right first move, and it is where the §4 defects would have surfaced fastest.

## §6 Scope: what is not proved

Stated plainly, because a certificate that hides its edges is worth less than one that names them.

| Gap                                    | Status                                                                                      |
| -------------------------------------- | -------------------------------------------------------------------------------------------- |
| **Implementation conformance**          | Not mechanized. C1–C3 above are currently a paper obligation for every port, this repo included. The largest remaining risk. |
| **(U) in general**                      | A premise. The dischargers cover the decidable cases; the rest fails per input at runtime.  |
| **Recursive `union`**                   | Unmodelled — and not for convenience. `union`'s unique admission is *anti-monotone* in its options, so a union whose options are genuinely recursive has no fixpoint semantics at all (§7, `Continuity.lean`). `Term.lazy` carries `Unit → Term`, which defeats the termination checker without adding a single term, so every term in the model is finite. `lazy` under `union` is therefore not merely awkward to model; it is outside the model, and (U) is why. |
| **(MP) under `legacy`**                 | Off, by design, on re-read attributes.                                                      |
| **`T` as an identity**                  | **Closed for `opaque`** — `opaq_T_identity` proves `(opaqCodecω ν).T = Uν` exactly, the case this row said bites hardest. Still open for the other constructors, and *false* for `union` without full (U): `T` is the union of the options' sets, but `e` refuses wherever two of them admit, so the surplus is real. The general blocker is gone — the "fuel exceeds depth" hypothesis is now `Value.depth`/`termDepth`. |
| **§1's numeral domain**                 | `Numeral := String`; grammar, 38 digits and magnitude unmodelled. So `decimal` currently holds every string. Now checkable: tighten the predicate and `typed_e_mem` reports whether the codec respects it. |
| **`(numeric)`'s `T ≠ ∅`**               | Dropped. `T ⊆ D` is vacuous while `D` is unmodelled, and the specification calls it an unchecked precondition; `T ≠ ∅` is simply absent. |
| **§6's equations**                      | **Nineteen of twenty settled.** The "do not hold" table is complete — eight machine-checked, and `optional(optional(c))` enforced by the syntax, since no `Field` constructor takes a `Field`. Ten of the eleven "Hold" rows are proved. The one open row is `union` associativity, the table's only *conditional* one: §6 requires (D) and (K) on both sides and holds it only on inputs satisfying (U), since an ambiguity inside the nested option fails locally on the left and globally on the right. |
| **`Double`**                            | Axiomatized with exactly the shortest-text round trip `(number)` consumes. IEEE-754 facts are not this calculus's theorems. |
| **Set-ness**                            | Wire sets and maps are lists; the quotient lives in `ker p`, where §2 puts it, not in the carrier. |

## §7 Tooling rationale

Recorded because the choice shapes what the model can say, and because the next port will face it.

### Where the cost went

Three buckets. **No mathlib** — roughly 1,300 of `Combinators.lean`'s 4,620 lines are traversal,
lookup and filter machinery, a large part of which a library supplies; this is being retired. **Fuel** — the calculus
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

All three defects of §4 are **finite counterexamples**: a handful of concrete values each. None
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
| **Lean + mathlib**  | Chosen. Retires the plumbing; does not remove the fuel encoding, but nothing does — see above. Best speedup per unit of disruption. |
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
2. ~~**Refute §6's "do not hold" table**~~ — **done**, all nine (`Refutations.lean`), and the
   "Hold" table with it, ten of eleven. What is left of §6 is `union` associativity alone, which
   needs (U) threaded through both nestings.
3. **Tighten §1's numeral domain**, now that `typed_e_mem` can check it.
4. ~~**De-fuel the denotation**~~ — **done** (§7), and with it `T` **as an identity** for
   `opaque`. What remains of that row is the other constructors, where the honest answer differs by
   rule: containers and wrappers should go through much as `opaque` did, but `union` needs (U) in
   full, not merely at canonical inputs, and is false without it.
5. **The remaining §6 equations.**

---

## Sources

The specification and its citations: [`codec-calculus.md`](./codec-calculus.md).
The model, its module map and its running remaining-work list: [`../formal/README.md`](../formal/README.md).
