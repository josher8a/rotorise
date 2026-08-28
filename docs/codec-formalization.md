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
| **(MP) under `legacy`**                 | Off, by design, on re-read attributes.                                                      |
| **`T` as an identity**                  | Proved as an upper bound — the pair writes and reads *no more* than `T`. That it holds *all* of `T` is unproved, and unprovable in the fuel encoding without a "fuel exceeds depth" hypothesis the model lacks. Bites hardest at `opaque`, where §3 says `Uν` *is* the held set. |
| **§1's numeral domain**                 | `Numeral := String`; grammar, 38 digits and magnitude unmodelled. So `decimal` currently holds every string. Now checkable: tighten the predicate and `typed_e_mem` reports whether the codec respects it. |
| **`(numeric)`'s `T ≠ ∅`**               | Dropped. `T ⊆ D` is vacuous while `D` is unmodelled, and the specification calls it an unchecked precondition; `T ≠ ∅` is simply absent. |
| **§6's equations**                      | Two of twenty proved — `nullable`'s idempotence and `union`'s commutativity, the rows other sections rely on. The nine "do not hold" rows are **unrefuted**, which given §4 is the most suspicious remaining surface. |
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

### The observation that matters

All three defects of §4 are **finite counterexamples**: a handful of concrete values each. None
needed a proof assistant. Bounded exhaustive checking over the existing implementation would have
found all three quickly. The proof assistant earned its keep on the *positive* theorem — soundness
of the algebra — which is what cannot be established by testing at all.

The corollary for planning: the remaining work is mostly §6's tables, and nine of those twenty rows
are refutations. **Reach for a counterexample finder before a proof, on any new side condition.**

### Which assistant

| Option              | Assessment                                                                                             |
| ------------------- | ------------------------------------------------------------------------------------------------------ |
| **Lean + mathlib**  | Chosen. Retires the plumbing; does not remove the fuel encoding. Best speedup per unit of disruption.  |
| **Isabelle/HOL**    | The strongest case for a switch. `sledgehammer` closes most leaf goals; codatatypes and `partial_function` remove fuel entirely; `nitpick`/`quickcheck` are counterexample finders in the same tool, which is what the remaining work needs. Rejected only because it means rewriting ~7,500 `sorry`-free lines. |
| **Rocq/Coq**        | No clear win over Lean. Same dependent-pattern-match friction, same partiality problem.                |
| **Agda**            | Better sized types, worse automation. Net loss here.                                                   |

Honest conclusion: **starting today, knowing the calculus is partial and the payoff is one soundness
theorem plus many counterexamples, Isabelle/HOL would be the better default.** That is a reason to
choose differently on a future formalization, not to discard this one.

## §8 Priorities

1. **Mechanize conformance** (§6, row 1) — C1–C3 for the TypeScript. The largest gap between "the
   calculus is sound" and "what ships is correct".
2. **Refute §6's "do not hold" table** — nine claims, no new machinery needed; `Codec.Equiv` and the
   counterexample idiom of `Discharge.lean` are in place.
3. **Tighten §1's numeral domain**, now that `typed_e_mem` can check it.
4. **`T` as an identity**, which needs a depth measure alongside fuel.
5. **The remaining §6 equations.**

---

## Sources

The specification and its citations: [`codec-calculus.md`](./codec-calculus.md).
The model, its module map and its running remaining-work list: [`../formal/README.md`](../formal/README.md).
