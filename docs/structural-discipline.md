# Structural impossibility over guards

The rule, as JH states it:

> Prefer making a bad state **unrepresentable** over **guarding** against it.

## Why — and it is not "so the TypeScript is easier to write"

`codec-formalization.md` §1–§2 sets the terms, and they are stricter than a portability argument:
the model is **not** a test suite for the implementation, nothing in `formal/` observes it, and
*"a target implementation is certified by exhibiting a homomorphism into the model — not by
re-deriving the laws."*

So the reason structural impossibility is worth preferring is not that it makes an implementation
easier to write. It is that **it decides what the certification obligation looks like.** A
constraint the model carries in a *type* is discharged by exhibiting a structure-preserving map —
a type-level check, once. A constraint the model carries in a *gate* becomes a proof obligation
the target owes **per site that can reach it**, and nothing in the model can tell whether the
target paid it.

That is why the priority order is the model first and the target after: a guarantee made
structural in the spec is a guarantee the target cannot silently fail to inherit. One made by
gate is one the target must be audited for, forever.

## The evidence, and it is downstream evidence

The audit produced the data to settle this, and it is unusually clean.

---

## 1. The evidence: every live bug was on the same side of the line

§9 audited `src/` against the five representation tightenings the model had just landed — an
audit of a target that had **not** been certified, which is exactly why there was anything to
find. Five live bugs. Sorting the five tightenings by whether the model's guarantee was structural
or a gate *on the target's side*:

| # | tightening | how TS carries it | bugs found |
| --- | --- | --- | --- |
| 1 | `M` unordered, unique-keyed | **structurally** — a JS object cannot hold a duplicate key, and no branch reads enumeration order | **0** |
| 2 | object field table is a set | **structurally** — `Record<string, AnyCodec>`, keys unique by construction | **0** |
| 3 | wire sets non-empty | **by gate** — four refusals in `codec.ts`, replicated per term | 1 (`native.ts` had none) |
| 5 | `Numeral.WF` on both halves | **by gate** — `isNumeral` at eight sites | 3 (`native.ts` wrote `⟨N,"5e-324"⟩`, read `{N:''}` as `0`, read `{NS:['abc']}`) |
| 4 | `ℓ` non-empty, repeat-free | **not expressible** — a rest parameter accepts zero arguments | 1, plus repeat-freedom still unchecked |

**Rows 1–2: zero bugs and zero checks.** The verdict in both cases was literally "by
construction". Nobody had to be careful, and no test defends them, because the host's own type
system refuses the bad state.

**Rows 3 and 5: four of the five bugs.** In both, the model made the condition *structural* —
`NEFinset`, `Attr.n : WFNumeral` — and the host had to *gate*. `codec.ts` gated correctly at every
site. `native.ts` gated at none, and had filed itself as `kind: 'opaque'` so the correspondence
table counted it as already covered. The gate was replicated eight times and one file's worth was
missing.

**Row 4: the case worth naming separately.** `NEFinset` is structural in Lean and TS *cannot* say
it — `literal(...allowed: readonly T[])` typechecks with zero arguments, and the obvious fix
(`(first: T, ...rest: T[])`) breaks `literal(...Object.values(Status))`, which spreads a plain
array. So the guarantee had to become a construction-time throw plus a test, and the residual
(no repeated alternatives) is *still* unchecked, because nothing forces it and nobody would notice.

That is the whole argument, from data: **the obligation is discharged by construction where the
target can carry the structure, and every defect lived where the target had to re-derive a gate.**

Read forward rather than backward, this is the reason to spend effort on the spec and not on the
target. Rows 1–2 needed no audit. Rows 3–5 needed one, got one, and it found five bugs — and would
need another one after the next change.

---

## 2. The three cases, and what each one owes

For every structural guarantee the model makes, the host is in exactly one of three positions.

### (a) The host carries it structurally — owe nothing

Verify by types and move on. `AttributeValue = ExactlyOne<AttributeCarries>` is the good example
at the carrier level: §9.5 checked the C1 embedding and found the set of host inhabitants with no
image in the model's `𝔸` is *closed* and enumerable, which is only possible because the host type
is doing the work.

### (b) The host must gate — owe a **named** gate and a test

Two rules, both learned the hard way:

1. **One owner.** `isNumeral` lived in `codec.ts` beside the codecs that first needed it, so
   `native.ts` — a sibling entry point that must not import a codec module — had a second answer
   to "what does an `N` carry", and its answer was `Number.isFinite`. Moving the predicate into
   `attribute.ts`, the module that *is* the unrefined `𝔸`, is why one commit closed four bugs.
   **A gate mirroring a carrier refinement belongs in the module that owns the carrier**, not in
   the module that first needed it.
2. **The test asserts both sides.** `native`'s numeral gates now diverge from the AWS SDK on
   purpose, so the spec asserts that the SDK really is permissive *and* that this refuses it. A
   test that only checks our behaviour cannot tell a deliberate divergence from a regression.

### (c) The host cannot express it — owe a refusal, a test, and a written reason

`literal()` is the template. The refusal is a `CodecError` at construction, beside the other two
construction-time refusals; the test pins it; and the code says *why the type cannot carry it*, so
the next reader does not "fix" the signature and break the spread caller.

Recording the reason is the part that gets skipped and the part that matters: an unexplained gate
is indistinguishable from an un-migrated one.

---

## 3. The exception: a gate a refutation depends on stays

Imported from `codec-audit.md` §14.2, because it is the one place the discipline inverts.

`Typed.literalN`'s `hD : ∀ d ∈ ℓ, Numeral.WF d.toDec` **can** be typed —
`NEFinset {d // WF d.toDec}` is admissible. Typing it deletes
`literalN_holds_what_it_cannot_write`, the theorem exhibiting a literal that is *held* and
unwritable, which is (B) failing.

Making a bad term unconstructible stops the model from **exhibiting** the defect. For a model
whose job is to be checked rather than trusted, "this cannot be said" is weaker than "this can be
said, and here is the theorem saying why it is wrong" — the second ports to a *test* in the host,
and the first ports to nothing.

The `℘⁺fin` repair paid this cost for real: typing it destroyed the only `Double`-free witness
that `opaque`'s exactness row over-claims.

---

## 4. Corollary: measures do not port, so they are pure overhead

`codec-audit.md` §13 found that `denote`'s `fuel` is unnecessary — a structural definition
compiles. The portability reading sharpens why that matters: **no line of `src/` has a fuel
parameter.** `fuel`, `Value.depth` and `Attr.depth` are measures standing in for a recursion the
checker could not see, and they correspond to *nothing* in the implementation. The ~1400 lines
around them are modelling artifacts, not model content.

So the discipline has a hierarchy, not one rule:

1. **measure → structure.** A measure has no host counterpart at all. Deleting one costs the
   correspondence nothing and is worth an order of magnitude more than (2) on this codebase.
2. **gate → type**, where the condition is decidable from a constructor's own arguments at
   construction — *and* where the host can mirror it, or where §2(b)/(c) is paid honestly.
3. **keep the gate** where a refutation depends on it.

---

## 5. Targets differ, which is a fact about certification, not a reason to chase targets

The same Lean structure ports with different fidelity, and the target matters:

* `NEFinset α` — TS: not expressible for a variadic; Rust: a newtype with a private constructor,
  or `NonEmpty<T>`. Row 4's bug does not exist in Rust.
* `literal (k : GroundKind) (ls : NEFinset k.Carrier)` — TS: a discriminated union of literal
  types, with the base/payload pairing enforced by conditional types and easy to widen by
  accident. Rust: an enum with a distinct payload type per variant, which *is* the indexed
  family. This is the clearest case where the model's newest shape ports better than its old one.
* `Attr.n : WFNumeral` — both hosts want a newtype with a checked constructor; TS has no
  nominal typing, so the branded-type trick is the closest thing and is defeated by a cast.

Practical consequence: **a guarantee that must be a gate in TypeScript may be structural in
Rust.** §2's three cases are re-answered per target, at the time that target is certified — not
in advance, and not as a reason to shape the model around one language. The model's job is to make
the guarantee structural *in the model*; how much of it each target can carry is that target's
certification, and `codec-formalization.md` §2 is explicit that this is a separate and currently
unmet obligation.

---

## 6. Checklist

For each structural guarantee in the model:

- [ ] Which of §2's three cases is this host in?
- [ ] (a) Named the host type that carries it — no gate, no test needed.
- [ ] (b) Gate lives in the module that owns the carrier, not the first caller. One owner.
- [ ] (b) Test asserts *both* sides where the behaviour diverges from a reference implementation.
- [ ] (c) Construction-time refusal, a test, and a comment saying why the type cannot carry it.
- [ ] Does a refutation depend on this being a gate in the model? If so, §3 — leave it.
- [ ] Is it a *measure* rather than a guard? If so it has no host counterpart; see §4.

The audit's own failure mode is worth carrying into this one: §12.3 records a constraint that
failed one test ("can it be a type?") and was filed as disposed of, instead of being handed to
the test it would fail next ("does anything enforce it?"). Un-typeable never means un-checkable.
