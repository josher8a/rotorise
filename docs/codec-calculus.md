# Rotorise Codec Calculus

What a codec _is_, stated without reference to any implementation of one: a quotient
embedding-projection pair into the attribute domain, a typing judgement with two indices, and the
equations between terms.

This document is normative for the semantics, and it names no implementation of one. Every claim
below stands on the argument written beside it; nothing here is true because something elsewhere
checks it.

**It states what is true now, and carries no history.** Several rules here were corrected once a
counterexample refuted them, and one term was removed; what was claimed before, what refuted it, and
what the correction cost are in the commit history: `git log --follow docs/codec-calculus.md`,
and the messages of the commits it names. A reader of this
document should never need either to understand a rule, only to learn how it came to be one.

---

## §1 The attribute domain

Everything a table holds lives in one set. Types are read as retracts of it, which is the device
this whole specification rests on.

```
-- members, and the attribute domain over them
m  ∈ Member  ::= S | N | B | BOOL | NULL | SS | NS | BS | L | M
a  ∈ 𝔸       ::= ⟨m, v⟩        where v ∈ Carries(m)

-- an item is an M without its wrapper: the one place a map is not written as one
i  ∈ Item    ::= Name ⇀fin 𝔸
```

The coproduct is **exact**: an attribute carries one member and no other. That is a fact about the
wire format and it is load-bearing here — `⟨S, "1"⟩` and `⟨N, "1"⟩` are distinct elements of `𝔸`, so
a codec choosing between them is choosing between distinguishable things.

| Member | `Carries(m)`      |                                                                                                                       |
| ------ | ----------------- | --------------------------------------------------------------------------------------------------------------------- |
| `S`    | `String`          | not normalised                                                                                                        |
| `N`    | `Numerals`        | optional sign, digits, optional point, optional exponent; ≤ 38 significant digits; magnitude 0 or `1e-130 … 9.9…e125` |
| `B`    | `Bytes`           |                                                                                                                       |
| `BOOL` | `Bool`            |                                                                                                                       |
| `NULL` | `𝟙`               | present, and carrying nothing                                                                                         |
| `SS`   | `℘⁺fin(String)`   | non-empty; unordered                                                                                                  |
| `NS`   | `℘⁺fin(Numerals)` | non-empty; unordered                                                                                                  |
| `BS`   | `℘⁺fin(Bytes)`    | non-empty; unordered                                                                                                  |
| `L`    | `𝔸*`              | ordered; heterogeneous                                                                                                |
| `M`    | `Name ⇀fin 𝔸`     |                                                                                                                       |

`Numerals` admits an exponent — DynamoDB states its own range as `1E-130` to `9.9999…E+125`, so
`"1e+21"` is a well-formed `N` and not a defect. The bound that bites is _magnitude_, not notation.

Note where `℘` appears and where it does not. `SS` is a _set_ and `L` is a _sequence_; nothing in the
domain identifies them. Every claim later about telling a set from an array traces back to this line.

---

## §2 What a codec is

A partial retraction of the attribute domain onto a set of values, together with the equivalence its
own reading induces.

```
c = (T, μ, e, p)      T ⊆ Value     μ ∈ Member ∪ {⊤}
                      e : T ⇀ 𝔸    encode — may fail
                      p : 𝔸 ⇀ T    decode — may fail
```

`μ = ⊤` reads as _not determined by the term_, not as _anything_. Which terms may leave it
undetermined is settled in §3.

### Laws

|        |                                             |                                                                      |
| ------ | ------------------------------------------- | -------------------------------------------------------------------- |
| **R**  | `∀ t ∈ dom(e). p(e(t)) = t`                 | Retraction. Writing then reading returns the value written, exactly. |
| **C**  | `∀ a ∈ dom(p). p(a) ∈ dom(e)`               | Canonizability. Whatever was read can be written back.               |
| **W**  | `μ ≠ ⊤ ⟹ ∀ t ∈ dom(e). e(t) = ⟨μ, _⟩`       | A term that names its member writes that member and no other.        |
| **MP** | `∀ a ∈ dom(p). member(e(p(a))) = member(a)` | Reading and writing back never changes a stored member.              |

The four are independent, and **(MP)** is well defined only because **(C)** holds — `e(p(a))` is an
attribute at all because everything readable re-encodes. One term is exempt from **(MP)** and only
one: `legacy`, whose entire purpose is to change what is stored (§3, §6) — and since **(MP)** is
recursive, a term _containing_ a `legacy` inherits the exemption on exactly the attributes the
migration rereads, and on no others. Nothing is exempt from the other three.

Only **(R)** is an equality on the nose. Taken as one, `e ∘ p = id` is _false_ and must be: digits have
a normal form, so writing back what was read is free to normalise it, and a schema may discard names
it does not declare. In the language of quotient lenses [1] `e ∘ p` is a
**canonizer** — total on `dom(p)` by **(C)** — and the equivalence it works modulo is not a parameter
a programmer chooses: it is `ker p`, forced by the reading itself. Write `a ≈c a′ ⟺ p(a) = p(a′)`.

### Corollary (Q — stability)

`∀ a ∈ dom(p). e(p(a)) ≈c a`.

_Proof._ By **(C)**, `p(a) ∈ dom(e)`. Put `t = p(a)`. By **(R)**, `p(e(t)) = t`. Substituting,
`p(e(p(a))) = p(a)`, which is `e(p(a)) ≈c a` by definition of `≈c`. ∎

So stability is retraction asked at a different _source of values_: **(R)** at values a generator
produced, **(Q)** at values a table returned. Both are worth checking, because what **(Q)** adds to
**(R)** is exactly **(C)** — and that containment is the thing most likely to be untrue.

### Corollary (read-side W)

`μ ≠ ⊤ ⟹ ∀ a ∈ dom(p). member(a) = μ`.

_Proof._ `p(a) ∈ dom(e)` by **(C)**, so `e(p(a)) = ⟨μ, _⟩` by **(W)**, and
`member(a) = member(e(p(a))) = μ` by **(MP)**. ∎

**(W)** constrains only the writing half; this corollary is what makes the reading half follow. A
`⇝ S` term does not merely write `S` — it _accepts_ nothing else, or a read-modify-write could
smuggle a member change through. `legacy` is precisely the sanctioned violation: it reads members the
current encoding no longer writes, and re-encoding them is the migration.

**(MP)** binds hardest where `μ = ⊤`. A term with a `μ` is pinned by **(W)** and the corollary above;
a term without one chooses per value, and **(R)** and **(Q)** do not stop it choosing differently on
the way back. A codec reading `⟨N, "1.5"⟩` to a string and writing `⟨S, "1.5"⟩` satisfies both — the
_value_ survives — while silently changing the stored type, so a numeric sort key stops ordering and a
typed index rejects the write. It holds per attribute and recursively: a member change three levels
inside an `M` is the same failure.

This is why `opaque` refuses `N` by default. Its refusal is **(MP)**, and §2 without it could not say
so.

Write `Can(c) = e[T]` for the **canonical** attributes: those a codec will actually produce. `e ∘ p`
is then the canonizer, mapping any readable attribute to the canonical representative of its class. A
codec is total on `Can(c)` and merely partial on `𝔸`, which is the precise sense in which a table is
more permissive than the schema describing it.

### What a codec ideally is

Those pieces assemble into something simpler than the four laws suggest, and it is worth stating
because it says where the complexity actually lives.

**Between `dom(e)` and `Can(c)`, a codec is a bijection.** `p ∘ e = id` there is **(R)**; `e ∘ p = id`
there follows from it, since a canonical attribute is `e(t)` for some `t` and **(R)** sends it back
to that `t`; and `e` is injective for the same reason. No quotient, no partiality, nothing to
choose. On that part a codec is a plain isomorphism between a set of values and a set of attributes,
and there is nothing further to say about it.

Everything else in §2 is one of exactly **two extensions** of that bijection, in the two directions
it can be extended:

|                 | extension                             | what it buys                                                    | the law that governs it |
| --------------- | ------------------------------------- | --------------------------------------------------------------- | ----------------------- |
| **quotient**    | `dom(p) ⊇ Can(c)`, strictly           | reading back what the store hands you, not only what you wrote  | **(C)**, and `≈c`       |
| **partiality**  | `dom(e) ⊆ T`, `dom(p) ⊊ 𝔸`            | refusing values and attributes that are not yours               | the domains themselves  |

So `e ∘ p = id` being false is not a defect of the pair, and not a weakening of the iso. It is the
first extension, seen from outside: on `Can(c)` the equation _does_ hold, and off it the canonizer
maps each class to its representative. The literature has a name for each — quotient lenses [1] for
the first, partial isomorphisms [2] for the second — and this calculus needs both, which is why
neither reference alone is the right one.

The same two relaxations reappear one level up, in the terms rather than in the pair: §3's `held` is
an iso and `refine` its prism, and §6's `legacy(c, r) ≈ c` on `Can(c)` is the quotient again at the
term level. That is not a coincidence but it is not a theorem either — the algebra that builds
codecs relaxes an iso in the two ways a codec itself does.

### When the deviations vanish

Both extensions can be driven to zero, and asking what it takes is the cleanest way to see what
each one is really for. They do not have the same answer, and in this calculus they cannot be
answered at once.

**The quotient collapses** when `ker p` is equality — when no two distinct attributes read to one
value. That fails for exactly two reasons, and one of them is about the medium:

- **`η` normalises `N`** (§3). This is the medium, and it is the calculus's one concession to
  something it does not model.
- **`drop` discards undeclared names** (§4). This is a schema's own decision, taken deliberately.

So a codec collapses the quotient by holding no set, reading no normalised numeral, and declaring
every name it means to keep. `decimal` is the witness that this is reachable: its `ker p` is
equality, which is precisely why its held set had to be narrowed to `Stored`.

**Partiality collapses** when `dom(p) = 𝔸` — when every attribute the domain admits is one this
codec reads. And here the answer is structural rather than a matter of care: **§1 fixes one `𝔸`
for many `T`.** A table holds items of several schemas; a codec is a retract of the domain, not a
description of it. So partiality is not a tax on textual representation, and no choice of format
removes it. It is the price of the domain being _shared_ — and it would be paid identically by a
free algebra, a fixed-width binary layout, or a memory image, as long as more than one `T` lives in
one `𝔸`. What removes it is one schema per store, which is a different architecture rather than a
better encoding.

**They do not collapse together.** `decimal` kills the quotient and keeps partiality; `opaque(lossy)`
comes closest to reading all of `𝔸` and keeps the quotient, since its `N` option reads through the
numeral-to-double reading. No term of this calculus has both at once, and §1 is why.

One deviation _does_ have a clean term-level answer, and it is worth separating from the other two
because it is often mistaken for them. Ambiguity in a `union` is not a property of the medium at
all — it is what happens when a choice is written without a tag. `(dunion)` is the tagged case, and
its **(U)** is a theorem rather than an obligation (§5). Whatever the storage looks like, that
collapse is available by declaring the discriminator.

---

## §3 The judgement

Two indices, because a codec has two sides: the values it holds, and the member it stores them in.
Both are needed, and neither determines the other.

```
⊢ c : T ⇝ μ        c holds T, and stores it as μ
```

### Ground terms

```
──────────────────────────────           ──────────────────────────────
⊢ string : String ⇝ S      (string)      ⊢ decimal : Stored ⇝ N (decimal)

D = { x ∈ Double : x = 0 ∨ 1e-130 ≤ |x| ≤ 9.9…e125 }
────────────────────────────────────────────────────── (number)
⊢ number : D ⇝ N

──────────────────────────────
⊢ boolean : Bool ⇝ BOOL    (boolean)

──────────────────────────────
⊢ binary : Bytes ⇝ B       (binary)

──────────────────────────────
⊢ null : {null} ⇝ NULL     (null)

⊢ g : T ⇝ μ,  g ground    ℓ₁ … ℓₙ ∈ T,  n ≥ 1,  pairwise distinct
───────────────────────────────────────────────────────────────── (literal)
⊢ literal(ℓ₁ … ℓₙ) : {ℓ₁ … ℓₙ} ⇝ μ
```

`number` is **not** restricted to integers, and not to `2⁵³`. Every finite double satisfies **(R)**,
because `String` on a double is by definition the shortest text reading back as that same double — so
`1.5` round-trips, and so does `2⁵³ + 1`, which _is_ `2⁵³` and round-trips as that. What bounds `D` is
DynamoDB's magnitude range: at most 38 significant digits, and magnitude zero or `1e-130 … 9.9…e125`.

`D` is **checked**, on both rules that write an `N` from a double. A term that writes an attribute
outside §1's `𝔸` is not a term of this calculus, so the bound cannot be a precondition recorded and
left to the service.

The two rules check it in the two different places their admissible sets live. `(number)` gates
**both halves**: `e` on the text the double is written as, and `p` on the double the text reads
back to, which is not redundant — a numeral the store holds can read back as a double past the
maximum, and gating only the write is the configuration that breaks **(C)**.

Both-halves gating is not an extra duty these rules carry; it is what a gate _is_ in this calculus.
A predicate checked on the way in and on the way out is `refine`, and both number rules are `refine`
— `number` at `D`, `decimal` at `Stored`. Neither base is an *ungated* one, and neither can be: with
the `N` carrier typed, an ungated numeric codec would have to write an attribute the domain has no
point for. `number` is itself the base on the double side, because §1's `Numerals` is the whole of
`Carries(N)`; `decimal`'s base is the numerals gated at well-formedness, which is the largest
decimal codec the carrier permits. Nothing about them is bespoke, and
the shape is the argument: an ad-hoc `if` can gate one half and a `refine` cannot. `(literal)` gates
at the **declaration**, alongside `n ≥ 1` and pairwise distinctness, because `ℓ` is data the term
owns and a premise on data is decidable when the codec is built.

That premise discharges the **write** side and only the write side: `ℓ` is fixed when the codec is
built, so every value `e` will ever accept has been checked already. It discharges nothing on the
read side. Reading an `N` as a value is wider than membership in `ℓ`, so an attribute that is not a
numeral at all can land on a value the set contains, and the check passes on something §1 has no
point for. **A premise bounds the values a term owns, and a stored attribute is not one of them.**
So a numeric `literal` reads through the same gate as `(number)`, and gets it from the same place:
its base **is** `number`, and `ℓ ⊆ T` is the rule's premise, so the stored text must be a numeral
before it is read as a value.

A subset of `D` chosen by the caller — a numeric enum member — is `refine(number, T)`, and has no
rule of its own because it needs none. A term whose `p` returned the double it read *without*
verifying membership in `T` would break **(C)**, and with it the claim that `: T` says anything; a
term that does verify is `refine(number, T)` on all four fields. An unchecked narrowing of a read is
a cast, and a cast belongs to `refine` — which does
the check — or to `held`, which is where the caller's own functions live.

`decimal` holds numerals, not a machine number. That is the one ground term whose held set is chosen
against the grain of the host language, and the reason is in the table in §1: `N` carries 38
significant digits and a double carries 15.

Its held set is `Stored`, and not §1's `Numerals`, because those are **different sets**. `Numerals`
is what the store *accepts*; `Stored` is what it *hands back*. DynamoDB normalises every `N` it
takes — `1.500` becomes `1.5`, `007` becomes `7`, `1e5` becomes `100000`, `-0` becomes `0` — and
`decimal`'s `p` is the identity on the digits, so anything outside the normal form is written as one
string and read as another.

This is the calculus's one concession to something it does not model. §2 composes `e` and `p`
directly; in use there is a store between them, and it is not the identity on attributes. Writing
`η` for the store's normalisation, a codec survives the round trip through it exactly when **`η`
lies inside `ker p`** — `≈c` of §2, the relation that already exists for "a different attribute
reading to the same value". `number` satisfies that for free, since `p(1.500)` and `p(1.5)` are the
same double; `decimal` cannot, because its `ker p` is equality. So the held set is narrowed to the
fixed points of `η`, which is what `Stored` is. `η` is observed, not stipulated: it is the store's
behaviour, and the calculus can only be arranged around it.

### A ground term either takes its member whole, or it is a refinement

Read the ground terms together and they fall into two kinds, with nothing in between. `string`,
`boolean`, `binary` and `null` take their member's carrier **whole** — every string is a `String`,
every bool a `Bool` — and there is nothing for them to check. The other four want a _subset_ of what
the store will hold at that member, and each is `refine` over one of those bases at the predicate
that names the subset:

| term            | base                | predicate     |
| --------------- | ------------------- | ------------- |
| `number`        | §1's `Numerals`     | `D` (§1)      |
| `decimal`       | numerals at `WF`    | `Stored` (§1) |
| `literal(g, ℓ)` | the ground term `g` | `∈ ℓ`         |

This is not a resemblance. A predicate wanted on **both** halves _is_ `refine`, because `e` and `p`
are partial and refusing is what the error channel does; a rule that gates one half and not the
other is the shape §3 spends a paragraph refusing at `(number)`. So a gate is never a rule's private
business, and its predicate belongs in `adm` — which is why the table in §5 now carries `D` and
`Stored` beside a literal's `ℓ`, and why `number` and `decimal` are `ident`: gating both ways is
deciding your own membership.

**Containers are the other kind, and they are not refinements.** `set`, `array`, `tuple`, `record`
and `object` narrow by their _subterms_ and their _names_, never by a predicate on the whole value,
so there is no `q` for `adm` to carry. §5 records the same fact from the other side: `adm` does not
propagate through a container, because it would have to contain the empty array whatever the element
is. Scalars are refined by predicates; containers are refined structurally, and only the first kind
has a gate to record.

`literal` is the one ground term whose member follows from its _values_ rather than from its name,
and the rule says so by reading both off a base: `ℓ` must lie in some ground term's held set, and
what that term stores is what the literal stores. One rule covers `S` and `N`, and covers `BOOL`,
`B` and `NULL` with nothing added — a boolean literal is `literal(true)`, at base `boolean`. The
base is determined by `ℓ`'s kind, `string` being the base for strings; `decimal` is what to write
when strings are wanted stored as `N`.

The rule is also not doing anything `refine` does not, and it is worth seeing why so that `literal`
reads as the abbreviation it is. `literal(ℓ)` is `refine(g, ∈ ℓ)`, and the general fact behind every
literal union is one statement rather than a rule per member:

> For **any derivable base**, a union of refinements with pairwise disjoint predicates admits
> uniquely on both sides.

`literal` at `string` and at `number` are two instantiations; `boolean` and `binary` are two more;
and the base need not be ground at all — two disjoint refinements of one `array(string)` separate by
the same argument. "Literal" was never the operative word — _one base, disjoint predicates_ was.
What `literal` adds over writing `refine` is that `ℓ` is data the term owns, so `adm` and `admA`
carry it (§5) and a reader sees the enumeration.

There is deliberately no derivation for a mixed set: a codec writes one member, and one `g` cannot
hold both a string and a double, so `literal(ℓ, k)` with `ℓ ∈ String` and `k ∈ D` has none. That is **(W)** and not an omission, and it is not
a limitation either — the spelling is `union(literal(ℓ), literal(k))`, whose options separate on
both sides for free, by distinct members on the readable one and disjoint kinds on the writable.
What the union concludes is `⊤`, which is the honest index for a term that writes two members. That is
what makes this the term for an enum indexed by number — the held set is the literal union and the
stored member is `N`, checked in both directions — and note that `⇝ N` carries `Numerals` on the wire
while the held set is numeric, so `(R)` obliges the reading to return the number and not its text.

### Containers

`(set)`'s premise line is **an index**, not a hypothesis. It read `⊢ c : T ⇝ μ` together with
`μ ∈ {S, N, B}`, and that second premise was the whole content: the member test was partial, so the
constructor accepted element terms the rule then refused — `set(union(string, boolean))` was the
standing witness. Four element terms survive it, so `SetBase` is those four, `b.held` and
`b.member` are functions of the index, and the refusal is a type error. **Four bases onto three wire
members**: `number` and `decimal` both store `NS` and are not the same base, one being the caller's
platform number and the other the host-independent spelling.

What that gives up, deliberately: `set(refine(b, q))` and `set(literal(…))` are **not** lost — a
restriction of the elements is a restriction of the set, which is `setCodec_restrict` — but
`set(held(…))` and `set(legacy(…))` are, having no set-level spelling and no appearance in any
schema.

```
b ∈ {string, number, decimal, binary}
─────────────────────────────────────── (set)
⊢ set(b) : ℘⁺fin(b.held) ⇝ b.member

⊢ c : T ⇝ μ                          ⊢ cᵢ : Tᵢ ⇝ μᵢ    i ∈ 1…n
──────────────────────── (array)     ───────────────────────────────────── (tuple)
⊢ array(c) : T* ⇝ L                  ⊢ tuple(c₁ … cₙ) : T₁ × … × Tₙ ⇝ L

⊢ cᵢ : Tᵢ ⇝ μᵢ  (i ∈ 1…n)    ⊢ c : T ⇝ μ
───────────────────────────────────────────────────────── (tuple-tail)
⊢ tuple(c₁ … cₙ, rest(c)) : T₁ × … × Tₙ × T* ⇝ L

⊢ c : T ⇝ μ
──────────────────────────────── (record)
⊢ record(c) : Name ⇀fin T ⇝ M
```

`rest` has no rule of its own, which is the point: it is not a term but a _position marker_, like
`optional` in §4. It appears only in the premise of `(tuple-tail)`, and once — so
`tuple(rest(c), c′)` and `tuple(rest(c), rest(c′))` have no derivation, and neither does
`array(rest(c))` nor a `rest` in any position §4 or §5 admits. A list is already every element; a map
has names and not positions.

The premise on `set` is the whole reason `μ` has to be an index and not an afterthought. A set's
member is _computed_ from its element's, so an element that does not name one names no set — and the
rule refuses it rather than a runtime check discovering it. Nothing else in the calculus reads its
subterm's member this way.

### Wrappers

```
⊢ c : I ⇝ μ    f : T → I    g : I → T    g ∘ f = id_T    f ∘ g = id_I
─────────────────────────────────────────────────────────────────────── (held)
⊢ held(c, f, g) : T ⇝ μ

⊢ c : T ⇝ μ    q ⊆ T
──────────────────────── (refine)
⊢ refine(c, q) : q ⇝ μ

⊢ c : T ⇝ μ    r : 𝔸 ⇀ T    ran(r) ⊆ dom(e)    a ∈ dom(r) ∩ dom(p) ⟹ r(a) = p(a)
──────────────────────────────────────────────────────────────────────────────────── (legacy)
⊢ legacy(c, r) : T ⇝ μ

⊢ c : T ⇝ μ
──────────────────────── (nullable)
⊢ nullable(c) : T + 𝟙 ⇝ ⊤

γ : 𝟙 → Codec    ⊢ γ(∗) : T ⇝ μ
─────────────────────────────── (lazy)
⊢ lazy(γ) : T ⇝ ⊤

e : T ⇀ 𝔸    p : 𝔸 ⇀ T    (R), (C), (MP) hold of (e, p)
───────────────────────────────────────────────────────── (custom)
⊢ custom(e, p) : T ⇝ ⊤

ν ∈ {refuse, lossy}
─────────────────────────── (opaque)
⊢ opaque(ν) : Uν ⇝ ⊤
```

These `⊤`s are forced for different reasons, and the distinction matters. `nullable` writes `μ` or
`NULL` and so names neither — and it is idempotent: the value language has one null, so the second
`𝟙` in `T + 𝟙 + 𝟙` is one nothing can inhabit distinctly, and `nullable(nullable(c)) ≡ nullable(c)`
(§6). `lazy` could be asked but answering would force the thunk, which is the recursion it exists to
break. `custom` is a pair of opaque functions and there is nothing to ask — which is also why its
premise is the laws themselves: nothing structural guarantees them, so the rule demands them.
Demanding **(R)** alone would under-demand, deriving a `⊤` term free to change stored members — the
exact term §2's argument for `opaque` says cannot exist. (**(W)** is vacuous at `⊤`, so the three
named are the whole obligation.)

`opaque` is the custom-class term the calculus ships, and it is primitive only in presentation: it
unfolds to the **union of everything self-identifying, closed under the containers** — a fixpoint of shape
`union(string, boolean, binary, ⟨NULL⟩, number?, set(opaque), array(opaque), record(opaque))` —
whose **(U)** holds because the options' kinds and members are pairwise disjoint. `Uν` is _defined_
as the values whose member is recoverable from the value alone, so **(R)** holds by construction;
what `ν` decides is `N`, the one member a bare value cannot answer for, and the fixpoint reading
gives the policy its sharpest statement: **`refuse` is the absence of the `number` option.** Nothing
is guessed, because there is nothing present to guess with. Under `lossy` the option is present and
`number ⇄ N`: the member survives every read-modify-write, and the digits survive only while they
fit a double.

`held` and `refine` are the same shape at different strengths: an **iso** and a **prism**. The
literature collapses them — invertible syntax descriptions [2] builds everything from an algebra of
partial isomorphisms, which is exactly the merged combinator.

They really are one term, and it is worth being exact about the sense. Write the merged combinator
as an adapter that may refuse on either half — `f` in front of the writing, `g` behind the reading:

```
e = λv. f(v) ⨾ e_c        p = λa. p_c(a) ⨾ g
```

`held(c, f, g)` is that with both halves **total**, and `refine(c, q)` is that with a **partial
identity** on both halves — refuse off `q`, pass through on it. The pairs agree on the nose, not up
to anything. So `refine` is not a second kind of adapter; it is the one adapter with a weaker
premise, and its whole content is that refusing _is_ available, because `e` and `p` are partial to
begin with.

They are kept apart for a reason outside the calculus, and only that one: a total `g` lets a
generator for `I` be pushed forward to one for `T`, while a partial one leaves only rejection
sampling. Same term, different search. The split is a note about testing, written into the syntax
so it cannot be lost — which is the same bargain `nullable` strikes with `union(c, null)`, and
should be read the same way.

`legacy`'s `r` is a bare partial map and not a codec, because only one direction is ever used: the
rule writes through `c` whatever it read through. Asking for a codec would ask for a half that cannot
be called, and would _force_ one wherever the older encoding's held set differs. The two side
premises are the soundness proof's levies (§5). `ran(r) ⊆ dom(e)` is **(C)**'s: a migration must
land on values the current encoding can write, or the read succeeds and the write-back is the
failure. The **coherence** premise — `r` agrees with `p` wherever both are defined — is what makes
`legacy` a migration and not a disguise: without it the term is a union with a privileged write
path, resolved by a precedence between its two readings, which is precisely the resolution order
**(U)** exists to refuse. With it, `p ∪ r` is a plain union of partial maps, nothing is privileged,
and a migrated row behaves _by law_ like a current one at the surface — how the migration achieves
that is the migration's duty, but that it must is the calculus's.

`nullable` carries **no side premise**, and that is worth stating because it once carried two. The
danger is real — a subterm moving `null` onto another member, or another member onto `null`, would
let the wrapper's `NULL` branch shadow a real value, failing **(R)** in one direction and **(MP)**
in the other — and the fix is not a premise but the wrapper's own definition. `nullable(c)` adds the
null point **unless `c` already owns it**, asked of both halves at once:

```
owns(c)  ⟺  null ∈ dom(e_c)  ∨  ⟨NULL, ∗⟩ ∈ dom(p_c)
```

Where `owns(c)`, the pair is `c`'s untouched. Where it does not, `c` reaches neither end of the null
point, and then **null-honesty is a theorem rather than an assumption**: if `e_c` wrote
`⟨NULL, ∗⟩`, **(R)** would make `p_c` read it straight back, and `owns(c)` would hold; if `p_c` read
some attribute to `null`, **(C)** would make `e_c` write the point, and `owns(c)` would hold again.
Both hypotheses are refuted, not required.

The guard must be **joint**. Asked per side, `c` could decline to write `null` while still reading
`⟨NULL, ∗⟩` — the null point's two ends would belong to different options, the round trip would go
out through one and back through the other, and **(R)** would break with nothing looking ambiguous
on either side taken alone.

None of this is a new kind of condition. `nullable(c)` is structurally the two-option union
`union(c, ⟨NULL⟩-point)`, the honesty conditions were exactly that pair's §5 side conditions —
uniqueness of admission on the way in, on the way out — and the guard is what makes them hold
instead of demanding that they do.

`(null)` above makes `union(c, null)` a term, so both spellings exist — and the relation between
them is a **dichotomy**, not a trade-off. It is now the wrapper's definition rather than a result
about it:

- where `c` does not touch the null point — `e_c(null)` and `p_c(⟨NULL, ∗⟩)` both undefined —
  `nullable(c)` and `union(c, null)` are the **same codec**;
- where `c` does touch it, `nullable(c)` is **equal to `c`**: the wrapper adds
  nothing. `nullable(opaque) = opaque`, `nullable(nullable(c)) = nullable(c)` — §6's idempotence
  row as an equation — and `nullable(union(…, null)) = union(…, null)`.

So `nullable` is either the union or the identity, and the precedence that distinguishes it buys
nothing a schema would want. (The two are also `≡` unconditionally; they
differ as codecs only in definedness, and only where the wrapper is redundant. The single term
outside both readings is `nullable(null)` — member `⊤` over the `NULL` point, of no use.)

Which settles what `nullable` is: **sugar** — idempotent insertion of the null option into a pair
that may already have it. It expresses nothing new, it costs no premise, and its idempotence is a
property of insertion rather than a fact about `𝟙`. The one term outside both branches of the
dichotomy is `nullable(null)`, which under the guard is simply `null`.

It is kept as a term for compatibility, and **not** because `union(c, null)` cannot replace it at
a `κ = ⊤` subterm — `held`, `custom`, `lazy`. It can: no discharger means an **obligation**, not a
refusal (§5), so `union(c, null)` is derivable there and carries **(U)** per input, which is what
`nullable`'s honesty premises were doing by hand.

---

## §4 Fields are not codecs

A second judgement, and the stratification is the point: presence is a property of a name binding,
never of an attribute.

```
⊢ f : T ⊗ π ⇝ μ    π ∈ {req, opt}     f holds T, with presence π, stored as μ
```

A field carries a member like anything else — an optional attribute is still stored somewhere, and
`Encoded` and every index key need to know where. What a field carries that an attribute does not is
the `⊗ π`, and that is the whole stratification: a rule demanding `⊢ c : T ⇝ μ` cannot be given
something whose judgement has a `⊗`.

```
⊢ c : T ⇝ μ                    ⊢ c : T ⇝ μ
────────────────── (field)     ────────────────────────────── (optional)
⊢ c : T ⊗ req ⇝ μ              ⊢ optional(c) : T ⊗ opt ⇝ μ

⊢ c : T ⇝ μ    v : 𝟙 → T    v(∗) ∈ dom(e)
────────────────────────────────────────────── (fallback)
⊢ fallback(c, v) : T ⊗ req ⇝ μ

⊢ fᵢ : Tᵢ ⊗ πᵢ  (i ∈ 1…n)    n₁ … nₙ distinct    ⊢ ρ : rest
───────────────────────────────────────────────────────────────────────── (object)
⊢ object({n₁ : f₁ … nₙ : fₙ}, ρ) : ⟨n₁ :^π₁ T₁ … nₙ :^πₙ Tₙ⟩ ⊕ R(ρ) ⇝ M

────────────────────────────────────────────────────────── (rest)
⊢ ρ : rest  ⟸  ρ = drop | ρ = refuse | ⊢ ρ : T ⇝ μ
```

Here `n :^opt T` is a binding the record may omit, `n :^req T` one it may not, and `R(ρ)` is the open
part: `∅` for `drop` and `refuse`, and `Name ⇀fin T` for a rest codec holding `T`. The two string
policies differ only in what `p` does with an undeclared name — drop it, or fail — which is a
difference in `dom(p)` and not in `T`. And `drop` is a **filter, never a traversal mode**: the
discard is decided by the name alone, before anything is decoded, so it cannot depend on a value and
the round trip through the declared names is untouched by what was discarded. That is the quotient
of §2 again — an item is `≈c` itself minus its undeclared names — and, now that `SS`/`NS`/`BS` carry
no ordering to lose, one of only two places `ker p` is not equality. The other is `η`.

### The stratification does work

No rule derives `⊢ optional(c) : T ⇝ μ`. Presence lives in `⊗ π` and nowhere else, so `optional` and
`fallback` are fields and never attributes — which makes `array(optional(c))` **not derivable**, since
`array`'s premise is an attribute judgement. Nor `set`, `tuple`, `record`, nor a union option, for the
same reason: none of those positions has a name for anything to be absent from.

Note also that `fallback` concludes `req`. It is not a weaker `optional`: it is a _total_ field whose
`p` is defined on rows that omit the name. The absence is in the row, never in the value.
`v(∗) ∈ dom(e)` is the soundness proof's levy (§5): a row omitting the name reads to the stand-in,
so the stand-in must be writable, or **(C)** fails at the one input the term exists to serve.

And a marker marks **once**. Both `(optional)` and `(fallback)` take an _attribute_ premise, so
`optional(optional(c))`, `optional(fallback(c, v))` and `fallback(optional(c), v)` have no derivation.
That is not tidiness: only the outermost mark was ever read, so `optional(fallback(c, v))` dropped the
stand-in and left the attribute simply absent, while `fallback(optional(c), v)` stood in on the way out
and then _required_ the value on the way back. Both spellings mean `fallback(c, v)`.

---

## §5 Choice, and its side conditions

The rules a grammar cannot state, because they relate siblings rather than a term to its subterms —
and, before them, the one semantic condition even the judgement cannot decide, which everything else
in this section exists to approximate.

### Unique admission

A union's pair is defined by **unique admission**. Each option answers, per input and per side,
whether the input could be its — an attribute on the way out, a value on the way in — and the union
acts through the option that answers alone:

|       |                                                              |                                                                                                                       |
| ----- | ------------------------------------------------------------ | ----------------------------------------------------------------------------------------------------------------------- |
| **U** | resolving one side alone resolves the other, the same option | Asked where the union *acts*: at each value it writes, and each attribute it reads. Ambiguity is a failure, never a rank. |

Read **(U)** carefully, because the scope is the whole content. `∣{i : cᵢ admits it}∣ = 1` at
*every* input would be a stronger demand, and a wrong one: where two options both admit, the union
is simply undefined, and a law quantified over `dom` cannot reach an input the pair declines. What
the laws need is that ambiguity never appears *on the far side of a round trip the union did take* —
`e(t)` unambiguous on the way out obliges `e(t)` to be unambiguous on the way back. An input the
union refuses outright asks nothing of anyone.

The difference is not idle, and it is where working schemas sit.
`union(array(literal("A")), array(literal("B")))` has both options admitting `[]`, so it declines to
write the empty array — but every value it does write is read back by the one option that wrote it.
Under the stronger reading the union is refused; under this one it is lawful, minus the empty case.

Declaration order is never consulted — which is what puts commutativity in §6, and why `legacy`'s
coherence premise (§3) matters beyond `legacy`: a precedence between readings anywhere in the
calculus would be a union resolved by rank, exactly what **(U)** refuses.

**(U)** quantifies over inputs, so it is not decidable at the declaration in general. The rest of
this section is its **dischargers** — decidable conditions, each sufficient for **(U)** on the
unions it covers:

| Discharger                                         | Decides                                               | From                          |
| -------------------------------------------------- | ----------------------------------------------------- | ----------------------------- |
| distinct members, or disjoint `admA`               | the readable side, where the stored attributes differ | `μ`, and `admA` below         |
| **(K)** — disjoint kinds, or disjoint `ident` sets | the writable side, where the runtime shapes differ    | `κ`, `ident` and `adm`, below |
| tag disjointness                                   | `(dunion)`, outright — both sides                     | the discriminator literals    |
| disjoint predicates over one base                  | refinements of a common `c`, outright — both sides    | the predicates `q`            |
| kind disjointness                                  | `opaque`'s fixpoint (§3), outright                    | one option per kind of §1     |

**Every row is one condition at a different projection.** Fix a partial map from inputs to labels —
a stored member, a runtime kind, a discriminator's tag — and give each option the set of labels it
answers to. Where those sets are pairwise disjoint, no input can reach two options, because the
label is a property of the _input_ and lands in at most one set. That is the whole argument.

Said more directly, without projections at all: **each option gets one set of values it may write
and one set of attributes it may read, and separation is disjointness of those two families.** A
projection is a way of _building_ such a set — `κ` gives the values whose kind it allows, `μ` the
attributes whose member it allows, a discriminator's tag the items carrying one of its tags — and
`adm`/`admA` are the sets themselves, the finest the table has.

Read that way the first two rows stop offering a _choice_. "Disjoint kinds **or** disjoint `adm`" is
a pairwise question; asked per option instead, the two constraints simply **intersect** — an option
may write `v` only if `κ` allows its kind _and_ `adm` allows the value. Disjointness of the
intersections follows from disjointness in either constraint, so the disjunction is what makes the
families disjoint, not a second mechanism. The two families are also independent, which is the point
the pairwise reading obscures: the writable side may be separated by a kind while the readable side
is separated by a member, and nothing has to reconcile the two.

What is left to distinguish the rows is one thing only: whether a row constrains _both_ families or
one. `μ` and `admA` label attributes; `κ` and `adm` label values; only a
discriminator's tag and §1's kind label both — which is exactly why only those two settle **(U)**
outright and the first two have to be combined.

Read that way, `(dunion)` below is not a second kind of sum. It is `(union)` with admission **read
off** the discriminator instead of attempted, and its `(U)` is a theorem because reading a label
off an input is something an option cannot be wrong about.

What no discharger covers stays an obligation the semantics enforces per input by failing — safe for
every law except **(R)** at a canonical attribute, and that residue is exactly what the theorem
below names. A `⊤` option is one **(K)** never separates, for the same reason it cannot be checked:
it could be anything. That costs nothing, because failing to discharge is not refusing — **(U)**
still guards each value the option is actually given.

### A weaker condition, proved and not adopted

The reading above rejects `∣{i : cᵢ admits it}∣ = 1` as too strong and settles for *undefined at the
overlap*. There is a third position between them, and it is worth recording because the model now
proves what it costs and what it buys.

**Confluent admission.** Where several options admit, require only that they **agree** — and then
act. Stated as *first-match plus an obligation*, which is what makes it usable: the rule takes the
first admitter and never compares attributes, while the obligation says the choice did not matter.
So declaration order enters the definition and leaves again as a theorem. `selectF` and
`ConfluentAt` (`Continuity.lean`) are the two halves.

It is strictly weaker than **(U)**, so strictly more total, and the case it gains is the one this
section already named as the price: `union(array(literal("A")), array(literal("B")))` writes `[]`,
because both options write `⟨L, []⟩` and the choice is inconsequential. "Lawful, minus the empty
case" loses the *minus*.

What it costs is stated as plainly. **Order-independence stops being unconditional.** Under **(U)**
commutativity is a fact about the definition — §6's `union(c₁, c₂, …) ≡ union(c₂, c₁, …)` has no
hypotheses. Under confluence it holds *given the obligation*, and a specification whose commutativity
rests on a premise is weaker as a specification, whatever it gains in totality. That trade is the
reason this is recorded here and not adopted.

And it changes what the fixpoint argument says. The non-continuity result
(`Continuity.lean`, and commit `7ed4e5e`) — *"a union whose options are genuinely
recursive has no fixpoint semantics"* — is a refutation of **counting**, not of `union`:

- `confluent_survives_the_refutation` — the recorded witness has both options writing `⟨S,"A"⟩`, so
  the weaker rule still resolves where counting collapses to `none`;
- `selectF_mono` — monotone given the obligation, which counting provably lacks;
- `selectF_continuous_list` — continuous, and in general this needs the obligation **at each
  stage** too. (`selectF_continuous`, the two-option case, escapes it by putting the growing option
  first, which makes it automatically the first admitter.) Counting's continuity *is*
  unconditional — its singleton requirement at the limit forces uniqueness at every earlier stage —
  and counting cannot be monotone at all. So one requirement, the obligation holding at every
  stage, buys both; what unique admission cannot buy at any price is monotonicity, being a
  *negative* condition on the other options.

Two things that are **not** established, and the second is why `lazy` under `union` stays
unmodelled. A fixpoint is not shown to exist — monotonicity and continuity are its obligations, not
its construction, and both theorems are the two-option case. And the obligation must hold at every
stage of an unrolling, which is not automatic: `string_decimal_not_confluent` is two *ground* terms
that both take `.str "1.5"` and store it differently. Where the options are pairwise disjoint it is
vacuous, so a syntactic disjointness test — `Orth1` and `OrthM`, `Orthogonality.lean` — is what would
license it.

**Normatively, the rule is unique admission as stated above.** This subsection records a proved
alternative and the trade, not a change to the judgement.

### The machinery of (K)

Three auxiliary functions, defined by structural recursion so that **(K)** is decidable rather than
judged. All are total over the terms of §3–§4.

`κ(c) ∈ ℘(Kind) ∪ {⊤}` is the kinds of _value_ a term accepts — a coarse partition of `Value` by
runtime shape, and the mirror of `μ` on the other side of the pair:

```
k ∈ Kind ::= string | number | boolean | binary | set | array | map | null
```

| `c`                                               | `κ(c)`                                       |
| ------------------------------------------------- | -------------------------------------------- |
| `string`, `decimal`                               | `{string}` — a decimal is _held_ as a string |
| `number`                                          | `{number}`                                   |
| `boolean` / `binary`                              | `{boolean}` / `{binary}`                     |
| `literal(ℓ₁ … ℓₙ)`                                | the kind of its base                         |
| `set(c)`                                          | `{set}`                                      |
| `array(c)`, `tuple(…)`                            | `{array}`                                    |
| `record(c)`, `object(…)`, `discriminatedUnion(…)` | `{map}`                                      |
| `null`                                            | `{null}`                                     |
| `nullable(c)`                                     | `κ(c) ∪ {null}`                              |
| `refine`, `optional`, `fallback`, `legacy`        | of the subterm                               |
| `union(c₁ … cₙ)`                                  | `⋃ κ(cᵢ)`                                    |
| `held`, `lazy`, `custom`, `opaque`                | `⊤`                                          |

`⊤` **absorbs**: wherever a row combines a subterm's answer — the pass-throughs, `nullable`'s `∪`,
`union`'s `⋃` — a subterm answering `⊤` makes the whole answer `⊤`. Not knowing part of what a term
accepts is not knowing what it accepts.

`held` is `⊤` deliberately, not by omission: an adapter exists precisely to change the kind of value
held — `held(set(string), …)` takes an array where `set(string)` takes a set — and its functions are
the caller's, so there is nothing to read an answer from. `lazy` again cannot be asked without
forcing.

`⊤` covers two situations the check treats alike and the semantics does not: **unknown** — `held`,
`lazy`, `custom`, whose answer exists but cannot be read — and **everything** — `opaque`, which
accepts every kind by design. **(K)** separates neither, and both fall to **(U)** per input. The
difference resurfaces only inside `opaque`'s own derivation, where "everything" is precisely what
makes its fixpoint's options pairwise kind-disjoint (§3).

`ident(c)` holds when a term decides its own membership — when "this option accepted the value" is
evidence, because the term checks the value against its own admissible set in **both** directions:

|            |                                                                                                                                                                                                            |
| ---------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| holds      | `literal` — the admissible set is checked; `discriminatedUnion` — a tag lookup fails honestly; `refine` — `q` is checked on the way in _and_ on the way out, which is what deciding your own membership is; `number` and `decimal`, for the same reason: each gates §1's bound on both halves; and `custom` and `opaque`, whose rows ask their own pair — a `custom`'s `T` _is_ `dom(ce)` |
| propagates | `set`, `array`, `record` through the element; `tuple` and `union` when _every_ subterm has it; `optional`, `fallback`, `legacy`, `nullable` through the subterm; and `lazy` and `held`, whose pairs *are* the subterm's — `held` applies `f` and asks it, exactly as `refine` does                                            |
| never      | everything else — the _ungated_ ground scalars `string`, `boolean`, `binary` and `null`, which accept their whole carrier and so decide nothing; and `object`, which decides, but not by attempting — see below                                                |

`object` is the other self-deciding term, and it decides by a different device: **names, not
attempts**. A name set `N` admits `object(s, ρ)` when every name in `N` is one `s` declares and every
`req`-marked name of `s` is in `N` — an `opt` binding widens admission, which makes two options
differing only in optional names the ambiguity to watch. Note what admission does _not_ read: `ρ`.
An undeclared name disqualifies the option even where its rest codec would hold it, so an object's
open part is unreachable through a union — the price of deciding by names is that only declared names
decide, and an open object that must be an option should declare what it means to keep.
`(dunion)`'s disjoint-literal premise below is the special case where the discriminator's names
decide alone.

```
⊢ cᵢ : Tᵢ ⇝ μᵢ  (i ∈ 1…n)    (D)
─────────────────────────────────────────────────────────────────── (union)
⊢ union(c₁ … cₙ) : ⋃ Tᵢ ⇝ (μ if ∀i. μᵢ = μ;  else ⊤)

⊢ oᵢ = object(sᵢ, ρᵢ) : Tᵢ ⇝ M    sᵢ(d) = literal(tᵢ)    tᵢ pairwise distinct
─────────────────────────────────────────────────────────────────────────────── (dunion)
⊢ discriminatedUnion(d, o₁ … oₙ) : ⋃ Tᵢ ⇝ M
```

Note that `(dunion)`'s premise asks `sᵢ(d)` to _be_ the literal — an attribute term, hence a `req`
field. A `fallback` around it has no derivation, and the proof says why rather than leaving it to
taste: a row omitting the discriminator would read to the fallback's stand-in, an arbitrary value
the tag sets never vouched for, and **(C)** would then re-encode a variant no tag selects.

**Arity one at the discriminator**, and n-ary literals everywhere else. The rule above read
`sᵢ(d) = literal(Lᵢ)` with `Lᵢ` a *set* of tags, pairwise disjoint; it now asks for a single tag
`tᵢ`, and disjointness of singletons is distinctness. **Nothing about the soundness of the
calculus required narrowing this**, and that is worth stating rather than leaving implicit:
`(literal)` is n-ary, a set of tags is a perfectly good admissible set, and pairwise disjointness
is exactly the condition (U) needs.

What required it is what a discriminated union *is*. It is a **lookup**: the stored tag chooses
the variant. A variant answering to two tags is a key that does not identify its variant, and a
reader who has the tag still cannot say which shape they hold without consulting the table twice.
JH's call, in his words — *"go with the middle, arity one at the discriminator only"*.

Three alternatives were declined, and each for a reason worth recording:

- **Keying the union by tag, with the discriminator injected from the key and absent from the
  variant body.** Declined for reuse and declaration flexibility: a variant would stop being an
  ordinary `object` term the user can name, reuse elsewhere and read on its own.
- **A variant helper in the implementation** to build the tagged object for you. Declined for the
  same reason, one level up — it makes the tagged shape the library's rather than the caller's.
- **Arity one for literals generally.** Declined because a set of alternatives is the natural
  spelling of an enum member and because the carrier is a `Finset`; the constraint belongs at the
  discriminator, where the lookup is, and nowhere else.

**Mechanization note, and it is a negative result.** The narrowing bought no proof simplification
whatsoever — the expectation going in was that it would. Every proof over `(dunion)` consumes only
the *nonemptiness* of the tag set (`tagsOf_ne_nil`'s four-job inversion, `dunion_stamp`,
`uniqueAdmission_byTag`, `ExactV_dunion`/`ExactA_dunion`), and none of them consults the arity. So
the premise changed from `Nonempty` to `card = 1`, one three-line bridge lemma was added to recover
the weaker fact, and the `dunion` machinery went from 39 declarations / 350 lines to 40 / 353
— the three lines being that bridge, with no proof changing length. The
constraint is a statement about the language, not a lever on the model.

|       |                                                                                |                                                                                                                                                        |
| ----- | ------------------------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------ |
| **D** | `∀ i ≠ j. ¬(Tᵢ ⊆ Tⱼ) ∧ ¬(Tⱼ ⊆ Tᵢ)`                                             | Well-formedness: no option's held set subsumes another's. Decidable from the held sets alone. It does **not** discharge the readable side — see below. |
| **K** | `∀ i ≠ j. κ(cᵢ) ∩ κ(cⱼ) = ∅ ∨ (ident(cᵢ) ∧ ident(cⱼ) ∧ adm(cᵢ) ∩ adm(cⱼ) = ∅)` | Writable: no value belongs to two options. A **discharger**, not a premise — it settles **(U)**'s writable side at the declaration where it holds, and where it fails the obligation stands. Needs `κ`, which the held sets do not determine. |

Only **(D)** is a premise. **(K)** is the writable side's discharger, and the asymmetry is not an
oversight: **(D)** is a condition on the judgement's own index, so the rule can demand it, while
**(K)** answers a question about inputs that the rule states as **(U)** and settles where it can.
A union no discharger covers is still a term — `union(array(literal("A")), array(literal("B")))`
and its `record` twin are ones people write — and what such a union lacks is not derivability but
the theorem: its **(U)** is unsettled at the declaration, and the semantics enforces it per input by
failing. Note where the failing lands. `adm` does not propagate through a container (below), so the
options collide at exactly one input — the empty array, the empty map — which is also the one input
neither writes nor reads once they collide, so the loss is that the union declines the empty case
and nothing else. The same union built from `object`s is decided outright, by names rather than by
`adm`: a `req` binding is a name the empty item lacks, so there is no empty case to collide at.

**(D)** and **(K)** ask the same kind of question of the two sides of the pair, and neither implies
the other. `union(array(string), array(number))` satisfies **(D)** — the held sets are incomparable —
and is not discharged by **(K)**: both accept a sequence, and neither is `ident`.
`union(set(string), set(number))` is the same story with a twist worth naming: its options write
_different members_, so reading was never in doubt. Only the direction that cannot be resolved is
left to **(U)** — and it is degraded twice over, because a set's member is computed from its element, so those
options are `⇝ SS` and `⇝ NS` and the union's own `μ` is `⊤` by the `(union)` rule. That is a second,
independent loss: a `⊤` term is one only **(MP)** constrains, where a `⇝ SS` term is pinned by
**(W)** and its read-side corollary.

Why `ident` exempts a pair is the interesting half. **Encoding does not validate.** A term's `e` is
defined on `T` and does whatever it does off it, so "this option encoded the value" carries no
information about whether the value was meant for it. Only a term that knows its own membership
answers a real question when attempted — which is why **(K)** discharges
`union(literal("A"), literal("B"))` although both accept a string.

But `ident` is only half of that exemption, and **(K)** cannot be weakened to
`κ(cᵢ) ∩ κ(cⱼ) = ∅ ∨ ident(cᵢ) ∨ ident(cⱼ)`. Two counterexamples:

- **One side is not enough.** `union(literal("A"), string)` has `ident` on the left, so the disjunction
  is satisfied — and both options admit `"A"`. A real answer from one option does not resolve a pair;
  the other option is still answering, and still meaninglessly.
- **Two sides are not enough either.** `ident` propagates through `array`, so
  `union(array(literal("A")), array(literal("B")))` has it on both — and both admit `[]`. Propagating
  `ident` through a container does not propagate _disjointness_ of what the options accept: every
  container admits its empty case, which no element ever sees.

What the exemption actually needs is what the worked example above quietly has: `ident` on **both**
sides, and admissible sets that do not meet. So the third auxiliary is the set a term checks against
when `ident(c)` holds — a `literal`'s values, a `discriminatedUnion`'s tags. It is deliberately _not_
propagated through the containers: it would have to contain the empty array whatever the element is,
so container options are never separated this way and the second counterexample stays refused.

**It is two functions, not one.** A codec is a pair, and a term's admissible set is a claim about one
half of it at a time: `adm(c) ⊆ Value` is what `e` will accept, `admA(c) ⊆ 𝔸` is what `p` will
accept. They agree on most terms and part on four — and the partings go both ways.

| term                        | `adm` — value side   | `admA` — attribute side           |
| --------------------------- | -------------------- | --------------------------------- |
| `literal(ℓ)` at base `string` | `ℓ`                | `ℓ`, as stored `S`                |
| `literal(ℓ)` at base `number` | `ℓ`                | `ℓ`, one read out — `admALit`     |
| `discriminatedUnion(d, o…)` | the pooled tags of the `oᵢ`, found by looking `d` up | the same, in the stored item |
| `number`                    | `D`                  | `dom(p)`, asked of the codec      |
| `decimal`                   | `Stored`             | `Stored`, as stored `N`           |
| `refine(c, q)`              | `adm(c) ∩ q`         | `admA(c) ∩ q∘p` — `refineReads`   |
| `legacy(c, r)`              | `adm(c)`             | `admA(c) ∪ dom(r)`                |
| `union(c₁ … cₙ)`            | `⋃ adm(cᵢ)`          | `⋃ admA(cᵢ)`                      |
| `nullable(c)`               | `adm(c) ∪ {null}`    | `admA(c) ∪ {⟨NULL, ∗⟩}`           |
| `held(c, f, g)`             | `adm(c) ∘ f`         | `admA(c)`                         |
| anything else               | `⊤`                  | `⊤`                               |

**No row parts into `⊤` any more; every one of them asks its codec.** Why each row reads the way
it does is below — the reasons are the rows' content, not their history.

Each `⊤` was bought with the observation that **no syntactic set of attributes bounds the readable
side** — true of `number`, of a numeric `literal`, and of `refine`. The inference does not follow: a
row is not confined to syntax. It may **ask the denotation**, and the denotation is exactly what
produces the value in question. `admA .number` is `dom(numberCodec.p)`; `admALit .number` is
`dom((literalCodec .number ℓ).p)`; `refine`'s row decodes with the base and applies `q` to the result
(`refineReads`). Each is `dom(p)` on the nose rather than a description of it, and each was
previously recorded as impossible. `held`'s value side went the same way for a different reason: `f`
is *data the term carries*, and a row is a function that may apply it, so `adm(c) ∘ f` is the
pullback rather than a `⊤`. `legacy`'s read side is that second reason again — `r` is data the term
carries just as `f` is, so the row may ask it.

What survives is no parting into `⊤` at all, and one asymmetry of *shape* without one: `held` pulls
back along `f` where `admA` passes through, because `g` is total and post-processes while `f` gates
the write.

Row by row, and the reason in each case is a fact about the term rather than about the table:

- **`legacy(c, r)`.** The whole content of `legacy` is that `p` reads attributes `c` does not, so a
  passthrough `admA` would claim a bound on exactly the direction `r` widens. `legacy(literal("A"), r)`
  with `r` reading `⟨N, "1"⟩` to `"A"` reads an attribute `admA(literal("A"))` refuses, so the
  passthrough is **unsound**, not merely coarse. What that refutes is the passthrough and not the
  row: the attributes `r` widens by are `dom(r)`, and `r` is data the term carries, so the row asks
  it — `admA(c) ∪ dom(r)` is exactly the two directions a `legacy` reads, and neither is a guess
  about syntax. The value side is untouched: `legacy` adds no way to *write*, so `adm` passes
  through.
- **A numeric `literal`.** Its read side goes through the numeral-to-double reading of §1, which is
  not a membership test on the stored text: distinct numerals read to the same double, so a
  syntactic set of values bounds no set of attributes. This is the one place the two literal rules
  part, and the reason is §1's and not §3's: a **string** literal's stored text _is_ its value, so
  `ℓ` bounds both sides and the table separates such a union unaided; a numeric literal's is not,
  so only the value side is bounded. Both rules are otherwise the same term — `refine` over the
  ground codec of their member, at `∈ ℓ`.

  The stored texts *are* known at the declaration, so `admA = { ⟨N, text(ℓᵢ)⟩ }` looks available. It
  is not, and the store is why: `literal(10²¹)` is written `⟨N, "1e+21"⟩` and handed back
  `⟨N, "1000000000000000000000"⟩`, which only the numeral-to-double read recovers. A syntactic `admA`
  would refuse a row the codec itself wrote — `ker p` shrinking below `η`. So no _table_ row bounds a
  numeric literal's attribute side, while its value side separates as a string literal's does.

  That is a limit of the table, not of the calculus, and the difference matters because it is the
  whole shape of a numeric literal set. `number` and every numeric literal are the **same base**
  under different predicates — the base being every finite double written as its shortest text, and
  the predicates `D` and `∈ ℓ`. Two literals over disjoint value sets are therefore two refinements
  of one base, and refinements of one base read an attribute to the _same_ value, so at most one
  predicate accepts it. Both sides separate. A numeric literal union is options told apart by the
  value a read produces, never by the text the store holds — and the table cannot see it because a
  table answers about one term at a time, where this is a fact about a family sharing a base.
- **`refine(c, q)`**, which parts because `q` is a predicate on **values**. It tightens what the
  term will write — `e` is defined only where `q` holds, so `adm(c) ∩ q` is a sound bound and a
  strictly better one than passing `adm(c)` through. The reading side cannot follow: `q` tests the
  value a read _produces_, and no syntactic set of attributes bounds that. Without the intersection
  a refinement's predicate is invisible to every discharger, and two refinements of one base with
  disjoint predicates — `refine(number, positive)` against `refine(number, negative)` — fall to
  **(U)** per input despite being disjoint by construction. With it they separate on the writable
  side, which is the only side `q` can speak for.

  This is also why `refine` _holds_ `ident` rather than propagating it: a term that checks its own
  set in both directions is the definition of deciding its own membership, and §3 already argues
  the point — a `p` returning the value it read without verifying `q` would break **(C)**.

  The readable side is not lost, though it cannot be recovered from this table. Two refinements of
  **one base** read an attribute to the _same_ value, so at most one predicate accepts it, and the
  readable side separates for exactly the reason the writable side does. That is a condition on a
  _pair sharing a base_ rather than on either option's admissible set, which is why it appears in
  the discharger table above and not here: `adm` and `admA` answer about one term at a time, and
  this answer is about two.
- **`held(c, f, g)`**, and this one parts the other way — the only row where `admA` sees further
  than `adm`. An adapter gates one side only: `f` sits in front of `e`, so `adm` pulls back
  along it; `g` sits behind `p` and is total, so it changes which value comes out and never which
  attributes go in.
  `dom(p)` is the subterm's exactly, and `admA` passes through.

  What this buys is a pair no other row reaches. `union(literal("A"), held(literal("B"), f, g))`
  separates on the readable side for *every* `f` and `g` — the footprints are `{S "A"}` and
  `{S "B"}` — while `union(literal("A"), held(literal("A"), f, g))`, the counterexample below,
  still does not. The wrapper never decides; the subterm does, and reading through the wrapper is
  what lets the question be asked of it. Note that the member disjunct is no help in either case:
  both options are `⇝ S`.

A union takes the `⋃` of its options', for the same reason `κ` does: a union admits what some
option admits. Without that row the union _spelling_ of a set of literals would forget both sets
where the single n-ary term keeps them, and the two would separate differently for no reason the
semantics gives. With it they do not — which is what makes `literal(ℓ₁, ℓ₂)` and
`union(literal(ℓ₁), literal(ℓ₂))` interchangeable rather than merely equal as pairs, and so what
makes `union` an honest escape hatch rather than a lossy one.

Two notes on what is _not_ in the table. `optional` and `fallback` are **fields** (§4), not terms,
so nothing passes through them: `adm` is a function on terms and has no case to give them. And the
`⊤` default makes **(K)**'s `ident` conjuncts mostly redundant rather than decorative — two terms
whose sets are both `⊤` can never be disjoint, so disjointness already implies each side carries a
real set, which is what `ident` says. They are kept because the
recovery needs a side condition, holding only where each option admits *something*, and a derivable
term admits nothing: `discriminatedUnion(d)` with no options is disjoint from every term, including
those carrying no set at all. A stated premise is easier to check than a recovered one.

The residue of the old rule is the honest one: the pairs `ident` genuinely resolves are the pairs of
`literal`s with disjoint values, and the pairs of `discriminatedUnion`s with disjoint tags — the
latter being the tag-disjointness row of the discharger table, arrived at from the other direction.

**(D)** as written is _incomparability_, not disjointness. Two object options `⟨a : String⟩` and
`⟨b : String⟩` are incomparable yet share the inhabitant `⟨a ↦ "1", b ↦ "2"⟩` — so **(D)** admits
them, and resolution falls to the name-set device above. The gap between the two is exactly the set
of unions resolved structurally rather than by type — and **(U)** is what fills it.

Stating **(D)** as genuine _disjointness_ would not be sound either, and the reason is the same
confusion twice: **held sets are sets of values, and (U)'s readable side quantifies over
attributes.** `held`
is precisely the term that separates the two — its adapter relabels — so two options can hold
disjoint sets of values and still read one attribute, each to its own value.
`union(literal("A"), held(literal("A"), f, g))` with `f` and `g` swapping `"B"` for `"A"` holds
`{"A"}` and `{"B"}`, which are disjoint on the nose, and both options read `S "A"` — the first to
`"A"`, the second to `"B"`.

So **(D)** is a well-formedness condition on the judgement's `T` index and not a discharger of
**(U)**: no condition on held sets can be one. What decides the readable side is a condition on
_stored attributes_ — distinct members `μᵢ ≠ μⱼ`, or disjoint `admA` — which is what the first row
of the discharger table takes. `admA` rather than `adm` is the point: a condition on values cannot decide a
question about attributes.

### Theorem (soundness)

Every derivable `⊢ c : T ⇝ μ`, and every `⊢ f : T ⊗ π ⇝ μ`, denotes a pair satisfying **(R)**,
**(C)**, **(W)**, and **(MP)** in the strong form `e(p(a)) ≼ a` defined below — with two residues,
both named exactly: **(MP)** is off on the attributes a `legacy` in the derivation rereads, and
every `(union)` in the derivation carries **(U)** _where the union acts_ as an obligation, which
the dischargers of this section settle at the declaration wherever they decide a pair — `(dunion)`
and `opaque` outright.

Three premises in §3–§4 — `ran(r) ⊆ dom(e)` and coherence on `(legacy)`, `v(∗) ∈ dom(e)` on
`(fallback)` — exist because this proof failed without them. That is the theorem earning its keep:
each names a term the calculus used to derive and the laws refuse. A fourth, null-honesty on
`(nullable)`, was one of them until the wrapper's guard (§3) made it a consequence of lawfulness;
that is the better outcome, and the only one of the four available, since the other three constrain
functions the caller supplies.

**Member agreement, recursively.** §2 states **(MP)** per attribute "and recursively"; the proof
needs that as a relation. Define `a ≼ a′` by recursion on `a`:

```
a ≼ a′  ⟺  member(a) = member(a′)
           ∧  member(a) = L ⟹ pointwise ≼ on shared positions
           ∧  member(a) = M ⟹ pointwise ≼ on shared names
```

Set members compare no deeper — an `SS` carries payloads, not attributes, so there is no member
inside one to disagree on. Shared names, because a reading may drop what a writing then omits: the
discard is the quotient of §2, not a member change. The strong law is `e(p(a)) ≼ a` on `dom(p)`,
and it implies **(MP)** as stated.

**Lemma (injectivity).** **(R)** makes `e` injective on `dom(e)`: if `e(t) = e(t′)` then
`t = p(e(t)) = p(e(t′)) = t′`. ∎

**Lemma (traversal).** One proof shape serves every product. Let a _step_ be an entrywise pair
between the entries of two lists, and lift it entrywise — defined where every entry is, positions
preserved. If the step satisfies a law pointwise, the lift satisfies it listwise: **(R)** because
positions re-read in place, **(C)** because each entry re-encodes, `≼` because a shared position
decodes and re-encodes through the same step, and lengths survive both directions. Keyed products need
no extra clause: `M` is a name set with a function on it, so keys are unique by type and `≼`'s `M`
clause compares at a shared key with no first occurrence to prefer. Proved once; every product case
below is an instantiation. ∎

**Proof.** By induction on the derivation, with one refinement recorded at `(lazy)`. Each case
first says what the pair _is_ — the denotation is part of the rule — then discharges the laws. The
grouping is the algebra of §7: points, wrappers, products, sums.

**Points.** Each ground term writes one member, totally on its held set, and reads exactly that
member back into the held set. **(W)** and **(C)** are immediate, `≼` is member equality with no
substructure, and **(R)** is the carrier's round trip: identity for `string`, `boolean`, `binary`,
`null` (whose held set is the single value `null` and whose payload is `∗`) and `decimal` (a numeral
in `Stored` is returned as written, which is what `Stored` is chosen to make true, so `Can(decimal)`
is the normalised part of `N`), shortest-text for `number` and a numeric `literal` — the §3 argument that
every finite double survives.

**Wrappers.**

_held._ `e = e_c ∘ f`, `p = g ∘ p_c`. **(R)**: `g(p_c(e_c(f t))) = g(f t) = t`. **(C)**:
`e(p(a))` asks `f(g(p_c a)) = p_c a ∈ dom(e_c)`, the premise's **(C)**. `≼`:
`e(p(a)) = e_c(p_c(a))`, the premise's hypothesis. **(W)**: the member is untouched.

_refine._ `e = e_c` on `q`; `dom(p) = p_c⁻¹(q)`. All four laws restrict.

_legacy._ `e = e_c`; `p = p_c ∪ r`, a function _because_ of coherence — without that premise the
definition needs a precedence between the two readings, and a precedence is a union with a
privileged write path, the resolution order **(U)** exists to refuse. **(R)**: `e_c(t) ∈ dom(p_c)`
by the premise's **(R)**, and coherence makes any overlap with `dom(r)` agree, so the composite
reads it to `t`. **(C)**: on `dom(p_c)` by the premise; on the extension it _is_
`ran(r) ⊆ dom(e)` — without it a migrated attribute reads and the write-back is the failure.
**(W)**: unchanged. `≼`: on `dom(p_c)` by hypothesis; on the extension it is exactly what the term
is licensed to break, and no further — `e(r(a))` is canonical, so the breach does not survive its
own round trip, which is the precise sense in which a migrated row behaves like a current one from
the first rewrite on.

_nullable._ Two cases, by the guard of §3, and neither carries a premise.

Where `owns(c)`, the pair _is_ `c`'s — `e = e_c`, `p = p_c` — and all four laws are the
hypothesis, restated at a `⊤` index where **(W)** is vacuous.

Where it does not, `e`: `null ↦ ⟨NULL, ∗⟩`, else `e_c`; `p`: `⟨NULL, ∗⟩ ↦ null`, else `p_c` — and
what were the honesty premises are now available as facts. **(R)** at `null` is immediate; at
`t ≠ null`, `e_c(t) ≠ ⟨NULL, ∗⟩`, because if it were, the hypothesis's **(R)** would give
`p_c(⟨NULL, ∗⟩) = t` and `owns(c)` would hold. So the `NULL` branch cannot shadow the reading —
without the guard, `nullable(held(nullable(string), f, g))` with `f` moving a sentinel onto `null`
would encode the sentinel as `⟨NULL, ∗⟩` and read back `null`; with it, the inner `nullable` owns
the point and the outer one adds nothing. **(C)**: `⟨NULL, ∗⟩` round-trips; else `p_c(a) ≠ null`,
because if it were, the hypothesis's **(C)** would put `null` in `dom(e_c)` and `owns(c)` would
hold, so the `e_c` branch answers. `≼` at `⟨NULL, ∗⟩` is exact; elsewhere it is the hypothesis, and
what rules out a non-`NULL` attribute reading to `null` and re-encoding as `⟨NULL, ∗⟩` — the member
change **(MP)** exists to refuse — is the same fact.

`owns(nullable(c))` always, so the second case never nests: §6's idempotence is the construction,
not an equation the proof has to earn.

_custom._ The laws are the premises, verbatim; **(W)** is vacuous at `⊤`.

_lazy._ The pair of `γ(∗)`. The induction needs a word, since `γ(∗)`'s derivation may contain
`lazy(γ)` again: induct on the pair (input size, derivation size), lexicographically. Containers
strictly shrink the input; the wrappers shrink the derivation and never grow the input; and a
`lazy` that re-enters itself without passing a container defines nothing at that input — the laws
quantify over `dom`, and hold over an empty one. Partiality is doing the termination argument's
work.

**Fields.** A field denotes a pair over presence-extended domains — `e♭ : T ⇀ 𝔸 ∪ {ε}`,
`p♭ : (𝔸 ∪ {ε}) ⇀ T`, `ε` the absent binding — with `member(ε)` undefined and the laws read over
`𝔸` as before. `(field)` and `(optional)` set `e♭ = e`, `p♭ = p`; absence is handled at `(object)`,
where an `opt` name absent in the item is a binding absent in the record, which round-trips by
construction. `(fallback)` adds `p♭(ε) = v(∗)`, and **(C)** at `ε` _is_ the premise
`v(∗) ∈ dom(e)`: a row missing the name reads to the stand-in, and the stand-in must be writable.
`≼` quantifies over `𝔸`, so `ε` asks nothing — that the canonizer materialises the attribute is
quotient, not member change.

**Products** — each an instantiation of the traversal Lemma.

_array, tuple, tuple‑tail, record._ The step is the subterm's pair at each position or name — a
tuple first aligns positions with their codecs, head positionally and tail uniformly, length
mismatches refusing. The Lemma gives all four laws from the induction hypotheses; a `legacy`
element is where the **(MP)** exemption propagates — pointwise, on the positions it rereads, per
§2.

_object._ The step dispatches each entry by its name: a declared name through its field, with the
`ε`-handling of the Fields case; an undeclared name by `ρ`. `drop` is a filter _before_ the step
(§4), so it needs no traversal mode of its own; the presence guards — every `req` name demanded in
both directions, every non-`opt` binding demanded of a value — are what keep the step total where
the Lemma needs it, and `(fallback)`'s stand-ins appear only for names a row omits, so a canonical
item adds none. **(W)**: `M`. `≼`: the Lemma's keyed clause; the names `drop` discards and the
stand-ins `fallback` materialises are each on one side only, and `≼` compares shared names — the
quotient again.

_set._ The premise gives `e_c(x) = ⟨μ, w(x)⟩`; the step is `w` outward and `p_c(⟨μ, ·⟩)` back, and
the wire set is the image of the held set under it. **(R)**: `w` is injective by the injectivity Lemma (member fixed,
`e_c` injective), so the written set holds one payload per element and the traversal Lemma reads
each back; non-emptiness survives both directions. **(C)**: entrywise, and the re-encoded elements
keep their member by `≼`, so the same payload projection re-succeeds. `p` need _not_ be injective —
two payloads reading to one value shrink the set, which is the quotient again and touches **(R)**
nowhere, since canonical payloads are `w`-images. **(W)**: `μS`, always. `≼`: member equality, and
a set has no interior members — the container fixes its elements' member, which is why the
element's own **(MP)** is never even invoked inside one.

**Sums.** Admission, per side: option `i` admits attribute `a` when the member/name filter passes
and `pᵢ(a)` is defined, and admits value `t` when the `κ`/name filter passes and `eᵢ(t)` is
defined. `p(a) = pᵢ(a)` for the unique admitting `i`, else undefined; `e(t)` dually — **(U)** as
semantics rather than aspiration. The laws, and where each needs **(U)**:

- **(R)**: `t ∈ dom(e)` names a unique `i` — that is what makes `e(t)` defined at all — and `i`
  admits `eᵢ(t)` back (the premise's **(R)**); _uniqueness_ of that admission is **(U)** on the
  attribute side, asked at exactly the attributes the union writes. Where it holds,
  `p(e(t)) = pᵢ(eᵢ(t)) = t`. Partiality cannot hide this: an ambiguous `e(t)` makes `p(e(t))`
  undefined, which **(R)** counts as failure. What partiality _does_ excuse is the input the union
  never wrote: `t ∉ dom(e)` is outside **(R)**'s quantifier, so an ambiguity there costs nothing.
- **(C)**: `a ∈ dom(p)` names a unique `i`; `pᵢ(a) ∈ dom(eᵢ)` by the premise's **(C)**, so `i`
  admits it, and uniqueness is **(U)** on the value side. Where it holds, `p(a) ∈ dom(e)`.
- `≼`: with both uniquenesses the route is the _same option in both directions_ — `i` admits
  `pᵢ(a)`, so `e` goes through `i` — and the premise's hypothesis closes it.
- **(W)**: when every `μᵢ = μ`, whichever option answers writes `⟨μ, _⟩`.

The dischargers close the residue where they apply:

_dunion._ A canonical item of option `i` carries the discriminator with a tag in `Lᵢ`; option
`j ≠ i` either does not admit the name set or its literal refuses the tag, `Lⱼ` being disjoint from
`Lᵢ` — so admission is unique on both sides, and the sum case closes with no residue. The one union
whose **(U)** is a theorem, which is what the term is _for_.

_opaque._ The fixpoint of §3: one option per kind, each self-identifying by construction — kinds
partition the values and members partition the attributes — so admission is unique on both sides at
every depth of the fixpoint, and the sum case closes with no residue here either. ∎

What remains outside the theorem is exactly what §3 already names: `(custom)`'s premises are the
caller's to keep, and each `(union)`'s residual **(U)**. `D` is not among them — it is a gate on
both halves of `(number)`, and a numeric `literal`'s base *is* `number`, so it is inside the theorem.

---

## §6 Equations

Which rewrites preserve the pair. Read `≡` as: the same `T`, the same `μ`, and `e` and `p` agreeing
everywhere both are defined.

### Hold

| Equation                                                              |                                                                                                                                                                                                                               |
| --------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `held(c, id, id) ≡ c`                                                 | Identity.                                                                                                                                                                                                                     |
| `held(held(c, f, g), f′, g′) ≡ held(c, f ∘ f′, g′ ∘ g)`               | Isos compose; note the reversal on the reading half.                                                                                                                                                                          |
| `refine(refine(c, q), q′) ≡ refine(c, q ∩ q′)`                        | Prisms meet.                                                                                                                                                                                                                  |
| `refine(c, T) ≡ c` for `⊢ c : T ⇝ μ`                                  | A refinement admitting everything is no refinement.                                                                                                                                                                           |
| `legacy(c, p_c) ≡ c`                                                  | An older reading that is the current one adds nothing.                                                                                                                                                                        |
| `legacy(c, r) ≈ c` on `Can(c)`                                        | A migration differs from its current encoding only off the canonical set.                                                                                                                                                     |
| `union(c) ≡ c`                                                        | Choice of one.                                                                                                                                                                                                                |
| `union(c₁, union(c₂, c₃)) ≡ union(c₁, c₂, c₃)`                        | Associative, where both sides satisfy (D) — and only on inputs satisfying (U): an ambiguity _inside_ the nested option fails locally on the left, where the outer union may still resolve, and globally on the right. |
| `union(c₁ … cₙ) ≡ union(c_σ(1) … c_σ(n))` for any permutation `σ`     | Commutative: resolution is unique admission (§5), never declaration order.                                                                                                                                                    |
| `nullable(nullable(c)) ≡ nullable(c)`                                 | Idempotent, by construction: `nullable` inserts the null option unless the pair has it, and after one insertion it has it. The value language has one null, so there is nothing for a second `𝟙` to be.                       |
| `μ(w(c)) = μ(c)` for `w ∈ {held, refine, legacy, optional, fallback}` | Wrappers preserve the member — a field's member is its attribute's (§4). What keeps a key's attribute type stable under refactoring.                                                                                          |

### Do not hold

| Equation                                                            |                                                                                                                                                                                                                                   |
| ------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `union(array(c₁), array(c₂)) ≢ array(union(c₁, c₂))`                | Left: a sequence homogeneous in one option. Right: a sequence of either, elementwise. Different held sets, and only the right has (K) to discharge its (U).                                                                           |
| `tuple(c₁ … cₙ, rest(c)) ≢ tuple(c₁ … cₙ) ` and `≢ array(union(…))` | A fixed head with a repeating tail is neither: a tuple has no tail and an array has no head.                                                                                                                                      |
| `set(union(c₁, c₂))` — not derivable                                | The premise on `set` demands a member, and a union of options writing different members has none.                                                                                                                                 |
| `refine(held(c, f, g), q) ≢ held(refine(c, q), f, g)`               | The refinement applies on opposite sides of the iso, so `q` is a subset of different sets. Two different terms, both meaningful.                                                                                                  |
| `union(c₁ … cₙ) ≢ union(c₁ … cₙ, c)`                                | Not closed under extension: a further option can violate (D) and make the term ill formed, or leave (U) unresolved where it was discharged before.                                                                                                                                 |
| `optional(optional(c))` — not derivable                             | A marker marks once, and nesting read only the outermost. `optional(fallback(c, v))` and `fallback(optional(c), v)` likewise.                                                                                                     |
| `lazy(γ) ≢ γ(∗)`                                                    | The pair is the same and the μ is not: `lazy` concludes `⊤` where `γ(∗)` may name its member, so `set(lazy(γ))` has no derivation. `≡` compares the index too, and this is the row where that matters.                            |
| `legacy(c, r)` breaks **(MP)**                                      | On purpose, and it is the only term licensed to: changing what is stored _is_ the migration, and §2's read-side corollary falls with it. So a `legacy` attribute cannot be an index key, which is the price and is worth stating. |
| `e ∘ p ≢ id`                                                        | The quotient, from §2. Equality holds only on `Can(c)`.                                                                                                                                                                           |

---

## §7 The three layers, and the algebra

Three layers answer different questions, and conflating them is what makes a side condition look
optional. A grammar over the terms — a regular tree grammar, with nonterminals indexed by `μ` — says
which terms can be _written_. It cannot express **(D)**, which relates siblings rather than a term to
its subterms, so well-formedness needs the judgement of §3 and §5 rather than a production — nor
**(K)** and **(U)**, which are not about the term at all but about the inputs it is given.
And the judgement in turn says nothing about what a term _means_; that is §2, the pair and its laws —
a connection §5's soundness theorem proves rather than leaves implied.

Which places the calculus: **§1** a universal domain, **§2** types as quotient retracts of it,
**§3–§5** a two-index typing relation with side conditions, tied back to §2 by soundness, **§6** the
equational theory. And the terms are generated by a small algebra, which the soundness proof's
grouping makes official: **points** (the ground terms); one **partial iso** (`held`, with `refine`
its prism); one **agreeing read-extension** (`legacy`); three **products** — positional (`array`,
`tuple`), keyed (`record`, `object`), unordered (`set`) — all instances of one traversal argument;
one **sum** (`union`), resolved by unique admission, with `(dunion)` and `opaque` the two whose (U)
is a theorem; and a **fixpoint** (`lazy`, and `opaque` again). Fields are the keyed product's
presence decoration, and `nullable` is that sum's guarded insertion (§3) rather than a term of its own.

One more thing the algebra makes visible, and it is worth stating because it is not obvious from
the rules. **The two halves of the pair are the same construction at two carriers, everywhere the
calculus builds something itself.** A sum filters by the admission _that side_ reads and acts
through the option answering alone — the same sentence for `e` and for `p`, with `κ`-admission
swapped for member-admission. Adjoining the null point is the same construction on values and on
attributes. A product traverses. Reading a discriminator's tag is one lookup, spelled once per
carrier.

Exactly three terms break it, and they are the same three every time: `held`, `refine` and
`legacy` — the wrappers carrying a **caller's function that is not itself a codec**. `held`'s `f`
gates the writing while `g` only post-processes the reading, which is why `admA` sees through it and
`adm` cannot (§5). `legacy`'s `r` widens the reading and touches the writing not at all. `refine`'s
`q` is a predicate on _values_, so it gates one carrier directly and the other only after a read.
`custom` is the degenerate case: both halves are the caller's, so there is no shared construction to
be symmetric about.

So the asymmetry in this calculus is not a property of encoding-versus-decoding. It is the mark of
where a caller's function enters, and it stays local to the four terms that admit one.
 That is the divisible /
decidable [4] skeleton, read invariantly because both directions are present at once.

---

## Sources

1. **Quotient Lenses.** J. Nathan Foster, Alexandre Pilkiewicz, Benjamin C. Pierce. ICFP 2008. —
   bidirectional transformations well behaved modulo a programmer-controlled equivalence, and
   canonizers.
   <https://www.cs.cornell.edu/~jnfoster/papers/quotient-lenses.pdf>
2. **Invertible Syntax Descriptions: Unifying Parsing and Pretty Printing.** Tillmann Rendel, Klaus
   Ostermann. Haskell Symposium 2010. — one description, both directions, over an algebra of partial
   isomorphisms.
   <https://www.semanticscholar.org/paper/Invertible-syntax-descriptions:-unifying-parsing-Rendel-Ostermann/44c0cf69d73e4a0673dd04b7da477f7a74f0b735>
3. **Embedding-projection pairs.** Retracts of a universal domain, after Scott (1972); standard in
   denotational semantics and in the semantics of gradual types.
   <https://www.pls-lab.org/en/Embedding_projection_pair>
4. **Divisible and Decidable.** The contravariant analogues of Applicative and Alternative — products
   and sums on the writing side.
   <https://hackage.haskell.org/package/contravariant-1.5.5/docs/Data-Functor-Contravariant-Divisible.html>
5. **Combinators for Bidirectional Tree Transformations: A Linguistic Approach to the View-Update
   Problem.** Foster, Greenwald, Moore, Pierce, Schmitt. TOPLAS 29(3), 2007. — the GetPut / PutGet
   laws, and the asymmetric lens the quotient version refines.
   <https://dl.acm.org/doi/10.1145/1232420.1232424>
6. **A Tangled Web of 12 Lens Laws.** A taxonomy of the variants, where the distinctions matter.
   <https://link.springer.com/chapter/10.1007/978-3-030-79837-6_11>
7. **Supported data types and naming rules in Amazon DynamoDB.** The `N` range, stated in exponent
   notation.
   <https://docs.aws.amazon.com/amazondynamodb/latest/developerguide/HowItWorks.NamingRulesDataTypes.html>
