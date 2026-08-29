# Rotorise Codec Calculus

What a codec _is_, stated without reference to any implementation of one: a quotient
embedding-projection pair into the attribute domain, a typing judgement with two indices, and the
equations between terms.

This document is normative for the semantics and deliberately mentions no TypeScript. Where the
implementation is named at all it is to record that a rule here is checked _somewhere_ — never to
define the rule. The calculus is also mechanized in Lean (`formal/`), and where a remark below cites
"the mechanized proof" it reports something that machine-checking forced or exhibited; the doc
remains the normative statement.

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

|        |                                             |                                                                       |
| ------ | ------------------------------------------- | --------------------------------------------------------------------- |
| **R**  | `∀ t ∈ dom(e). p(e(t)) = t`                 | Retraction. Writing then reading returns the value written, exactly.  |
| **C**  | `∀ a ∈ dom(p). p(a) ∈ dom(e)`               | Canonizability. Whatever was read can be written back.                |
| **W**  | `μ ≠ ⊤ ⟹ ∀ t ∈ dom(e). e(t) = ⟨μ, _⟩`       | A term that names its member writes that member and no other.         |
| **MP** | `∀ a ∈ dom(p). member(e(p(a))) = member(a)` | Reading and writing back never changes a stored member.               |

The four are independent, and **(MP)** is well defined only because **(C)** holds — `e(p(a))` is an
attribute at all because everything readable re-encodes. One term is exempt from **(MP)** and only
one: `legacy`, whose entire purpose is to change what is stored (§3, §6) — and since **(MP)** is
recursive, a term _containing_ a `legacy` inherits the exemption on exactly the attributes the
migration rereads, and on no others. Nothing is exempt from the other three.

Only **(R)** is an equality on the nose. Taken as one, `e ∘ p = id` is _false_ and must be: a set has
no order to preserve, so writing back what was read is free to reorder it, and digits have a normal
form, so writing back is free to normalise. In the language of quotient lenses [1] `e ∘ p` is a
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
⊢ string : String ⇝ S      (string)      ⊢ decimal : Numerals ⇝ N (decimal)

D = { x ∈ Double : x = 0 ∨ 1e-130 ≤ |x| ≤ 9.9…e125 }
────────────────────────────────────────────────────── (number)
⊢ number : D ⇝ N

T ⊆ D,  T ≠ ∅
────────────────────────────── (numeric)
⊢ numeric(T) : T ⇝ N

──────────────────────────────
⊢ boolean : Bool ⇝ BOOL    (boolean)

──────────────────────────────
⊢ binary : Bytes ⇝ B       (binary)

──────────────────────────────
⊢ null : {null} ⇝ NULL     (null)

ℓ₁ … ℓₙ ∈ String,  n ≥ 1,  pairwise distinct
────────────────────────────────────────────── (literal-S)
⊢ literal(ℓ₁ … ℓₙ) : {ℓ₁ … ℓₙ} ⇝ S

ℓ₁ … ℓₙ ∈ D,  n ≥ 1,  pairwise distinct
────────────────────────────────────────────────────── (literal-N)
⊢ literal(ℓ₁ … ℓₙ) : {ℓ₁ … ℓₙ} ⇝ N
```

`number` is **not** restricted to integers, and not to `2⁵³`. Every finite double satisfies **(R)**,
because `String` on a double is by definition the shortest text reading back as that same double — so
`1.5` round-trips, and so does `2⁵³ + 1`, which _is_ `2⁵³` and round-trips as that. What bounds `D` is
DynamoDB's magnitude range, and `D` is an **unchecked precondition**: the implementation writes
whatever `String` produces, so `5e-324` is written and the service rejects it on arrival. Recorded
here rather than in the type, because that is where it is.

`numeric` is `number` with the held set chosen by the caller — the term for a numeric enum member.
The subset is the same kind of **unchecked precondition** as `D`, on the other side of the pair: `p`
returns the double it read and does not verify membership in `T`. `refine(number, T)` is the same
held set _with_ the check; `numeric(T)` is the claim without it, and a claim and a check are
different terms.

`decimal` holds `Numerals`, not a machine number. That is the one ground term whose held set is chosen
against the grain of the host language, and the reason is in the table in §1: `N` carries 38
significant digits and a double carries 15.

`literal` is the one ground term with **two** rules, because it is the only one whose member follows
from its _values_ rather than from its name. There is deliberately no rule admitting a mixed set: a
codec writes one member, so `literal(ℓ, k)` with `ℓ ∈ String` and `k ∈ D` has no derivation. That is
what makes this the term for an enum indexed by number — the held set is the literal union and the
stored member is `N`, checked in both directions — and note that `⇝ N` carries `Numerals` on the wire
while the held set is numeric, so `(R)` obliges the reading to return the number and not its text.

### Containers

```
⊢ c : T ⇝ μ      μ ∈ {S, N, B}
──────────────────────────────── (set)
⊢ set(c) : ℘⁺fin(T) ⇝ μS

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

⊢ c : T ⇝ μ    e(t) = ⟨NULL, ∗⟩ ⟹ t = null    p(a) = null ⟹ member(a) = NULL
──────────────────────────────────────────────────────────────────────────────── (nullable)
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

`opaque` is the custom-class term the calculus ships, and it is primitive only in presentation: the
mechanized model exhibits it as the **union of everything self-identifying, closed under the
containers** — a fixpoint of shape
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
partial isomorphisms, which is exactly the merged combinator. They are separate here for a reason
outside the calculus: a total `g` lets a generator for `I` be pushed forward to one for `T`, while a
partial one leaves only rejection sampling. Same terms, different search.

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

`nullable`'s two side premises are **null-honesty** — `c` speaks of `NULL` only for `null`, in both
directions. They too were forced by the proof: a subterm moving `null` onto another member, or
another member onto `null`, lets the outer `NULL` branch shadow a real value, failing **(R)** in one
direction and **(MP)** in the other. Every term of this calculus is null-honest except what `custom`
or an ill-chosen `held` iso can build — and `nullable` itself is, which is what makes the
idempotence of §6 lawful rather than lucky.

Null-honesty is not a new kind of condition. `nullable(c)` is structurally the two-option union
`union(c, ⟨NULL⟩-point)`, and the two premises are exactly that pair's §5 side conditions —
write-honesty is uniqueness of admission on the way in, read-honesty on the way out. The mechanized
proof closes the `nullable` case on precisely those premises and nothing else.

Both spellings are available: `(null)` above makes `union(c, null)` a term, so a schema may write
either. They are not interchangeable, and the difference is precedence. `nullable` resolves the
`NULL` reading by **precedence**; the union demands disjointness. Concretely, `nullable` accepts a
base that already handles `null` — `nullable(nullable(c))`, `nullable(opaque)` — and the union
rejects it, because both options admit and (U) fails, the same way the member algebra rejects
`set(set(c))`. Prefer the union when you want that rejection; prefer `nullable` when the base may
itself be null-aware.

The two constructions are **equivalent** in the sense of §6, with no side condition whatsoever
(`equiv_orNull_altCodec`): `≡` compares the pairs where both are defined, and the only place they
differ is where the union is *un*defined. They are the same *codec* only when `c` does not touch
the null point at all — `e_c(null)` and `p_c(⟨NULL, ∗⟩)` both undefined (`orNull_eq_altCodec`),
which is strictly stronger than honesty, since honesty constrains which attribute a value is
written to and says nothing about whether `c` writes `null` at all. Where the base does handle
null, the wrapper answers and the union refuses, because both options admit. The witness is not
exotic: it is `nullable(nullable(c))`, the term whose idempotence §6 records
(`orNull_ne_altCodec`). So `nullable` is not sugar for the union: desugaring it would not preserve
that row, and would make `nullable(nullable(c))` undefined at `null`.

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
of §2 again — an item is `≈c` itself minus its undeclared names — the same class of loss as a set's
reordering.

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

|       |                                        |                                                                    |
| ----- | -------------------------------------- | ------------------------------------------------------------------ |
| **U** | `∀ input. ∣{ i : cᵢ admits it }∣ = 1`  | Per value and per attribute. Ambiguity is a failure, never a rank. |

Declaration order is never consulted — which is what puts commutativity in §6, and why `legacy`'s
coherence premise (§3) matters beyond `legacy`: a precedence between readings anywhere in the
calculus would be a union resolved by rank, exactly what **(U)** refuses.

**(U)** quantifies over inputs, so it is not decidable at the declaration in general. The rest of
this section is its **dischargers** — decidable conditions, each sufficient for **(U)** on the
unions it covers:

| Discharger                           | Decides                                             | From                       |
| ------------------------------------ | --------------------------------------------------- | -------------------------- |
| distinct members, or disjoint `adm`  | the readable side, where the stored attributes differ | `μ`, and `adm` below       |
| **(K)** — disjoint kinds, or disjoint `ident` sets | the writable side, where the runtime shapes differ  | `κ`, `ident` and `adm`, below |
| tag disjointness                     | `(dunion)`, outright — both sides                   | the discriminator literals |
| kind disjointness                    | `opaque`'s fixpoint (§3), outright                  | one option per kind of §1  |

What no discharger covers stays an obligation the semantics enforces per input by failing — safe for
every law except **(R)** at a canonical attribute, and that residue is exactly what the theorem
below names. A `⊤` option is exempt from **(K)** for the same reason it cannot be checked: it could
be anything, refusing it against everything would refuse unions that work, and **(U)** still guards
each value it is actually given.

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
| `number`, `numeric(T)`                            | `{number}`                                   |
| `boolean` / `binary`                              | `{boolean}` / `{binary}`                     |
| `literal(ℓ₁ … ℓₙ)`                                | `{string}` or `{number}`, by the values      |
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
accepts every kind by design. Both are exempt from **(K)** and fall to **(U)** per input. The
difference resurfaces only inside `opaque`'s own derivation, where "everything" is precisely what
makes its fixpoint's options pairwise kind-disjoint (§3).

`ident(c)` holds when a term decides its own membership — when "this option accepted the value" is
evidence, because the term checks the value against its own admissible set in **both** directions:

|            |                                                                                                                                                                                                            |
| ---------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| holds      | `literal` — the admissible set is checked; `discriminatedUnion` — a tag lookup fails honestly                                                                                                              |
| propagates | `set`, `array`, `record` through the element; `tuple` and `union` when _every_ subterm has it; `refine`, `optional`, `fallback`, `legacy` through the subterm                                              |
| never      | everything else — the ground scalars, `custom`, `opaque`, `lazy`; `held`, whose functions are the caller's; and `nullable`, deliberately: two nullable options both admit the null neither subterm decides |

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
⊢ cᵢ : Tᵢ ⇝ μᵢ  (i ∈ 1…n)    (D)    (K)
─────────────────────────────────────────────────────────────────── (union)
⊢ union(c₁ … cₙ) : ⋃ Tᵢ ⇝ (μ if ∀i. μᵢ = μ;  else ⊤)

⊢ oᵢ = object(sᵢ, ρᵢ) : Tᵢ ⇝ M    sᵢ(d) = literal(Lᵢ)    Lᵢ pairwise disjoint
─────────────────────────────────────────────────────────────────────────────── (dunion)
⊢ discriminatedUnion(d, o₁ … oₙ) : ⋃ Tᵢ ⇝ M
```

Note that `(dunion)`'s premise asks `sᵢ(d)` to _be_ the literal — an attribute term, hence a `req`
field. A `fallback` around it has no derivation, and the proof says why rather than leaving it to
taste: a row omitting the discriminator would read to the fallback's stand-in, an arbitrary value
the tag sets never vouched for, and **(C)** would then re-encode a variant no tag selects.

|       |                                                      |                                                                                                                                 |
| ----- | ---------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------- |
| **D** | `∀ i ≠ j. ¬(Tᵢ ⊆ Tⱼ) ∧ ¬(Tⱼ ⊆ Tᵢ)`                   | Well-formedness: no option's held set subsumes another's. Decidable from the held sets alone. It does **not** discharge the readable side — see below.                    |
| **K** | `∀ i ≠ j. κ(cᵢ) ∩ κ(cⱼ) = ∅ ∨ (ident(cᵢ) ∧ ident(cⱼ) ∧ adm(cᵢ) ∩ adm(cⱼ) = ∅)` | Writable: no value belongs to two options. Needs `κ`, which the held sets do not determine.                                     |

**(D)** and **(K)** ask the same kind of question of the two sides of the pair, and neither implies
the other. `union(array(string), array(number))` satisfies **(D)** — the held sets are incomparable —
and violates **(K)**: both accept a sequence, and neither is `ident`.
`union(set(string), set(number))` is the same story with a twist worth naming: its options write
_different members_, so reading was never in doubt. It is refused for the direction that cannot be
resolved — and degraded twice over, because a set's member is computed from its element, so those
options are `⇝ SS` and `⇝ NS` and the union's own `μ` is `⊤` by the `(union)` rule. That is a second,
independent loss: a `⊤` term is one only **(MP)** constrains, where a `⇝ SS` term is pinned by
**(W)** and its read-side corollary.

Why `ident` exempts a pair is the interesting half. **Encoding does not validate.** A term's `e` is
defined on `T` and does whatever it does off it, so "this option encoded the value" carries no
information about whether the value was meant for it. Only a term that knows its own membership
answers a real question when attempted — which is why `union(literal("A"), literal("B"))` is well
formed under **(K)** although both accept a string.

But `ident` is only half of that exemption, and an earlier statement of **(K)** —
`κ(cᵢ) ∩ κ(cⱼ) = ∅ ∨ ident(cᵢ) ∨ ident(cⱼ)` — was wrong to stop there. Two counterexamples,
both machine-checked (`Calculus/Discharge.lean`):

- **One side is not enough.** `union(literal("A"), string)` has `ident` on the left, so the disjunction
  is satisfied — and both options admit `"A"`. A real answer from one option does not resolve a pair;
  the other option is still answering, and still meaninglessly.
- **Two sides are not enough either.** `ident` propagates through `array`, so
  `union(array(literal("A")), array(literal("B")))` has it on both — and both admit `[]`. Propagating
  `ident` through a container does not propagate _disjointness_ of what the options accept: every
  container admits its empty case, which no element ever sees.

What the exemption actually needs is what the worked example above quietly has: `ident` on **both**
sides, and admissible sets that do not meet. So `adm(c)`, the third auxiliary, is the set a term
checks against when `ident(c)` holds — a `literal`'s values, a `discriminatedUnion`'s tags. It is
compared only between two `ident` terms, and it is deliberately _not_ propagated through the
containers: `adm(array(c))` would have to contain the empty array whatever `c` is, so container
options are never separated this way and the second counterexample stays refused. `refine`,
`optional`, `fallback` and `legacy` pass `adm` through, as they pass `ident` through.

The residue of the old rule is the honest one: the pairs `ident` genuinely resolves are the pairs of
`literal`s with disjoint values, and the pairs of `discriminatedUnion`s with disjoint tags — the
latter being the tag-disjointness row of the discharger table, arrived at from the other direction.

**(D)** as written is _incomparability_, not disjointness. Two object options `⟨a : String⟩` and
`⟨b : String⟩` are incomparable yet share the inhabitant `⟨a ↦ "1", b ↦ "2"⟩` — so **(D)** admits
them, and resolution falls to the name-set device above. The gap between the two is exactly the set
of unions resolved structurally rather than by type — and **(U)** is what fills it.

An earlier version of this section went on to claim that stating **(D)** as genuine _disjointness_
would be sound. It would not, and the reason is worth keeping, because it is the same confusion
twice: **held sets are sets of values, and (U)'s readable side quantifies over attributes.** `held`
is precisely the term that separates the two — its adapter relabels — so two options can hold
disjoint sets of values and still read one attribute, each to its own value.
`union(literal("A"), held(literal("A"), f, g))` with `f` and `g` swapping `"B"` for `"A"` holds
`{"A"}` and `{"B"}`, which are disjoint on the nose, and both options read `S "A"` — the first to
`"A"`, the second to `"B"`. Machine-checked as `not_uAtCan_literal_held`.

So **(D)** is a well-formedness condition on the judgement's `T` index and not a discharger of
**(U)**: no condition on held sets can be one. What decides the readable side is a condition on
_stored attributes_ — distinct members `μᵢ ≠ μⱼ`, or disjoint `adm` — which is what the mechanized
discharger takes.

### Theorem (soundness)

Every derivable `⊢ c : T ⇝ μ`, and every `⊢ f : T ⊗ π ⇝ μ`, denotes a pair satisfying **(R)**,
**(C)**, **(W)**, and **(MP)** in the strong form `e(p(a)) ≼ a` defined below — with two residues,
both named exactly: **(MP)** is off on the attributes a `legacy` in the derivation rereads, and
every `(union)` in the derivation carries **(U)** _at its canonical inputs_ as an obligation, which
the dischargers of this section settle at the declaration wherever they decide a pair — `(dunion)`
and `opaque` outright.

Four premises in §3–§4 — `ran(r) ⊆ dom(e)` and coherence on `(legacy)`, null-honesty on
`(nullable)`, `v(∗) ∈ dom(e)` on `(fallback)` — exist because this proof failed without them. That
is the theorem earning its keep: each names a term the calculus used to derive and the laws refuse.

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
decodes and re-encodes through the same step, and lengths survive both directions. Keyed lists add
one clause: entries are dispatched and compared _by name_, first occurrence first, so the lookup
form of `≼`'s `M` clause follows from the pointwise one. Proved once; every product case below is
an instantiation. ∎

**Proof.** By induction on the derivation, with one refinement recorded at `(lazy)`. Each case
first says what the pair _is_ — the denotation is part of the rule, not of any implementation —
then discharges the laws. The grouping is the mechanization's module structure, so the prose proof
and the machine proof can be audited against each other case for case.

**Points.** Each ground term writes one member, totally on its held set, and reads exactly that
member back into the held set. **(W)** and **(C)** are immediate, `≼` is member equality with no
substructure, and **(R)** is the carrier's round trip: identity for `string`, `boolean`, `binary`,
`null` (whose held set is the single value `null` and whose payload is `∗`) and `decimal` (a numeral is stored as written, so `Can(decimal)` is all of `N`), shortest-text for
`number` and `literal‑N` — the §3 argument that every finite double survives. `numeric(T)`: the
normative reading is `number`'s restricted to attributes landing in `T`, and every law restricts
with it; the implementation elides the restriction, which is §3's unchecked precondition — off it,
**(C)** and **(R)** are the implementation's to lose, not the term's.

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

_nullable._ `e`: `null ↦ ⟨NULL, ∗⟩`, else `e_c`; `p`: `⟨NULL, ∗⟩ ↦ null`, else `p_c`. The two
honesty premises are one per direction. **(R)** at `null` is immediate; at `t ≠ null`,
`e_c(t) ≠ ⟨NULL, ∗⟩` by write-honesty, so the outer `NULL` branch cannot shadow the reading — drop
the premise and `nullable(held(nullable(string), f, g))`, with `f` moving a sentinel onto `null`,
encodes the sentinel as `⟨NULL, ∗⟩` and reads back `null`. **(C)**: `⟨NULL, ∗⟩` round-trips; else
`p_c(a) ≠ null` by read-honesty (`a`'s member is not `NULL`), so the `e_c` branch answers, defined
by the premise's **(C)**. `≼` at `⟨NULL, ∗⟩` is exact; elsewhere it is the hypothesis —
read-honesty is what rules out a non-`NULL` attribute reading to `null` and re-encoding as
`⟨NULL, ∗⟩`, the member change **(MP)** exists to refuse. Both honesty conditions hold _of_
`nullable(c)` itself, so `nullable(nullable(c))` is derivable and §6's idempotence is an equation
rather than an accident.

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
the wire set is the lifted list. **(R)**: `w` is injective by the injectivity Lemma (member fixed,
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

- **(R)**: `t ∈ dom(e)` names a unique `i`, and `i` admits `eᵢ(t)` back (the premise's **(R)**);
  _uniqueness_ of that admission is **(U)** on the attribute side at a canonical input — the
  theorem's residue. Where it holds, `p(e(t)) = pᵢ(eᵢ(t)) = t`. Partiality cannot hide this: an
  ambiguous `e(t)` makes `p(e(t))` undefined, which **(R)** counts as failure.
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
caller's to keep, `(number)` and `(numeric)` carry unchecked preconditions, and each `(union)`'s
residual **(U)**. Each law is checked per term in the implementation's law suite, and the proof's
grouping above is the mechanization's file structure — the preamble's "checked _somewhere_", twice
over.

---

## §6 Equations

Which rewrites preserve the pair. Read `≡` as: the same `T`, the same `μ`, and `e` and `p` agreeing
everywhere both are defined.

### Hold

| Equation                                                              |                                                                                           |
| --------------------------------------------------------------------- | ----------------------------------------------------------------------------------------- |
| `held(c, id, id) ≡ c`                                                 | Identity.                                                                                 |
| `held(held(c, f, g), f′, g′) ≡ held(c, f ∘ f′, g′ ∘ g)`               | Isos compose; note the reversal on the reading half.                                      |
| `refine(refine(c, q), q′) ≡ refine(c, q ∩ q′)`                        | Prisms meet.                                                                              |
| `refine(c, T) ≡ c` for `⊢ c : T ⇝ μ`                                  | A refinement admitting everything is no refinement.                                       |
| `legacy(c, p_c) ≡ c`                                                  | An older reading that is the current one adds nothing.                                    |
| `legacy(c, r) ≈ c` on `Can(c)`                                        | A migration differs from its current encoding only off the canonical set.                 |
| `union(c) ≡ c`                                                        | Choice of one.                                                                            |
| `union(c₁, union(c₂, c₃)) ≡ union(c₁, c₂, c₃)`                        | Associative, where both sides satisfy (D) and (K) — and only on inputs satisfying (U): an ambiguity _inside_ the nested option fails locally on the left, where the outer union may still resolve, and globally on the right. |
| `union(c₁ … cₙ) ≡ union(c_σ(1) … c_σ(n))` for any permutation `σ`     | Commutative: resolution is unique admission (§5), never declaration order.                |
| `nullable(nullable(c)) ≡ nullable(c)`                                 | Idempotent: the value language has one null, so the outer `𝟙` is the only one ever written or read — lawful because `nullable` is itself null-honest (§3). |
| `μ(w(c)) = μ(c)` for `w ∈ {held, refine, legacy, optional, fallback}` | Wrappers preserve the member — a field's member is its attribute's (§4). What keeps a key's attribute type stable under refactoring. |

### Do not hold

| Equation                                                            |                                                                                                                                                         |
| ------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `union(array(c₁), array(c₂)) ≢ array(union(c₁, c₂))`                | Left: a sequence homogeneous in one option. Right: a sequence of either, elementwise. Different held sets, and only the right is well formed under (K). |
| `tuple(c₁ … cₙ, rest(c)) ≢ tuple(c₁ … cₙ) ` and `≢ array(union(…))` | A fixed head with a repeating tail is neither: a tuple has no tail and an array has no head.                                                            |
| `set(union(c₁, c₂))` — not derivable                                | The premise on `set` demands a member, and a union of options writing different members has none.                                                       |
| `refine(held(c, f, g), q) ≢ held(refine(c, q), f, g)`               | The refinement applies on opposite sides of the iso, so `q` is a subset of different sets. Two different terms, both meaningful.                        |
| `union(c₁ … cₙ) ≢ union(c₁ … cₙ, c)`                                | Not closed under extension: a further option can violate (D) or (K) and make the term ill formed.                                                       |
| `optional(optional(c))` — not derivable                             | A marker marks once, and nesting read only the outermost. `optional(fallback(c, v))` and `fallback(optional(c), v)` likewise.                           |
| `lazy(γ) ≢ γ(∗)`                                                    | The pair is the same and the μ is not: `lazy` concludes `⊤` where `γ(∗)` may name its member, so `set(lazy(γ))` has no derivation. `≡` compares the index too, and this is the row where that matters. |
| `legacy(c, r)` breaks **(MP)**                                      | On purpose, and it is the only term licensed to: changing what is stored _is_ the migration, and §2's read-side corollary falls with it. So a `legacy` attribute cannot be an index key, which is the price and is worth stating. |
| `e ∘ p ≢ id`                                                        | The quotient, from §2. Equality holds only on `Can(c)`.                                                                                                 |

---

## §7 What each layer is

The three layers answer different questions and are easy to conflate. A grammar over the terms — a
regular tree grammar, with nonterminals indexed by `μ` — says which terms can be _written_. It cannot
express **(D)** or **(K)**, which relate siblings, so well-formedness needs the judgement of §3 and §5
rather than a production. And the judgement in turn says nothing about what a term _means_; that is
§2, the pair and its laws — a connection §5's soundness theorem proves rather than leaves implied.

Which places the calculus: **§1** a universal domain, **§2** types as quotient retracts of it,
**§3–§5** a two-index typing relation with side conditions, tied back to §2 by soundness, **§6** the
equational theory. And the terms are generated by a small algebra, which the soundness proof's
grouping makes official: **points** (the ground terms); one **partial iso** (`held`, with `refine`
its prism); one **agreeing read-extension** (`legacy`); three **products** — positional (`array`,
`tuple`), keyed (`record`, `object`), quotiented (`set`) — all instances of one traversal argument;
one **sum** (`union`), resolved by unique admission, with `(dunion)` and `opaque` the two whose (U)
is a theorem; and a **fixpoint** (`lazy`, and `opaque` again). Fields are the keyed product's
presence decoration, and `nullable` is a sum in precedence clothing (§3). That is the divisible /
decidable [4] skeleton, read invariantly because both directions are present at once — and it is
also the mechanization's module structure, which is what keeps the prose proof and the machine
proof auditable against each other.

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
