import Calculus.Objects

/-!
# Sums (§5), and unknown values

`altCodec` over `OptionSem`s that carry their *admission as data*, with `UniqueAdmission`
as (U) in premise form. `dunionTable` is not one of them: a discriminated union is a
**lookup**, and its key set makes the fact. `opaqCodec` is `altCodec`'s fueled fixpoint
over everything self-identifying, and the `refuse` policy is the absence of the number
option.
-/

namespace Calculus

noncomputable section
/-! ## Sums (§5): admission as data -/

/-- One union option: its admission functions and its pair. The doc's `κ`/`ident`/name
    devices become *builders* of these. -/
structure OptionSem where
  admitA : Attr → Bool
  admitV : Value → Bool
  c : Codec

/-- Name admission (objects): every present name declared, every required name present.
    The spec is a `MapOf Bool` — the declared names with each one's required flag —
    for the same reason the field table is: a list of pairs admits orderings and
    repeats that a declaration does not have. -/
def keysOk (spec : MapOf Bool) (keys : Finset Name) : Bool :=
  decide (∀ k ∈ keys, k ∈ spec.1) &&
  decide (∀ k : {k // k ∈ spec.1}, spec.2 k = true → k.1 ∈ keys)

/-- An object option decides by names, never by being attempted. -/
def OptionSem.byNames (spec : MapOf Bool) (c : Codec) : OptionSem :=
  { admitA := fun a => match a with | .m keys _ => keysOk spec keys | _ => false
    admitV := fun v => match v with | .map keys _ => keysOk spec keys | _ => false
    c := c }

/-- Any other option is admitted by attempt — the doc's `ident` caveat lives in the
    (U) premise, not here. -/
def OptionSem.byAttempt (c : Codec) : OptionSem :=
  { admitA := fun a => (c.p a).isSome
    admitV := fun v => (c.e v).isSome
    c := c }

/-- An attempted option admits an attribute exactly when its `p` is defined there — the
    §1 rule applied to admission, so no proof takes `byAttempt` apart by hand. -/
@[simp] theorem OptionSem.byAttempt_admitA {c : Codec} {a : Attr} :
    (OptionSem.byAttempt c).admitA a = (c.p a).isSome := rfl

/-- …and a value exactly when its `e` is. -/
@[simp] theorem OptionSem.byAttempt_admitV {c : Codec} {v : Value} :
    (OptionSem.byAttempt c).admitV v = (c.e v).isSome := rfl

/-- The `⟨NULL⟩` point as a union option — §3's second half of `nullable(c)` read as
    `union(c, ⟨NULL⟩-point)`. It decides by attempting, like any ground option. -/
abbrev nullOption : OptionSem := .byAttempt nullCodec

/-- §5's discriminator projection: the tag an item carries at `d`, where it carries one.
    A membership decision and a function application, where the list representation needed
    a `lookup`. -/
def Value.tagText : Value → Option String
  | .str s => some s
  | _ => none

/-- …and its stored twin, which reads **two** members. A decimal tag writes a `.str` and stores
    an `.n`, so the value side has one row and the stored side has two. The host's tag reader
    accepts `S` or `N` and returns the text carried by either; this is that rule.

    Named beside `Value.tagText` rather than written inline in `tagOfV`/`tagOfA`, because a
    lemma about a tag is then a lemma about these and not about a match under a `dif`. -/
def Attr.tagText : Attr → Option String
  -- the binders are not `s` and `n`: this definition opens the `Attr` namespace, where those
  -- two names are the constructors themselves
  | .s text => some text
  | .n num => some num.1
  | _ => none

/-- One discriminator's tag, read off a value. -/
def tagAtV (d : Name) : Value → Option String
  | .map keys f => if h : d ∈ keys then (f ⟨d, h⟩).tagText else none
  | _ => none

/-- **A member's assignment, read off a value**: one tag per key, `none` if any key is absent.

    A finite function on the key set, so the keys have no order and neither does the reading.
    `Finset.attach` gives the decidable `∀ k ∈ ks` the totality check needs without enumerating,
    which `Finset.toList` would and which reaches `Classical.choice`. -/
def tagOfV (ks : Finset Name) (v : Value) : Option (Assignment ks) :=
  if h : ∀ k ∈ ks, (tagAtV k v).isSome then
    some (fun k => (tagAtV k.1 v).get (h k.1 k.2))
  else none

/-- One key's tag on the stored side, where the field may be `S` **or** `N`.

    A decimal tag writes a `.str` and stores an `N`, so the value side is covered by the `.str`
    row above and the stored side needs this one. The host reads a tag from the stored item and
    accepts `S` or `N`, returning the text carried by either. This is that rule. -/
def tagAtA (d : Name) : Attr → Option String
  | .m keys g => if h : d ∈ keys then (g ⟨d, h⟩).tagText else none
  | _ => none

/-- The same on the stored side. -/
def tagOfA (ks : Finset Name) (a : Attr) : Option (Assignment ks) :=
  if h : ∀ k ∈ ks, (tagAtA k a).isSome then
    some (fun k => (tagAtA k.1 a).get (h k.1 k.2))
  else none

/-- The builder `denote` uses for a union option. -/
def optionSemOf (c : Codec) : Option (MapOf Bool) → OptionSem
  | some spec => .byNames spec c
  | none => .byAttempt c

/-- §5 (U) at every option's canonical pairs: each is admitted by that option alone, on
    both sides. The strong form, and what every discharger in `Discharge` produces. -/
def UniqueAdmission (os : List OptionSem) : Prop :=
  ∀ o ∈ os, ∀ t a, o.c.e t = some a →
    os.filter (·.admitA a) = [o] ∧ os.filter (·.admitV t) = [o]

/-- **§5 (U) where the laws consume it**, and the soundness theorem's actual residue.

    `UniqueAdmission` quantifies over every canonical pair of every *option*. The four
    laws never ask that much: they ask only about inputs the *union itself* resolves,
    because `altCodec` is undefined wherever the filter is not a singleton, and a law
    quantified over `dom` cannot reach an input the pair declines. This is that
    restriction — resolving one side of the pair resolves the other, through the same
    option — and the three uses in `lawfulCore_altCodec` and `lawful_altCodec` are
    exactly its two clauses.

    Strictly weaker, and the gap holds working schemas.
    `union(array(literal "A"), array(literal "B"))` collides at `[]`, which is a
    canonical pair of each option and so refutes `UniqueAdmission`
    (`not_uAtCan_array_literals`) — while the union declines to write `[]` at all, so it
    never acts there and no law is ever asked. `adm` stops at the containers (§5), which
    is why the collision is the empty case and nothing else. `uAtAct_array_literals` is
    that union meeting this condition, so the two are separated by a theorem and not by
    an argument. -/
def UniqueBothWays (os : List OptionSem) : Prop :=
  (∀ o ∈ os, ∀ t a, os.filter (·.admitV t) = [o] → o.c.e t = some a →
    os.filter (·.admitA a) = [o]) ∧
  (∀ o ∈ os, ∀ a t a', os.filter (·.admitA a) = [o] → o.c.p a = some t →
    o.c.e t = some a' → os.filter (·.admitV t) = [o])

/-- The strong form implies the one the laws need — so every discharger still discharges,
    unchanged. The converse fails, which is the whole point. -/
theorem uniqueBothWays_of_uniqueAdmission {os : List OptionSem}
    (hU : UniqueAdmission os) : UniqueBothWays os :=
  ⟨fun o ho t a _ he => (hU o ho t a he).1,
   fun o ho _ t a' _ _ he => (hU o ho t a' he).2⟩

/-- A union's member: `μ` when unanimous, else `⊤` (§5 `(union)`). -/
def unanimous : List (Option Member) → Option Member
  | [] => none
  | μ :: μs => if μs.all (· == μ) then μ else none

/-- **One side of a sum.** Both halves of `altCodec` are this: filter the options by the
    admission *that side* reads, and act through the one that answers alone. The two
    differ only in which admission and which half of the pair — so stating the shape once
    is what lets `altCodec_e` and `altCodec_p` be the same theorem at two instances,
    instead of one theorem written twice. -/
def select {A B : Type} (os : List OptionSem) (adm : OptionSem → A → Bool)
    (run : OptionSem → A → Option B) (x : A) : Option B :=
  match os.filter (adm · x) with
  | [o] => run o x
  | _ => none

/-- `union`: the sum, resolved by unique admission — never by declaration order. -/
def altCodec (os : List OptionSem) (μA : Option Member) : Codec :=
  { T := fun v => ∃ o ∈ os, o.c.T v
    μ := μA
    e := select os (·.admitV) (·.c.e)
    p := select os (·.admitA) (·.c.p) }

/-! ## Unknown values (§3 `(opaque)`) -/

/-- §3 `(opaque)`'s eight self-identifying options; `rec` is where the recursion goes.

    Named because three statements cite it — `opaqCodec`, `opaq_onKinds`,
    `uniqueAdmission_opaque` — and a list spelled three times can drift twice. **`refuse` is
    the absence of an option**, spelled here as the empty codec. -/
def opaqOptions (lossy : Bool) (rec : Codec) : List OptionSem :=
  [.byAttempt stringCodec, .byAttempt booleanCodec, .byAttempt binaryCodec,
   .byAttempt nullCodec,
   .byAttempt (if lossy then numberCodec else Codec.empty),
   .byAttempt (setCodec rec), .byAttempt (arrayCodec rec), .byAttempt (recordCodec rec)]

/-- `opaque` is not special: it is the recursive union of everything self-identifying,
    closed under the containers — "the values whose type is recoverable", as a
    fixpoint of the algebra. Its (U) is kind-disjointness (`uniqueAdmission_opaque`,
    via `uniqueAdmission_of_kinds`). -/
def opaqCodec : Nat → Bool → Codec
  | 0, _ => .empty
  | fuel+1, lossy => altCodec (opaqOptions lossy (opaqCodec fuel lossy)) none

end

end Calculus
