import Calculus.Objects

/-!
# Sums (§5), and unknown values

`altCodec` over `OptionSem`s that carry their *admission as data*, with `UniqueAdmission`
as (U) in premise form. `opaqCodec` is `altCodec`'s fueled fixpoint over everything
self-identifying, and the `refuse` policy is the absence of the number option.
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

/-- Name admission (objects): every present name allowed, and every absent name allowed.
    The spec is a `BodySpec` — the declared names with what admission reads at each, and the
    open block — for the same reason the field table is a `MapOf`: a list of pairs admits
    orderings and repeats that a declaration does not have.

    **An open body declares every name.** Its block claims each name the field table does not,
    so the present-name half asks nothing of an open body and the required-name half is
    unchanged: a name the body requires must still be there. A closed body is the same test it
    always was, `wild = none` making the first conjunct the plain containment. -/
def keysOkV (spec : BodySpec) (keys : Finset Name) : Bool :=
  (spec.wild.isSome || decide (∀ k ∈ keys, k ∈ spec.names.1)) &&
  (decide (∀ k : {k // k ∈ spec.names.1},
    (spec.names.2 k).presenceV.2 = false → k.1 ∈ keys) &&
  decide (∀ k : {k // k ∈ spec.names.1},
    (spec.names.2 k).presenceV.1 = false → k.1 ∉ keys))

/-- The read-side name admission. A stand-in changes only the read presence element. -/
def keysOkA (spec : BodySpec) (keys : Finset Name) : Bool :=
  (spec.wild.isSome || decide (∀ k ∈ keys, k ∈ spec.names.1)) &&
  (decide (∀ k : {k // k ∈ spec.names.1},
    (spec.names.2 k).presenceA.2 = false → k.1 ∈ keys) &&
  decide (∀ k : {k // k ∈ spec.names.1},
    (spec.names.2 k).presenceA.1 = false → k.1 ∉ keys))

/-- One present name's content, on the write side: where the name's field is a literal, the
    value is the one the literal names. A name the spec does not declare is the open block's,
    and reads that block's alternatives; under a closed body `keysOkV` has already refused it,
    so the answer there is never consulted. -/
def altsOkV : Option Alts → Value → Bool
  | some ⟨g, x⟩, v => inL g x v
  | none, _ => true

def litOkV (spec : BodySpec) (k : Name) (v : Value) : Bool :=
  match spec.names.at k with
  | some ns => altsOkV ns.alts v
  | none => altsOkV (spec.wild.getD none) v

/-- …and on the read side, where the test is the literal codec's own. `inL` is a predicate on
    a `Value` and the stored side holds an `Attr`, so the read test asks the codec that decodes
    it rather than a second membership. -/
def altsOkA : Option Alts → Attr → Bool
  | some ⟨g, x⟩, a => ((literalCodec g x).p a).isSome
  | none, _ => true

def litOkA (spec : BodySpec) (k : Name) (a : Attr) : Bool :=
  match spec.names.at k with
  | some ns => altsOkA ns.alts a
  | none => altsOkA (spec.wild.getD none) a

/-- **Content admission (objects): every present name whose field is a literal carries one of
    that literal's alternatives.**

    The other half of an object option's admission, and the half `keysOkV` alone cannot state.
    Present-only: the quantifier runs over the *map's* key set, so an absent name is `keysOkV`'s
    business. `Finset.attach`'s decidable `∀ k ∈ keys` is what `decide` resolves through, the
    same route `valPresentT` takes and the one `Finset.toList` would spoil. -/
def literalsOk (spec : BodySpec) (keys : Finset Name)
    (f : {k // k ∈ keys} → Value) : Bool :=
  decide (∀ k : {k // k ∈ keys}, litOkV spec k.1 (f k) = true)

/-- …and its read-side twin. -/
def literalsOkA (spec : BodySpec) (keys : Finset Name)
    (g : {k // k ∈ keys} → Attr) : Bool :=
  decide (∀ k : {k // k ∈ keys}, litOkA spec k.1 (g k) = true)

/-! ### What the open block does, pinned

Four cases, stated on `keysOkV` and `literalsOk` together because that pair **is** an object
option's admission. They are `by decide`, so each is the kernel running the definitions rather
than a claim about them. -/

/-- No declared name: everything the body claims, it claims through its block. -/
private def noNames : MapOf NameSpec := ⟨∅, fun k => absurd k.2 (Finset.notMem_empty k.1)⟩

/-- An open block at a term that pins no literal, which is every non-literal term. -/
private def openAny : BodySpec := ⟨noNames, some none⟩

/-- An open block at the literal `"x"`. -/
private def openLit : BodySpec := ⟨noNames, some (some ⟨.string, "x"⟩)⟩

/-- No block at all. -/
private def closedNone : BodySpec := ⟨noNames, none⟩

/-- **An open block admits an undeclared name**, which is the whole of the change: the body
    claims the name, so `keysOkV` passes, and the block pins nothing, so the content is free. -/
theorem open_block_admits_undeclared :
    (keysOkV openAny {"A"} && literalsOk openAny {"A"} (fun _ => .str "y")) = true := by decide

/-- **A literal block refuses the wrong value at an undeclared name.** The block does real
    work rather than only widening: an undeclared name is read by the block's alternatives the
    way a declared name is read by its field's. -/
theorem open_literal_block_refuses :
    (keysOkV openLit {"A"} && literalsOk openLit {"A"} (fun _ => .str "y")) = false := by decide

/-- …and admits the right one. -/
theorem open_literal_block_admits :
    (keysOkV openLit {"A"} && literalsOk openLit {"A"} (fun _ => .str "x")) = true := by decide

/-- **A closed body is unchanged.** No block, so an undeclared name is refused on the first
    conjunct exactly as it always was. -/
theorem closed_refuses_undeclared :
    (keysOkV closedNone {"A"} && literalsOk closedNone {"A"} (fun _ => .str "y")) = false := by
  decide

/-- The open block makes an undeclared name top on the write side. -/
theorem open_block_presence_topV :
    keysOkV openAny {"A"} = true := by decide

/-- The same undeclared name is top on the read side. -/
theorem open_block_presence_topA :
    keysOkA openAny {"A"} = true := by decide

/-- The forbidden lattice element refuses a present name on both sides. The checks reduce in the
    kernel. `Body.spec` maps an optional bottom slot to this element. -/
private def forbiddenNames : MapOf NameSpec :=
  ⟨{"A"}, fun _ => ⟨(false, true), (false, true), none⟩⟩

private def forbiddenSpec : BodySpec := ⟨forbiddenNames, none⟩

theorem optional_never_forbidsV :
    keysOkV forbiddenSpec {"A"} = false := by decide

theorem optional_never_forbidsA :
    keysOkA forbiddenSpec {"A"} = false := by decide

/-- A bottom slot with a stand-in admits an absent name on the read side. -/
private def bottomFallbackNames : MapOf NameSpec :=
  ⟨{"A"}, fun _ => ⟨(true, false), (false, true), none⟩⟩

private def bottomFallbackSpec : BodySpec := ⟨bottomFallbackNames, none⟩

example :
    keysOkA bottomFallbackSpec ∅ = true := by decide

/-- An object option decides by structure, never by being attempted: the names lie in the
    spec's interval, and every present literal field carries one of its alternatives. -/
def OptionSem.byStructure (spec : BodySpec) (c : Codec) : OptionSem :=
  { admitA := fun a => match a with
      | .m keys g => keysOkA spec keys && literalsOkA spec keys g
      | _ => false
    admitV := fun v => match v with
      | .map keys f => keysOkV spec keys && literalsOk spec keys f
      | _ => false
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

/-- The builder `denote` uses for a union option. -/
def optionSemOf (c : Codec) : Option BodySpec → OptionSem
  | some spec => .byStructure spec c
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

/-! ### Sub-selection

A slice keeps some of the options and drops the rest. `(D)` survives that by itself, because it is
a `Pairwise` property and `List.Pairwise.sublist` carries it to any sublist with no axioms at all.
`UniqueBothWays` does **not**, and the reason is the singleton filter test below. -/

/-- A list that holds at most one entry, and holds this one, is exactly it. -/
theorem eq_singleton_of_mem_of_length_le_one {α : Type} {l : List α} {x : α}
    (hx : x ∈ l) (hl : l.length ≤ 1) : l = [x] := by
  cases l with
  | nil => exact absurd hx (by simp)
  | cons y ys =>
    cases ys with
    | nil =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rw [hx]
    | cons z zs => simp at hl

/-- A list no two of whose entries stand in any relation holds at most one entry. -/
theorem length_le_one_of_pairwise_false {α : Type} {l : List α}
    (h : List.Pairwise (fun _ _ : α => False) l) : l.length ≤ 1 := by
  cases l with
  | nil => simp
  | cons x xs =>
    cases xs with
    | nil => simp
    | cons y ys => exact absurd ((List.pairwise_cons.mp h).1 y (by simp)) id

/-- **No value and no attribute is admitted by two options.**

    The certificate a discriminated selection carries and an undiscriminated one does not. Pass 7's
    structural meet is a syntactic test that implies this; stated here as the property the lemma
    below actually needs, so the lemma does not wait on the test. -/
def AdmitsAtMostOne (os : List OptionSem) : Prop :=
  (∀ t, (os.filter (·.admitV t)).length ≤ 1) ∧
  (∀ a, (os.filter (·.admitA a)).length ≤ 1)

/-- **(U) at the acting options survives a sub-selection, under the certificate and not without it.**

    `UniqueBothWays` reads `os.filter (·.admitV t) = [o]`, which is a *singleton* test, so it is not
    monotone on its own: dropping an option can turn a filter of two into a filter of one, making a
    premise that was vacuous live and demanding a conclusion nothing previously required. **Slicing
    an uncertified union can break it.**

    Under `AdmitsAtMostOne` the question does not arise. No filter is ever longer than one, so a
    singleton in the sub-selection is a singleton in the whole, the original's obligation applies,
    and the answer restricts. The certificate is why a slice of a union is safe, and it is a
    premise rather than decoration. -/
theorem uAtAct_sublist {os us : List OptionSem} (hsub : us.Sublist os)
    (hcert : AdmitsAtMostOne os) (h : UniqueBothWays os) : UniqueBothWays us := by
  -- one argument, used on both halves: a singleton of the sub-selection is the whole's singleton
  have lift : ∀ (p : OptionSem → Bool) (o : OptionSem),
      (os.filter p).length ≤ 1 → us.filter p = [o] → os.filter p = [o] := by
    intro p o hlen hus
    have ho : o ∈ us.filter p := by rw [hus]; exact List.mem_singleton_self o
    have hmem := List.mem_filter.mp ho
    exact eq_singleton_of_mem_of_length_le_one
      (List.mem_filter.mpr ⟨hsub.subset hmem.1, hmem.2⟩) hlen
  -- and one for the conclusion: the whole's singleton restricts, because the member is kept
  have drop : ∀ (p : OptionSem → Bool) (o : OptionSem),
      o ∈ us → os.filter p = [o] → us.filter p = [o] := by
    intro p o hou hos
    have hp : p o = true := (List.mem_filter.mp (by rw [hos]; exact List.mem_singleton_self o)).2
    have hsl : (us.filter p).Sublist [o] := hos ▸ hsub.filter p
    have ho : o ∈ us.filter p := List.mem_filter.mpr ⟨hou, hp⟩
    exact eq_singleton_of_mem_of_length_le_one ho (hsl.length_le)
  exact
    ⟨fun o ho t a hus he =>
       drop _ o ho (h.1 o (hsub.subset ho) t a (lift _ o (hcert.1 t) hus) he),
     fun o ho a t a' hus hp he =>
       drop _ o ho (h.2 o (hsub.subset ho) a t a' (lift _ o (hcert.2 a) hus) hp he)⟩

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
