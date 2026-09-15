import Calculus.Orthogonality

/-!
# The slice

A dissection and a union each carry members, and a clause selects among them. The first half of
this file is the dissection's slice and the second is the union's. Both keep members and move
nothing else, and the two clauses differ because the two selections read different data: a
dissection's key is a tag and a union option is told apart by its structure.

A clause names some of the keys and admits a set of tags at each. The extraction keeps the members
the clause admits; the exclusion keeps the members it rejects. Both give a dissection over the
**same keys** and fewer members.

**No key moves, and a pinned key is not special.** A key the clause pins to one tag is a constant
key on the fibre, and no normalisation drops a constant key. The field stays a required literal in
every member's body, because the codec writes the tag out of it, so the item carries that key
whatever the key set says: dropping it from the key set would change no admitted value and no
written attribute. A one-member result is a one-member dissection that still reads its key off
every item.

**(D) is certificate-preserving on its own, and (U) is not.** Well-formedness of a union is a
`Pairwise` property, and `List.Pairwise.sublist` carries it to any sub-selection with an empty
axiom set. So keeping fewer members proves nothing new about (D) at either level. (U) reads a
singleton filter instead, which no sub-selection preserves without a certificate: that is the
premise the union's half takes and the dissection's half needs no name for.

Not in `Merge.lean`, which says of itself that it is a syntactic operation on `Body` with a typing
corollary and sits with what it is about. These are syntactic operations on `TagMap` and on the
option list, so they sit here by the same rule. The product of two dissections is a merge and
belongs there.
-/

namespace Calculus

/-! ## The clause of a dissection -/

/-- **A partial assignment that admits a set of tags at each key it names.**

    `keys` are the keys the clause speaks about, a subset of the dissection's. `tags` gives the
    admitted set at each, and `ne` says every such set admits something: a key admitting nothing
    keeps no member, which is `never` said in a place that cannot say it.

    A subset and a function on it, rather than a total function into `Option (Finset String)`. The
    two decide by the same routes, measured, so decidability does not choose between them; this one
    is chosen because `tags k` is a tag set at the site rather than an `Option` every later
    statement unwraps. -/
structure Clause (ks : Finset Name) where
  keys : Finset Name
  sub  : keys ⊆ ks
  tags : {k // k ∈ keys} → Finset String
  ne   : ∀ k, (tags k).Nonempty

/-- Whether a clause admits an assignment: its tag at every key the clause names is one the
    clause allows. -/
def Clause.admits {ks : Finset Name} (c : Clause ks) (asg : Assignment ks) : Prop :=
  ∀ k ∈ c.keys, ∀ h : k ∈ c.keys, asg ⟨k, c.sub h⟩ ∈ c.tags ⟨k, h⟩

/-- Admission is decided by `∀ k ∈ keys`, the route `asgEq` takes and the record carries. -/
instance {ks : Finset Name} (c : Clause ks) (asg : Assignment ks) :
    Decidable (c.admits asg) := by
  unfold Clause.admits; infer_instance

/-! ## The two operations on a dissection -/

/-- **The extraction**: the members the clause admits, over the same keys.

    An extraction that keeps nothing is the empty table over `ks`, which `typed_dunion_nil` already
    types, so there is no case split and no sum of results. -/
def TagMap.extract {α : Type} (m : TagMap α) (c : Clause m.ks.1) : TagMap α :=
  { ks := m.ks
    keys := m.keys.filter c.admits
    get := fun k => m.get ⟨k.1, (Finset.mem_filter.mp k.2).1⟩ }

/-- **The exclusion**: the members the clause rejects, over the same keys. The complement filter,
    and the same shape as the extraction, because neither moves a key. -/
def TagMap.exclude {α : Type} (m : TagMap α) (c : Clause m.ks.1) : TagMap α :=
  { ks := m.ks
    keys := m.keys.filter (fun asg => ¬ c.admits asg)
    get := fun k => m.get ⟨k.1, (Finset.mem_filter.mp k.2).1⟩ }

/-- A member of the extraction is a member of the original that the clause admits. -/
theorem TagMap.mem_extract {α : Type} {m : TagMap α} {c : Clause m.ks.1}
    {asg : Assignment m.ks.1} : asg ∈ (m.extract c).keys ↔ asg ∈ m.keys ∧ c.admits asg :=
  Finset.mem_filter

/-- ...and a member of the exclusion is one it rejects. -/
theorem TagMap.mem_exclude {α : Type} {m : TagMap α} {c : Clause m.ks.1}
    {asg : Assignment m.ks.1} : asg ∈ (m.exclude c).keys ↔ asg ∈ m.keys ∧ ¬ c.admits asg :=
  Finset.mem_filter

/-- A key of the extraction is a key of the original, named once so the typing corollaries do not
    each have to pin `Finset.mem_filter`'s decidability argument at the site. -/
theorem TagMap.extract_sub {α : Type} {m : TagMap α} {c : Clause m.ks.1}
    (k : {x // x ∈ (m.extract c).keys}) : k.1 ∈ m.keys :=
  (TagMap.mem_extract.mp k.2).1

/-- ...and the same for the exclusion. -/
theorem TagMap.exclude_sub {α : Type} {m : TagMap α} {c : Clause m.ks.1}
    (k : {x // x ∈ (m.exclude c).keys}) : k.1 ∈ m.keys :=
  (TagMap.mem_exclude.mp k.2).1

/-! ## The typing corollaries of a dissection's slice -/

/-- **The extraction of a derivable dissection is derivable.**

    The kept members carry the original judgements and the original `hone`, at the same keys.
    Nothing is proved about a member that was not proved before: the extraction keeps members and
    moves nothing, so each premise is the one it already had. -/
theorem typed_dunion_extract {variants : TagMap Body} (c : Clause variants.ks.1)
    {Ts : {k // k ∈ variants.keys} → Held}
    (h : ∀ k, Typed (.object (variants.get k)) (Ts k) (some .M))
    (hone : ∀ k, (variants.get k).namesTags variants.ks.1 k.1) :
    Typed (.dunion (variants.extract c))
      (HVariants (variants.extract c) (fun k => Ts ⟨k.1, TagMap.extract_sub k⟩))
      (some .M) :=
  .dunion (fun _k => h _) (fun _k => hone _)

/-- **The exclusion of a derivable dissection is derivable**, by the same argument at the
    complement. -/
theorem typed_dunion_exclude {variants : TagMap Body} (c : Clause variants.ks.1)
    {Ts : {k // k ∈ variants.keys} → Held}
    (h : ∀ k, Typed (.object (variants.get k)) (Ts k) (some .M))
    (hone : ∀ k, (variants.get k).namesTags variants.ks.1 k.1) :
    Typed (.dunion (variants.exclude c))
      (HVariants (variants.exclude c) (fun k => Ts ⟨k.1, TagMap.exclude_sub k⟩))
      (some .M) :=
  .dunion (fun _k => h _) (fun _k => hone _)

/-- The extraction holds no value the original did not: a witness at the extraction names a member
    the original also has. A re-indexing rather than an identity, because the two held sets are
    quantified over different member sets. -/
theorem hvariants_extract {variants : TagMap Body} (c : Clause variants.ks.1)
    {Ts : {k // k ∈ variants.keys} → Held} {v : Value}
    (hv : HVariants (variants.extract c) (fun k => Ts ⟨k.1, TagMap.extract_sub k⟩) v) :
    HVariants variants Ts v :=
  hv.elim fun _k hk => ⟨_, hk⟩


/-! ## The slice of a certified union

The same two operations one level up, where the members are option terms rather than a keyed
table. **The clause carries an `Alts` at each key it names, not a tag set.** A tag is read back as
text, so a `dunion`'s discriminator sits at `string` or `decimal` and the clause above is a
`Finset String`. A union option is told apart by the meet instead: `OrthS` separates two objects at
`boolean` and `binary` as well as at those two, so a clause over text could not slice a union the
classifier certifies. Non-emptiness is `Alts`'s own, which is why the record below has no `ne`
field where `Clause` has one.

**The certificate is a premise here, and it was not above.** A `TagMap`'s keys make (D) and (U) by
themselves. A `List Term` makes neither: `UniqueBothWays` reads a singleton filter, so dropping an
option can turn a filter of two into a filter of one and demand an answer nothing previously owed.
`uAtAct_sublist` is that argument, and it takes `AdmitsAtMostOne`. So the two (U) corollaries below
take `Separated`, and a union with no certificate has no slice.
-/

/-- The alternatives lie inside the clause's, at one base.

    `disjAlts` with the membership turned round, and it is deliberately the same shape. -/
def subAlts {α : Type} [DecidableEq α] (ls c : NEFinset α) : Bool :=
  decide (∀ x ∈ ls.1, x ∈ c.1)

/-- A declared name's alternatives lie inside the clause's, at the same base.

    Four rows, and they are `altsDisj`'s four for `altsDisj`'s reasons: `number` declines because
    `WFDouble`'s equality is a field of `numericHost`, and `null` because its one alternative is
    every null literal's, so a clause there would keep each member rather than select among them.
    A name pinned at one base against a clause at another is no match, which is the `_` row. -/
def altsSub : Option Alts → Alts → Bool
  | some ⟨.string, ls⟩,  ⟨.string, c⟩  => subAlts ls c
  | some ⟨.decimal, ls⟩, ⟨.decimal, c⟩ => subAlts ls c
  | some ⟨.boolean, ls⟩, ⟨.boolean, c⟩ => subAlts ls c
  | some ⟨.binary, ls⟩,  ⟨.binary, c⟩  => subAlts ls c
  | _, _ => false

/-- **A clause at union level**: the names it speaks about, and the alternatives it admits at each.

    No index, where `Clause` is indexed by the dissection's key set. A union declares no key set,
    so a name the clause asks for that no option declares is a clause that keeps nothing, which is
    `never` said in a place that can say it. -/
structure AltClause where
  keys : Finset Name
  alts : {k // k ∈ keys} → Alts

/-- One clause key, answered against one option's spec: the name is declared, it is **required**,
    and its alternatives lie inside the clause's.

    `litDisjAt`'s shape with the subset test in place of the disjointness one, and `required` is
    read for `litDisjAt`'s reason. An optional literal name admits the map that omits the name, so
    the option holds values outside every fibre the clause describes and the clause does not
    describe the option. A `fallback` literal **is** required — `Body.spec` marks it so, and §4's
    `(fallback)` concludes `req` — so a fallback discriminator is kept here where `tagsOfField`
    refuses it. The two rules differ because this one writes no tag. -/
def litSubAt (s : MapOf NameSpec) (c : AltClause) (k : {k // k ∈ c.keys}) : Bool :=
  match s.at k.1 with
  | some ns => ns.required && altsSub ns.alts (c.alts k)
  | none => false

/-- **Whether a clause describes an option**: the option is an object, and it answers at every key
    the clause names. A non-object option has no spec and is never kept. -/
def AltClause.admits (c : AltClause) (t : Term) : Bool :=
  match specOf t with
  | some s => decide (∀ k : {k // k ∈ c.keys}, litSubAt s c k = true)
  | none => false

/-- **The extraction**: the options the clause describes, in their original order. -/
def AltClause.extract (c : AltClause) (opts : List Term) : List Term :=
  opts.filter c.admits

/-- **The exclusion**: the complement of the same predicate, so the two partition the options and
    no option is both kept and dropped. -/
def AltClause.exclude (c : AltClause) (opts : List Term) : List Term :=
  opts.filter (fun t => ! c.admits t)

/-- The extraction keeps options and reorders none, which is what every corollary below reads. -/
theorem AltClause.extract_sublist (c : AltClause) (opts : List Term) :
    (c.extract opts).Sublist opts := List.filter_sublist

/-- ...and the same for the exclusion. -/
theorem AltClause.exclude_sublist (c : AltClause) (opts : List Term) :
    (c.exclude opts).Sublist opts := List.filter_sublist

/-! ### The typing corollaries -/

/-- **A sub-selection of typed options is typed**, at held sets and members that are the
    sub-selections of the originals.

    An existential, because the three lists the rule reads are positional: a selection speaks about
    the option, and the held set and the member at that position go or stay with it. The `Sublist`s
    are what the callers need, and they are what (D) and `HUnion` are each read through.

    On the sub-selection and not on the filter. The filter form decides `p t` at each step and
    splits on the answer; this one recurses on `List.Sublist`, which already carries the decision
    in its constructor, and inverts the judgement in each case. -/
theorem TypedListμ.sublist {opts' opts : List Term} {Ts μs} (hsub : opts'.Sublist opts)
    (h : TypedListμ opts Ts μs) :
    ∃ Ts' μs', TypedListμ opts' Ts' μs' ∧ Ts'.Sublist Ts ∧ μs'.Sublist μs := by
  -- the recursion runs on `hsub`: `TypedListμ` is mutually inductive with `Typed`, and the
  -- `induction` tactic declines a mutually inductive type
  induction hsub generalizing Ts μs with
  | slnil => cases h; exact ⟨[], [], .nil, .slnil, .slnil⟩
  | cons _ _ ih =>
    cases h with
    | cons _ hs =>
      obtain ⟨Ts', μs', hts, hsT, hsμ⟩ := ih hs
      exact ⟨Ts', μs', hts, hsT.cons _, hsμ.cons _⟩
  | cons_cons _ _ ih =>
    cases h with
    | cons ht hs =>
      obtain ⟨Ts', μs', hts, hsT, hsμ⟩ := ih hs
      exact ⟨_ :: Ts', _ :: μs', .cons ht hts, hsT.cons_cons _, hsμ.cons_cons _⟩

/-- **The extraction of a derivable union is derivable.**

    Nothing is proved about an option that was not proved before: each kept option carries the
    judgement it already had. (D) is a `Pairwise` property, so `List.Pairwise.sublist` carries it
    to the kept held sets with an empty axiom set. The one lemma this needs is `TypedListμ.sublist`
    above, and that lemma is about the positional lists, not about (D). -/
theorem typed_union_extract {opts : List Term} {Ts μs} (c : AltClause)
    (h : TypedListμ opts Ts μs) (hD : DIncomp Ts) :
    ∃ Ts' μs', Ts'.Sublist Ts ∧ μs'.Sublist μs ∧
      Typed (.union (c.extract opts)) (HUnion Ts') (unanimous μs') := by
  obtain ⟨Ts', μs', hts, hsT, hsμ⟩ := h.sublist (c.extract_sublist opts)
  exact ⟨Ts', μs', hsT, hsμ, .union hts (List.Pairwise.sublist hsT hD)⟩

/-- **The exclusion of a derivable union is derivable**, by the same argument at the complement. -/
theorem typed_union_exclude {opts : List Term} {Ts μs} (c : AltClause)
    (h : TypedListμ opts Ts μs) (hD : DIncomp Ts) :
    ∃ Ts' μs', Ts'.Sublist Ts ∧ μs'.Sublist μs ∧
      Typed (.union (c.exclude opts)) (HUnion Ts') (unanimous μs') := by
  obtain ⟨Ts', μs', hts, hsT, hsμ⟩ := h.sublist (c.exclude_sublist opts)
  exact ⟨Ts', μs', hsT, hsμ, .union hts (List.Pairwise.sublist hsT hD)⟩

/-- The slice holds no value the original did not. A sub-selection of the held sets, so the
    disjunction narrows. -/
theorem hunion_sublist {Ts' Ts : List Held} (hs : Ts'.Sublist Ts) {v : Value}
    (hv : HUnion Ts' v) : HUnion Ts v :=
  hv.elim fun T hT => ⟨T, hs.subset hT.1, hT.2⟩

/-! ### The certificate, and (U) -/

/-- Denoting the options commutes with keeping some of them: `semsOf` is a map. -/
theorem semsOf_sublist {opts' opts : List Term} (hs : opts'.Sublist opts) :
    (semsOf opts').Sublist (semsOf opts) :=
  List.Sublist.map _ hs

/-- **The classifier's certificate survives the slice**, because it is `Pairwise`. -/
theorem separated_sublist {opts' opts : List Term} (hs : opts'.Sublist opts)
    (h : Separated opts) : Separated opts' :=
  List.Pairwise.sublist hs h

/-- **(U) at the acting options survives the extraction, under the certificate.**

    `Separated` is the premise and not decoration. `UniqueBothWays` is a singleton test and is not
    monotone on its own, so slicing an uncertified union can make a vacuous premise live;
    `uAtAct_sublist` is where that argument is written, and `admitsAtMostOne_of_separated` is what
    supplies it here. -/
theorem uAtAct_extract {opts : List Term} (c : AltClause)
    (hsep : Separated opts) (h : UAtAct opts) : UAtAct (c.extract opts) :=
  uAtAct_sublist (semsOf_sublist (c.extract_sublist opts))
    (admitsAtMostOne_of_separated hsep) h

/-- ...and the exclusion, at the complement of the same predicate. -/
theorem uAtAct_exclude {opts : List Term} (c : AltClause)
    (hsep : Separated opts) (h : UAtAct opts) : UAtAct (c.exclude opts) :=
  uAtAct_sublist (semsOf_sublist (c.exclude_sublist opts))
    (admitsAtMostOne_of_separated hsep) h

end Calculus
