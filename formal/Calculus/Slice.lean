import Calculus.Typing

/-!
# The slice of a dissection

A clause names some of the keys and admits a set of tags at each. The extraction keeps the members
the clause admits; the exclusion keeps the members it rejects. Both give a dissection over the
**same keys** and fewer members.

**No key moves, and a pinned key is not special.** A key the clause pins to one tag is a constant
key on the fibre, and no normalisation drops a constant key. The field stays a required literal in
every member's body, because the codec writes the tag out of it, so the item carries that key
whatever the key set says: dropping it from the key set would change no admitted value and no
written attribute. A one-member result is a one-member dissection that still reads its key off
every item.

**The selection is certificate-preserving on its own.** Well-formedness of a union is a `Pairwise`
property, and `List.Pairwise.sublist` carries it to any sub-selection with an empty axiom set. So
keeping fewer members needs no lemma of its own, and there is none here.

Not in `Merge.lean`, which says of itself that it is a syntactic operation on `Body` with a typing
corollary and sits with what it is about. This is a syntactic operation on `TagMap`, so it sits
here by the same rule. The product of two dissections is a merge and belongs there.
-/

namespace Calculus

/-! ## The clause -/

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

/-! ## The two operations -/

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

/-! ## The typing corollaries -/

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

end Calculus
