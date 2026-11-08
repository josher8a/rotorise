import Calculus.Dynamo.Alg.KeyMatch
import Calculus.Dynamo.Alg.DerivedItem

/-!
# The row of an item, built from the keys

The graph of an item (`Split.graph`) joins a key part to the row that the codec writes. Its key
function is free and total. The host key function is `keyOf`, which refuses: an absent part, a
segment that holds the separator, a spec that selects nothing, an empty value. This file builds the
key part from `keyOf`, at the member of each key name, and states the row that results.

The key of a name is read at the item as printed text: a string is its text, and a number is its
numeral. `carrierOf` gives that text the carrier of the member of the name. A string key is the text,
and a composite key is the join of its segments. A number key is the numeral of the text, and the text
that is no numeral is a refusal. A composite key is a string, so a composite key at a number key name
is a refusal. A refused key is a refusal of the whole key part.

**The member `B` is outside the model.** An item of strings carries no bytes, so the key part of a
name at `B` has no value to build. Each definition takes `mem k ≠ .b` for each key name, and that
premise is the narrowing: the row of an item with a bytes key is no statement of the model.

**The row restricts the refused points away.** A key part is built or refused. Where a key is refused,
the graph needs a key part to join, so it takes the empty key part, and the restriction then removes
the item from the codec. `rowGraph_refuses` states that the removal is complete: at an item whose key is
refused the row writes nothing, and no row reads as that item. The empty key part is never a value of
the row.
-/

namespace Calculus

namespace DerivedItem

open Alg

variable (KS : Finset String) (mem : {k // k ∈ KS} → Member)

/-- **The carrier that the text of a key takes at a member.** A refusal is `none`, and no key is
    `some none`. A string key at `S` is the text. The segments of a composite key at `S` are the
    write of the key codec (`keyWrite`): their join with the separator where the segments are good,
    and a refusal where they are not (`carrierOf_segs_good`, `carrierOf_segs_bad`). A number key at
    `N` is the numeral of the text, where the text is a numeral. -/
def carrierOf (V : DerivedKey.StringView) (c : Char) :
    (m : Member) → m ≠ .b → DerivedKey.Out → Option (Option m.Carrier)
  | .b, h, _ => absurd rfl h
  | _, _, .nothing => some none
  | _, _, .refused => none
  | .s, _, .raw v => some (some v)
  | .s, _, .segs ss =>
      match DerivedKey.keyWrite V c (DerivedKey.segsAttr ss) with
      | some (.s k) => some (some k)
      | _ => none
  | .n, _, .raw v => if h : Numeral.WF v = true then some (some ⟨v, h⟩) else none
  | .n, _, .segs _ => none

/-- **The segments of a composite key that are good give their join.** The key part at a string
    member is the write of the key codec. -/
theorem carrierOf_segs_good (V : DerivedKey.StringView) (c : Char) (hb : Member.s ≠ .b)
    {ss : List String} (h : DerivedKey.Good V c ss) :
    carrierOf V c .s hb (.segs ss) = some (some (DerivedKey.joinS V c ss)) := by
  simp [carrierOf, DerivedKey.keyWrite, DerivedKey.segsAttr, DerivedKey.strs_map, h]

/-- **The segments of a composite key that are not good give a refusal.** The separator is a segment
    of the key, or the list is empty, so the key codec writes nothing. -/
theorem carrierOf_segs_bad (V : DerivedKey.StringView) (c : Char) (hb : Member.s ≠ .b)
    {ss : List String} (h : ¬ DerivedKey.Good V c ss) :
    carrierOf V c .s hb (.segs ss) = none := by
  simp [carrierOf, DerivedKey.keyWrite, DerivedKey.segsAttr, DerivedKey.strs_map, h]

/-- The printed text of an attribute: a string is its text, and a number is its numeral. -/
def printedAttr : Attr → Option String
  | .s v => some v
  | .n v => some v.1
  | _ => none

/-- **The item as the key spec reads it**: the printed text of each top-level attribute. -/
def itemOf (t : Value) : DerivedKey.Item String :=
  fun nm => (mA.out t).bind fun m => (m.at nm).bind printedAttr

variable {KS} {mem}
variable (V : DerivedKey.StringView) (hb : ∀ k, mem k ≠ .b) (c : Char) (specs : {k // k ∈ KS} → DerivedKey.KeySpec String)

/-- **The key part that the keys build at an item, or a refusal.** Each key name reads its spec at the
    item with `keyOf`, and gives the carrier of its member. One refused key refuses the key part. -/
def keyPartOf (item : DerivedKey.Item String) : Option (KeyPart KS mem) :=
  if h : ∀ k, (carrierOf V c (mem k) (hb k) (DerivedKey.keyOf false false item (specs k))).isSome then
    some fun k => (carrierOf V c (mem k) (hb k) (DerivedKey.keyOf false false item (specs k))).get (h k)
  else none

/-- **A composite key whose segments are not good refuses the key part.** A key name at a string
    member whose key is the segments of a list that is not good (it holds the separator, or it is
    empty) has no key part, so the row refuses the item. -/
theorem keyPartOf_none_of_bad {item : DerivedKey.Item String} {k : {k // k ∈ KS}}
    (hk : mem k = .s) {ss : List String}
    (ho : DerivedKey.keyOf false false item (specs k) = .segs ss) (hg : ¬ DerivedKey.Good V c ss) :
    keyPartOf V hb c specs item = none := by
  unfold keyPartOf
  rw [dif_neg]
  intro hall
  have h1 := hall k
  have key : ∀ (m : Member) (hm : m ≠ .b), m = .s → carrierOf V c m hm (.segs ss) = none := by
    intro m hm e
    subst e
    exact carrierOf_segs_bad V c hm hg
  rw [ho, key (mem k) (hb k) hk] at h1
  cases h1

/-- **The row of an item with derived keys.** The graph of the codec, with the key part that the keys
    build. A refused key part is the empty key part for the graph, and the restriction removes each
    such item (`rowGraph_refuses`). -/
def rowGraph (c0 : Codec) : Codec :=
  ((split KS mem).graph c0
      (fun t => (keyPartOf V hb c specs (itemOf t)).getD fun _ => none)).restrict
    fun t => (keyPartOf V hb c specs (itemOf t)).isSome

variable {c0 : Codec} {t a : Value}

/-- **The row of an item is the row of the codec with the key part that the keys build.** -/
theorem rowGraph_e :
    (rowGraph V hb c specs c0).e t = some a ↔
      ∃ r y, c0.e t = some r ∧ keyPartOf V hb c specs (itemOf t) = some y ∧
        a = (split KS mem).join r y := by
  unfold rowGraph
  rw [restrict_e_def]
  beta_reduce
  cases hk : keyPartOf V hb c specs (itemOf t) with
  | none =>
      rw [if_neg (show ¬ ((none : Option (KeyPart KS mem)).isSome = true) from Bool.false_ne_true)]
      constructor
      · intro h; cases h
      · rintro ⟨r, y, -, hy, -⟩
        cases hy
  | some y =>
      rw [if_pos (show ((some y).isSome = true) from rfl), Alg.Split.graph_e]
      have hg : (keyPartOf V hb c specs (itemOf t)).getD (fun _ => none) = y := by
        rw [hk]
        rfl
      constructor
      · rintro ⟨r, hr, rfl⟩
        exact ⟨r, y, hr, rfl, congrArg _ hg⟩
      · rintro ⟨r, y', hr, hy, rfl⟩
        cases hy
        exact ⟨r, hr, congrArg _ hg.symm⟩

/-- **The row of an item is lawful.** The key part adds no premise: the restriction keeps the law. -/
theorem rowGraph_lawful
    (hc : Lawful c0)
    (hw : ∀ {t r}, c0.e t = some r → (split KS mem).rows r ∧ (split KS mem).drop r = r) :
    Lawful (rowGraph V hb c specs c0) :=
  Lawful.restrict (Alg.Split.graph_lawful (s := split KS mem) hc hw) _

/-- **A refused key removes the item from the row.** Where the keys refuse, the row writes nothing at
    the item, and no row reads as the item. So the empty key part, which the graph takes there, is
    never a value of the row. -/
theorem rowGraph_refuses
    (hc : Lawful c0)
    (hw : ∀ {t r}, c0.e t = some r → (split KS mem).rows r ∧ (split KS mem).drop r = r)
    (h : keyPartOf V hb c specs (itemOf t) = none) :
    (rowGraph V hb c specs c0).e t = none ∧ ∀ a, (rowGraph V hb c specs c0).p a ≠ some t := by
  have he : (rowGraph V hb c specs c0).e t = none := by
    cases hx : (rowGraph V hb c specs c0).e t with
    | none => rfl
    | some a =>
        obtain ⟨r, y, -, hy, -⟩ := (rowGraph_e V hb c specs).mp hx
        rw [h] at hy
        cases hy
  refine ⟨he, fun a hp => ?_⟩
  have := (rowGraph_lawful V hb c specs hc hw).canon hp
  rw [he] at this
  cases this

end DerivedItem

end Calculus
