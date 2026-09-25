import Calculus.AlgRelations
import Calculus.AlgLists

/-!
# A second universe: JSON

The codec algebra takes its carriers as parameters. This module instantiates the algebra at a
JSON carrier, and imports no DynamoDB carrier. So the laws, the combinators and the join
are facts of the algebra, and not facts of one store.

The caller holds JSON values, and the store holds JSON values. So the caller carrier and the
stored carrier are both `Json`, and the member of a value is its JSON kind. A number is an
`Int`, so that no numeral parser enters the module.

The module instantiates these parts of the generic layer: the record `Alg.Codec`, the laws
`Alg.Lawful`, the refinement by `Alg.Lawful.restrict`, the adapter by `Alg.Lawful.through`, and
the join by `Alg.lawful_altCodec`, and the array by `Alg.lawful_entrywise`. The compatibility of
the join comes from `Alg.compat_of_common_bound'`: the identity codec bounds each ground codec,
because the two carriers are one type.

The module writes only three things itself: the carrier, the ground codecs with their laws, and
the prism of an array. Each of the three reads the carrier.
-/

namespace Calculus.JSON

/-- A JSON value. A number is an integer. -/
inductive Json where
  | null
  | bool (b : Bool)
  | num (n : Int)
  | str (s : String)
  | arr (xs : List Json)
  | obj (kvs : List (String × Json))

/-- The kind of a JSON value: the member that (W) reads. -/
inductive JMember where
  | null | bool | num | str | arr | obj
  deriving DecidableEq

/-- The kind of a JSON value. -/
def Json.member : Json → JMember
  | .null => .null
  | .bool _ => .bool
  | .num _ => .num
  | .str _ => .str
  | .arr _ => .arr
  | .obj _ => .obj

/-! ## Ground codecs -/

/-- The partial identity on the values of one kind. -/
def gate (m : JMember) (v : Json) : Option Json :=
  if v.member = m then some v else none

/-- The gate passes a value of its kind unchanged, and refuses every other value. -/
theorem gate_eq_some {m : JMember} {v a : Json} :
    gate m v = some a ↔ v.member = m ∧ a = v := by
  unfold gate
  split
  · next hm => exact ⟨(fun h => ⟨hm, (Option.some.inj h).symm⟩), (fun ⟨_, h⟩ => h ▸ rfl)⟩
  · next hm => exact ⟨(fun h => nomatch h), (fun ⟨h, _⟩ => absurd h hm)⟩

/-- The ground codec of one kind: the caller value is the stored value. -/
def ground (m : JMember) : Alg.Codec Json Json JMember :=
  { T := fun v => v.member = m
    μ := some m
    e := gate m
    p := gate m }

/-- A ground codec is lawful: the gate is its own inverse, and the gate passes one kind. -/
theorem lawful_ground (m : JMember) : Alg.Lawful Json.member (ground m) where
  retract he := let ⟨hm, h⟩ := gate_eq_some.mp he; gate_eq_some.mpr ⟨h ▸ hm, h.symm⟩
  canon hp := let ⟨hm, h⟩ := gate_eq_some.mp hp; gate_eq_some.mpr ⟨h ▸ hm, h.symm⟩
  writes hμ _ _ he :=
    let ⟨hm, h⟩ := gate_eq_some.mp he
    (h ▸ hm).trans (Option.some.inj hμ)

/-- The string codec. -/
def str : Alg.Codec Json Json JMember := ground .str
/-- The number codec. -/
def num : Alg.Codec Json Json JMember := ground .num
/-- The boolean codec. -/
def bool : Alg.Codec Json Json JMember := ground .bool
/-- The null codec. -/
def null : Alg.Codec Json Json JMember := ground .null

/-- The string codec is lawful. -/
theorem lawful_str : Alg.Lawful Json.member str := lawful_ground .str
/-- The number codec is lawful. -/
theorem lawful_num : Alg.Lawful Json.member num := lawful_ground .num
/-- The boolean codec is lawful. -/
theorem lawful_bool : Alg.Lawful Json.member bool := lawful_ground .bool
/-- The null codec is lawful. -/
theorem lawful_null : Alg.Lawful Json.member null := lawful_ground .null

/-! ## Derived codecs, lawful by the generic laws alone -/

/-- The non-negative numbers: a refinement of `num`. -/
def natNum : Alg.Codec Json Json JMember :=
  num.restrict fun v => match v with | .num n => decide (0 ≤ n) | _ => false

/-- A refinement of a lawful codec is lawful. -/
theorem lawful_natNum : Alg.Lawful Json.member natNum := lawful_num.restrict _

/-- The sign flip of a number. Every other value is unchanged. -/
def negate : Json → Json
  | .num n => .num (-n)
  | v => v

/-- The sign flip is an involution. -/
theorem negate_negate (v : Json) : negate (negate v) = v := by
  cases v <;> simp only [negate, Int.neg_neg]

/-- The negated numbers: the caller holds `n`, and the store holds `-n`. -/
def negNum : Alg.Codec Json Json JMember := num.through negate negate

/-- An involution cancels on each side, so the adapter keeps the laws. -/
theorem lawful_negNum : Alg.Lawful Json.member negNum :=
  lawful_num.through ⟨fun v _ => negate_negate v, fun v _ => negate_negate v⟩

/-- The identity codec. Each ground codec is below the identity codec, because the caller
    carrier is the stored carrier. -/
def idCodec : Alg.Codec Json Json JMember :=
  { T := fun _ => True, μ := none, e := some, p := some }

/-- The identity codec reads canonically. -/
theorem canon_idCodec : Alg.Canon idCodec := fun _ _ h => (Option.some.inj h).symm ▸ rfl

/-- A ground codec is below the identity codec. -/
theorem sub_ground_id (m : JMember) : Alg.Sub (ground m) idCodec :=
  ⟨fun _ _ h => (gate_eq_some.mp h).2 ▸ rfl, fun _ _ h => (gate_eq_some.mp h).2 ▸ rfl⟩

/-- **A union of lawful codecs below the identity codec is lawful.** The identity codec is the
    common bound, so each pair of options is compatible. The union names no member. -/
theorem lawful_join {os : List (Alg.Codec Json Json JMember)}
    (h : ∀ o ∈ os, Alg.Lawful Json.member o ∧ Alg.Sub o idCodec) :
    Alg.Lawful Json.member (Alg.altCodec os none) :=
  Alg.lawful_altCodec (fun o ho => (h o ho).1)
    (fun _ ho _ ho' =>
      Alg.compat_of_common_bound' (h _ ho).2 (h _ ho').2 canon_idCodec (h _ ho').1)
    (fun _ hμ => nomatch hμ)

/-- A string or a number. -/
def strOrNum : Alg.Codec Json Json JMember := Alg.altCodec [str, num] none

/-- The union of the string codec and the number codec is lawful. -/
theorem lawful_strOrNum : Alg.Lawful Json.member strOrNum :=
  lawful_join fun o ho => by
    cases ho with
    | head => exact ⟨lawful_str, sub_ground_id _⟩
    | tail _ ho => cases ho with
      | head => exact ⟨lawful_num, sub_ground_id _⟩
      | tail _ ho => nomatch ho

/-! ## Arrays -/

/-- The array constructor, as a prism. The caller side and the stored side share the prism. -/
def arrP : Alg.Ctor (List Json) Json where
  into := .arr
  out := fun v => match v with | .arr xs => some xs | _ => none
  out_into _ := rfl
  into_out {v _} h := by cases v <;> first | cases h; rfl | exact nomatch h

/-- The array codec over an element codec: each entry through the element codec. -/
def arr (c : Alg.Codec Json Json JMember) : Alg.Codec Json Json JMember :=
  Alg.entrywise arrP arrP .arr (fun xs => ∀ x ∈ xs, c.T x) c.e c.p

/-- An array of a lawful element codec is lawful, entry by entry. -/
theorem lawful_arr {c : Alg.Codec Json Json JMember} (h : Alg.Lawful Json.member c) :
    Alg.Lawful Json.member (arr c) :=
  Alg.lawful_entrywise (fun _ => rfl) (fun _ _ => h.retract) (fun _ _ => h.canon)

/-- An array of strings. -/
def strArr : Alg.Codec Json Json JMember := arr str

/-- An array of strings is lawful. -/
theorem lawful_strArr : Alg.Lawful Json.member strArr := lawful_arr lawful_str

end Calculus.JSON
