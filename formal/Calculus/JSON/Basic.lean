import Calculus.Lang.HeldFree
import Calculus.Lang.ExactA

/-!
# A second universe: JSON

The codec algebra takes its carrier as a parameter. This module instantiates the algebra at a
JSON carrier, and imports no DynamoDB carrier. So the laws, the combinators and the join
are facts of the algebra, and not facts of one store.

The carrier is `Json`, and the member of a value is its JSON kind. A number is an
`Int`, so that no numeral parser enters the module.

The module instantiates these parts of the generic layer: the record `Alg.Codec`, the laws
`Alg.Lawful`, the refinement by `Alg.Lawful.restrict`, the adapter by `Alg.Lawful.through`, the
array by `Alg.lawful_entrywise`, and the term language with its soundness at the signature
`jsonSyn`. A union term is lawful by `Alg.soundness`, and its options are compatible by
`Alg.compat_of_HF`: the identity codec bounds each ground codec.

The module writes only four things itself: the carrier, the ground codecs with their laws, the
prism of an array, and the signature. Each of the four reads the carrier.
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
def ground (m : JMember) : Alg.Codec Json JMember :=
  Alg.Codec.ofEP (T := fun v => v.member = m)
    (μ := some m)
    (e := gate m)
    (p := gate m)

/-- A ground codec is lawful: the gate is its own inverse, and the gate passes one kind. -/
theorem lawful_ground (m : JMember) : Alg.Lawful Json.member (ground m) :=
  .ofRC (fun he => let ⟨hm, h⟩ := gate_eq_some.mp he; gate_eq_some.mpr ⟨h ▸ hm, h.symm⟩)
    (fun hp => let ⟨hm, h⟩ := gate_eq_some.mp hp; gate_eq_some.mpr ⟨h ▸ hm, h.symm⟩)
    (fun hμ _ _ he =>
      let ⟨hm, h⟩ := gate_eq_some.mp he
      (h ▸ hm).trans (Option.some.inj hμ))

/-- The string codec. -/
def str : Alg.Codec Json JMember := ground .str
/-- The number codec. -/
def num : Alg.Codec Json JMember := ground .num
/-- The boolean codec. -/
def bool : Alg.Codec Json JMember := ground .bool
/-- The null codec. -/
def null : Alg.Codec Json JMember := ground .null

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
def natNum : Alg.Codec Json JMember :=
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
def negNum : Alg.Codec Json JMember := num.through negate negate

/-- An involution cancels on each side, so the adapter keeps the laws. -/
theorem lawful_negNum : Alg.Lawful Json.member negNum :=
  lawful_num.through ⟨fun v _ => negate_negate v, fun v _ => negate_negate v⟩

/-- A ground codec is below the identity codec. -/
theorem sub_ground_id (m : JMember) : Alg.Sub (ground m) Alg.idCodec :=
  .ofEP (fun _ _ h => (gate_eq_some.mp h).2 ▸ rfl) (fun _ _ h => (gate_eq_some.mp h).2 ▸ rfl)

/-! ## The JSON signature

The term language and its soundness are the generic ones at `jsonSyn`. JSON's primitives are its
kinds, and a predicate is a function. The term language has no list, map or set former here, and
the top is the identity codec. -/

/-- **The JSON signature**: the kinds, a predicate at each side, and no generator. -/
abbrev jsonSig : Alg.Sig where
  Ground := JMember
  P _ := Json → Bool
  G _ := Empty
  decG _ := inferInstance

/-- **The JSON syntax**: the signature at the host orientation. -/
abbrev jsonSyn : Alg.Syn := ⟨jsonSig, .host⟩

/-- **The JSON meaning** of that signature. Both carriers are `Json`, and a predicate is its own
    meaning. -/
instance jsonSem : Alg.Mean jsonSig where
  V := Json
  Mem := JMember
  mem := Json.member
  decM := inferInstance
  ground := ground
  lawful_ground := lawful_ground
  carrier_ground _ := ⟨fun he => (gate_eq_some.mp he).1, fun hp => (gate_eq_some.mp hp).2 ▸
    (gate_eq_some.mp hp).1⟩
  eval
    | false, q => q
    | true, q => q
  truth _ _ := true
  eval_truth
    | false, _ => rfl
    | true, _ => rfl
  d _ := 1
  d_pos _ := Nat.one_pos
  list := none
  map := none
  set := none

/-- **The one table of JSON**: the universe names no generator, so it has no `held`. -/
def jsonTable : Alg.Table jsonSyn := fun g => nomatch g

variable {α : Alg.Table jsonSyn}

/-- **The one stored table of JSON**: the store names no generator. -/
def jsonTableA : Alg.Table jsonSyn.op := fun g => nomatch g

variable {β : Alg.Table jsonSyn.op}

/-- The laws of the identity codec that the held-free theory reads: each kind is below it. -/
instance id_topLaws : Alg.TopLaws jsonSyn where
  ground := sub_ground_id
  set _ h := nomatch h

/-- A string or a number, as a term. -/
def strOrNumTerm : Alg.Term jsonSyn := .union [.prim .str, .prim .num]

/-- A string or a number. -/
noncomputable def strOrNum : Alg.Codec Json JMember := Alg.denote jsonTable jsonTableA strOrNumTerm

/-- **The union of the string codec and the number codec is lawful**, by the generic soundness:
    the two options are held-free, so the identity codec bounds both, and they are compatible. -/
theorem lawful_strOrNum : Alg.Lawful Json.member strOrNum := by
  have hty : ∀ m, Alg.Typed jsonTable jsonTableA (Alg.Term.prim (S := jsonSyn) m) (ground m).T (some m) :=
    fun m => .prim m
  refine Alg.soundness (.union (.cons (hty _) (.cons (hty _) .nil))) ⟨⟨trivial, trivial, trivial⟩,
    fun s hs t ht => ?_⟩
  have hl : ∀ x ∈ [Alg.Term.prim (S := jsonSyn) .str, .prim .num],
      Alg.Lawful Json.member (Alg.denote jsonTable jsonTableA x) := fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact lawful_ground _
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact lawful_ground _
      · exact nomatch hx
  have hf : ∀ x ∈ [Alg.Term.prim (S := jsonSyn) .str, .prim .num], Alg.HF x := fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · trivial
    · rcases List.mem_cons.mp hx with rfl | hx
      · trivial
      · exact nomatch hx
  exact Alg.compat_of_HF (S := jsonSyn) (hf s hs) (hf t ht) (hl t ht)

/-! ## Exactness

The row of a kind is the kind test. So the exactness of every admission row of the term language
holds at `jsonSyn`, by `Alg.Adm_exact` and `Alg.AdmA_exact`. -/

/-- The gate admits exactly the values of its kind. -/
theorem gate_isSome (m : JMember) (v : Json) : (gate m v).isSome = decide (v.member = m) := by
  unfold gate
  split <;> simp_all

/-- The value-side row of a kind. -/
instance jsonPrimAdm : Alg.PrimAdm jsonSyn where
  admV m v := decide (v.member = m)
  admV_exact m v := by rw [show (Alg.Syn.ground m).f jsonSyn.o v = gate m v from rfl, gate_isSome]

/-- The attribute-side row of a kind: each kind's gate is self-dual. -/
instance jsonPrimAdmA : Alg.PrimAdmA jsonSyn := Alg.PrimAdm.dual fun _ => rfl

/-- The string-or-number term admits exactly what its codec writes, and reads exactly what its
    codec reads. -/
theorem exact_strOrNum : Alg.ExactV α β strOrNumTerm [] ∧ Alg.ExactA α β strOrNumTerm [] :=
  ⟨Alg.Adm_exact _ _, Alg.AdmA_exact _ _⟩

/-! ## Arrays -/

/-- The array constructor, as a prism. The caller side and the stored side share the prism. -/
def arrP : Alg.Ctor (List Json) Json where
  into := .arr
  out := fun v => match v with | .arr xs => some xs | _ => none
  out_into _ := rfl
  into_out {v _} h := by cases v <;> first | cases h; rfl | exact nomatch h

/-- The array codec over an element codec: each entry through the element codec. -/
def arr (c : Alg.Codec Json JMember) : Alg.Codec Json JMember :=
  Alg.entrywise arrP arrP .arr (fun xs => ∀ x ∈ xs, c.T x) c.e c.p

/-- An array of a lawful element codec is lawful, entry by entry. -/
theorem lawful_arr {c : Alg.Codec Json JMember} (h : Alg.Lawful Json.member c) :
    Alg.Lawful Json.member (arr c) :=
  Alg.lawful_entrywise (fun _ => rfl) (fun _ _ => h.retract) (fun _ _ => h.canon)

/-- An array of strings. -/
def strArr : Alg.Codec Json JMember := arr str

/-- An array of strings is lawful. -/
theorem lawful_strArr : Alg.Lawful Json.member strArr := lawful_arr lawful_str

end Calculus.JSON
