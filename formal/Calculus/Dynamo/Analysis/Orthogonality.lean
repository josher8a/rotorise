import Calculus.Dynamo.Analysis.ExactA
import Calculus.Lang.Occupancy

/-!
# Orthogonality — the DynamoDB shapes and separation

`Obligations (.union opts)` carries pairwise compatibility. Two separated options are compatible
(`pairwiseCompat_of_separated`). The decidable certificate is `certPair` (`Meet.lean`): two
options are orthogonal when `meet'` meets them at the bottom, or when their occupancies are
disjoint on both sides. `meet'` answers the bottom where the domains and the ranges of the two
terms meet at the bottom. The meet refuses a closure, and the occupancies read no predicate, so
the shape test certifies a pair that the meet cannot state.

The occupancies, the shape test `Orth1` and their soundness are generic (`Alg.occV`, `Alg.occA`,
`Alg.Orth1`, `Alg.occV_sound`, `Alg.occA_sound`). This module holds what DynamoDB supplies to them,
the shapes `dynOcc` and their laws `dynOccSound`, and `Separates`.

## Sound, never complete, and why there is no `unknown`

Semantic orthogonality is undecidable in this language — `refine t q` carries an arbitrary
`Value → Bool` and `held t P f g` an arbitrary pair of maps. So the certificate answers a
*narrower* question, and the answer `false` means "no certificate", never "not orthogonal".
An opaque subterm occupies every shape, and a pair involving it fails to be certified.

## Both halves of the pair

`Separates` takes **two** families, one over `Value` and one over `Attr`, and asks each to be
pairwise disjoint. A pair can be separated on one side and not on the other, and then it is not
separated. `held` is the witness: its write occupancy is its caller-side term's, and its read
occupancy is its stored-side term's. So `union(held(string, number, f, g), string)`, the decimal
adapter against a string, separates on the write side and meets on the read side.

The two sides coincide below `opaque`: under `HF`, `occA_le_occV` puts the read occupancy inside
the write occupancy under `Member.slot`, so a held-free pair disjoint on the write side is
disjoint on the read side.

## The write-side slot is the `Value` constructor, not `Kind`

`Kind` collapses `strSet`, `numSet` and `binSet` to `.set`, so `κ (set string)` and
`κ (set number)` are equal. The ten `Value` constructors can tell them apart, so the sharper
partition is *available in the model*: a set writes the wire family of each scalar slot its
element writes, and `℘⁺fin` has no empty inhabitant, so a written set has an element whose slot
names the family. `Slot` below is that partition. The read-side slot is
`Member`, which `Attr.member` already computes.
-/

namespace Calculus

open Alg (occV occA occV_sound occA_sound)

/-! ## Slots

`Slot` is the `Value` constructor as data. `Member` is reused unchanged for the read side —
`Attr.member` is already the constructor tag there.

**`Slot` and `Member` are in bijection**: the ten slots match the ten members one for one.

The two types are kept apart anyway, and deliberately, because the bijection is a FACT ABOUT
THE PRESENT TABLE rather than a property of the design. A slot is what a value is built with
and a member is what the store files it under; nothing makes them the same kind of thing, and
an adapter that gives a host carrier its own slot would part them again. Merging them is a
change to make on purpose, with the reason written down, and not by noticing they line up. -/

inductive Slot where
  | str | num | bool | bin | null | strSet | numSet | binSet | arr | map
deriving DecidableEq, Repr

/-- The constructor a value is built with. Ten of them, where `Value.kind` has eight. -/
def Value.slot : Value → Slot
  | .str _    => .str
  | .num _    => .num
  | .bool _   => .bool
  | .bin _    => .bin
  | .null     => .null
  | .strSet _ => .strSet
  | .numSet _ => .numSet
  | .binSet _ => .binSet
  | .arr _    => .arr
  | .map _ _  => .map

/-- Enumerations, so the disjointness test is a `List.all` rather than a `Fintype` instance —
    `decide` over these is the whole of what makes `Orth1` checkable by `by decide`. -/
def Slot.all : List Slot :=
  [.str, .num, .bool, .bin, .null, .strSet, .numSet, .binSet, .arr, .map]

theorem Slot.mem_all (s : Slot) : s ∈ Slot.all := by cases s <;> simp [Slot.all]

def Member.all : List Member := [.S, .N, .B, .BOOL, .NULL, .SS, .NS, .BS, .L, .M]

theorem Member.mem_all (m : Member) : m ∈ Member.all := by cases m <;> simp [Member.all]

/-- A literal base's *value* slot, as against `GroundKind.member`, its stored member. -/
def GroundKind.slot : GroundKind → Slot
  | .string  => .str
  | .number  => .num
  | .boolean => .bool
  | .binary  => .bin
  | .null    => .null

/-- The element slot of a set slot: the scalar constructor a wire family's payloads are built
    with. The three set slots have one, and every other slot has none. -/
def Slot.setElem : Slot → Option Slot
  | .strSet => some .str
  | .numSet => some .num
  | .binSet => some .bin
  | _ => none

/-- …and the element member of a set member, on the read side. -/
def Member.setElem : Member → Option Member
  | .SS => some .S
  | .NS => some .N
  | .BS => some .B
  | _ => none

/-- The slot a member's values are built with: the bijection above, as a function. -/
def Member.slot : Member → Slot
  | .S => .str | .N => .num | .B => .bin | .BOOL => .bool | .NULL => .null
  | .SS => .strSet | .NS => .numSet | .BS => .binSet | .L => .arr | .M => .map

/-! ## The shapes of DynamoDB -/

/-- **The DynamoDB shapes**: `Slot` on the value side, `Member` on the attribute side. A primitive
    occupies the slot and the member of its base, and a set slot names its element slot. -/
instance dynOcc : Alg.Occ dynSyn where
  ShV := Slot
  ShA := Member
  decV := inferInstance
  decA := inferInstance
  allV := Slot.all
  mem_allV := Slot.mem_all
  allA := Member.all
  mem_allA := Member.mem_all
  primV | .base k | .literal k _ => occOnly k.slot
  primA | .base k | .literal k _ => occOnly k.member
  setV := Slot.setElem
  setA := Member.setElem
  listV := .arr
  listA := .L
  mapV := .map
  mapA := .M

/-- **The DynamoDB shape maps and their landing facts.** A base or a literal writes its slot and
    reads its member, a written set has an element because `℘⁺fin` has no empty inhabitant, and
    the prisms build `arr`, `L`, `map` and `M`. -/
noncomputable instance dynOccSound : Alg.OccSound dynSyn where
  shapeV := Value.slot
  shapeA := Attr.member
  prim_e g v h := by
    have h' := (Alg.PrimAdm.admV_exact (S := dynSyn) g v).mpr h
    cases g with
    | base k => cases k <;> cases v <;> first | rfl | exact nomatch h'
    | literal k x =>
        cases k <;> cases v <;> first | rfl | simp [Alg.PrimAdm.admV, AdmLit, inL] at h'
  prim_p g a h := by
    have h' := (Alg.PrimAdmA.admA_exact (S := dynSyn) g a).mpr h
    cases g with
    | base k => cases k <;> cases a <;> first | rfl | exact nomatch h'
    | literal k x => cases k <;> cases a <;> first | rfl | exact nomatch h'
  set_e L hL c v h := by
    cases hL
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h
    rcases setCodec_e_eq.mp ha with ⟨S, rfl, hS⟩ | ⟨S, rfl, hS⟩ | ⟨S, rfl, hS⟩ <;>
      obtain ⟨x, hx⟩ := S.2 <;> exact ⟨_, encSet_elem hS x hx, rfl⟩
  set_p L hL c a h := by
    cases hL
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h
    rcases setCodec_p_eq.mp hw with ⟨S, rfl, hS⟩ | ⟨S, rfl, hS⟩ | ⟨S, rfl, hS⟩ <;>
      obtain ⟨x, hx⟩ := S.2 <;> exact ⟨_, decSet_elem hS x hx, rfl⟩
  list_e L hL _ := by cases hL; rfl
  list_p L hL _ := by cases hL; rfl
  map_e F hF _ := by cases hF; rfl
  map_p F hF _ := by cases hF; rfl

/-! The rows of the occupancies that read the DynamoDB shapes. `simp` does not unfold an
instance, so a proof that computes an occupancy reads these rows. -/

/-- A base writes its slot. -/
theorem occV_base (k : GroundKind) : occV (Term.base k) = occOnly k.slot := rfl
/-- A literal writes the slot of its base. -/
theorem occV_literal (k : GroundKind) (x : k.Carrier) : occV (Term.literal k x) = occOnly k.slot := rfl
/-- A base reads its member. -/
theorem occA_base (k : GroundKind) : occA (Term.base k) = occOnly k.member := rfl
/-- A literal reads the member of its base. -/
theorem occA_literal (k : GroundKind) (x : k.Carrier) : occA (Term.literal k x) = occOnly k.member :=
  rfl
/-- A set writes the set slot of each element slot. -/
theorem occV_set (t : Term) :
    occV (Term.set t) = fun s => s.setElem.elim false fun e => occV t e || t.hasVar := rfl
/-- A set reads the set member of each element member. -/
theorem occA_set (t : Term) :
    occA (Term.set t) = fun m => m.setElem.elim false fun e => occA t e || t.hasVar := rfl
/-- A list writes `arr`. -/
theorem occV_list (pre : List Term) sp suf : occV (Term.list pre sp suf) = occOnly Slot.arr := rfl
/-- A list reads `L`. -/
theorem occA_list (pre : List Term) sp suf : occA (Term.list pre sp suf) = occOnly Member.L := rfl
/-- An object writes `map`. -/
theorem occV_object (b : Body) : occV (Term.object b) = occOnly Slot.map := rfl
/-- An object reads `M`. -/
theorem occA_object (b : Body) : occA (Term.object b) = occOnly Member.M := rfl

/-! ## Separation

The families each option is confined to are the occupancy **intersected with the option's own
admission**. Disjointness in either factor makes the intersection disjoint, so the slot test
separates through the occupancy and the meet through the admission, with no second family. -/

def OrthSV (t : Term) : Value → Prop :=
  fun v => occV t v.slot = true ∧ Adm t v = true

def OrthSA (t : Term) : Attr → Prop :=
  fun a => occA t a.member = true ∧ AdmA t a = true

/-- **What the discharger consumes.** Both families disjoint, as a `Prop`, of which the
    certificate is the decidable part. A new certificate is a new theorem producing `Separates`,
    not a new case in `pairwiseCompat_of_separated`. -/
def Separates (x y : Term) : Prop :=
  (∀ v, OrthSV x v → ¬ OrthSV y v) ∧ (∀ a, OrthSA x a → ¬ OrthSA y a)

/-- **The whole premise the discharger takes**, as one name: every pair of options separated.

    `Separates` is the rule for a pair and this is the rule for a list, so the certificate
    produces the first and a caller supplies the second.

    **It names the guarantee where the guarantee already lives, and moves nothing.** `Typed.union`
    cannot take it: `Separates` is stated on `Adm`, in `ExactV.lean`, and
    the import chain is `Typing` then `Soundness` then `ExactV` then `ExactA` then this
    file. A premise here is four modules above the judgement it would constrain. So an undischarged
    union stays *underivable* through `Obligations`, which is where it was, rather than becoming
    unrepresentable.

    **And unrepresentable is not available anyway.** A `Term.union` carrying its own witness needs
    either an inductive indexed by the option list it constrains, which is induction-induction, or
    a field whose type is computed from the term, which is induction-recursion. Lean 4 rejects both:
    the first as `unknown identifier` on the type being defined, the second as `invalid mutual
    block: either all elements of the block must be inductive/structure declarations, or they must
    all be definitions`. The one shape that works is a pre-term with a well-formedness subtype, and
    that re-founds the term language. -/
def Separated (opts : List Term) : Prop := List.Pairwise Separates opts

/-- **Pairwise separation bounds the admitters at one.** Separation says no two options admit
    one input, and admission implies occupancy through `occV_sound`, so the two conjuncts of
    `OrthSV` are both in hand. -/
theorem admitsAtMostOne_of_separated {opts : List Term} (h : Separated opts) :
    AdmitsAtMostOne (denoteList opts) := by
  constructor
  · intro v
    rw [filter_AdmList (fun t _ => Adm_exact t) v, List.length_map]
    refine length_le_one_of_pairwise_false (List.Pairwise.imp_of_mem ?_
      (List.Pairwise.filter _ (h.imp fun hs => hs.1 v)))
    intro x y hx hy hxy
    have hax : Adm x v = true := (List.mem_filter.mp hx).2
    have hay : Adm y v = true := (List.mem_filter.mp hy).2
    exact hxy ⟨occV_sound x v hax, hax⟩
      ⟨occV_sound y v hay, hay⟩
  · intro a
    rw [filter_AdmAList (fun t _ => AdmA_exact t) a, List.length_map]
    refine length_le_one_of_pairwise_false (List.Pairwise.imp_of_mem ?_
      (List.Pairwise.filter _ (h.imp fun hs => hs.2 a)))
    intro x y hx hy hxy
    have hax : AdmA x a = true := (List.mem_filter.mp hx).2
    have hay : AdmA y a = true := (List.mem_filter.mp hy).2
    exact hxy ⟨occA_sound x a hax, hax⟩
      ⟨occA_sound y a hay, hay⟩

/-- Two members that both meet `P`, in a list where no related pair both meets `P`, are one. -/
theorem eq_of_pairwise_excl {α : Type} {P : α → Prop} {R : α → α → Prop}
    (hR : ∀ x y, R x y → P x → P y → False) :
    ∀ {l : List α}, l.Pairwise R → ∀ x ∈ l, ∀ y ∈ l, P x → P y → x = y
  | [], _, _, hx, _, _, _, _ => nomatch hx
  | h :: tl, hp, x, hx, y, hy, px, py => by
    have hp' := List.pairwise_cons.mp hp
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact (hR _ _ (hp'.1 y hy') px py).elim
    · exact (hR _ _ (hp'.1 x hx') py px).elim
    · exact eq_of_pairwise_excl hR hp'.2 x hx' y hy' px py

/-- **Pairwise separation gives the union's obligation.** No input reaches two separated
    options, so an option never acts where another reads. -/
theorem pairwiseCompat_of_separated {opts : List Term}
    (hlaw : ∀ t ∈ opts, Lawful (denote t)) (h : Separated opts) : PairwiseCompat opts := by
  intro s hs t ht a v hp hact
  have hsA : AdmA s a = true := (AdmA_exact s a).mpr (by rw [hp]; rfl)
  have hsV : Adm s v = true := (Adm_exact s v).mpr ((hlaw s hs).defined hp)
  have hst : t = s := by
    rcases hact with hq | he
    · have htA : AdmA t a = true := (AdmA_exact t a).mpr hq
      exact eq_of_pairwise_excl (P := fun u => OrthSA u a) (fun x y hxy px py => hxy.2 a px py)
        h t ht s hs ⟨occA_sound t a htA, htA⟩
        ⟨occA_sound s a hsA, hsA⟩
    · have htV : Adm t v = true := (Adm_exact t v).mpr he
      exact eq_of_pairwise_excl (P := fun u => OrthSV u v) (fun x y hxy px py => hxy.1 v px py)
        h t ht s hs ⟨occV_sound t v htV, htV⟩
        ⟨occV_sound s v hsV, hsV⟩
  subst hst; exact hp

/-- Each codec is compatible with itself. -/
theorem compat_self (c : Codec) : Compat c c := fun _ _ hp _ => hp

/-- **An empty option is compatible with every option**: `never` reads nothing and writes
    nothing, so neither side of `Compat` has a case. -/
theorem compat_never_left (c : Codec) : Compat (denote .never) c := fun _ _ hp _ => nomatch hp

/-- …and on the other side. -/
theorem compat_never_right (c : Codec) : Compat c (denote .never) := fun _ _ _ hact => by
  rcases hact with h | h <;> exact nomatch h

/-- **A union with an empty option meets its obligation**, whatever the other option is. -/
theorem pairwiseCompat_never_right (x : Term) : PairwiseCompat [x, .never] := by
  intro s hs t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ht
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    first | exact compat_self _ | exact compat_never_left _ | exact compat_never_right _

/-- …and with the empty option first. -/
theorem pairwiseCompat_never_left (x : Term) : PairwiseCompat [.never, x] := by
  intro s hs t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ht
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    first | exact compat_self _ | exact compat_never_left _ | exact compat_never_right _

end Calculus
