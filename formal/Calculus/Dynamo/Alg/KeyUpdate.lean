import Calculus.Dynamo.Alg.KeyMatch

/-!
# The footprint at a partial item, and the key update

A key reads some names of the item. Where a match reads a discriminator that the item lacks, the key
reads the names under every arm, because the item has not chosen one. Where the item holds the
discriminator, the key reads the names under the chosen arm. `KeySpec.ReadsAt g` is that footprint
at the item `g`, and the host function componentsOf is its computation. An item that knows more
reads less (`ReadsAt.mono`), and two items that agree on the footprint of the first give one key
(`keyOf_congr_at`). The static footprint `KeySpec.Reads` is the footprint at the item that knows
nothing (`readsAt_none_iff`), so `keyOf_congr` is a corollary and not a second theorem.

A key update is a function of the keys of the schema, the values that the codec decides, and the
change. The change is the written attributes: a written attribute has a value, or the change removes
it. The update reads the keys at the item that the change makes over the decided values, which has
no value at a removed name. A key that the change touches is rebuilt. A key that the change does
not touch is left alone. The result is a refusal, or a patch: a touched key name maps to the key as
an optional printed key, where `some` is a SET and `none` is a REMOVE. A key carries its member, and
the printer of the update reads the member of the key, so the patch holds the key at the member of
the key. The type `M` of the member and the type `A` of a printed key are parameters of this file.

The law of the update (`update_commute`): where the update gives a patch, and `x` is an item that
agrees with the decided values, the key part of `x` with the change applied is the key part of `x`
with the patch written over it. The proof reads the antitone footprint and the dynamic congruence.

The footprint of a spec is a predicate, because the arms are a function of the literal. A computed
footprint needs a finite presentation of the spec, which is `Tree`. A key of the schema carries the
computed footprint and the proof that it is the predicate, so the update is a function and the laws
read the predicate.
-/

namespace Calculus

namespace DerivedKey

variable {N : Type} {allowPartial enforce : Bool} {i i' : Item N}

/-! ## The footprint at a partial item -/

/-- **The names that a spec reads at an item**: the names of the arm, or the discriminator and the
    names under the arm that the item selects. Where the item lacks the discriminator, the names
    under each arm. -/
inductive KeySpec.ReadsAt {N : Type} (g : Item N) : KeySpec N → N → Prop
  | arm {a : Arm N} {n : N} : n ∈ a.reads → KeySpec.ReadsAt g (.arm a) n
  | disc {d : N} {arms : String → KeySpec N} : KeySpec.ReadsAt g (.match_ d arms) d
  | under {d : N} {arms : String → KeySpec N} {n : N} (v : String) :
      (g d = none ∨ g d = some v) → KeySpec.ReadsAt g (arms v) n →
        KeySpec.ReadsAt g (.match_ d arms) n

/-- **The footprint at an item is inside the static footprint.** -/
theorem KeySpec.ReadsAt.reads {g : Item N} {s : KeySpec N} {n : N} (h : s.ReadsAt g n) :
    s.Reads n := by
  induction h with
  | arm hn => exact .arm hn
  | disc => exact .disc
  | under v _ _ ih => exact .under v ih

/-- **The static footprint is the footprint at the item that knows nothing.** -/
theorem readsAt_none_iff {s : KeySpec N} {n : N} :
    s.ReadsAt (fun _ => none) n ↔ s.Reads n := by
  refine ⟨KeySpec.ReadsAt.reads, fun h => ?_⟩
  induction h with
  | arm hn => exact .arm hn
  | disc => exact .disc
  | under v _ ih => exact .under v (Or.inl rfl) ih

/-- **Antitone.** Where `y` extends `g`, the footprint at `y` is inside the footprint at `g`: an
    item that knows less reads more. -/
theorem KeySpec.ReadsAt.mono {g y : Item N} (hy : ∀ n v, g n = some v → y n = some v)
    {s : KeySpec N} {n : N} (h : s.ReadsAt y n) : s.ReadsAt g n := by
  induction h with
  | arm hn => exact .arm hn
  | disc => exact .disc
  | @under d arms n v hd _ ih =>
      refine .under v ?_ ih
      cases hg : g d with
      | none => exact Or.inl rfl
      | some w =>
          right
          have hw := hy d w hg
          rcases hd with h | h
          · rw [h] at hw
            exact absurd hw (by simp)
          · rw [h] at hw
            rw [Option.some.inj hw]

/-- **The dynamic congruence.** Two items that agree on the footprint at the first give one key. -/
theorem keyOf_congr_at {s : KeySpec N} (h : ∀ n, s.ReadsAt i n → i n = i' n) :
    keyOf allowPartial enforce i s = keyOf allowPartial enforce i' s := by
  induction s with
  | arm a => exact Arm.key_congr fun n hn => h n (.arm hn)
  | match_ d arms ih =>
      have hd : i d = i' d := h d .disc
      cases hi : i d with
      | none => rw [keyOf_refused (select_absent hi), keyOf_refused (select_absent (hd ▸ hi))]
      | some v =>
          rw [keyOf_match hi, keyOf_match (hd ▸ hi)]
          exact ih v fun n hn => h n (.under v (Or.inr hi) hn)

/-- **The static congruence is the dynamic congruence at the static footprint.** Two items that
    agree on each name that the spec reads give one key. -/
theorem keyOf_congr {s : KeySpec N} (h : ∀ n, s.Reads n → i n = i' n) :
    keyOf allowPartial enforce i s = keyOf allowPartial enforce i' s :=
  keyOf_congr_at fun n hn => h n hn.reads

/-! ## The key update -/

/-- **The order of the names that a key reads.** `pre m n` holds where the path `m` is the path `n`,
    or a path above it: a prefix at a name. The host reads a write to a path as a write to each
    path above it and below it, and reads a path as held by a given name above it. The order is a
    decidable `Bool`, so no decision reads a classical instance. -/
class PathName (N : Type) where
  pre : N → N → Bool
  pre_refl : ∀ n, pre n n = true

variable [DecidableEq N] [PathName N] {M A : Type}

/-- A change: finitely many written names, each with a value, or with `none` where the change
    removes the attribute. A name that the change does not write has no entry. The host change is
    an object with finitely many own properties. -/
structure Change (N : Type) where
  entries : List (N × Option String)

/-- The entry of a change at a name. -/
def Change.apply (ch : Change N) (n : N) : Option (Option String) := ch.entries.lookup n

instance : CoeFun (Change N) (fun _ => N → Option (Option String)) := ⟨Change.apply⟩

omit [PathName N] in
/-- **A name that the lookup finds is in the list.** -/
theorem lookup_mem {β : Type} :
    ∀ (l : List (N × β)) (n : N) (w : β), l.lookup n = some w → (n, w) ∈ l
  | [], n, w, h => by simp [List.lookup] at h
  | (a, b) :: rest, n, w, h => by
      rcases Decidable.em (n = a) with hn | hn
      · subst hn
        simp only [List.lookup, beq_self_eq_true] at h
        have := Option.some.inj h
        subst this
        exact List.mem_cons_self
      · have hb : (n == a) = false := by simpa using hn
        simp only [List.lookup, hb] at h
        exact List.mem_cons_of_mem _ (lookup_mem rest n w h)

/-- **The names that a change reaches**: each name that is a written name, above one, or below one.
    The host decides the same relation for a component and a written name. -/
def reached (ch : Change N) (n : N) : Bool :=
  ch.entries.any fun e => PathName.pre e.1 n || PathName.pre n e.1

/-- **A written name is reached.** -/
theorem reached_of_apply {ch : Change N} {n : N} {v : Option String} (h : ch n = some v) :
    reached ch n = true := by
  have hm := lookup_mem ch.entries n v h
  simp only [reached, List.any_eq_true]
  exact ⟨(n, v), hm, by simp [PathName.pre_refl]⟩

/-- **The item that the update reads**: the change over the decided values. The host builds it as
    `{ ...decided, ...changed }`, and never reads the item that the entry replaces. So a name that
    the change does not write has the decided value, or none. -/
def given (d : Item N) (ch : Change N) : Item N :=
  fun n => match ch n with
    | some v => v
    | none => d n

/-- The change over an item: a written name has the written value, a removed name has no value, and
    a name that the change reaches without writing it has no value, because it is below a written
    name, which replaces the attribute, or above one, which then holds an object. A name that the
    codec decides keeps the value of the item, because the codec writes it again. Any other name has
    the value of the item. -/
def applied (d : Item N) (ch : Change N) (x : Item N) : Item N :=
  fun n => match ch n with
    | some v => v
    | none => if reached ch n && (d n).isNone then none else x n

/-- A key of the schema: the name, the member of the key, the spec, whether the key is the key of
    the table, and the footprint of the spec at an item as a list, with the proof that the list is
    the predicate. -/
structure KeyDef (N M : Type) where
  name : String
  mem : M
  spec : KeySpec N
  ofTable : Bool
  foot : Item N → List N
  foot_iff : ∀ g n, spec.ReadsAt g n ↔ n ∈ foot g

/-- Why the update refuses: the change writes a decided attribute at another value, the change
    touches a key that it cannot rewrite, or the build of a key throws. -/
inductive Refusal where
  | decided
  | rewrite (key : String)
  | unbuilt (key : String)
  deriving DecidableEq

/-- What the update does to one key: nothing, a refusal, or a written key (`none` is a removal). -/
inductive Step (A : Type) where
  | untouched
  | refused (r : Refusal)
  | written (v : Option A)

/-- A key is touched where the footprint at the given item holds a name that the change reaches and
    the codec does not decide. A removal is a write, and a write to a path reaches the paths above
    it and below it. -/
def KeyDef.touched (k : KeyDef N M) (d : Item N) (ch : Change N) : Bool :=
  (k.foot (given d ch)).any fun n => reached ch n && (d n).isNone

/-- A key lacks a component where the footprint holds a name that the change does not reach and the
    codec does not decide. A name that the change reaches is held: a removal, or a write above or
    below it, so the key is built from the given item, which has no value there, and the build
    gives a refusal or no key. The host reads a decided name at the name, as this definition does. A
    decided name is a constant that a key prints, so the entry refuses a path below it at
    construction. -/
def KeyDef.lacks (k : KeyDef N M) (d : Item N) (ch : Change N) : Bool :=
  (k.foot (given d ch)).any fun n => !reached ch n && (d n).isNone

/-- **The step of one key.** A touched key of the table, or a touched key that lacks a component, is
    a refusal. Any other touched key is the key of the given item. -/
def KeyDef.step (print : M → Out → Option (Option A)) (d : Item N) (ch : Change N)
    (k : KeyDef N M) : Step A :=
  if k.touched d ch then
    if k.ofTable || k.lacks d ch then .refused (.rewrite k.name)
    else
      match print k.mem (keyOf false false (given d ch) k.spec) with
      | none => .refused (.unbuilt k.name)
      | some v => .written v
  else .untouched

/-- The refusal of a step. -/
def Step.refusal : Step A → Option Refusal
  | .refused r => some r
  | _ => none

/-- The entry of a step in the patch. -/
def Step.entry (k : KeyDef N M) : Step A → Option (String × Option A)
  | .written v => some (k.name, v)
  | _ => none

/-- The result of the update: a refusal, or a patch of key names to optional keys. -/
inductive Verdict (A : Type) where
  | refused (r : Refusal)
  | patch (p : List (String × Option A))

/-- **The key update.** The decided values and the change are lists of a name and a printed value.
    The printer `print` reads the member of a key and the key, and gives the printed key, `none` for
    a refusal. The update refuses where the change writes a decided name at another value.
    Otherwise the first refusal of a key in order is the result, or the patch of the written keys.
    A change at a name is a value, or `none` for a removal, and a removal of a decided name writes
    another value. -/
def update (print : M → Out → Option (Option A)) (keys : List (KeyDef N M))
    (dec : List (N × String)) (ch : List (N × Option String)) : Verdict A :=
  if dec.any (fun p => (ch.lookup p.1).any fun v => v != some p.2) then .refused .decided
  else
    match keys.findSome? fun k => (k.step print (fun n => dec.lookup n) ⟨ch⟩).refusal with
    | some r => .refused r
    | none => .patch (keys.filterMap fun k =>
        (k.step print (fun n => dec.lookup n) ⟨ch⟩).entry k)

/-- A change is consistent with the decided values where each written decided name has the decided
    value. A removal of a decided name is not consistent. -/
def Consistent (d : Item N) (ch : Change N) : Prop :=
  ∀ n v w, ch n = some v → d n = some w → v = some w

/-- The item that the update reads extends nothing but itself: a name that it holds is held by the
    change over any item that agrees with the decided values. -/
theorem given_extends {d x : Item N} {ch : Change N} (hx : ∀ n v, d n = some v → x n = some v) :
    ∀ n v, given d ch n = some v → applied d ch x n = some v := by
  intro n v h
  simp only [given, applied] at h ⊢
  cases hc : ch n with
  | some w => rw [hc] at h; exact h
  | none =>
      rw [hc] at h
      simp [h, hx n v h]

/-- **A written key is the key of the changed item.** The update gives `v` at a key, and the key of
    the item with the change applied is `v`. The proof reads the dynamic congruence at the given
    item. -/
theorem KeyDef.step_written {print : M → Out → Option (Option A)} {d x : Item N} {ch : Change N}
    {k : KeyDef N M}
    {v : Option A}
    (hx : ∀ n v, d n = some v → x n = some v) (hs : k.step print d ch = .written v) :
    print k.mem (keyOf false false (applied d ch x) k.spec) = some v := by
  unfold KeyDef.step at hs
  rcases Decidable.em (k.touched d ch = true) with ht | ht
  · rw [if_pos ht] at hs
    rcases Decidable.em ((k.ofTable || k.lacks d ch) = true) with hl | hl
    · rw [if_pos hl] at hs; cases hs
    · rw [if_neg hl] at hs
      have hlacks : k.lacks d ch = false := by
        cases h : k.lacks d ch
        · rfl
        · exact absurd (by simp [h]) hl
      cases hb : print k.mem (keyOf false false (given d ch) k.spec) with
      | none => rw [hb] at hs; cases hs
      | some w =>
          rw [hb] at hs
          have hw : w = v := by cases hs; rfl
          subst hw
          have hcong : keyOf false false (given d ch) k.spec =
              keyOf false false (applied d ch x) k.spec := by
            refine keyOf_congr_at fun n hn => ?_
            have hmem : n ∈ k.foot (given d ch) := (k.foot_iff _ n).mp hn
            have hheld : ¬ (reached ch n = false ∧ d n = none) := by
              have := hlacks
              simp only [KeyDef.lacks, List.any_eq_false] at this
              simpa using this n hmem
            cases hc : ch n with
            | some w => simp [given, applied, hc]
            | none =>
                cases hr : reached ch n with
                | true =>
                    cases hd : d n with
                    | none => simp [given, applied, hc, hr, hd]
                    | some u => simp [given, applied, hc, hr, hd, hx n u hd]
                | false =>
                    cases hd : d n with
                    | none => exact absurd ⟨hr, hd⟩ hheld
                    | some u => simp [given, applied, hc, hr, hd, hx n u hd]
          rw [← hcong]
          exact hb
  · rw [if_neg ht] at hs; cases hs

/-- **An untouched key is the key of the item.** The footprint at the changed item is inside the
    footprint at the given item (the antitone law), and the change writes none of it. -/
theorem KeyDef.step_untouched {print : M → Out → Option (Option A)} {d x : Item N}
    {ch : Change N} {k : KeyDef N M}
    (hc : Consistent d ch) (hx : ∀ n v, d n = some v → x n = some v)
    (hs : k.step print d ch = .untouched) :
    keyOf false false (applied d ch x) k.spec = keyOf false false x k.spec := by
  have ht : k.touched d ch = false := by
    unfold KeyDef.step at hs
    rcases Decidable.em (k.touched d ch = true) with ht | ht
    · rw [if_pos ht] at hs
      rcases Decidable.em ((k.ofTable || k.lacks d ch) = true) with hl | hl
      · rw [if_pos hl] at hs; cases hs
      · rw [if_neg hl] at hs
        cases hw : print k.mem (keyOf false false (given d ch) k.spec) with
        | none => rw [hw] at hs; cases hs
        | some w => rw [hw] at hs; cases hs
    · simpa using ht
  refine keyOf_congr_at fun n hn => ?_
  have hmem : n ∈ k.foot (given d ch) :=
    (k.foot_iff _ n).mp (KeySpec.ReadsAt.mono (given_extends hx) hn)
  have hnot : ¬ (reached ch n = true ∧ (d n).isNone = true) := by
    intro h
    have := ht
    simp only [KeyDef.touched, List.any_eq_false] at this
    exact this n hmem (by simp [h.1, h.2])
  cases hcn : ch n with
  | none =>
      cases hr : reached ch n with
      | false => simp [applied, hcn, hr]
      | true =>
          cases hd : d n with
          | none => exact absurd ⟨hr, by simp [hd]⟩ hnot
          | some u => simp [applied, hcn, hr, hd]
  | some w =>
      have hr : reached ch n = true := reached_of_apply hcn
      cases hdn : d n with
      | none => exact absurd ⟨hr, by simp [hdn]⟩ hnot
      | some u =>
          have hwu : w = some u := hc n w u hcn hdn
          subst hwu
          simp [applied, hcn, hx n u hdn]

/-- **The update commutes with encode.** Where the update gives a patch `P`, and `x` is an item that
    agrees with the decided values, the key part of `x` with the change applied is the key part of
    `x` with `P` written over it: a key of `P` has the written key at the changed item, and a key
    outside `P` has the same key at `x` and at the changed item. The premises are the three of the
    host: the change agrees with the decided values (the host checks it first), the item agrees
    with the decided values (the codec decides them), and the names of the keys differ (the keys
    of an object). -/
theorem update_commute {print : M → Out → Option (Option A)}
    {keys : List (KeyDef N M)}
    {dec : List (N × String)} {ch : List (N × Option String)} {P : List (String × Option A)}
    (hnd : (keys.map KeyDef.name).Nodup) (hP : update print keys dec ch = .patch P)
    {x : Item N} (hx : ∀ n v, dec.lookup n = some v → x n = some v) :
    ∀ k ∈ keys,
      (∀ v, (k.name, v) ∈ P →
        print k.mem (keyOf false false (applied (fun n => dec.lookup n) ⟨ch⟩ x) k.spec) = some v) ∧
      ((∀ v, (k.name, v) ∉ P) →
        keyOf false false (applied (fun n => dec.lookup n) ⟨ch⟩ x) k.spec =
          keyOf false false x k.spec) := by
  unfold update at hP
  rcases Decidable.em (dec.any (fun p => (ch.lookup p.1).any fun v => v != some p.2) = true) with hdec | hdec
  · rw [if_pos hdec] at hP; cases hP
  · rw [if_neg hdec] at hP
    have hdec' : dec.any (fun p => (ch.lookup p.1).any fun v => v != some p.2) = false := by
      cases h : dec.any (fun p => (ch.lookup p.1).any fun v => v != some p.2)
      · rfl
      · exact absurd h hdec
    have hcons : Consistent (fun n => dec.lookup n) ⟨ch⟩ := by
      intro n v w hv hw
      have hv' : ch.lookup n = some v := hv
      have hmem := lookup_mem dec n w hw
      have := List.any_eq_false.mp hdec' (n, w) hmem
      simp only [hv', Option.any_some, bne_iff_ne, ne_eq] at this
      exact Decidable.of_not_not this
    cases hf : keys.findSome? (fun k =>
        (k.step print (fun n => dec.lookup n) ⟨ch⟩).refusal) with
    | some r => rw [hf] at hP; cases hP
    | none =>
        rw [hf] at hP
        have hP' := Verdict.patch.inj hP
        have hnone := List.findSome?_eq_none_iff.mp hf
        intro k hk
        constructor
        · intro v hv
          rw [← hP'] at hv
          obtain ⟨k', hk', he⟩ := List.mem_filterMap.mp hv
          cases hs : k'.step print (fun n => dec.lookup n) ⟨ch⟩ with
          | untouched => rw [hs] at he; cases he
          | refused r => rw [hs] at he; cases he
          | written w =>
              rw [hs] at he
              have he' := Option.some.inj he
              have hname : k'.name = k.name := (Prod.mk.inj he').1
              have hw : w = v := (Prod.mk.inj he').2
              subst hw
              have hkk : k' = k := List.inj_on_of_nodup_map hnd hk' hk hname
              subst hkk
              exact KeyDef.step_written hx hs
        · intro hnot
          cases hs : k.step print (fun n => dec.lookup n) ⟨ch⟩ with
          | untouched => exact KeyDef.step_untouched hcons hx hs
          | refused r =>
              have := hnone k hk
              rw [hs] at this
              cases this
          | written w =>
              exfalso
              refine hnot w ?_
              rw [← hP']
              exact List.mem_filterMap.mpr ⟨k, hk, by rw [hs]; rfl⟩

/-! ## The finite presentation of a spec -/

/-- A spec as a finite tree: an arm, or a match on one discriminator with a list of arms. The list
    gives the function of the literal through `KeySpec.ofList`, where the first entry of a literal
    wins. -/
inductive Tree (N : Type) where
  | arm (a : Arm N)
  | match_ (d : N) (arms : List (String × Tree N))

mutual
/-- The spec of a tree. -/
def Tree.spec {N : Type} : Tree N → KeySpec N
  | .arm a => .arm a
  | .match_ d arms => .match_ d (KeySpec.ofList (Tree.armsSpec arms))

/-- The entries of a list of arms, as specs. -/
def Tree.armsSpec {N : Type} : List (String × Tree N) → List (String × KeySpec N)
  | [] => []
  | (l, t) :: rest => (l, t.spec) :: Tree.armsSpec rest
end

mutual
/-- **The footprint of a tree at an item, as a list**: the computation that the host does in
    componentsOf. -/
def Tree.foot {N : Type} (g : Item N) : Tree N → List N
  | .arm a => a.reads
  | .match_ d arms =>
      d :: match g d with
        | none => Tree.footAll g [] arms
        | some v => Tree.footLit g v arms

/-- The names under the arm of a literal: the first entry of the literal, or none. -/
def Tree.footLit {N : Type} (g : Item N) (v : String) : List (String × Tree N) → List N
  | [] => []
  | (l, t) :: rest => if l = v then t.foot g else Tree.footLit g v rest

/-- The names under each arm, where an entry of a literal that an earlier entry names is shadowed. -/
def Tree.footAll {N : Type} (g : Item N) (seen : List String) :
    List (String × Tree N) → List N
  | [] => []
  | (l, t) :: rest =>
      (if l ∈ seen then [] else t.foot g) ++ Tree.footAll g (l :: seen) rest
end

/-- The spec of a list of arms at a literal. -/
theorem Tree.ofList_cons {N : Type} (l : String) (t : Tree N) (rest : List (String × Tree N))
    (v : String) :
    KeySpec.ofList (Tree.armsSpec ((l, t) :: rest)) v =
      if l = v then t.spec else KeySpec.ofList (Tree.armsSpec rest) v := by
  rcases Decidable.em (l = v) with h | h
  · rw [if_pos h]
    have hb : (v == l) = true := beq_iff_eq.mpr h.symm
    simp only [KeySpec.ofList, Tree.armsSpec, List.lookup, hb, Option.getD_some]
  · rw [if_neg h]
    have hb : (v == l) = false := beq_eq_false_iff_ne.mpr fun e => h e.symm
    simp only [KeySpec.ofList, Tree.armsSpec, List.lookup, hb]

/-- The spec of no arm is the arm that the host lacks. -/
theorem Tree.ofList_nil {N : Type} (v : String) :
    KeySpec.ofList (Tree.armsSpec ([] : List (String × Tree N))) v = .arm .missing := rfl

mutual
/-- **The footprint of a tree is the list.** -/
theorem Tree.foot_iff {N : Type} (g : Item N) :
    ∀ (t : Tree N) (n : N), t.spec.ReadsAt g n ↔ n ∈ t.foot g
  | .arm a, n => by
      refine ⟨fun h => ?_, KeySpec.ReadsAt.arm⟩
      cases h with
      | arm hn => exact hn
  | .match_ d arms, n => by
      simp only [Tree.spec, Tree.foot]
      cases hg : g d with
      | none =>
          constructor
          · intro h
            cases h with
            | disc => exact List.mem_cons_self
            | under v _ hr =>
                exact List.mem_cons_of_mem _
                  ((Tree.footAll_iff g n arms []).mpr ⟨v, List.not_mem_nil, hr⟩)
          · intro h
            rcases List.mem_cons.mp h with rfl | h
            · exact .disc
            · obtain ⟨v, _, hr⟩ := (Tree.footAll_iff g n arms []).mp h
              exact .under v (Or.inl hg) hr
      | some w =>
          constructor
          · intro h
            cases h with
            | disc => exact List.mem_cons_self
            | under v hv hr =>
                have hvw : v = w := by
                  rcases hv with hv | hv
                  · rw [hg] at hv; exact absurd hv (by simp)
                  · rw [hg] at hv; exact (Option.some.inj hv).symm
                subst hvw
                exact List.mem_cons_of_mem _ ((Tree.footLit_iff g v n arms).mp hr)
          · intro h
            rcases List.mem_cons.mp h with rfl | h
            · exact .disc
            · exact .under w (Or.inr hg) ((Tree.footLit_iff g w n arms).mpr h)

/-- The footprint under the arm of a literal. -/
theorem Tree.footLit_iff {N : Type} (g : Item N) (v : String) (n : N) :
    ∀ xs : List (String × Tree N),
      (KeySpec.ofList (Tree.armsSpec xs) v).ReadsAt g n ↔ n ∈ Tree.footLit g v xs
  | [] => by
      rw [Tree.ofList_nil]
      refine ⟨fun h => ?_, fun h => absurd h List.not_mem_nil⟩
      cases h with
      | arm hn => exact absurd hn (by simp [Arm.reads])
  | (l, t) :: rest => by
      rw [Tree.ofList_cons]
      simp only [Tree.footLit]
      rcases Decidable.em (l = v) with h | h
      · rw [if_pos h, if_pos h]
        exact Tree.foot_iff g t n
      · rw [if_neg h, if_neg h]
        exact Tree.footLit_iff g v n rest

/-- The footprint under each arm that a literal selects, outside the literals seen. -/
theorem Tree.footAll_iff {N : Type} (g : Item N) (n : N) :
    ∀ (xs : List (String × Tree N)) (seen : List String),
      n ∈ Tree.footAll g seen xs ↔
        ∃ v, v ∉ seen ∧ (KeySpec.ofList (Tree.armsSpec xs) v).ReadsAt g n
  | [], seen => by
      simp only [Tree.footAll]
      refine ⟨fun h => absurd h List.not_mem_nil, ?_⟩
      rintro ⟨v, _, h⟩
      rw [Tree.ofList_nil] at h
      cases h with
      | arm hn => exact absurd hn (by simp [Arm.reads])
  | (l, t) :: rest, seen => by
      simp only [Tree.footAll, List.mem_append]
      constructor
      · rintro (h | h)
        · rcases Decidable.em (l ∈ seen) with hs | hs
          · rw [if_pos hs] at h
            exact absurd h List.not_mem_nil
          · rw [if_neg hs] at h
            refine ⟨l, hs, ?_⟩
            rw [Tree.ofList_cons, if_pos rfl]
            exact (Tree.foot_iff g t n).mpr h
        · obtain ⟨v, hv, hr⟩ := (Tree.footAll_iff g n rest (l :: seen)).mp h
          have hl : l ≠ v := fun e => hv (e ▸ List.mem_cons_self)
          refine ⟨v, fun e => hv (List.mem_cons_of_mem _ e), ?_⟩
          rw [Tree.ofList_cons, if_neg hl]
          exact hr
      · rintro ⟨v, hv, hr⟩
        rw [Tree.ofList_cons] at hr
        rcases Decidable.em (l = v) with hlv | hlv
        · subst hlv
          rw [if_pos rfl] at hr
          left
          rw [if_neg hv]
          exact (Tree.foot_iff g t n).mp hr
        · rw [if_neg hlv] at hr
          right
          exact (Tree.footAll_iff g n rest (l :: seen)).mpr
            ⟨v, fun e => by
              rcases List.mem_cons.mp e with e | e
              · exact hlv e.symm
              · exact hv e, hr⟩
end

/-- **A key of the schema from a tree**: the member of the key, and the computed footprint, which is
    the list of the tree. -/
def KeyDef.ofTree {N : Type} (name : String) (mem : M) (t : Tree N) (ofTable : Bool) :
    KeyDef N M :=
  ⟨name, mem, t.spec, ofTable, fun g => t.foot g, fun g n => Tree.foot_iff g t n⟩

/-! ## The blocks -/

/-- The change off the decided names: the names that the change reaches and the codec does not
    decide. -/
def Written (d : Item N) (ch : Change N) (n : N) : Prop := reached ch n = true ∧ d n = none

/-- Two names are tied where one key reads both at the given item, and the codec decides neither. -/
def Tie (keys : List (KeyDef N M)) (d : Item N) (ch : Change N) (n m : N) : Prop :=
  ∃ k ∈ keys, n ∈ k.foot (given d ch) ∧ m ∈ k.foot (given d ch) ∧ d n = none ∧ d m = none

/-- The block of a name is the names that the ties reach from the name. -/
inductive Tied (keys : List (KeyDef N M)) (d : Item N) (ch : Change N) : N → N → Prop
  | refl (n : N) : Tied keys d ch n n
  | step {n m o : N} : Tie keys d ch n m → Tied keys d ch m o → Tied keys d ch n o

/-- A set of names is a union of blocks where the set holds the block of each name that it holds. -/
def UnionOfBlocks (keys : List (KeyDef N M)) (d : Item N) (ch : Change N) (W : N → Prop) : Prop :=
  ∀ n m, Tied keys d ch n m → W n → W m

omit [PathName N] in
/-- **A union of blocks is a set that one tie does not leave.** -/
theorem unionOfBlocks_iff {keys : List (KeyDef N M)} {d : Item N} {ch : Change N} {W : N → Prop} :
    UnionOfBlocks keys d ch W ↔ ∀ n m, Tie keys d ch n m → W n → W m := by
  refine ⟨fun h n m ht hn => h n m (.step ht (.refl m)) hn, fun h n m hs => ?_⟩
  induction hs with
  | refl => exact id
  | step ht _ ih => exact fun hn => ih (h _ _ ht hn)

/-- A key is touched where the footprint at the given item holds a name of the change. -/
theorem KeyDef.touched_iff {k : KeyDef N M} {d : Item N} {ch : Change N} :
    k.touched d ch = true ↔ ∃ n ∈ k.foot (given d ch), Written d ch n := by
  simp [KeyDef.touched, Written, List.any_eq_true]

/-- A key lacks a component where the footprint holds a name that the change does not reach and the
    codec does not decide. -/
theorem KeyDef.lacks_iff {k : KeyDef N M} {d : Item N} {ch : Change N} :
    k.lacks d ch = true ↔ ∃ n ∈ k.foot (given d ch), reached ch n = false ∧ d n = none := by
  simp [KeyDef.lacks, List.any_eq_true]

omit [PathName N] in
/-- **The given item lacks a name where the change removes it, or neither the change nor the codec
    holds it.** A removal is the one write that leaves the name without a value. -/
theorem given_eq_none {d : Item N} {ch : Change N} {n : N} :
    given d ch n = none ↔ ch n = some none ∨ (ch n = none ∧ d n = none) := by
  simp only [given]
  cases hc : ch n with
  | none => simp
  | some v => cases v <;> simp

/-- **No touched key lacks a component exactly where the change is a union of blocks.** The
    refusal of a touched key that lacks a component says that the change cuts a block. -/
theorem noLacks_iff_unionOfBlocks {keys : List (KeyDef N M)} {d : Item N} {ch : Change N} :
    (∀ k ∈ keys, k.touched d ch = true → k.lacks d ch = false) ↔
      UnionOfBlocks keys d ch (Written d ch) := by
  rw [unionOfBlocks_iff]
  constructor
  · rintro h n m ⟨k, hk, hn, hm, dn, dm⟩ wn
    have hl := h k hk (KeyDef.touched_iff.mpr ⟨n, hn, wn⟩)
    have hh : ¬ (reached ch m = false ∧ d m = none) := fun e =>
      absurd (KeyDef.lacks_iff.mpr ⟨m, hm, e⟩) (by simp [hl])
    refine ⟨?_, dm⟩
    cases hr : reached ch m with
    | true => rfl
    | false => exact absurd ⟨hr, dm⟩ hh
  · intro h k hk ht
    obtain ⟨n, hn, wn⟩ := KeyDef.touched_iff.mp ht
    cases hl : k.lacks d ch with
    | false => rfl
    | true =>
        obtain ⟨m, hm, hrm, hdm⟩ := KeyDef.lacks_iff.mp hl
        have := (h n m ⟨k, hk, hn, hm, wn.2, hdm⟩ wn).1
        rw [hrm] at this
        cases this

/-- **The refusal rule is: the change is a union of blocks, and no block of the change holds a
    component of a key of the table.** A touched key of the table is a refusal, and a touched key
    that lacks a component is a refusal. The block of a name of a union of blocks is inside the
    union, so the second clause reads the change itself. -/
theorem noRewrite_iff {keys : List (KeyDef N M)} {d : Item N} {ch : Change N} :
    (∀ k ∈ keys, ¬ (k.touched d ch = true ∧ (k.ofTable || k.lacks d ch) = true)) ↔
      UnionOfBlocks keys d ch (Written d ch) ∧
        ∀ k ∈ keys, k.ofTable = true → ∀ n ∈ k.foot (given d ch), ¬ Written d ch n := by
  rw [← noLacks_iff_unionOfBlocks]
  constructor
  · intro h
    refine ⟨fun k hk ht => ?_, fun k hk hT n hn wn => ?_⟩
    · cases hl : k.lacks d ch with
      | false => rfl
      | true => exact absurd ⟨ht, by simp [hl]⟩ (h k hk)
    · exact h k hk ⟨KeyDef.touched_iff.mpr ⟨n, hn, wn⟩, by simp [hT]⟩
  · rintro ⟨h1, h2⟩ k hk ⟨ht, hr⟩
    cases hT : k.ofTable with
    | true =>
        obtain ⟨n, hn, wn⟩ := KeyDef.touched_iff.mp ht
        exact h2 k hk hT n hn wn
    | false =>
        rw [hT] at hr
        simp only [Bool.false_or] at hr
        simp [h1 k hk ht] at hr

/-! ## A removal -/

/-- **A strict print stops at an absent part.** A list with an absent part prints nothing. -/
theorem printed_false_of_none : ∀ {ps : List (Option Comp)}, none ∈ ps → printed false ps = none
  | [], h => by simp at h
  | none :: _, _ => rfl
  | some _ :: r, h => by
      have hr : none ∈ r := by simpa using h
      simp [printed, printed_false_of_none hr]

/-- A leaf of plain parts: a part prints nothing where the attribute that it reads has no value. -/
def Leaf.Plain (l : Leaf N) : Prop := ∀ p ∈ l.comps, p.print none = none

omit [DecidableEq N] [PathName N] in
/-- **A leaf of plain parts gives no key at an item that lacks an attribute that a part reads.** The
    strict build prints each part, so an absent part is a refusal. -/
theorem keyOf_leaf_removed {l : Leaf N} (hp : l.Plain) {p : Part N} (hpm : p ∈ l.comps) {n : N}
    (hn : p.name = some n) (hi : i n = none) :
    keyOf false enforce i (.arm (.leaf l)) = .refused := by
  have hmem : none ∈ l.parts i :=
    List.mem_map.mpr ⟨p, hpm, by simp [Part.eval, hn, hi, hp p hpm]⟩
  simp [keyOf, select, Arm.key, build, printed_false_of_none hmem]

/-- **A removal of a component of a leaf of plain parts is the refusal of the build of the changed
    item.** The change removes the attribute that a part reads, the codec does not decide it, and
    the key is not a key of the table and lacks no other component. The item that the update reads
    has no value there, so the key of that item is a refusal, and the update answers as that key
    does: the build throws. -/
theorem KeyDef.step_removal_leaf {print : M → Out → Option (Option A)}
    (hprint : ∀ m, print m .refused = none) {d : Item N} {ch : Change N} {k : KeyDef N M}
    {l : Leaf N} (hs : k.spec = .arm (.leaf l))
    (hp : l.Plain) {p : Part N} (hpm : p ∈ l.comps) {n : N} (hn : p.name = some n)
    (hch : ch n = some none) (hd : d n = none) (hT : k.ofTable = false)
    (hl : k.lacks d ch = false) : k.step print d ch = .refused (.unbuilt k.name) := by
  have hmem : n ∈ k.foot (given d ch) :=
    (k.foot_iff _ n).mp (hs ▸ KeySpec.ReadsAt.arm (by
      simp only [Arm.reads, Leaf.reads, List.mem_flatMap]
      exact ⟨p, hpm, by simp [hn]⟩))
  have ht : k.touched d ch = true :=
    KeyDef.touched_iff.mpr ⟨n, hmem, by simp [Written, reached_of_apply hch, hd]⟩
  have hg : given d ch n = none := by simp [given, hch]
  have hk : keyOf false false (given d ch) k.spec = .refused := by
    rw [hs]; exact keyOf_leaf_removed hp hpm hn hg
  simp [KeyDef.step, ht, hT, hl, hk, hprint]

/-- **A removal of a key of one attribute is a removal of the key.** The change removes the
    attribute, and the codec does not decide it. The key of the item that the update reads is no
    key, so the update answers as that key does: a removal. -/
theorem KeyDef.step_removal_attr {print : M → Out → Option (Option A)}
    (hprint : ∀ m, print m .nothing = some none) {d : Item N} {ch : Change N} {k : KeyDef N M}
    {n : N}
    (hs : k.spec = .arm (.attr n)) (hch : ch n = some none) (hd : d n = none)
    (hT : k.ofTable = false) : k.step print d ch = .written none := by
  have hmem : n ∈ k.foot (given d ch) :=
    (k.foot_iff _ n).mp (hs ▸ KeySpec.ReadsAt.arm (by simp [Arm.reads]))
  have ht : k.touched d ch = true :=
    KeyDef.touched_iff.mpr ⟨n, hmem, by simp [Written, reached_of_apply hch, hd]⟩
  have hl : k.lacks d ch = false := by
    simp only [KeyDef.lacks, List.any_eq_false]
    intro m hm
    have hm' : KeySpec.ReadsAt (given d ch) k.spec m := (k.foot_iff _ m).mpr hm
    rw [hs] at hm'
    cases hm' with
    | arm h =>
        have : m = n := by simpa [Arm.reads] using h
        subst this
        simp [reached_of_apply hch]
  have hg : given d ch n = none := by simp [given, hch]
  have hk : keyOf false false (given d ch) k.spec = .nothing := by
    rw [hs]; simp [keyOf, select, Arm.key, hg]
  simp [KeyDef.step, ht, hT, hl, hk, hprint]

end DerivedKey

end Calculus
