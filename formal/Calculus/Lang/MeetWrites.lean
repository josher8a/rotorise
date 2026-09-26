import Calculus.Lang.MeetRows
import Calculus.Lang.Typing

/-!
# The member that the meet names, over a universe signature

`Alg.meet_writes` states that where the meet names a member, any member that a factor names is that
one. The proof recurses on the left operand, as the meet does. Only the leaf family reads a fact of
the universe: a primitive meet names the member that each factor names. A universe supplies that
law in the class `LeafWrites`, outside `Sem` and outside `Leaf`.
-/

namespace Calculus.Alg

variable {S : Syn} [Sem S]

/-- **The member law of a leaf meet**: two primitives meet at a primitive that names the member
    each factor names. -/
class LeafWrites (S : Syn) [Sem S] [Leaf S] : Prop where
  /-- Where the met primitive names a member, each factor names that member or none. -/
  prim_μ : ∀ g g' h : S.Ground, Leaf.prim g g' = some h → ∀ m, Sem.groundμ h = some m →
    (∀ mx, Sem.groundμ g = some mx → mx = m) ∧ (∀ my, Sem.groundμ g' = some my → my = m)

/-- Normalising a refinement keeps the member it stores, because the bottom stores none and so
    does the refinement over it. -/
theorem μSyn_refineOf [Leaf S] {z : Term S} {p : S.Pred} {m : Sem.M S}
    (h : μSyn (Term.refineOf z p) = some m) : μSyn z = some m := by
  cases z <;>
    first
      | exact h
      | (simp only [Term.refineOf] at h
         split at h
         · simpa [μSyn] using h
         · exact absurd h (by simp [μSyn])
         · exact h)

/-- A unanimous list names one member, so every entry is that member. -/
theorem unanimous_all : ∀ {μs : List (Option (Sem.M S))} {m : Sem.M S},
    unanimous μs = some m → ∀ u ∈ μs, u = some m
  | [], _, h => by simp [unanimous] at h
  | μ :: μs, m, h => by
      simp only [unanimous] at h
      split at h
      next hall =>
        subst h
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu'
        · rfl
        · exact of_decide_eq_true (by simpa using (List.all_eq_true.mp hall) u hu')
      next => exact absurd h (by simp)

/-- An option's member is one of the list's. -/
theorem mem_μSynList : ∀ {os : List (Term S)} {o : Term S}, o ∈ os → μSyn o ∈ μSynList os
  | [], _, h => by simp at h
  | t :: ts, o, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_μSynList h')

/-- Every option of a union that names a member names that one. -/
theorem μSyn_union_mem {os : List (Term S)} {m : Sem.M S} (h : μSyn (.union os) = some m) :
    ∀ o ∈ os, μSyn o = some m := by
  intro o ho
  exact unanimous_all (by simpa only [μSyn] using h) _ (mem_μSynList ho)

/-- …and a list of survivors that names a member has one that does. -/
theorem μSyn_ofOptions_mem {ts : List (Term S)} {m : Sem.M S}
    (h : μSyn (Term.ofOptions ts) = some m) : ∃ t ∈ ts, μSyn t = some m := by
  match ts with
  | [] => exact absurd h (by simp [Term.ofOptions, μSyn])
  | [t] => exact ⟨t, by simp, h⟩
  | a :: b :: rest =>
      exact ⟨a, by simp, μSyn_union_mem (os := a :: b :: rest) h a (by simp)⟩

/-! ## The member the meet names, structurally

The same three layers the homomorphism uses. The containers never read the recursion here:
`μSyn` of a `list` and of an `object` is the former's member whatever the payload meets to, so
only the refinement and the union rows recurse. -/

/-- `fam` carries the member with one term fixed on the left, over the operands it is handed. -/
def WritesFam (x : Term S) (fam : Term S → Option (Term S)) : Prop :=
  ∀ y z, Delegated y → fam y = some z → ∀ m : Sem.M S, μSyn z = some m →
    (∀ mx, μSyn x = some mx → mx = m) ∧ (∀ my, μSyn y = some my → my = m)

mutual
/-- Every row that reads the right operand alone names the family's member. -/
theorem writes_meetSRight [Leaf S] {x : Term S} {fam : Term S → Option (Term S)} (hf : WritesFam x fam) :
    ∀ (y : Term S) z, meetSRight fam y = some z → ∀ m : Sem.M S, μSyn z = some m →
      (∀ mx, μSyn x = some mx → mx = m) ∧ (∀ my, μSyn y = some my → my = m)
  | .never, _, h, _, hz => by
      simp only [meetSRight, Option.some.injEq] at h; subst h
      exact absurd hz (by simp [μSyn])
  | .held _ _ _ _, _, h, _, _ => by simp [meetSRight] at h
  | .refine y p, _, h, m, hz => by
      simp only [meetSRight] at h
      split at h
      · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
        replace hz := μSyn_refineOf hz
        have ih := writes_meetSRight hf y w hw m hz
        exact ⟨ih.1, fun my hmy => ih.2 my (by simpa [μSyn] using hmy)⟩
      · exact absurd h (by simp)
  | .union os, _, h, m, hz => by
      obtain ⟨zs, hF, _, _, rfl⟩ := meetSRight_union h
      obtain ⟨w, hw, hwm⟩ := μSyn_ofOptions_mem hz
      obtain ⟨o, ho, hP⟩ :=
        forall₂_mem_right (writes_meetSRightL hf os zs hF) (List.mem_of_mem_filter hw)
      have ih := hP m hwm
      exact ⟨ih.1, fun my hmy => ih.2 my (μSyn_union_mem hmy o ho)⟩
  | .prim g, _, h, m, hz => hf (.prim g) _ trivial h m hz
  | .set b, _, h, m, hz => hf (.set b) _ trivial h m hz
  | .opaq, _, h, m, hz => hf .opaq _ trivial h m hz
  | .list p q s, _, h, m, hz => hf (.list p q s) _ trivial h m hz
  | .object b, _, h, m, hz => hf (.object b) _ trivial h m hz
termination_by structural y => y

/-- The union row's options, lifted pointwise. -/
theorem writes_meetSRightL [Leaf S] {x : Term S} {fam : Term S → Option (Term S)} (hf : WritesFam x fam) :
    ∀ os zs, List.Forall₂ (fun t w => meetSRight fam t = some w) os zs →
      List.Forall₂ (fun t w => ∀ m : Sem.M S, μSyn w = some m →
        (∀ mx, μSyn x = some mx → mx = m) ∧ (∀ my, μSyn t = some my → my = m)) os zs
  | [], _, h => by cases h; exact .nil
  | t :: ts, _, h => by
      cases h with
      | cons hh ht =>
          exact .cons (fun m hm => writes_meetSRight hf t _ hh m hm)
            (writes_meetSRightL hf ts _ ht)
termination_by structural os => os
end

/-- **The one leaf family carries the member.** Two primitives meet at a primitive whose member
    is each factor's, by the leaf law; the top names no member; the bottom names none. -/
theorem writes_famPrim [Leaf S] [LeafWrites S] (g : S.Ground) : WritesFam (.prim g) (famPrim g) := by
  intro y z hd h m hz
  cases y <;> first | exact hd.elim | skip
  case prim g' =>
      simp only [famPrim, Option.some.injEq] at h
      subst h
      cases hp : Leaf.prim g g' with
      | some k =>
          simp only [hp, μSyn] at hz
          exact LeafWrites.prim_μ g g' k hp m hz
      | none => simp only [hp] at hz; exact absurd hz (by simp [μSyn])
  case opaq =>
      simp only [famPrim] at h
      cases ht : Leaf.primTop g with
      | false => simp [ht] at h
      | true =>
          simp only [ht, if_true, Option.some.injEq] at h
          subst h
          exact ⟨fun mx hmx => by rw [hz] at hmx; exact (Option.some.inj hmx).symm,
            fun my hmy => absurd hmy (by simp [μSyn])⟩
  all_goals (simp only [famPrim, Option.some.injEq] at h; subst h; exact absurd hz (by simp [μSyn]))

/-- The top names no member, so the pair agrees vacuously on the left. -/
theorem writes_famOpaq [Leaf S] : WritesFam (.opaq : Term S) famOpaq := by
  intro y z hd h m hz
  cases y <;> first | exact hd.elim | skip
  case prim g =>
      simp only [famOpaq] at h
      cases ht : Leaf.primTop g with
      | false => simp [ht] at h
      | true =>
          simp only [ht, if_true, Option.some.injEq] at h
          subst h
          exact ⟨fun mx hmx => absurd hmx (by simp [μSyn]),
            fun my hmy => by rw [hz] at hmy; exact (Option.some.inj hmy).symm⟩
  case opaq =>
      simp only [famOpaq, Option.some.injEq] at h; subst h; exact absurd hz (by simp [μSyn])
  all_goals simp [famOpaq] at h

/-- **A set names the member its former gives the element's member, and so does every set it
    meets.** The element meet carries the element's member, and the other rows answer the bottom,
    which names none. -/
theorem writes_famSet (a : Term S) {mt : Term S → Option (Term S)}
    (ih : ∀ y z, mt y = some z → ∀ m : Sem.M S, μSyn z = some m →
      (∀ mx, μSyn a = some mx → mx = m) ∧ (∀ my, μSyn y = some my → my = m)) :
    WritesFam (.set a) (famSet a mt) := by
  intro y z hd h m hz
  cases y <;> first | exact hd.elim | skip
  case set y =>
      simp only [famSet] at h
      split at h
      · next z' hz' =>
        split at h
        · simp only [Option.some.injEq] at h; subst h; exact absurd hz (by simp [μSyn])
        · split at h
          · exact nomatch h
          · simp only [Option.some.injEq] at h; subst h
            rcases hL : Sem.set (S := S) with _ | F
            · simp only [μSyn, hL, reduceCtorEq] at hz
            · simp only [μSyn, hL, Option.bind_eq_some_iff] at hz
              obtain ⟨e, he, hsm⟩ := hz
              have hw := ih y z' hz' e he
              refine ⟨fun mx hmx => ?_, fun my hmy => ?_⟩
              · simp only [μSyn, hL, Option.bind_eq_some_iff] at hmx
                obtain ⟨ea, hea, hsa⟩ := hmx
                rw [hw.1 ea hea, hsm] at hsa; exact (Option.some.inj hsa).symm
              · simp only [μSyn, hL, Option.bind_eq_some_iff] at hmy
                obtain ⟨ey, hey, hsy⟩ := hmy
                rw [hw.2 ey hey, hsm] at hsy; exact (Option.some.inj hsy).symm
      · exact nomatch h
  case opaq => simp [famSet] at h
  all_goals (simp only [famSet, Option.some.injEq] at h; subst h; exact absurd hz (by simp [μSyn]))

/-- **A list names the list former's member, and a list it meets names that member too.** The
    family answers a list or the bottom. The bottom names no member, so wherever the answer names a
    member, that member is the former's, and so is each operand's. -/
theorem writes_famList {fpre : List (Term S → Option (Term S))}
    {fsp : Option (Term S → Option (Term S))} {fsuf : List (Term S → Option (Term S))}
    {pre : List (Term S)} {sp : Option (Term S)} {suf : List (Term S)} :
    WritesFam (.list pre sp suf) (famList fpre fsp fsuf) := by
  intro y z hd h m hz
  rcases famList_isList h with rfl | ⟨p, q, s, rfl⟩
  · exact absurd hz (by simp [μSyn])
  · simp only [μSyn] at hz
    refine ⟨fun mx hmx => ?_, fun my hmy => ?_⟩
    · simp only [μSyn, hz, Option.some.injEq] at hmx; exact hmx.symm
    · cases y <;> simp only [famList] at h <;>
        first
          | (simp only [μSyn, hz, Option.some.injEq] at hmy; exact hmy.symm)
          | exact absurd h (by simp)

/-- **An object names the map former's member**, and the bottom it can answer names none. -/
theorem writes_famObj {a : Body S}
    {g : {k // k ∈ a.fields} → ObjectSlot S → Option (ObjectSlot S)}
    {mw : Term S → Option (Term S)} :
    WritesFam (.object a) (famObj a g mw) := by
  intro y z hd h m hz
  cases y <;> first | exact hd.elim | skip
  case object b =>
      rcases objObj_cases (by simpa [famObj] using h) with rfl | ⟨c, rfl⟩
      · exact absurd hz (by simp [μSyn])
      · simp only [μSyn] at hz
        refine ⟨fun mx hmx => ?_, fun my hmy => ?_⟩
        · simp only [μSyn, hz, Option.some.injEq] at hmx; exact hmx.symm
        · simp only [μSyn, hz, Option.some.injEq] at hmy; exact hmy.symm
  case opaq => simp [famObj] at h
  all_goals (simp only [famObj, Option.some.injEq] at h; subst h; exact absurd hz (by simp [μSyn]))

mutual
/-- **Where the meet names a member, any member a factor names is that one.** `μSyn z` is a
    hypothesis and not a conclusion, because the converse fails twice: a bottom names no member,
    so two factors naming different members meet at a term that names none, and a refinement over
    the bottom is not the bottom, so excluding `never` does not repair it. -/
theorem meet_writes [Leaf S] [LeafWrites S] : ∀ (x y : Term S) z, Term.meet x y = some z → ∀ m : Sem.M S, μSyn z = some m →
    (∀ mx, μSyn x = some mx → mx = m) ∧ (∀ my, μSyn y = some my → my = m)
  | .never, _, _, h, _, hz => by
      simp only [Term.meet, Option.some.injEq] at h; subst h
      exact absurd hz (by simp [μSyn])
  | .held _ _ _ _, y, _, h, _, hz => by
      cases y <;>
        first
          | (simp only [Term.meet, Option.some.injEq] at h; subst h
             exact absurd hz (by simp [μSyn]))
          | exact absurd h (by simp [Term.meet])
  | .mu _, y, _, h, _, hz => by
      cases y <;>
        first
          | (simp only [Term.meet, Option.some.injEq] at h; subst h
             exact absurd hz (by simp [μSyn]))
          | exact absurd h (by simp [Term.meet])
  | .refine x p, y, _, h, m, hz => by
      cases y with
      | never =>
          simp only [Term.meet, Option.some.injEq] at h; subst h
          exact absurd hz (by simp [μSyn])
      | _ =>
        simp only [Term.meet] at h
        split at h
        · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
          replace hz := μSyn_refineOf hz
          have ih := meet_writes x _ w hw m hz
          exact ⟨fun mx hmx => ih.1 mx (by simpa [μSyn] using hmx), ih.2⟩
        · exact absurd h (by simp)
  | .union os, y, _, h, m, hz => by
      cases y with
      | never =>
          simp only [Term.meet, Option.some.injEq] at h; subst h
          exact absurd hz (by simp [μSyn])
      | _ =>
        obtain ⟨zs, hF, _, _, rfl⟩ := meet_union_of h (by simp)
        obtain ⟨w, hw, hwm⟩ := μSyn_ofOptions_mem hz
        obtain ⟨o, ho, hP⟩ :=
          forall₂_mem_right (writes_meetL os _ zs hF) (List.mem_of_mem_filter hw)
        have ih := hP m hwm
        exact ⟨fun mx hmx => ih.1 mx (μSyn_union_mem hmx o ho), ih.2⟩
  | .prim g, y, z, h, m, hz => writes_meetSRight (writes_famPrim g) y z h m hz
  | .set a, y, z, h, m, hz =>
      writes_meetSRight (writes_famSet a (fun u w hw => meet_writes a u w hw)) y z h m hz
  | .opaq, y, z, h, m, hz => writes_meetSRight (writes_famOpaq) y z h m hz
  | .list pre sp suf, y, z, h, m, hz => by
      cases sp with
      | none =>
          exact writes_meetSRight (writes_famList (pre := pre) (sp := none) (suf := suf)
            (fpre := Term.meetSTs pre) (fsp := none)
            (fsuf := Term.meetSTs suf)) y z h m hz
      | some t =>
          exact writes_meetSRight (writes_famList (pre := pre) (sp := some t) (suf := suf)
            (fpre := Term.meetSTs pre) (fsp := some (Term.meet t))
            (fsuf := Term.meetSTs suf)) y z h m hz
  | .object (.mk fs f none), y, z, h, m, hz =>
      writes_meetSRight (writes_famObj (a := .mk fs f none)
        (g := fun k => ObjectSlot.meet (f k)) (mw := fun _ => some .never)) y z h m hz
  | .object (.mk fs f (some t)), y, z, h, m, hz =>
      writes_meetSRight (writes_famObj (a := .mk fs f (some t))
        (g := fun k => ObjectSlot.meet (f k)) (mw := Term.meet t)) y z h m hz
termination_by structural x => x

/-- The union row's options, lifted pointwise at the fixed partner. -/
theorem writes_meetL [Leaf S] [LeafWrites S] : ∀ (os : List (Term S)) (y : Term S) (zs : List (Term S)),
    List.Forall₂ (fun t w => Term.meet t y = some w) os zs →
    List.Forall₂ (fun t w => ∀ m : Sem.M S, μSyn w = some m →
      (∀ mx, μSyn t = some mx → mx = m) ∧ (∀ my, μSyn y = some my → my = m)) os zs
  | [], _, _, h => by cases h; exact .nil
  | t :: ts, y, _, h => by
      cases h with
      | cons hh ht =>
          exact .cons (fun m hm => meet_writes t y _ hh m hm) (writes_meetL ts y _ ht)
termination_by structural os => os
end

end Calculus.Alg
