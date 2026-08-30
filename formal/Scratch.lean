import Calculus
open Calculus

theorem filter_eq_singleton_of_labels {β α ι : Type}
    {adm : β → α → Bool} {key : α → Option ι} {x : α} :
    ∀ {os : List β} {Ss : List (ι → Prop)},
      List.Forall₂ (fun o S => ∀ y, adm o y = true → ∃ l, key y = some l ∧ S l) os Ss →
      List.Pairwise (fun S T => ∀ l, S l → ¬ T l) Ss →
      ∀ o ∈ os, adm o x = true → os.filter (adm · x) = [o]
  | [], _, .nil, _, _, ho, _ => nomatch ho
  | o₀ :: os', S₀ :: Ss', .cons h₀ hz, hp, o, ho, hx => by
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hp
    by_cases h0 : adm o₀ x = true
    · obtain ⟨l, hkey, hS₀⟩ := h₀ x h0
      have hnone : ∀ o' ∈ os', adm o' x = false := by
        intro o' ho'
        cases hq : adm o' x with
        | false => rfl
        | true =>
          obtain ⟨S', hS'mem, hrel⟩ := hz.mem_left ho'
          obtain ⟨l', hkey', hS'⟩ := hrel x hq
          rw [hkey] at hkey'
          cases hkey'
          exact absurd hS' (hhead S' hS'mem l hS₀)
      obtain rfl : o = o₀ := by
        rcases List.mem_cons.mp ho with rfl | ho'
        · rfl
        · exact absurd hx (by rw [hnone o ho']; exact Bool.noConfusion)
      rw [List.filter_cons_of_pos (p := (adm · x)) h0, filter_nil_of hnone]
    · have ho' : o ∈ os' := by
        rcases List.mem_cons.mp ho with rfl | h
        · exact absurd hx (by simp_all)
        · exact h
      rw [List.filter_cons_of_neg (p := (adm · x)) (by simpa using h0)]
      exact filter_eq_singleton_of_labels hz htail o ho' hx

/-- An option pinned to a *set* of labels, under a partial projection of each side. -/
def OptionSem.Labelled {L : Type} (πV : Value → Option L) (πA : Attr → Option L)
    (o : OptionSem) (S : L → Prop) : Prop :=
  (∀ v, o.admitV v = true → ∃ l, πV v = some l ∧ S l) ∧
  (∀ a, o.admitA a = true → ∃ l, πA a = some l ∧ S l)

theorem uniqueAdmission_of_labels {L : Type} {πV : Value → Option L} {πA : Attr → Option L}
    {os : List OptionSem} {Ss : List (L → Prop)}
    (hz : List.Forall₂ (OptionSem.Labelled πV πA) os Ss)
    (hdisj : List.Pairwise (fun S T => ∀ l, S l → ¬ T l) Ss)
    (hw : ∀ o ∈ os, ∀ t a, o.c.e t = some a → o.admitV t = true ∧ o.admitA a = true) :
    UniqueAdmission os := fun o ho t a he =>
  ⟨filter_eq_singleton_of_labels (hz.imp fun _ _ h => h.2) hdisj o ho (hw o ho t a he).2,
   filter_eq_singleton_of_labels (hz.imp fun _ _ h => h.1) hdisj o ho (hw o ho t a he).1⟩

-- instance 1: kinds, one label per option
example {os : List OptionSem} {ks : List Kind}
    (hz : List.Forall₂ OptionSem.OnKind os ks) (hnd : ks.Nodup)
    (hw : ∀ o ∈ os, ∀ t a, o.c.e t = some a → o.admitV t = true ∧ o.admitA a = true) :
    UniqueAdmission os := by
  refine uniqueAdmission_of_labels (πV := fun v => some v.kind) (πA := fun a => some a.kind)
    (Ss := ks.map (fun k l => l = k)) ?_ ?_ hw
  · rw [List.forall₂_map_right_iff]
    exact hz.imp fun _ _ h =>
      ⟨fun v hv => ⟨_, rfl, h.1 v hv⟩, fun a ha => ⟨_, rfl, h.2 a ha⟩⟩
  · rw [List.pairwise_map]
    exact hnd.imp fun hne l hl hl' => hne (hl.symm.trans hl')

-- instance 2: discriminator tags, a set per option
def tagOfV (d : Name) : Value → Option String
  | .map kvs => match kvs.lookup d with | some (.str s) => some s | _ => none
  | _ => none

def tagOfA (d : Name) : Attr → Option String
  | .m kvs => match kvs.lookup d with | some (.s s) => some s | _ => none
  | _ => none

theorem labelled_byTag {d : Name} {tags : List String} {c : Codec} :
    OptionSem.Labelled (tagOfV d) (tagOfA d) (.byTag d tags c) (· ∈ tags) := by
  refine ⟨fun v hv => ?_, fun a ha => ?_⟩
  · obtain ⟨kvs, tag, rfl, hlk, htag⟩ := byTag_admitV.mp hv
    exact ⟨tag, by simp only [tagOfV, hlk], mem_of_contains htag⟩
  · obtain ⟨kvs, tag, rfl, hlk, htag⟩ := byTag_admitA.mp ha
    exact ⟨tag, by simp only [tagOfA, hlk], mem_of_contains htag⟩

example {d : Name} {os : List (List String × Codec)}
    (hstamp : ∀ o ∈ os, ∀ t a, o.2.e t = some a →
      ∃ tag ∈ o.1, (∃ kvs, a = .m kvs ∧ kvs.lookup d = some (.s tag)) ∧
        (∃ kvs, t = .map kvs ∧ kvs.lookup d = some (.str tag)))
    (hdisj : List.Pairwise (fun x y => ∀ tag ∈ x.1, tag ∉ y.1) os) :
    UniqueAdmission (os.map fun o => .byTag d o.1 o.2) := by
  refine uniqueAdmission_of_labels (πV := tagOfV d) (πA := tagOfA d)
    (Ss := os.map (fun o l => l ∈ o.1)) ?_ ?_ ?_
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun o _ => labelled_byTag
  · rw [List.pairwise_map]
    exact hdisj.imp fun h l hl => h l hl
  · refine forall_mem_map fun o ho t a he => ?_
    replace he : o.2.e t = some a := he
    obtain ⟨tag, htag, ⟨kvsA, rfl, hlkA⟩, ⟨kvsV, rfl, hlkV⟩⟩ := hstamp o ho t a he
    exact ⟨byTag_admitV.mpr ⟨kvsV, tag, rfl, hlkV, contains_of_mem htag⟩,
           byTag_admitA.mpr ⟨kvsA, tag, rfl, hlkA, contains_of_mem htag⟩⟩
