import Calculus.Alg.Containers
import Calculus.Alg.Relations

/-!
# Recursion, over any carriers

A recursive codec reads each input at the stage of its body that the input's own depth names. The
construct reads a universe only through one depth on the carrier, and the depth reads no
orientation. The guard is `Contractive`: the
body reads its argument only at inputs strictly shallower than its own input.

The combinators keep agreement. A container reads its element codecs one layer down, so it turns
agreement below `d` into agreement below `d + 1`. The universe supplies that fact as the depth of
its prisms. A sum and a restriction read the same input, so they keep the depth.
-/

namespace Calculus.Alg

variable {V M : Type} {member : V → M} (depth : V → Nat)

/-! ## Agreement below a depth -/

/-- Two codecs agree on every input of depth at most `d`, at each orientation. `Lawful` relates
    the two orientations, so a statement about one orientation alone cannot carry the laws to a
    limit. -/
structure AgreeLe (d : Nat) (c₁ c₂ : Codec V M) : Prop where
  f : ∀ (o : Orient) (x : V), depth x ≤ d → c₁.f o x = c₂.f o x

namespace AgreeLe

variable {depth} {d : Nat} {c₁ c₂ c₃ : Codec V M}

/-- Agreement from agreement at each orientation. -/
theorem ofF (h : ∀ o x, depth x ≤ d → c₁.f o x = c₂.f o x) : AgreeLe depth d c₁ c₂ := ⟨h⟩

/-- A codec agrees with itself at every depth. -/
theorem refl (d : Nat) (c : Codec V M) : AgreeLe depth d c c := ⟨fun _ _ _ => rfl⟩

/-- Agreement below a depth is symmetric. -/
theorem symm (h : AgreeLe depth d c₁ c₂) : AgreeLe depth d c₂ c₁ :=
  ⟨fun o x hx => (h.f o x hx).symm⟩

/-- Agreement below a depth is transitive. -/
theorem trans (h : AgreeLe depth d c₁ c₂) (h' : AgreeLe depth d c₂ c₃) : AgreeLe depth d c₁ c₃ :=
  ⟨fun o x hx => (h.f o x hx).trans (h'.f o x hx)⟩

/-- Agreement below a depth holds below every smaller depth. -/
theorem mono {d' : Nat} (h : AgreeLe depth d c₁ c₂) (hd : d' ≤ d) : AgreeLe depth d' c₁ c₂ :=
  ⟨fun o x hx => h.f o x (le_trans hx hd)⟩

/-- Where every input has depth at least one, any two codecs agree below depth zero. -/
theorem zero (hd : ∀ v, 0 < depth v) (c₁ c₂ : Codec V M) :
    AgreeLe depth 0 c₁ c₂ :=
  ⟨fun _ x hx => absurd hx (Nat.not_le.mpr (hd x))⟩

/-- Two codecs with one map agree at every depth. -/
theorem of_eq (h : c₁.f = c₂.f) : AgreeLe depth d c₁ c₂ :=
  ⟨fun o x _ => congrFun (congrFun h o) x⟩

/-- …and agreement at every depth is one map, because every input has a depth. -/
theorem eq_of_forall (h : ∀ d, AgreeLe depth d c₁ c₂) : c₁.f = c₂.f :=
  funext fun o => funext fun x => (h _).f o x le_rfl

end AgreeLe

/-! ## The construct -/

/-- **The guard, on a body.** The body reads its argument only at inputs strictly shallower than
    its own input, on both sides. -/
def Contractive (B : Codec V M → Codec V M) : Prop :=
  ∀ d c₁ c₂, AgreeLe depth d c₁ c₂ → AgreeLe depth (d + 1) (B c₁) (B c₂)

/-- **The recursive codec**: each input read at the stage its own depth names. The member is
    `⊤`, because the stages need not agree on one. The held set is the write domain, so the held
    set of a recursive term is its admission with no induction over the stages. -/
def muCodec (B : Codec V M → Codec V M) : Codec V M where
  T v := ((muStage B (depth v)).e v).isSome = true
  μ := none
  f o x := (muStage B (depth x)).f o x

variable {depth}

/-- The limit sends an input at the stage that the depth of the input names. -/
theorem muCodec_f (B : Codec V M → Codec V M) (o : Orient) (x : V) :
    (muCodec depth B).f o x = (muStage B (depth x)).f o x := rfl

/-! ### The converse of the construct -/

section Stages
variable (hd : ∀ v, 0 < depth v) {B : Codec V M → Codec V M}
include hd


/-- Each stage agrees with the next one below its own index. -/
theorem muStage_stable (hB : Contractive depth B) :
    ∀ n, AgreeLe depth n (muStage B n) (muStage B (n + 1))
  | 0 => AgreeLe.zero hd _ _
  | n + 1 => hB n _ _ (muStage_stable hB n)

/-- **Stability.** Past the depth of the input, a later stage changes nothing. -/
theorem muStage_agree (hB : Contractive depth B) {d : Nat} :
    ∀ k, AgreeLe depth d (muStage B d) (muStage B (d + k))
  | 0 => AgreeLe.refl _ _
  | k + 1 => (muStage_agree hB k).trans ((muStage_stable hd hB (d + k)).mono (by omega))

/-- Any two stages at or past `d` agree below `d`. -/
theorem muStage_agree_le (hB : Contractive depth B) {d n : Nat} (h : d ≤ n) :
    AgreeLe depth d (muStage B d) (muStage B n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact muStage_agree hd hB k

/-- The limit agrees with the stage `n` below `n`. -/
theorem muCodec_agree (hB : Contractive depth B) (n : Nat) :
    AgreeLe depth n (muCodec depth B) (muStage B n) :=
  ⟨fun o x hx => (muStage_agree_le hd hB hx).f o x le_rfl⟩

/-- **The fixed point.** The limit sends what its body sends over the limit, at each
    orientation. -/
theorem muCodec_fix (hB : Contractive depth B) (o : Orient) (x : V) :
    (muCodec depth B).f o x = (B (muCodec depth B)).f o x := by
  obtain ⟨k, hk⟩ : ∃ k, depth x = k + 1 :=
    ⟨depth x - 1, by have := hd x; omega⟩
  rw [muCodec_f, hk]
  exact (hB k _ _ (muCodec_agree hd hB k).symm).f o x (by omega)

/-- **Lawful stages give a lawful limit.** The input reads at its own depth, and the output at
    its own depth. Stability moves both answers to the stage at the larger of the two depths,
    and that stage is lawful. One proof serves each orientation. -/
theorem lawful_muCodec (hB : Contractive depth B)
    (hs : ∀ n, Lawful member (muStage B n)) : Lawful member (muCodec depth B) where
  inv {o x y} h := by
    have hl := Nat.le_max_left (depth x) (depth y)
    have hr := Nat.le_max_right (depth x) (depth y)
    rw [muCodec_f, (muStage_agree_le hd hB hl).f o x le_rfl] at h
    rw [muCodec_f, (muStage_agree_le hd hB hr).f o.op y le_rfl]
    exact (hs _).inv h
  writes hμ := nomatch hμ

end Stages

/-- A lawful limit is on its held set. The held set is the write domain, and a lawful codec writes
    every value it reads. -/
theorem carrier_muCodec {B : Codec V M → Codec V M} (h : Lawful member (muCodec depth B)) :
    Carrier (muCodec depth B) :=
  ⟨fun he => Option.isSome_iff_exists.mpr ⟨_, he⟩,
   fun hp => Option.isSome_iff_exists.mpr ⟨_, h.canon hp⟩⟩

/-- Two bodies that preserve agreement below `d` give limits that agree below `d`. -/
theorem agreeLe_muCodec {d : Nat} {B₁ B₂ : Codec V M → Codec V M}
    (h : ∀ c₁ c₂, AgreeLe depth d c₁ c₂ → AgreeLe depth d (B₁ c₁) (B₂ c₂)) :
    AgreeLe depth d (muCodec depth B₁) (muCodec depth B₂) := by
  have hs : ∀ n, AgreeLe depth d (muStage B₁ n) (muStage B₂ n) := fun n => by
    induction n with
    | zero => exact AgreeLe.refl _ _
    | succ n ih => exact h _ _ ih
  exact ⟨fun o x hx => (hs _).f o x hx⟩

/-! ## The combinators keep agreement -/

/-- First-match resolution reads each option at the input only. -/
theorem select_congr {X R : Type} {run : Codec V M → X → Option R} {x : X} :
    ∀ {os₁ os₂ : List (Codec V M)}, List.Forall₂ (fun o₁ o₂ => run o₁ x = run o₂ x) os₁ os₂ →
      select os₁ run x = select os₂ run x
  | [], [], .nil => rfl
  | o₁ :: os₁, o₂ :: os₂, .cons h hs => by
      have ih := select_congr hs
      simp only [select, List.find?_cons] at ih ⊢
      rw [h]
      cases run o₂ x <;> simp [ih, h]

/-- A sum reads its options at its own input, so it keeps the depth of their agreement. -/
theorem agreeLe_altCodec {d : Nat} {os₁ os₂ : List (Codec V M)} (μ₁ μ₂ : Option M)
    (h : List.Forall₂ (AgreeLe depth d) os₁ os₂) :
    AgreeLe depth d (altCodec os₁ μ₁) (altCodec os₂ μ₂) :=
  ⟨fun o x hx => select_congr (h.imp fun _ _ hc => hc.f o x hx)⟩

/-- The two-sided restriction keeps agreement below a depth. -/
theorem agreeLe_refine2 {d : Nat} {c₁ c₂ : Codec V M} (h : AgreeLe depth d c₁ c₂)
    (qV : V → Bool) (qA : V → Bool) :
    AgreeLe depth d (refine2 c₁ qV qA) (refine2 c₂ qV qA) :=
  ⟨fun o x hx => by simp only [refine2, h.f o x hx]⟩

/-- A row of codecs that agree below `d`, zipped with inputs no deeper than `d`, traverses to
    one answer. -/
theorem traverse_zip_congr {α β : Type} {d : Nat} {run : Codec V M → α → Option β}
    {dx : α → Nat}
    (hrun : ∀ c₁ c₂ x, AgreeLe depth d c₁ c₂ → dx x ≤ d → run c₁ x = run c₂ x) :
    ∀ {ds₁ ds₂ : List (Codec V M)} (xs : List α), List.Forall₂ (AgreeLe depth d) ds₁ ds₂ →
      (∀ x ∈ xs, dx x ≤ d) →
      traverse (fun cx => run cx.1 cx.2) (ds₁.zip xs)
        = traverse (fun cx => run cx.1 cx.2) (ds₂.zip xs)
  | _, _, [], .nil, _ => rfl
  | _, _, [], .cons _ _, _ => rfl
  | _, _, _ :: _, .nil, _ => rfl
  | _, _, x :: xs, .cons hc hcs, hx => by
      simp only [List.zip_cons_cons, traverse_cons]
      rw [hrun _ _ x hc (hx x List.mem_cons_self),
        traverse_zip_congr hrun xs hcs fun y hy => hx y (List.mem_cons_of_mem _ hy)]

/-- …and so does a row that the shape may refuse, when both rows refuse together. -/
theorem traverse_row_congr {α β : Type} {d : Nat} {run : Codec V M → α → Option β}
    {dx : α → Nat}
    (hrun : ∀ c₁ c₂ x, AgreeLe depth d c₁ c₂ → dx x ≤ d → run c₁ x = run c₂ x)
    (xs : List α) (hx : ∀ x ∈ xs, dx x ≤ d) :
    ∀ {r₁ r₂ : Option (List (Codec V M))}, Option.Rel (List.Forall₂ (AgreeLe depth d)) r₁ r₂ →
      (r₁.map (·.zip xs)).bind (traverse fun cx => run cx.1 cx.2)
        = (r₂.map (·.zip xs)).bind (traverse fun cx => run cx.1 cx.2)
  | _, _, .none => rfl
  | _, _, .some h => traverse_zip_congr hrun xs h hx

/-- A `list` reads each element one layer down, so it turns agreement below `d` into agreement
    below `d + 1`. The universe supplies the depth of its list prism. -/
theorem agreeLe_listCodec {sL : Summand (List V) V M member}
    (hd : ∀ vs, ∀ x ∈ vs, depth x + 1 ≤ depth (sL.p.into vs)) {d : Nat}
    {pre₁ pre₂ suf₁ suf₂ : List (Codec V M)} {sp₁ sp₂ : Option (Codec V M)}
    (hpre : List.Forall₂ (AgreeLe depth d) pre₁ pre₂) (hsp : Option.Rel (AgreeLe depth d) sp₁ sp₂)
    (hsuf : List.Forall₂ (AgreeLe depth d) suf₁ suf₂) :
    AgreeLe depth (d + 1) (listCodec sL pre₁ sp₁ suf₁)
      (listCodec sL pre₂ sp₂ suf₂) := by
  refine .ofF fun o v hv => ?_
  show ((sL.p.out v).bind _).map sL.p.into = ((sL.p.out v).bind _).map sL.p.into
  cases h : sL.p.out v with
  | none => rfl
  | some vs =>
    have hvv := sL.p.into_out h
    simp only [Option.bind_some, alignL]
    exact congrArg (Option.map sL.p.into) (traverse_row_congr (fun _ _ x hc hx => hc.f o x hx) vs
      (fun x hx => by have := hd vs x hx; rw [← hvv] at this; omega)
      (slotsL_rel hpre hsp hsuf vs.length))

/-! ### Objects

An object reads its entry codecs at the entries of a map, one layer below the map. A slot's
behavior at absence reads the shape of its field and never its codec, so two tables of one shape
act alike at absence. -/

section ObjectAgree
variable {R : Codec V M → Codec V M → Prop} {keys : Finset String}
  {F₁ F₂ : {k // k ∈ keys} → FieldSem V M}

/-- A lookup in two tables of one key set is related where the fields are. -/
theorem mapOf_at_rel (hF : ∀ k, FieldSem.Rel R (F₁ k) (F₂ k)) (k : String) :
    Option.Rel (FieldSem.Rel R) ((⟨keys, F₁⟩ : MapOf (FieldSem V M)).at k)
      ((⟨keys, F₂⟩ : MapOf (FieldSem V M)).at k) := by
  unfold MapOf.at
  split
  · exact .some (hF _)
  · exact .none

/-- The codec an entry goes through is related where the table and the rest codec are. -/
theorem entryCodec_rel {rc₁ rc₂ : Option (Codec V M)} (hr : Option.Rel R rc₁ rc₂) :
    ∀ {o₁ o₂ : Option (FieldSem V M)}, Option.Rel (FieldSem.Rel R) o₁ o₂ →
      Option.Rel R (match o₁ with | some fs => some fs.codec | none => rc₁)
        (match o₂ with | some fs => some fs.codec | none => rc₂)
  | _, _, .none => hr
  | _, _, .some h => .some h.codec

end ObjectAgree

/-- An object reads each entry one layer below the map, so it turns agreement below `d` into
    agreement below `d + 1`. The universe supplies the depth of its keyed-map prism. -/
theorem agreeLe_objectCodec {sM : Summand (MapOf V) V M member}
    (hd : ∀ (m : MapOf V) k, depth (m.get k) + 1 ≤ depth (sM.p.into m)) {d : Nat}
    {keys : Finset String} {F₁ F₂ : {k // k ∈ keys} → FieldSem V M}
    {r₁ r₂ : RestSem V M} (hF : ∀ k, FieldSem.Rel (AgreeLe depth d) (F₁ k) (F₂ k))
    (hr : RestSem.Rel (AgreeLe depth d) r₁ r₂) :
    AgreeLe depth (d + 1) (objectCodec sM ⟨keys, F₁⟩ r₁)
      (objectCodec sM ⟨keys, F₂⟩ r₂) := by
  have hent : ∀ k, Option.Rel (AgreeLe depth d) (entryCodec ⟨keys, F₁⟩ (rcOf r₁) k)
      (entryCodec ⟨keys, F₂⟩ (rcOf r₂) k) := fun k => entryCodec_rel hr.rcOf (mapOf_at_rel hF k)
  have hbind : ∀ {α β : Type} (run : Codec V M → α → Option β) (x : α),
      (∀ c₁ c₂, AgreeLe depth d c₁ c₂ → run c₁ x = run c₂ x) → ∀ k,
      (entryCodec ⟨keys, F₁⟩ (rcOf r₁) k).bind (run · x)
        = (entryCodec ⟨keys, F₂⟩ (rcOf r₂) k).bind (run · x) := fun run x hrun k =>
    optionRel_bind (fun _ _ h => hrun _ _ h) (hent k)
  unfold objectCodec
  refine .ofF fun o v hv => ?_
  show ((sM.p.out v).bind _).map sM.p.into = ((sM.p.out v).bind _).map sM.p.into
  cases h : sM.p.out v with
  | none => rfl
  | some m =>
    have hvv := sM.p.into_out h
    refine congrArg (Option.map sM.p.into) ?_
    simp only [Option.bind_some, objAt_eq_objP]
    refine objP_congr fun k _ => ?_
    rcases Decidable.em (k ∈ m.keys) with hk | hk
    · rw [MapOf.at_of_mem ⟨k, hk⟩]
      exact congrArg (Option.map some) (hbind (·.f o ·) (m.get ⟨k, hk⟩) (fun _ _ h => h.f o _ (by
        have := hd m ⟨k, hk⟩; rw [← hvv] at this; omega)) k)
    · rw [MapOf.at_none hk]
      exact absentOf_rel o (mapOf_at_rel hF k)

end Calculus.Alg
