import Calculus.Alg.Containers
import Calculus.Alg.Relations

/-!
# Recursion, over any carriers

A recursive codec reads each input at the stage of its body that the input's own depth names. The
construct reads a universe only through a depth on each carrier. The guard is `Contractive`: the
body reads its argument only at inputs strictly shallower than its own input.

The combinators keep agreement. A container reads its element codecs one layer down, so it turns
agreement below `d` into agreement below `d + 1`. The universe supplies that fact as the depth of
its prisms. A sum and a restriction read the same input, so they keep the depth.
-/

namespace Calculus.Alg

variable {V M : Type} {member : V → M} (dV : V → Nat) (dA : V → Nat)

/-! ## Agreement below a depth -/

/-- Two codecs agree on every input of depth at most `d`, on both sides. `Lawful` relates the
    two sides, so a statement about one side alone cannot carry the laws to a limit. -/
structure AgreeLe (d : Nat) (c₁ c₂ : Codec V M) : Prop where
  e : ∀ v, dV v ≤ d → c₁.e v = c₂.e v
  p : ∀ a, dA a ≤ d → c₁.p a = c₂.p a

namespace AgreeLe

variable {dV dA} {d : Nat} {c₁ c₂ c₃ : Codec V M}

/-- A codec agrees with itself at every depth. -/
theorem refl (d : Nat) (c : Codec V M) : AgreeLe dV dA d c c :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- Agreement below a depth is symmetric. -/
theorem symm (h : AgreeLe dV dA d c₁ c₂) : AgreeLe dV dA d c₂ c₁ :=
  ⟨fun v hv => (h.e v hv).symm, fun a ha => (h.p a ha).symm⟩

/-- Agreement below a depth is transitive. -/
theorem trans (h : AgreeLe dV dA d c₁ c₂) (h' : AgreeLe dV dA d c₂ c₃) : AgreeLe dV dA d c₁ c₃ :=
  ⟨fun v hv => (h.e v hv).trans (h'.e v hv), fun a ha => (h.p a ha).trans (h'.p a ha)⟩

/-- Agreement below a depth holds below every smaller depth. -/
theorem mono {d' : Nat} (h : AgreeLe dV dA d c₁ c₂) (hd : d' ≤ d) : AgreeLe dV dA d' c₁ c₂ :=
  ⟨fun v hv => h.e v (le_trans hv hd), fun a ha => h.p a (le_trans ha hd)⟩

/-- Where every input has depth at least one, any two codecs agree below depth zero. -/
theorem zero (hV : ∀ v, 0 < dV v) (hA : ∀ a, 0 < dA a) (c₁ c₂ : Codec V M) :
    AgreeLe dV dA 0 c₁ c₂ :=
  ⟨fun v hv => absurd hv (Nat.not_le.mpr (hV v)),
   fun a ha => absurd ha (Nat.not_le.mpr (hA a))⟩

/-- Two codecs with one pair of halves agree at every depth. -/
theorem of_eq (he : c₁.e = c₂.e) (hp : c₁.p = c₂.p) : AgreeLe dV dA d c₁ c₂ :=
  ⟨fun v _ => congrFun he v, fun a _ => congrFun hp a⟩

/-- Agreement below a depth, at an orientation: the two maps at `o` agree at each input of
    depth at most `d`. -/
theorem f (h : AgreeLe dV dA d c₁ c₂) :
    ∀ (o : Orient) (x : Side V o.c), Side.elim dV dA o.c x ≤ d → c₁.f o x = c₂.f o x :=
  Orient.both h.e h.p

/-- …and agreement at every depth is one pair of halves, because every input has a depth. -/
theorem eq_of_forall (h : ∀ d, AgreeLe dV dA d c₁ c₂) : c₁.e = c₂.e ∧ c₁.p = c₂.p :=
  ⟨funext fun v => (h _).e v le_rfl, funext fun a => (h _).p a le_rfl⟩

end AgreeLe

/-! ## The construct -/

/-- **The guard, on a body.** The body reads its argument only at inputs strictly shallower than
    its own input, on both sides. -/
def Contractive (B : Codec V M → Codec V M) : Prop :=
  ∀ d c₁ c₂, AgreeLe dV dA d c₁ c₂ → AgreeLe dV dA (d + 1) (B c₁) (B c₂)

/-- **The recursive codec**: each input read at the stage its own depth names. The member is
    `⊤`, because the stages need not agree on one. The held set is the write domain, so the held
    set of a recursive term is its admission with no induction over the stages. -/
def muCodec (B : Codec V M → Codec V M) : Codec V M where
  T v := ((muStage B (dV v)).e v).isSome = true
  μ := none
  f o x := (muStage B (Side.elim dV dA o.c x)).f o x

variable {dV dA}

/-- The limit sends an input at the stage that the depth of the input names. -/
theorem muCodec_f (B : Codec V M → Codec V M) (o : Orient) (x : Side V o.c) :
    (muCodec dV dA B).f o x = (muStage B (Side.elim dV dA o.c x)).f o x := rfl

/-! ### The converse of the construct -/

section Stages
variable (hV : ∀ v, 0 < dV v) (hA : ∀ a, 0 < dA a) {B : Codec V M → Codec V M}
include hV hA

/-- Every input has a positive depth, at each side. -/
theorem depth_pos : ∀ (s : Bool) (x : Side V s), 0 < Side.elim dV dA s x
  | false, v => hV v
  | true, a => hA a

/-- Each stage agrees with the next one below its own index. -/
theorem muStage_stable (hB : Contractive dV dA B) :
    ∀ n, AgreeLe dV dA n (muStage B n) (muStage B (n + 1))
  | 0 => AgreeLe.zero hV hA _ _
  | n + 1 => hB n _ _ (muStage_stable hB n)

/-- **Stability.** Past the depth of the input, a later stage changes nothing. -/
theorem muStage_agree (hB : Contractive dV dA B) {d : Nat} :
    ∀ k, AgreeLe dV dA d (muStage B d) (muStage B (d + k))
  | 0 => AgreeLe.refl _ _
  | k + 1 => (muStage_agree hB k).trans ((muStage_stable hV hA hB (d + k)).mono (by omega))

/-- Any two stages at or past `d` agree below `d`. -/
theorem muStage_agree_le (hB : Contractive dV dA B) {d n : Nat} (h : d ≤ n) :
    AgreeLe dV dA d (muStage B d) (muStage B n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact muStage_agree hV hA hB k

/-- The limit agrees with the stage `n` below `n`. -/
theorem muCodec_agree (hB : Contractive dV dA B) (n : Nat) :
    AgreeLe dV dA n (muCodec dV dA B) (muStage B n) :=
  ⟨fun v hv => (muStage_agree_le hV hA hB hv).e v le_rfl,
   fun a ha => (muStage_agree_le hV hA hB ha).p a le_rfl⟩

/-- **The fixed point.** The limit sends what its body sends over the limit, at each
    orientation. -/
theorem muCodec_fix (hB : Contractive dV dA B) (o : Orient) (x : Side V o.c) :
    (muCodec dV dA B).f o x = (B (muCodec dV dA B)).f o x := by
  obtain ⟨k, hk⟩ : ∃ k, Side.elim dV dA o.c x = k + 1 :=
    ⟨Side.elim dV dA o.c x - 1, by have := depth_pos hV hA o.c x; omega⟩
  rw [muCodec_f, hk]
  exact (hB k _ _ (muCodec_agree hV hA hB k).symm).f o x (by omega)

/-- **Lawful stages give a lawful limit.** The input reads at its own depth, and the output at
    its own depth. Stability moves both answers to the stage at the larger of the two depths,
    and that stage is lawful. One proof serves each orientation. -/
theorem lawful_muCodec (hB : Contractive dV dA B)
    (hs : ∀ n, Lawful member (muStage B n)) : Lawful member (muCodec dV dA B) where
  inv {o x y} h := by
    have hl := Nat.le_max_left (Side.elim dV dA o.c x) (Side.elim dV dA o.s y)
    have hr := Nat.le_max_right (Side.elim dV dA o.c x) (Side.elim dV dA o.s y)
    rw [muCodec_f, (muStage_agree_le hV hA hB hl).f o x le_rfl] at h
    rw [muCodec_f, (muStage_agree_le hV hA hB hr).f o.op y le_rfl]
    exact (hs _).inv h
  writes hμ := nomatch hμ

end Stages

/-- A lawful limit is on its held set. The held set is the write domain, and a lawful codec writes
    every value it reads. -/
theorem carrier_muCodec {B : Codec V M → Codec V M} (h : Lawful member (muCodec dV dA B)) :
    Carrier (muCodec dV dA B) :=
  ⟨fun he => Option.isSome_iff_exists.mpr ⟨_, he⟩,
   fun hp => Option.isSome_iff_exists.mpr ⟨_, h.canon hp⟩⟩

/-- Two bodies that preserve agreement below `d` give limits that agree below `d`. -/
theorem agreeLe_muCodec {d : Nat} {B₁ B₂ : Codec V M → Codec V M}
    (h : ∀ c₁ c₂, AgreeLe dV dA d c₁ c₂ → AgreeLe dV dA d (B₁ c₁) (B₂ c₂)) :
    AgreeLe dV dA d (muCodec dV dA B₁) (muCodec dV dA B₂) := by
  have hs : ∀ n, AgreeLe dV dA d (muStage B₁ n) (muStage B₂ n) := fun n => by
    induction n with
    | zero => exact AgreeLe.refl _ _
    | succ n ih => exact h _ _ ih
  exact ⟨fun v hv => (hs _).e v hv, fun a ha => (hs _).p a ha⟩

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
    (h : List.Forall₂ (AgreeLe dV dA d) os₁ os₂) :
    AgreeLe dV dA d (altCodec os₁ μ₁) (altCodec os₂ μ₂) :=
  ⟨fun v hv => select_congr (h.imp fun _ _ hc => hc.e v hv),
   fun a ha => select_congr (h.imp fun _ _ hc => hc.p a ha)⟩

/-- The two-sided restriction keeps agreement below a depth. -/
theorem agreeLe_refine2 {d : Nat} {c₁ c₂ : Codec V M} (h : AgreeLe dV dA d c₁ c₂)
    (qV : V → Bool) (qA : V → Bool) :
    AgreeLe dV dA d (refine2 c₁ qV qA) (refine2 c₂ qV qA) :=
  ⟨fun v hv => by simp only [refine2_e_def, h.e v hv],
    fun a ha => by simp only [refine2_p_def, h.p a ha]⟩

/-- A restriction reads its codec at its own input, so it keeps the depth. -/
theorem agreeLe_restrict {d : Nat} {c₁ c₂ : Codec V M} (h : AgreeLe dV dA d c₁ c₂)
    (q : V → Bool) : AgreeLe dV dA d (c₁.restrict q) (c₂.restrict q) :=
  agreeLe_refine2 h q _

/-- A row of codecs that agree below `d`, zipped with inputs no deeper than `d`, traverses to
    one answer. -/
theorem traverse_zip_congr {α β : Type} {d : Nat} {run : Codec V M → α → Option β}
    {depth : α → Nat}
    (hrun : ∀ c₁ c₂ x, AgreeLe dV dA d c₁ c₂ → depth x ≤ d → run c₁ x = run c₂ x) :
    ∀ {ds₁ ds₂ : List (Codec V M)} (xs : List α), List.Forall₂ (AgreeLe dV dA d) ds₁ ds₂ →
      (∀ x ∈ xs, depth x ≤ d) →
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
    {depth : α → Nat}
    (hrun : ∀ c₁ c₂ x, AgreeLe dV dA d c₁ c₂ → depth x ≤ d → run c₁ x = run c₂ x)
    (xs : List α) (hx : ∀ x ∈ xs, depth x ≤ d) :
    ∀ {r₁ r₂ : Option (List (Codec V M))}, Option.Rel (List.Forall₂ (AgreeLe dV dA d)) r₁ r₂ →
      (r₁.map (·.zip xs)).bind (traverse fun cx => run cx.1 cx.2)
        = (r₂.map (·.zip xs)).bind (traverse fun cx => run cx.1 cx.2)
  | _, _, .none => rfl
  | _, _, .some h => traverse_zip_congr hrun xs h hx

/-- A `list` reads each element one layer down, so it turns agreement below `d` into agreement
    below `d + 1`. The universe supplies the depth of its two list prisms. -/
theorem agreeLe_listCodec {pV : Ctor (List V) V} {pA : Ctor (List V) V} {μL : M}
    (hdV : ∀ vs, ∀ x ∈ vs, dV x + 1 ≤ dV (pV.into vs))
    (hdA : ∀ as, ∀ x ∈ as, dA x + 1 ≤ dA (pA.into as)) {d : Nat}
    {pre₁ pre₂ suf₁ suf₂ : List (Codec V M)} {sp₁ sp₂ : Option (Codec V M)}
    (hpre : List.Forall₂ (AgreeLe dV dA d) pre₁ pre₂) (hsp : Option.Rel (AgreeLe dV dA d) sp₁ sp₂)
    (hsuf : List.Forall₂ (AgreeLe dV dA d) suf₁ suf₂) :
    AgreeLe dV dA (d + 1) (listCodec pV pA μL pre₁ sp₁ suf₁)
      (listCodec pV pA μL pre₂ sp₂ suf₂) := by
  refine ⟨fun v hv => ?_, fun a ha => ?_⟩
  · show ((pV.out v).bind _).map pA.into = ((pV.out v).bind _).map pA.into
    cases h : pV.out v with
    | none => rfl
    | some vs =>
      have hvv := pV.into_out h
      simp only [Option.bind_some, alignL]
      exact congrArg (Option.map pA.into) (traverse_row_congr (fun _ _ x hc hx => hc.e x hx) vs
        (fun x hx => by have := hdV vs x hx; rw [← hvv] at this; omega)
        (slotsL_rel hpre hsp hsuf vs.length))
  · show ((pA.out a).bind _).map pV.into = ((pA.out a).bind _).map pV.into
    cases h : pA.out a with
    | none => rfl
    | some as =>
      have haa := pA.into_out h
      simp only [Option.bind_some, alignL]
      exact congrArg (Option.map pV.into) (traverse_row_congr (fun _ _ x hc hx => hc.p x hx) as
        (fun x hx => by have := hdA as x hx; rw [← haa] at this; omega)
        (slotsL_rel hpre hsp hsuf as.length))

/-! ### Objects

An object reads its entry codecs at the entries of a map, one layer below the map. The presence
guards and the name filter read the shape of each field and never its codec, so two tables of one
shape guard and filter alike. -/

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

/-- Two tables of one shape guard the write side alike. -/
theorem valPresentB_rel (hF : ∀ k, FieldSem.Rel R (F₁ k) (F₂ k)) (names : Finset String) :
    valPresentB ⟨keys, F₁⟩ names = valPresentB ⟨keys, F₂⟩ names :=
  decide_eq_decide.mpr (forall_congr' fun k => by rw [(hF k).valPresentAt names k.1])

end ObjectAgree

/-- An object reads each entry one layer below the map, so it turns agreement below `d` into
    agreement below `d + 1`. The universe supplies the depth of its two keyed-map prisms. -/
theorem agreeLe_objectCodec {mV : Ctor (MapOf V) V} {mA : Ctor (MapOf V) V} {μM : M}
    (hdV : ∀ (m : MapOf V) k, dV (m.get k) + 1 ≤ dV (mV.into m))
    (hdA : ∀ (m : MapOf V) k, dA (m.get k) + 1 ≤ dA (mA.into m)) {d : Nat}
    {keys : Finset String} {F₁ F₂ : {k // k ∈ keys} → FieldSem V M}
    {r₁ r₂ : RestSem V M} (hF : ∀ k, FieldSem.Rel (AgreeLe dV dA d) (F₁ k) (F₂ k))
    (hr : RestSem.Rel (AgreeLe dV dA d) r₁ r₂) :
    AgreeLe dV dA (d + 1) (objectCodec mV mA μM ⟨keys, F₁⟩ r₁)
      (objectCodec mV mA μM ⟨keys, F₂⟩ r₂) := by
  have hent : ∀ k, Option.Rel (AgreeLe dV dA d) (entryCodec ⟨keys, F₁⟩ (rcOf r₁) k)
      (entryCodec ⟨keys, F₂⟩ (rcOf r₂) k) := fun k => entryCodec_rel hr.rcOf (mapOf_at_rel hF k)
  have hbind : ∀ {α β : Type} (run : Codec V M → α → Option β) (x : α),
      (∀ c₁ c₂, AgreeLe dV dA d c₁ c₂ → run c₁ x = run c₂ x) → ∀ k,
      (entryCodec ⟨keys, F₁⟩ (rcOf r₁) k).bind (run · x)
        = (entryCodec ⟨keys, F₂⟩ (rcOf r₂) k).bind (run · x) := fun run x hrun k =>
    optionRel_bind (fun _ _ h => hrun _ _ h) (hent k)
  unfold objectCodec
  refine ⟨fun v hv => ?_, fun a ha => ?_⟩
  · show ((mV.out v).bind _).map mA.into = ((mV.out v).bind _).map mA.into
    cases h : mV.out v with
    | none => rfl
    | some m =>
      have hvv := mV.into_out h
      refine congrArg (Option.map mA.into) ?_
      simp only [Option.bind_some, objWrite, objAt, valPresentB_rel hF]
      split
      · congr 2
        funext k
        exact hbind (·.e ·) (m.get k) (fun _ _ h => h.e _ (by
          have := hdV m k; rw [← hvv] at this; omega)) k.1
      · rfl
  · show ((mA.out a).bind _).map mV.into = ((mA.out a).bind _).map mV.into
    cases h : mA.out a with
    | none => rfl
    | some m =>
      have haa := mA.into_out h
      refine congrArg (Option.map mV.into) ?_
      simp only [Option.bind_some, objRead, objAt, valPresentB_rel hF]
      split
      · congr 2
        funext k
        exact hbind (·.p ·) (m.get k) (fun _ _ h => h.p _ (by
          have := hdA m k; rw [← haa] at this; omega)) k.1
      · rfl

end Calculus.Alg
