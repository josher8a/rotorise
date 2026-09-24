import Calculus.Sums
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Guarded recursion

A recursive codec is the limit of its stages. A **body** `B : Codec → Codec` builds one stage
from the one before, and the stages start at `Codec.empty`. The limit reads each input at the
stage its own depth names: `Value.depth` on the write side and `Attr.depth` on the read side.
The budget is a structural recursion on the input, so a closed term still reduces by `rfl`.

The one premise is `Contractive`: the body reads its argument only at inputs strictly shallower
than its own input. A container gives that, because an element is one layer below its container.
From it alone the stages agree past the depth of the input (`muStage_agree`), the limit is a
fixed point of the body (`muCodec_e_fix`, `muCodec_p_fix`), and lawful stages give a lawful limit
(`lawful_muCodec`). No option of the body has to be disjoint from another for these three.

`opaque` is `muCodec opaqStep`, and `Term.mu` denotes `muCodec` of its body.
-/

namespace Calculus

/-! ## Depth: the budget of a recursive codec -/

mutual

/-- The stage a recursive codec needs to see all of `v`: leaves need `1`, and each container
    layer needs one more. -/
def Value.depth : Value → Nat
  | .str _ | .num _ | .bool _ | .bin _ | .null => 1
  -- A value set holds scalars, so it is one layer deep whatever its size — the same
  -- reason `SS`/`NS`/`BS` are `2` on the attribute side.
  | .strSet _ | .numSet _ | .binSet _ => 2
  | .arr vs => Value.depthL vs + 1
  -- §1's `M` is a key *set* with a function on it, so a map's layer is the largest
  -- entry budget over the key set — a `Finset.sup`, where the array's is a list fold.
  | .map keys f => (keys.attach.sup fun k => Value.depth (f k)) + 1

def Value.depthL : List Value → Nat
  | [] => 1
  | v :: vs => max (Value.depth v) (Value.depthL vs)

end

mutual

/-- The read-side budget. Wire sets carry payloads, not attributes, so `SS`/`NS`/`BS`
    are one layer deep regardless of length. -/
def Attr.depth : Attr → Nat
  | .s _ | .n _ | .b _ | .bool _ | .null => 1
  | .ss _ | .ns _ | .bs _ => 2
  | .l as => Attr.depthL as + 1
  | .m keys f => (keys.attach.sup fun k => Attr.depth (f k)) + 1

def Attr.depthL : List Attr → Nat
  | [] => 1
  | a :: as => max (Attr.depth a) (Attr.depthL as)

end

/-- Every value has depth at least one, so a stage at depth zero reads nothing. -/
theorem Value.depth_pos (v : Value) : 0 < Value.depth v := by
  cases v <;> simp [Value.depth]

/-- Every attribute has depth at least one. -/
theorem Attr.depth_pos (a : Attr) : 0 < Attr.depth a := by
  cases a <;> simp [Attr.depth]

/-- An element of an array is no deeper than the array's list budget. -/
theorem Value.depth_le_depthL : ∀ {vs : List Value} {v : Value}, v ∈ vs →
    Value.depth v ≤ Value.depthL vs
  | _ :: _, _, .head _ => Nat.le_max_left _ _
  | _ :: _, _, .tail _ h => le_trans (Value.depth_le_depthL h) (Nat.le_max_right _ _)

/-- …and the read side of the same. -/
theorem Attr.depth_le_depthL : ∀ {as : List Attr} {a : Attr}, a ∈ as →
    Attr.depth a ≤ Attr.depthL as
  | _ :: _, _, .head _ => Nat.le_max_left _ _
  | _ :: _, _, .tail _ h => le_trans (Attr.depth_le_depthL h) (Nat.le_max_right _ _)

/-- Every entry of a map is one layer shallower than the map. -/
theorem Value.depth_map_entry {keys : Finset Name} {f : {k // k ∈ keys} → Value}
    (k : {k // k ∈ keys}) : Value.depth (f k) + 1 <= Value.depth (.map keys f) :=
  Nat.succ_le_succ
    (Finset.le_sup (f := fun k => Value.depth (f k)) (Finset.mem_attach _ k))

/-- …and the read side of the same. -/
theorem Attr.depth_map_entry {keys : Finset Name} {f : {k // k ∈ keys} → Attr}
    (k : {k // k ∈ keys}) : Attr.depth (f k) + 1 <= Attr.depth (.m keys f) :=
  Nat.succ_le_succ
    (Finset.le_sup (f := fun k => Attr.depth (f k)) (Finset.mem_attach _ k))

/-! ## Agreement below a depth -/

/-- Two codecs agree on every input of depth at most `d`, on both sides. `Lawful` relates the
    two sides, so a statement about one side alone cannot carry the laws to a limit. -/
structure AgreeLe (d : Nat) (c₁ c₂ : Codec) : Prop where
  e : ∀ v, Value.depth v ≤ d → c₁.e v = c₂.e v
  p : ∀ a, Attr.depth a ≤ d → c₁.p a = c₂.p a

namespace AgreeLe

variable {d : Nat} {c₁ c₂ c₃ : Codec}

/-- A codec agrees with itself at every depth. -/
theorem refl (d : Nat) (c : Codec) : AgreeLe d c c := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- Agreement below a depth is symmetric. -/
theorem symm (h : AgreeLe d c₁ c₂) : AgreeLe d c₂ c₁ :=
  ⟨fun v hv => (h.e v hv).symm, fun a ha => (h.p a ha).symm⟩

/-- Agreement below a depth is transitive. -/
theorem trans (h : AgreeLe d c₁ c₂) (h' : AgreeLe d c₂ c₃) : AgreeLe d c₁ c₃ :=
  ⟨fun v hv => (h.e v hv).trans (h'.e v hv), fun a ha => (h.p a ha).trans (h'.p a ha)⟩

/-- Agreement below a depth holds below every smaller depth. -/
theorem mono {d' : Nat} (h : AgreeLe d c₁ c₂) (hd : d' ≤ d) : AgreeLe d' c₁ c₂ :=
  ⟨fun v hv => h.e v (le_trans hv hd), fun a ha => h.p a (le_trans ha hd)⟩

/-- Every input has depth at least one, so any two codecs agree below depth zero. -/
theorem zero (c₁ c₂ : Codec) : AgreeLe 0 c₁ c₂ :=
  ⟨fun v hv => absurd hv (Nat.not_le.mpr (Value.depth_pos v)),
   fun a ha => absurd ha (Nat.not_le.mpr (Attr.depth_pos a))⟩

/-- Two codecs with one pair of halves agree at every depth. -/
theorem of_eq (he : c₁.e = c₂.e) (hp : c₁.p = c₂.p) : AgreeLe d c₁ c₂ :=
  ⟨fun v _ => congrFun he v, fun a _ => congrFun hp a⟩

/-- …and agreement at every depth is one pair of halves, because every input has a depth. -/
theorem eq_of_forall (h : ∀ d, AgreeLe d c₁ c₂) : c₁.e = c₂.e ∧ c₁.p = c₂.p :=
  ⟨funext fun v => (h _).e v le_rfl, funext fun a => (h _).p a le_rfl⟩

end AgreeLe

/-! ## The construct -/

/-- **The guard, on a body.** The body reads its argument only at inputs strictly shallower than
    its own input, on both sides. -/
def Contractive (B : Codec → Codec) : Prop :=
  ∀ d c₁ c₂, AgreeLe d c₁ c₂ → AgreeLe (d + 1) (B c₁) (B c₂)

/-- The stage `n` of the body `B`: `n` applications of `B` to `Codec.empty`. A structural
    recursion on `n`, so a stage at a numeral reduces by `rfl`. -/
def muStage (B : Codec → Codec) : Nat → Codec
  | 0 => .empty
  | n + 1 => B (muStage B n)

/-- **The recursive codec**: each input read at the stage its own depth names. The member is
    `⊤`, as `(lazy)` concludes it, because the stages need not agree on one. The held set is the
    write domain, so the held set of a recursive term is its admission with no induction over
    the stages. -/
def muCodec (B : Codec → Codec) : Codec :=
  { T := fun v => ((muStage B (Value.depth v)).e v).isSome = true
    μ := none
    e := fun v => (muStage B (Value.depth v)).e v
    p := fun a => (muStage B (Attr.depth a)).p a }

/-- The limit writes a value at the stage the value's depth names. -/
theorem muCodec_e (B : Codec → Codec) (v : Value) :
    (muCodec B).e v = (muStage B (Value.depth v)).e v := rfl

/-- The limit reads an attribute at the stage the attribute's depth names. -/
theorem muCodec_p (B : Codec → Codec) (a : Attr) :
    (muCodec B).p a = (muStage B (Attr.depth a)).p a := rfl

/-- A property that `Codec.empty` has and that each application of the body keeps holds at
    every stage. -/
theorem muStage_induct {B : Codec → Codec} {P : Codec → Prop} (h0 : P .empty)
    (hs : ∀ c, P c → P (B c)) : ∀ n, P (muStage B n)
  | 0 => h0
  | n + 1 => hs _ (muStage_induct h0 hs n)

/-- Each stage agrees with the next one below its own index. -/
theorem muStage_stable {B : Codec → Codec} (hB : Contractive B) :
    ∀ n, AgreeLe n (muStage B n) (muStage B (n + 1))
  | 0 => AgreeLe.zero _ _
  | n + 1 => hB n _ _ (muStage_stable hB n)

/-- **Stability.** Past the depth of the input, a later stage changes nothing. -/
theorem muStage_agree {B : Codec → Codec} (hB : Contractive B) {d : Nat} :
    ∀ k, AgreeLe d (muStage B d) (muStage B (d + k))
  | 0 => AgreeLe.refl _ _
  | k + 1 => (muStage_agree hB k).trans ((muStage_stable hB (d + k)).mono (by omega))

/-- Any two stages at or past `d` agree below `d`. -/
theorem muStage_agree_le {B : Codec → Codec} (hB : Contractive B) {d n : Nat} (h : d ≤ n) :
    AgreeLe d (muStage B d) (muStage B n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact muStage_agree hB k

/-- The limit agrees with the stage `n` below `n`. -/
theorem muCodec_agree {B : Codec → Codec} (hB : Contractive B) (n : Nat) :
    AgreeLe n (muCodec B) (muStage B n) :=
  ⟨fun v hv => (muStage_agree_le hB hv).e v le_rfl,
   fun a ha => (muStage_agree_le hB ha).p a le_rfl⟩

/-- **The fixed point, write side.** The limit writes what its body writes over the limit. -/
theorem muCodec_e_fix {B : Codec → Codec} (hB : Contractive B) (v : Value) :
    (muCodec B).e v = (B (muCodec B)).e v := by
  obtain ⟨k, hk⟩ : ∃ k, Value.depth v = k + 1 :=
    ⟨Value.depth v - 1, by have := Value.depth_pos v; omega⟩
  rw [muCodec_e, hk]
  exact (hB k _ _ (muCodec_agree hB k).symm).e v (by omega)

/-- **The fixed point, read side.** -/
theorem muCodec_p_fix {B : Codec → Codec} (hB : Contractive B) (a : Attr) :
    (muCodec B).p a = (B (muCodec B)).p a := by
  obtain ⟨k, hk⟩ : ∃ k, Attr.depth a = k + 1 :=
    ⟨Attr.depth a - 1, by have := Attr.depth_pos a; omega⟩
  rw [muCodec_p, hk]
  exact (hB k _ _ (muCodec_agree hB k).symm).p a (by omega)

/-- **Lawful stages give a lawful limit.** The write side reads at the depth of the value and
    the read side at the depth of the attribute. Stability moves both answers to the stage
    at the larger of the two depths, and that stage is lawful. -/
theorem lawful_muCodec {B : Codec → Codec} (hB : Contractive B)
    (hs : ∀ n, Lawful (muStage B n)) : Lawful (muCodec B) := by
  refine ⟨fun {v a} he => ?_, fun {a v} hp => ?_, fun hμ => nomatch hμ⟩
  · have hN := muStage_agree_le hB (Nat.le_max_left (Value.depth v) (Attr.depth a))
    rw [muCodec_e, hN.e v le_rfl] at he
    rw [muCodec_p, (muStage_agree_le hB (Nat.le_max_right (Value.depth v) (Attr.depth a))).p a
      le_rfl]
    exact (hs _).retract he
  · have hN := muStage_agree_le hB (Nat.le_max_left (Attr.depth a) (Value.depth v))
    rw [muCodec_p, hN.p a le_rfl] at hp
    rw [muCodec_e, (muStage_agree_le hB (Nat.le_max_right (Attr.depth a) (Value.depth v))).e v
      le_rfl]
    exact (hs _).canon hp

/-- A lawful limit is on its held set. The held set is the write domain, and a lawful codec writes
    every value it reads. -/
theorem carrier_muCodec {B : Codec → Codec} (h : Lawful (muCodec B)) : Carrier (muCodec B) :=
  ⟨fun he => Option.isSome_iff_exists.mpr ⟨_, he⟩,
   fun hp => Option.isSome_iff_exists.mpr ⟨_, h.canon hp⟩⟩

/-- Two bodies that preserve agreement below `d` give limits that agree below `d`. -/
theorem agreeLe_muCodec {d : Nat} {B₁ B₂ : Codec → Codec}
    (h : ∀ c₁ c₂, AgreeLe d c₁ c₂ → AgreeLe d (B₁ c₁) (B₂ c₂)) :
    AgreeLe d (muCodec B₁) (muCodec B₂) := by
  have hs : ∀ n, AgreeLe d (muStage B₁ n) (muStage B₂ n) := fun n => by
    induction n with
    | zero => exact AgreeLe.refl _ _
    | succ n ih => exact h _ _ ih
  exact ⟨fun v hv => (hs _).e v hv, fun a ha => (hs _).p a ha⟩

/-! ## The combinators keep agreement

A container reads its element codecs one layer down, so it turns agreement below `d` into
agreement below `d + 1`. A sum, a restriction and a relabelling read the same input, so they
keep the depth. -/

/-- First-match resolution reads each option at the input only. -/
theorem select_congr {A R : Type} {run : Codec → A → Option R} {x : A} :
    ∀ {os₁ os₂ : List Codec}, List.Forall₂ (fun o₁ o₂ => run o₁ x = run o₂ x) os₁ os₂ →
      select os₁ run x = select os₂ run x
  | [], [], .nil => rfl
  | o₁ :: os₁, o₂ :: os₂, .cons h hs => by
      have ih := select_congr hs
      simp only [select, List.find?_cons] at ih ⊢
      rw [h]
      cases run o₂ x <;> simp [ih, h]

/-- A sum reads its options at its own input, so it keeps the depth of their agreement. -/
theorem agreeLe_altCodec {d : Nat} {os₁ os₂ : List Codec} (μ₁ μ₂ : Option Member)
    (h : List.Forall₂ (AgreeLe d) os₁ os₂) : AgreeLe d (altCodec os₁ μ₁) (altCodec os₂ μ₂) :=
  ⟨fun v hv => select_congr (h.imp fun _ _ hc => hc.e v hv),
   fun a ha => select_congr (h.imp fun _ _ hc => hc.p a ha)⟩

/-- A restriction reads its codec at its own input, so it keeps the depth. -/
theorem agreeLe_restrict {d : Nat} {c₁ c₂ : Codec} (h : AgreeLe d c₁ c₂) (q : Value → Bool) :
    AgreeLe d (c₁.restrict q) (c₂.restrict q) :=
  ⟨fun v hv => congrArg (fun x => if q v = true then x else none) (h.e v hv),
   fun a ha => congrArg (fun x => Option.bind x fun v => if q v = true then some v else none)
     (h.p a ha)⟩

/-- `Option.map` keeps a relation that the two functions keep. -/
theorem optionRel_map {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {f : α → γ} {g : β → δ} (hfg : ∀ x y, R x y → S (f x) (g y)) :
    ∀ {a : Option α} {b : Option β}, Option.Rel R a b → Option.Rel S (a.map f) (b.map g)
  | _, _, .none => .none
  | _, _, .some h => .some (hfg _ _ h)

/-- `Option.bind` sends related inputs to one answer when the two functions agree on them. -/
theorem optionRel_bind {α β γ : Type} {R : α → β → Prop} {f : α → Option γ} {g : β → Option γ}
    (hfg : ∀ x y, R x y → f x = g y) :
    ∀ {a : Option α} {b : Option β}, Option.Rel R a b → a.bind f = b.bind g
  | _, _, .none => rfl
  | _, _, .some h => hfg _ _ h

/-- Related options are defined together. -/
theorem optionRel_isSome {α β : Type} {R : α → β → Prop} :
    ∀ {a : Option α} {b : Option β}, Option.Rel R a b → a.isSome = b.isSome
  | _, _, .none => rfl
  | _, _, .some _ => rfl

/-- A slot row of one shape pairs related codecs position by position. -/
theorem slots_rel {R : Codec → Codec → Prop} :
    ∀ (n : Nat) {cs₁ cs₂ : List Codec} {t₁ t₂ : Option Codec},
      List.Forall₂ R cs₁ cs₂ → Option.Rel R t₁ t₂ →
      Option.Rel (List.Forall₂ R) (slots cs₁ t₁ n) (slots cs₂ t₂ n)
  | 0, _, _, _, _, .nil, _ => .some .nil
  | 0, _, _, _, _, .cons _ _, _ => .none
  | _ + 1, _, _, _, _, .nil, .none => .none
  | n + 1, _, _, _, _, .nil, .some hc =>
      optionRel_map (fun _ _ h => .cons hc h) (slots_rel n .nil (.some hc))
  | n + 1, _, _, _, _, .cons hc hcs, ht =>
      optionRel_map (fun _ _ h => .cons hc h) (slots_rel n hcs ht)

/-- A `list` shape assigns related rows to related parts, position by position. -/
theorem slotsL_rel {R : Codec → Codec → Prop} {pre₁ pre₂ suf₁ suf₂ : List Codec}
    {sp₁ sp₂ : Option Codec} (hpre : List.Forall₂ R pre₁ pre₂) (hsp : Option.Rel R sp₁ sp₂)
    (hsuf : List.Forall₂ R suf₁ suf₂) (n : Nat) :
    Option.Rel (List.Forall₂ R) (slotsL pre₁ sp₁ suf₁ n) (slotsL pre₂ sp₂ suf₂ n) := by
  unfold slotsL
  rw [hsuf.length_eq]
  split
  · exact .none
  · exact optionRel_map (fun _ _ h => List.rel_append h hsuf) (slots_rel _ hpre hsp)

/-- A row of codecs that agree below `d`, zipped with inputs no deeper than `d`, traverses to
    one answer. -/
theorem traverse_zip_congr {α β : Type} {d : Nat} {run : Codec → α → Option β}
    {depth : α → Nat} (hrun : ∀ c₁ c₂ x, AgreeLe d c₁ c₂ → depth x ≤ d → run c₁ x = run c₂ x) :
    ∀ {ds₁ ds₂ : List Codec} (xs : List α), List.Forall₂ (AgreeLe d) ds₁ ds₂ →
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
theorem traverse_row_congr {α β : Type} {d : Nat} {run : Codec → α → Option β}
    {depth : α → Nat} (hrun : ∀ c₁ c₂ x, AgreeLe d c₁ c₂ → depth x ≤ d → run c₁ x = run c₂ x)
    (xs : List α) (hx : ∀ x ∈ xs, depth x ≤ d) :
    ∀ {r₁ r₂ : Option (List Codec)}, Option.Rel (List.Forall₂ (AgreeLe d)) r₁ r₂ →
      (r₁.map (·.zip xs)).bind (traverse fun cx => run cx.1 cx.2)
        = (r₂.map (·.zip xs)).bind (traverse fun cx => run cx.1 cx.2)
  | _, _, .none => rfl
  | _, _, .some h => traverse_zip_congr hrun xs h hx

/-- A `list` reads each element one layer down, so it turns agreement below `d` into agreement
    below `d + 1`. -/
theorem agreeLe_listCodec {d : Nat} {pre₁ pre₂ suf₁ suf₂ : List Codec}
    {sp₁ sp₂ : Option Codec} (hpre : List.Forall₂ (AgreeLe d) pre₁ pre₂)
    (hsp : Option.Rel (AgreeLe d) sp₁ sp₂) (hsuf : List.Forall₂ (AgreeLe d) suf₁ suf₂) :
    AgreeLe (d + 1) (listCodec pre₁ sp₁ suf₁) (listCodec pre₂ sp₂ suf₂) := by
  refine ⟨fun v hv => ?_, fun a ha => ?_⟩
  · cases v with
    | arr vs =>
      exact congrArg (Option.map Attr.l) (traverse_row_congr (fun _ _ x hc hx => hc.e x hx) vs
        (fun x hx => by
          have := Value.depth_le_depthL hx; simp only [Value.depth] at hv; omega)
        (slotsL_rel hpre hsp hsuf vs.length))
    | _ => rfl
  · cases a with
    | l as =>
      exact congrArg (Option.map Value.arr) (traverse_row_congr (fun _ _ x hc hx => hc.p x hx) as
        (fun x hx => by
          have := Attr.depth_le_depthL hx; simp only [Attr.depth] at ha; omega)
        (slotsL_rel hpre hsp hsuf as.length))
    | _ => rfl

/-- An array is the spread-only `list`, and so reads its elements one layer down. -/
theorem agreeLe_arrayCodec {d : Nat} {c₁ c₂ : Codec} (h : AgreeLe d c₁ c₂) :
    AgreeLe (d + 1) (arrayCodec c₁) (arrayCodec c₂) := by
  rw [arrayCodec_eq_listCodec, arrayCodec_eq_listCodec]
  exact agreeLe_listCodec .nil (.some h) .nil

/-- A record reads each entry one layer below the map. -/
theorem agreeLe_recordCodec {d : Nat} {c₁ c₂ : Codec} (h : AgreeLe d c₁ c₂) :
    AgreeLe (d + 1) (recordCodec c₁) (recordCodec c₂) := by
  refine ⟨fun v hv => ?_, fun a ha => ?_⟩
  · cases v with
    | map keys f =>
      have hk : ∀ k, c₁.e (f k) = c₂.e (f k) := fun k =>
        h.e _ (by have := Value.depth_map_entry (f := f) k; omega)
      simp only [recordCodec, hk]
    | _ => rfl
  · cases a with
    | m keys g =>
      have hk : ∀ k, c₁.p (g k) = c₂.p (g k) := fun k =>
        h.p _ (by have := Attr.depth_map_entry (f := g) k; omega)
      simp only [recordCodec, hk]
    | _ => rfl

/-- A set reads its element codec at scalars, which are one layer below the set. -/
theorem agreeLe_setCodec {d : Nat} {c₁ c₂ : Codec} (h : AgreeLe d c₁ c₂) :
    AgreeLe (d + 1) (setCodec c₁) (setCodec c₂) := by
  refine ⟨fun v hv => ?_, fun a ha => ?_⟩
  · cases v with
    | strSet S => exact encSet_congr fun x _ => h.e _ (by simp only [Value.depth] at hv ⊢; omega)
    | numSet S => exact encSet_congr fun x _ => h.e _ (by simp only [Value.depth] at hv ⊢; omega)
    | binSet S => exact encSet_congr fun x _ => h.e _ (by simp only [Value.depth] at hv ⊢; omega)
    | _ => rfl
  · cases a with
    | ss S => exact decSet_congr fun x _ => h.p _ (by simp only [Attr.depth] at ha ⊢; omega)
    | ns S => exact decSet_congr fun x _ => h.p _ (by simp only [Attr.depth] at ha ⊢; omega)
    | bs S => exact decSet_congr fun x _ => h.p _ (by simp only [Attr.depth] at ha ⊢; omega)
    | _ => rfl

/-! ### Objects

An object reads its entry codecs at the entries of a map, one layer below the map. The presence
guards and the name filter read the shape of each field and never its codec, so two tables of one
shape guard and filter alike. -/

/-- Two fields of one shape whose codecs stand in `R`. -/
def FieldSem.Rel (R : Codec → Codec → Prop) : FieldSem → FieldSem → Prop
  | .req c₁, .req c₂ => R c₁ c₂
  | .opt c₁, .opt c₂ => R c₁ c₂
  | _, _ => False

/-- Two rest policies of one shape whose codecs stand in `R`. -/
def RestSem.Rel (R : Codec → Codec → Prop) : RestSem → RestSem → Prop
  | .drop, .drop => True
  | .refuse, .refuse => True
  | .codec c₁, .codec c₂ => R c₁ c₂
  | _, _ => False

section ObjectAgree
variable {R : Codec → Codec → Prop} {keys : Finset Name} {F₁ F₂ : {k // k ∈ keys} → FieldSem}

/-- Related fields have related codecs. -/
theorem FieldSem.Rel.codec : ∀ {f₁ f₂ : FieldSem}, FieldSem.Rel R f₁ f₂ → R f₁.codec f₂.codec
  | .req _, .req _, h => h
  | .opt _, .opt _, h => h

/-- The write-side presence guard reads the shape of a field, never its codec. -/
theorem FieldSem.Rel.valPresentAt (names : Finset Name) (k : Name) :
    ∀ {f₁ f₂ : FieldSem}, FieldSem.Rel R f₁ f₂ → valPresentAt names k f₁ = valPresentAt names k f₂
  | .req _, .req _, _ => rfl
  | .opt _, .opt _, _ => rfl

/-- The read-side presence guard reads the shape of a field, never its codec. -/
theorem FieldSem.Rel.reqPresentAt (names : Finset Name) (k : Name) :
    ∀ {f₁ f₂ : FieldSem}, FieldSem.Rel R f₁ f₂ → reqPresentAt names k f₁ = reqPresentAt names k f₂
  | .req _, .req _, _ => rfl
  | .opt _, .opt _, _ => rfl

/-- Related rest policies give related rest codecs. -/
theorem RestSem.Rel.rcOf : ∀ {r₁ r₂ : RestSem}, RestSem.Rel R r₁ r₂ →
    Option.Rel R (Calculus.rcOf r₁) (Calculus.rcOf r₂)
  | .drop, .drop, _ => .none
  | .refuse, .refuse, _ => .none
  | .codec _, .codec _, h => .some h

/-- A lookup in two tables of one key set is related where the fields are. -/
theorem mapOf_at_rel (hF : ∀ k, FieldSem.Rel R (F₁ k) (F₂ k)) (k : Name) :
    Option.Rel (FieldSem.Rel R) ((⟨keys, F₁⟩ : MapOf FieldSem).at k)
      ((⟨keys, F₂⟩ : MapOf FieldSem).at k) := by
  unfold MapOf.at
  split
  · exact .some (hF _)
  · exact .none

/-- The codec an entry goes through is related where the table and the rest codec are. -/
theorem entryCodec_rel {rc₁ rc₂ : Option Codec} (hr : Option.Rel R rc₁ rc₂) :
    ∀ {o₁ o₂ : Option FieldSem}, Option.Rel (FieldSem.Rel R) o₁ o₂ →
      Option.Rel R (match o₁ with | some fs => some fs.codec | none => rc₁)
        (match o₂ with | some fs => some fs.codec | none => rc₂)
  | _, _, .none => hr
  | _, _, .some h => .some h.codec

/-- Two tables of one shape guard the write side alike. -/
theorem valPresentB_rel (hF : ∀ k, FieldSem.Rel R (F₁ k) (F₂ k)) (names : Finset Name) :
    valPresentB ⟨keys, F₁⟩ names = valPresentB ⟨keys, F₂⟩ names :=
  decide_eq_decide.mpr (forall_congr' fun k => by rw [(hF k).valPresentAt names k.1])

/-- Two tables of one shape guard the read side alike. -/
theorem reqPresentB_rel (hF : ∀ k, FieldSem.Rel R (F₁ k) (F₂ k)) (names : Finset Name) :
    reqPresentB ⟨keys, F₁⟩ names = reqPresentB ⟨keys, F₂⟩ names :=
  decide_eq_decide.mpr (forall_congr' fun k => by rw [(hF k).reqPresentAt names k.1])

/-- Two tables of one shape filter the names alike. -/
theorem keepB_rel (hF : ∀ k, FieldSem.Rel R (F₁ k) (F₂ k)) :
    ∀ {r₁ r₂ : RestSem}, RestSem.Rel R r₁ r₂ → keepB r₁ ⟨keys, F₁⟩ = keepB r₂ ⟨keys, F₂⟩
  | .drop, .drop, _ => funext fun k => optionRel_isSome (mapOf_at_rel hF k)
  | .refuse, .refuse, _ => rfl
  | .codec _, .codec _, _ => rfl

end ObjectAgree

/-- An object reads each entry one layer below the map, so it turns agreement below `d` into
    agreement below `d + 1`. -/
theorem agreeLe_objectCodec {d : Nat} {keys : Finset Name} {F₁ F₂ : {k // k ∈ keys} → FieldSem}
    {r₁ r₂ : RestSem} (hF : ∀ k, FieldSem.Rel (AgreeLe d) (F₁ k) (F₂ k))
    (hr : RestSem.Rel (AgreeLe d) r₁ r₂) :
    AgreeLe (d + 1) (objectCodec ⟨keys, F₁⟩ r₁) (objectCodec ⟨keys, F₂⟩ r₂) := by
  have hent : ∀ k, Option.Rel (AgreeLe d) (entryCodec ⟨keys, F₁⟩ (rcOf r₁) k)
      (entryCodec ⟨keys, F₂⟩ (rcOf r₂) k) := fun k => entryCodec_rel hr.rcOf (mapOf_at_rel hF k)
  have hbind : ∀ {α β : Type} (run : Codec → α → Option β) (x : α),
      (∀ c₁ c₂, AgreeLe d c₁ c₂ → run c₁ x = run c₂ x) → ∀ k,
      (entryCodec ⟨keys, F₁⟩ (rcOf r₁) k).bind (run · x)
        = (entryCodec ⟨keys, F₂⟩ (rcOf r₂) k).bind (run · x) := fun run x hrun k =>
    optionRel_bind (fun _ _ h => hrun _ _ h) (hent k)
  unfold objectCodec
  rw [keepB_rel hF hr]
  refine ⟨fun v hv => ?_, fun a ha => ?_⟩
  · cases v with
    | map ks f =>
      refine congrArg (Option.map mA.into) ?_
      simp only [mapV, Option.bind_some, objWrite, valPresentB_rel hF]
      split
      · congr 2
        funext k
        exact hbind (·.e ·) (f k) (fun _ _ h => h.e _ (by
          have := Value.depth_map_entry (f := f) k; omega)) k.1
      · rfl
    | _ => rfl
  · cases a with
    | m ks g =>
      refine congrArg (Option.map mapV.into) ?_
      simp only [mA, Option.bind_some, objRead, reqPresentB_rel hF]
      split
      · congr 2
        funext k
        exact hbind (·.p ·) _ (fun _ _ h => h.p _ (by
          have := Attr.depth_map_entry (f := g) ⟨k.1, (Finset.mem_filter.mp k.2).1⟩; omega)) k.1
      · rfl
    | _ => rfl

end Calculus
