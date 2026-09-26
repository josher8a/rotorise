import Calculus.Lang.MeetRows
import Calculus.Lang.Typing

/-!
# The typed fragment is closed under the meet, over a universe signature

`Alg.typed_meet` states that where two derivable terms have a meet, the meet is derivable. The
proof recurses on the left operand, as the meet does. No row reads a law of the universe: a leaf
meet answers a primitive, which `Typed.prim` derives, or the bottom, or a factor. A container row
takes its former from the judgement of a factor.

The meet builds unions, and a union of derivable options is derivable (`typed_ofOptions`), so the
rows that distribute a union owe only the survivors' derivability (`survivors`). The object rows
write the merged field table down from one judgement per name: the key set is finite, so the
witnesses make a function (`exists_fun_of_finset`) without a choice.
-/

namespace Calculus.Alg

variable {S : Syn} [Sem S]

/-! ## Witnesses over a finite key set -/

/-- A list of existence claims has one witness function. -/
theorem exists_fun_of_list {α : Type} [Inhabited α] {Q : String → α → Prop} :
    ∀ l : List String, (∀ k ∈ l, ∃ x, Q k x) → ∃ f : String → α, ∀ k ∈ l, Q k (f k)
  | [], _ => ⟨fun _ => default, fun _ hk => nomatch hk⟩
  | a :: l, h => by
      obtain ⟨x, hx⟩ := h a List.mem_cons_self
      obtain ⟨f, hf⟩ := exists_fun_of_list l (fun k hk => h k (List.mem_cons_of_mem _ hk))
      refine ⟨fun k => if k = a then x else f k, fun k hk => ?_⟩
      cases hka : decide (k = a) with
      | true =>
          have e : k = a := of_decide_eq_true hka
          subst e; simp only [if_pos]; exact hx
      | false =>
          have e : ¬ k = a := of_decide_eq_false hka
          simp only [if_neg e]
          exact hf k ((List.mem_cons.mp hk).resolve_left e)

/-- **A finite key set's existence claims have one witness function**, with no choice: the key
    set is a list under its quotient, and a list is finite. -/
theorem exists_fun_of_finset {α : Type} [Inhabited α] (s : Finset String)
    {P : ∀ k, k ∈ s → α → Prop} (h : ∀ k (hk : k ∈ s), ∃ x, P k hk x) :
    ∃ f : String → α, ∀ k (hk : k ∈ s), P k hk (f k) := by
  obtain ⟨l, hl⟩ : ∃ l : List String, ∀ k, k ∈ s ↔ k ∈ l := by
    obtain ⟨m, nd⟩ := s
    induction m using Quot.inductionOn with
    | h l => exact ⟨l, fun k => Iff.rfl⟩
  obtain ⟨f, hf⟩ := exists_fun_of_list (Q := fun k x => ∀ hk : k ∈ s, P k hk x) l
    (fun k hk => by
      obtain ⟨x, hx⟩ := h k ((hl k).mpr hk)
      exact ⟨x, fun _ => hx⟩)
  exact ⟨f, fun k hk => hf k ((hl k).mp hk) hk⟩

/-! ## The typed fragment is closed under the meet -/

/-- Option judgements for a list, where each option has one. -/
theorem typedListμ_of_all : ∀ {ss : List (Term S)}, (∀ t ∈ ss, ∃ T μ, Typed t T μ) →
    ∃ Ts μs, TypedListμ ss Ts μs
  | [], _ => ⟨[], [], .nil⟩
  | t :: ts, h => by
    obtain ⟨T, μ, hty⟩ := h t List.mem_cons_self
    obtain ⟨Ts, μs, hs⟩ := typedListμ_of_all (fun u hu => h u (List.mem_cons_of_mem _ hu))
    exact ⟨T :: Ts, μ :: μs, .cons hty hs⟩

/-- **A list of derivable survivors gives a derivable union.** -/
theorem typed_ofOptions {ss : List (Term S)}
    (h : ∀ t ∈ ss, ∃ T μ, Typed t T μ) : ∃ T μ, Typed (Term.ofOptions ss) T μ := by
  rcases ss with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · exact ⟨_, _, Typed.never⟩
  · exact h a List.mem_cons_self
  · obtain ⟨Ts, μs, hL⟩ := typedListμ_of_all h
    exact ⟨_, _, Typed.union hL⟩

/-- Each option of a derivable union is derivable. -/
theorem typedListμ_mem : ∀ {os : List (Term S)} {Ts μs}, TypedListμ os Ts μs →
    ∀ t ∈ os, ∃ T μ, Typed t T μ
  | _, _, _, .nil, _, ht => nomatch ht
  | _, _, _, .cons hty hs, t, ht => by
    rcases List.mem_cons.mp ht with rfl | ht'
    · exact ⟨_, _, hty⟩
    · exact typedListμ_mem hs t ht'

/-- …and the term under a refinement. -/
theorem typed_refine_inv {a : Term S} {p : S.Pred} :
    (∃ T μ, Typed (.refine a p) T μ) → ∃ T μ, Typed a T μ
  | ⟨_, _, h⟩ => by cases h with | refine h' => exact ⟨_, _, h'⟩

/-- …and the body under a recursive term. -/
theorem typed_mu_inv {b : Term S} : (∃ T μ, Typed (.mu b) T μ) → ∃ T μ, Typed b T μ
  | ⟨_, _, h⟩ => by cases h with | mu _ h' => exact ⟨_, _, h'⟩

/-- Normalising a refinement keeps it derivable: the bottom is derivable too. -/
theorem typed_refineOf [Leaf S] {t : Term S} {p : S.Pred} (h : ∃ T μ, Typed t T μ) :
    ∃ T μ, Typed (Term.refineOf t p) T μ := by
  obtain ⟨T, μ, hT⟩ := h
  cases t <;>
    first
      | exact ⟨_, _, Typed.refine hT⟩
      | exact ⟨_, _, Typed.never⟩
      | (simp only [Term.refineOf]
         split
         · obtain ⟨T', μ', hT'⟩ := typed_refine_inv ⟨_, _, hT⟩
           exact ⟨_, _, Typed.refine hT'⟩
         · exact ⟨_, _, Typed.never⟩
         · exact ⟨_, _, Typed.refine hT⟩)

/-- Judgements for a list, from one per element. -/
theorem typedList_of_all : ∀ {ts : List (Term S)}, (∀ t ∈ ts, ∃ T μ, Typed t T μ) →
    ∃ Ts, TypedList ts Ts
  | [], _ => ⟨[], .nil⟩
  | t :: ts, h => by
    obtain ⟨T, μ, hty⟩ := h t List.mem_cons_self
    obtain ⟨Ts, hs⟩ := typedList_of_all (fun u hu => h u (List.mem_cons_of_mem _ hu))
    exact ⟨T :: Ts, .cons hty hs⟩

/-- …and for a tail. -/
theorem typedOpt_of_all : ∀ {tail : Option (Term S)}, (∀ t ∈ tail, ∃ T μ, Typed t T μ) →
    ∃ Tt, TypedOpt tail Tt
  | none, _ => ⟨none, .none⟩
  | some t, h => by
    obtain ⟨T, μ, hty⟩ := h t rfl
    exact ⟨some T, .some hty⟩

/-- Normalising a tuple keeps it derivable: a declared position at the bottom gives the
    bottom, which is derivable. -/
theorem typed_listOf {L} (hL : Sem.list (S := S) = some L) {pre : List (Term S)}
    {sp : Option (Term S)} {suf : List (Term S)}
    (hp : ∀ t ∈ pre, ∃ T μ, Typed t T μ) (hs : ∀ t ∈ sp, ∃ T μ, Typed t T μ)
    (hf : ∀ t ∈ suf, ∃ T μ, Typed t T μ) :
    ∃ T μ, Typed (Term.listOf pre sp suf) T μ := by
  unfold Term.listOf
  split
  · exact ⟨_, _, Typed.never⟩
  · obtain ⟨Tp, hTp⟩ := typedList_of_all hp
    obtain ⟨Ts, hTs⟩ := typedOpt_of_all hs
    obtain ⟨Tf, hTf⟩ := typedList_of_all hf
    exact ⟨_, _, Typed.list hL hTp hTs hTf⟩

/-- Inversions for a tuple: each declared position, and the tail. -/
theorem typedList_mem : ∀ {ts : List (Term S)} {Ts}, TypedList ts Ts → ∀ t ∈ ts, ∃ T μ, Typed t T μ
  | _, _, .nil, _, ht => nomatch ht
  | _, _, .cons hty hs, t, ht => by
    rcases List.mem_cons.mp ht with rfl | ht'
    · exact ⟨_, _, hty⟩
    · exact typedList_mem hs t ht'

/-- Inversions: a derivable container gives derivable components. -/
theorem typed_list_inv {pre : List (Term S)} {sp : Option (Term S)} {suf : List (Term S)} :
    (∃ T μ, Typed (.list pre sp suf) T μ) →
    (∀ t ∈ pre, ∃ T μ, Typed t T μ) ∧ (∀ t ∈ sp, ∃ T μ, Typed t T μ) ∧
      (∀ t ∈ suf, ∃ T μ, Typed t T μ)
  | ⟨_, _, h⟩ => by
    cases h with
    | list _ hp hs hf =>
        refine ⟨typedList_mem hp, ?_, typedList_mem hf⟩
        cases hs with
        | none => exact fun t ht => nomatch ht
        | some hty => exact fun t ht => by cases ht; exact ⟨_, _, hty⟩

/-- The term a slot carries. -/
def ObjectSlot.termOf : ObjectSlot S → Term S
  | .req t | .optional t => t

/-- A typed field carries a derivable term, whichever mark it has. -/
theorem typedField_termOf {fd : ObjectSlot S} {T π μ} (h : TypedField fd T π μ) :
    ∃ T' μ', Typed (ObjectSlot.termOf fd) T' μ' := by
  cases h with
  | req h' => exact ⟨_, _, h'⟩
  | optional h' => exact ⟨_, _, h'⟩

/-- Inversion for an object: every declared slot's term is derivable, and the open block is
    typed. -/
theorem typed_object_inv {b : Body S} (h : ∃ T μ, Typed (.object b) T μ) :
    (∀ k, ∃ T μ, Typed (ObjectSlot.termOf (b.at k)) T μ) ∧ ∃ R, TypedWild b.wild R := by
  obtain ⟨T, μ, hT⟩ := h
  cases hT with
  | object _ hf hr => exact ⟨fun k => typedField_termOf (hf k), _, hr⟩

/-- A derivable `list` names a list former. -/
theorem list_former_of_typed {pre : List (Term S)} {sp : Option (Term S)} {suf : List (Term S)} :
    (∃ T μ, Typed (.list pre sp suf) T μ) → ∃ L, Sem.list (S := S) = some L
  | ⟨_, _, h⟩ => by cases h with | list hL _ _ _ => exact ⟨_, hL⟩

/-- A derivable object names a map former. -/
theorem map_former_of_typed {b : Body S} :
    (∃ T μ, Typed (.object b) T μ) → ∃ F, Sem.map (S := S) = some F
  | ⟨_, _, h⟩ => by cases h with | object hF _ _ => exact ⟨_, hF⟩

/-- A slot whose term is derivable is a typed slot at its own mark. -/
theorem typedField_of {fd : ObjectSlot S} {T μ} (h : Typed (ObjectSlot.termOf fd) T μ) :
    TypedField fd T (ObjectSlot.isReq fd) μ := by
  cases fd with
  | req t => exact TypedField.req h
  | optional t => exact TypedField.optional h

/-- **The meet keeps derivability.** Each survivor of a derivable union's meet is derivable. -/
theorem survivors {os zs ss : List (Term S)} (hy : ∃ T μ, Typed (.union os) T μ)
    (hT : List.Forall₂ (fun t w => (∃ T μ, Typed t T μ) → ∃ T μ, Typed w T μ) os zs)
    (hs : ss.Sublist zs) : ∀ w ∈ ss, ∃ T μ, Typed w T μ := by
  obtain ⟨T, μ, hty⟩ := hy
  cases hty with
  | union hL =>
    intro w hw
    obtain ⟨t, ht, hr⟩ := forall₂_mem_right hT (hs.subset hw)
    obtain ⟨T', -, μ', hty'⟩ := TypedListμ.mem hL t ht
    exact hr ⟨T', μ', hty'⟩

-- the object rows put the whole field table to `decide` under a binder
set_option maxHeartbeats 1000000

/-- `f` carries derivability with one term fixed on the left, at EVERY right operand. -/
def TypedSound (x : Term S) (f : Term S → Option (Term S)) : Prop :=
  ∀ y z, f y = some z → (∃ T μ, Typed x T μ) → (∃ T μ, Typed y T μ) → ∃ T μ, Typed z T μ

/-- `fam` carries derivability with one term fixed on the left, over the operands it is handed. -/
def TypedFam (x : Term S) (fam : Term S → Option (Term S)) : Prop :=
  ∀ y z, Delegated y → fam y = some z → (∃ T μ, Typed x T μ) → (∃ T μ, Typed y T μ) →
    ∃ T μ, Typed z T μ

/-- An object is derivable where every declared slot's term is and the open block is typed. The
    judgements at the names make one witness function over the finite key set. -/
theorem typed_object_of {F} (hF : Sem.map (S := S) = some F) {fs : Finset String}
    {Fs : {k // k ∈ fs} → ObjectSlot S} {w : Option (Term S)} {R : Option (S.V → Prop)}
    (hf : ∀ k, ∃ T μ, Typed (ObjectSlot.termOf (Fs k)) T μ) (hr : TypedWild w R) :
    ∃ T μ, Typed (.object (.mk fs Fs w)) T μ := by
  obtain ⟨g, hg⟩ := exists_fun_of_finset (α := (S.V → Prop) × Option (Sem.M S)) fs
    (P := fun k hk x => Typed (ObjectSlot.termOf (Fs ⟨k, hk⟩)) x.1 x.2)
    (fun k hk => by obtain ⟨T, μ, h⟩ := hf ⟨k, hk⟩; exact ⟨(T, μ), h⟩)
  exact ⟨_, _, Typed.object (body := .mk fs Fs w) (R := R) hF
    (bind := fun k => (ObjectSlot.isReq (Fs k), (g k.1).1))
    (μs := fun k => (g k.1).2)
    (fun k => typedField_of (hg k.1 k.2)) hr⟩

mutual
/-- Every row that reads the right operand alone is derivable wherever the family is. -/
theorem typed_meetSRight [Leaf S] {x : Term S} {fam : Pairing → Term S → Option (Term S)}
    (hf : ∀ q, TypedFam x (fam q)) :
    ∀ (y : Term S) (p : Pairing) z, meetSRight fam p y = some z → (∃ T μ, Typed x T μ) →
      (∃ T μ, Typed y T μ) → ∃ T μ, Typed z T μ
  | .never, _, _, h, _, _ => by
      simp only [meetSRight, Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩
  | .var _, _, _, h, _, _ => by simp [meetSRight] at h
  | .held _ _ _ _, _, _, h, _, _ => by simp [meetSRight] at h
  | .mu b, p, _, h, hx, hy => by
      simp only [meetSRight] at h
      exact typed_meetSRight hf b (shiftR p) _ h hx (typed_mu_inv hy)
  | .refine y q, p, _, h, hx, hy => by
      simp only [meetSRight] at h
      split at h
      · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
        exact typed_refineOf (typed_meetSRight hf y p w hw hx (typed_refine_inv hy))
      · obtain ⟨w, -, hw⟩ := Option.bind_eq_some_iff.mp h
        split at hw
        · cases hw; exact ⟨_, _, Typed.never⟩
        · exact nomatch hw
  | .union os, p, _, h, hx, hy => by
      obtain ⟨zs, hF, rfl⟩ := meetSRight_union h
      exact typed_ofOptions (survivors hy
        ((typed_meetSRightL hf os p zs hF).imp fun _ _ k => k hx)
        (List.filter_sublist (p := fun w : Term S => !w.isNever)))
  | .prim g, p, _, h, hx, hy => hf p (.prim g) _ trivial h hx hy
  | .set b, p, _, h, hx, hy => hf p (.set b) _ trivial h hx hy
  | .opaq, p, _, h, hx, hy => hf p .opaq _ trivial h hx hy
  | .list pr q s, p, _, h, hx, hy => hf p (.list pr q s) _ trivial h hx hy
  | .object b, p, _, h, hx, hy => hf p (.object b) _ trivial h hx hy
termination_by structural y => y

/-- The list companion: the union row's options, lifted pointwise. -/
theorem typed_meetSRightL [Leaf S] {x : Term S} {fam : Pairing → Term S → Option (Term S)}
    (hf : ∀ q, TypedFam x (fam q)) :
    ∀ os (p : Pairing) zs, List.Forall₂ (fun t w => meetSRight fam p t = some w) os zs →
      List.Forall₂ (fun t w => (∃ T μ, Typed x T μ) → (∃ T μ, Typed t T μ) →
        ∃ T μ, Typed w T μ) os zs
  | [], _, _, h => by cases h; exact .nil
  | t :: ts, p, _, h => by
      cases h with
      | cons hh ht =>
          exact .cons (fun hx hy => typed_meetSRight hf t p _ hh hx hy)
            (typed_meetSRightL hf ts p _ ht)
termination_by structural os => os
end

/-- The tactic every flat family uses: a row answers one of its factors, the bottom, or nothing. -/
local macro "typed_fam" fam:ident : tactic => `(tactic|
  (intro y z hd h hx hy
   cases y <;> first | exact hd.elim | skip
   all_goals
     (simp only [$fam:ident] at h
      repeat' split at h
      all_goals
        first
          | (simp only [reduceCtorEq] at h; done)
          | (simp only [Option.some.injEq] at h
             subst h
             first
               | exact hx
               | exact hy
               | exact ⟨_, _, Typed.never⟩
               | exact ⟨_, _, Typed.opaq⟩
               | exact ⟨_, _, Typed.prim _⟩))))

/-- The one leaf family answers a primitive, a factor or the bottom, and each is derivable. -/
theorem typed_famPrim [Leaf S] (g : S.Ground) : TypedFam (.prim g) (famPrim g) := by
  typed_fam famPrim

/-- The top meets a primitive at the primitive and itself at itself. -/
theorem typed_famOpaq [Leaf S] : TypedFam (.opaq : Term S) famOpaq := by typed_fam famOpaq

/-- **Two sets meet at a set of the element meet**, which is derivable where the element meet is,
    or at the bottom. -/
theorem typed_famSet (a : Term S) {mt : Term S → Option (Term S)} (ih : TypedSound a mt) :
    TypedFam (.set a) (famSet a mt) := by
  intro y z hd h hx hy
  cases y <;> first | exact hd.elim | skip
  case set y =>
      simp only [famSet] at h
      split at h
      · exact nomatch h
      split at h
      · next z' hz =>
        split at h
        · simp only [Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩
        · split at h
          · exact nomatch h
          · simp only [Option.some.injEq] at h; subst h
            obtain ⟨_, _, hxa⟩ := hx
            obtain ⟨_, _, hyy⟩ := hy
            cases hxa with | set hL hxa' =>
            cases hyy with | set _ hyy' =>
            obtain ⟨T, μ, hz'⟩ := ih y z' hz ⟨_, _, hxa'⟩ ⟨_, _, hyy'⟩
            exact ⟨_, _, Typed.set hL hz'⟩
      · exact nomatch h
  case opaq => simp [famSet] at h
  all_goals (simp only [famSet, Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩)

/-! ### The container families -/

/-- …and the same two tuples' positions zipped. -/
theorem typed_zipF_lift :
    ∀ {ts us : List (Term S)} {fs : List (Term S → Option (Term S))} {vs : List (Term S)},
      List.Forall₂ TypedSound ts fs → (∀ t ∈ ts, ∃ T μ, Typed t T μ) →
      (∀ u ∈ us, ∃ T μ, Typed u T μ) →
      List.Forall₂ (fun (p : (Term S → Option (Term S)) × Term S) v => p.1 p.2 = some v) (fs.zip us) vs →
      ∀ v ∈ vs, ∃ T μ, Typed v T μ := by
  intro ts
  induction ts with
  | nil => intro us fs vs hfs _ _ hv; cases hfs; cases hv; intro v hvm; exact nomatch hvm
  | cons t ts ihs =>
      intro us fs vs hfs hts hus hv
      cases hfs with
      | cons hf hfs' =>
          cases us with
          | nil => cases hv; intro v hvm; exact nomatch hvm
          | cons u us =>
              cases hv with
              | cons hh ht =>
                  intro v hvm
                  rcases List.mem_cons.mp hvm with rfl | hvm'
                  · exact hf u v hh (hts t List.mem_cons_self) (hus u List.mem_cons_self)
                  · exact ihs hfs' (fun w hw => hts w (List.mem_cons_of_mem _ hw))
                      (fun w hw => hus w (List.mem_cons_of_mem _ hw)) ht v hvm'

/-- **The one positional container's family, on the derivation.** Every term the answer holds
    is a meet of a term one shape declares with a term the other declares, and `rowOfG_mem`
    says a row holds nothing else. -/
theorem typed_famList {pre suf : List (Term S)} {sp : Option (Term S)}
    {fpre fsuf : List (Term S → Option (Term S))} {fsp : Option (Term S → Option (Term S))}
    (hp : List.Forall₂ TypedSound pre fpre)
    (hs : (sp = none ∧ fsp = none) ∨ ∃ t f, sp = some t ∧ fsp = some f ∧ TypedSound t f)
    (hf : List.Forall₂ TypedSound suf fsuf) :
    TypedFam (.list pre sp suf) (famList fpre fsp fsuf) := by
  intro y z hd h hx hy
  obtain ⟨hpre, hsp, hsuf⟩ := typed_list_inv hx
  obtain ⟨Lf, hLf⟩ := list_former_of_typed hx
  cases y <;> first | exact hd.elim | skip
  case list pre₂ sp₂ suf₂ =>
      obtain ⟨hpre₂, hsp₂, hsuf₂⟩ := typed_list_inv hy
      have hall : ∀ t ∈ pre ++ suf, ∃ T μ, Typed t T μ := by
        intro w hw
        rcases List.mem_append.mp hw with h' | h'
        exacts [hpre w h', hsuf w h']
      simp only [famList] at h
      rcases hs with ⟨rfl, rfl⟩ | ⟨t, f, rfl, rfl, hsound⟩
      · simp only [listMeetRow] at h
        rw [show rowOfG fpre none fsuf (fpre.length + fsuf.length) = some (fpre ++ fsuf) from
          by rw [rowOfG_none_eq, if_pos rfl]] at h
        cases hR : rowOfG pre₂ sp₂ suf₂ (fpre.length + fsuf.length) with
        | none =>
            rw [hR] at h
            simp only [Option.some.injEq] at h
            subst h
            exact ⟨_, _, Typed.never⟩
        | some us =>
            rw [hR] at h
            obtain ⟨row, hrow, rfl⟩ := Option.map_eq_some_iff.mp h
            refine typed_listOf hLf ?_ (by simp) (by simp)
            refine typed_zipF_lift (forall₂_append hp hf) hall ?_
              (allSome_map_forall₂ _ (by rw [← zipF_eq]; exact hrow))
            intro u hu
            rcases rowOfG_mem hR hu with h' | h' | h'
            exacts [hpre₂ u h', hsp₂ u h', hsuf₂ u h']
      · cases sp₂ with
        | none =>
            simp only [listMeetRow] at h
            rw [show rowOfG pre₂ none suf₂ (pre₂.length + suf₂.length)
                = some (pre₂ ++ suf₂) from by rw [rowOfG_none_eq, if_pos rfl]] at h
            cases hL : rowOfG fpre (some f) fsuf (pre₂.length + suf₂.length) with
            | none =>
                rw [hL] at h
                simp only [Option.some.injEq] at h
                subst h
                exact ⟨_, _, Typed.never⟩
            | some fs =>
                rw [hL] at h
                obtain ⟨row, hrow, rfl⟩ := Option.map_eq_some_iff.mp h
                obtain ⟨ts, hts, htsF⟩ :=
                  rowOfG_forall₂_left hp (Or.inr ⟨t, f, rfl, rfl, hsound⟩) hf hL
                refine typed_listOf hLf ?_ (by simp) (by simp)
                refine typed_zipF_lift htsF ?_ ?_
                  (allSome_map_forall₂ _ (by rw [← zipF_eq]; exact hrow))
                · intro w hw
                  rcases rowOfG_mem hts hw with h' | h' | h'
                  exacts [hpre w h', hsp w h', hsuf w h']
                · intro u hu
                  rcases List.mem_append.mp hu with h' | h'
                  exacts [hpre₂ u h', hsuf₂ u h']
        | some c =>
            simp only [listMeetRow] at h
            split at h
            · next hdom =>
                obtain ⟨fs, hfs⟩ :=
                  rowOfG_total (pre := fpre) (suf := fsuf) (c := f)
                    (n := max fpre.length pre₂.length + max fsuf.length suf₂.length) (by omega)
                obtain ⟨us, hus⟩ :=
                  rowOfG_total (pre := pre₂) (suf := suf₂) (c := c)
                    (n := max fpre.length pre₂.length + max fsuf.length suf₂.length) (by omega)
                rw [hfs, hus] at h
                cases hfc : f c with
                | none => rw [hfc] at h; exact absurd h (by simp)
                | some spz =>
                    rw [hfc] at h
                    obtain ⟨row, hrow, rfl⟩ := Option.map_eq_some_iff.mp h
                    obtain ⟨ts, hts, htsF⟩ :=
                      rowOfG_forall₂_left hp (Or.inr ⟨t, f, rfl, rfl, hsound⟩) hf hfs
                    have hrowT : ∀ w ∈ row, ∃ T μ, Typed w T μ := by
                      refine typed_zipF_lift htsF ?_ ?_
                        (allSome_map_forall₂ _ (by rw [← zipF_eq]; exact hrow))
                      · intro w hw
                        rcases rowOfG_mem hts hw with h' | h' | h'
                        exacts [hpre w h', hsp w h', hsuf w h']
                      · intro u hu
                        rcases rowOfG_mem hus hu with h' | h' | h'
                        exacts [hpre₂ u h', hsp₂ u h', hsuf₂ u h']
                    refine typed_listOf hLf (fun w hw => hrowT w (List.mem_of_mem_take hw)) ?_
                      (fun w hw => hrowT w (List.mem_of_mem_drop hw))
                    intro w hw
                    cases hw
                    exact hsound c spz hfc (hsp t rfl) (hsp₂ c rfl)
            · exact absurd h (by simp)
  case opaq => simp [famList] at h
  all_goals
    (simp only [famList, Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩)

/-- A typed body's block is typed: the open block's term, or the bottom. -/
theorem typed_block {b : Body S} (h : ∃ R, TypedWild b.wild R) : ∃ T μ, Typed b.block T μ := by
  obtain ⟨R, hR⟩ := h
  cases b with
  | mk fs f w =>
    cases hR with
    | none => exact ⟨_, _, Typed.never⟩
    | some ht => exact ⟨_, _, ht⟩

/-- **Two objects meet pointwise, and the meet stays in the typed fragment.** -/
theorem typed_famObj {a : Body S} {g : {k // k ∈ a.fields} → ObjectSlot S → Option (ObjectSlot S)}
    {mw : Term S → Option (Term S)}
    (hg : ∀ (k : {k // k ∈ a.fields}) (fl fm : ObjectSlot S), g k fl = some fm →
      (∃ T μ, Typed (ObjectSlot.termOf (a.at k)) T μ) → (∃ T μ, Typed (ObjectSlot.termOf fl) T μ) →
      ∃ T μ, Typed (ObjectSlot.termOf fm) T μ)
    (hw : ∀ y z, mw y = some z → (∃ T μ, Typed a.block T μ) → (∃ T μ, Typed y T μ) →
      ∃ T μ, Typed z T μ) :
    TypedFam (.object a) (famObj a g mw) := by
  intro y z hd h hx hy
  obtain ⟨hfa, hra⟩ := typed_object_inv hx
  obtain ⟨Fm, hF⟩ := map_former_of_typed hx
  cases y <;> first | exact hd.elim | skip
  case object b =>
      obtain ⟨hfb, hrb⟩ := typed_object_inv hy
      simp only [famObj] at h
      unfold objObj at h
      split at h
      next => simp only [Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩
      next =>
        split at h
        next => exact absurd h (by simp)
        next zb hwz =>
          split at h
          next hall =>
            simp only [Option.some.injEq] at h; subst h
            have hFs : ∀ k : {k // k ∈ (a.fields ∪ b.fields).filter (fun k =>
                (if h : k ∈ a.fields ∪ b.fields then
                  !(zb.isNever && ObjectSlot.isAbsentOpt (objSlot a b g mw ⟨k, h⟩))
                else false) = true)},
                ∃ T μ, Typed (ObjectSlot.termOf ((objSlot a b g mw
                  ⟨k.1, (Finset.mem_filter.mp k.2).1⟩).getD (.optional .never))) T μ := by
              intro k
              obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp
                (of_decide_eq_true hall ⟨k.1, (Finset.mem_filter.mp k.2).1⟩)
              rw [hs, Option.getD_some]
              unfold objSlot at hs
              split at hs
              next ha =>
                refine hg _ _ _ hs (hfa _) ?_
                split
                · exact hfb _
                · exact typed_block hrb
              next ha =>
                have hb := (Finset.mem_union.mp (Finset.mem_filter.mp k.2).1).resolve_left ha
                have hty := hfb ⟨k.1, hb⟩
                cases hf : b.at ⟨k.1, hb⟩ with
                | req y =>
                  rw [hf] at hs hty
                  simp only [ObjectSlot.through, Option.map_eq_some_iff] at hs
                  obtain ⟨z, hz, rfl⟩ := hs
                  exact hw _ _ hz (typed_block hra) hty
                | optional y =>
                  rw [hf] at hs hty
                  simp only [ObjectSlot.through, Option.map_eq_some_iff] at hs
                  obtain ⟨z, hz, rfl⟩ := hs
                  exact hw _ _ hz (typed_block hra) hty
            rcases Bool.eq_false_or_eq_true zb.isNever with hn | hn
            · rw [if_pos hn]
              exact typed_object_of hF hFs TypedWild.none
            · obtain ⟨T, μ, ht⟩ := hw _ _ hwz (typed_block hra) (typed_block hrb)
              rw [if_neg (by rw [hn]; exact Bool.false_ne_true)]
              exact typed_object_of hF hFs (TypedWild.some ht)
          next => exact absurd h (by simp)
  case opaq => simp [famObj] at h
  all_goals
    (simp only [famObj, Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩)

/-! ### The outer theorem -/

mutual
/-- **The typed fragment is closed under the meet.** Where two derivable terms have a meet, the
    meet is derivable. The union row owes only the survivors' derivability (`survivors`). -/
theorem typed_meet [Leaf S] : ∀ (p : Pairing) (x y : Term S) z, Term.meet p x y = some z →
    (∃ T μ, Typed x T μ) → (∃ T μ, Typed y T μ) → ∃ T μ, Typed z T μ
  | _, .never, _, _, h, _, _ => by
      simp only [Term.meet, Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩
  | _, .held _ _ _ _, y, _, h, _, _ => by
      cases y <;>
        first
          | (simp only [Term.meet, Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩)
          | exact absurd h (by simp [Term.meet])
  | _, .var _, y, _, h, _, _ => by
      cases y <;>
        first
          | (simp only [Term.meet, Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩)
          | (simp only [Term.meet, Option.map_eq_some_iff] at h
             obtain ⟨_, _, rfl⟩ := h
             exact ⟨_, _, Typed.var _⟩)
          | exact absurd h (by simp [Term.meet])
  -- two recursive terms meet at the lowered body meet or at a guarded recursive term of it, and
  -- an unfolding meets the body
  | p, .mu b, y, _, h, hx, hy => by
      cases y <;>
        first
          | (simp only [Term.meet, Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩)
          | (simp only [Term.meet, Option.bind_eq_some_iff] at h
             obtain ⟨w, hw, hz⟩ := h
             obtain ⟨_, _, hwt⟩ :=
               typed_meet (pairMu p) b _ w hw (typed_mu_inv hx) (typed_mu_inv hy)
             split at hz
             · cases hz; exact ⟨_, _, Typed.never⟩
             · split at hz
               · cases hz; exact ⟨_, _, typed_rename _ hwt⟩
               · split at hz
                 · next hg => cases hz; exact ⟨_, _, Typed.mu hg hwt⟩
                 · exact nomatch hz)
          | (simp only [Term.meet] at h
             exact typed_meet (shiftL p) b _ _ h (typed_mu_inv hx) hy)
  | p, .refine x q, y, _, h, hx, hy => by
      cases y with
      | never =>
          simp only [Term.meet, Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩
      | _ =>
        simp only [Term.meet] at h
        split at h
        · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
          exact typed_refineOf (typed_meet p x _ w hw (typed_refine_inv hx) hy)
        · obtain ⟨w, -, hw⟩ := Option.bind_eq_some_iff.mp h
          split at hw
          · cases hw; exact ⟨_, _, Typed.never⟩
          · exact nomatch hw
  | p, .union os, y, _, h, hx, hy => by
      cases y with
      | never =>
          simp only [Term.meet, Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩
      | _ =>
        obtain ⟨zs, hF, rfl⟩ := meet_union_of h (by simp)
        exact typed_ofOptions (survivors hx
          ((typed_meetL p os _ zs hF).imp fun _ _ k ht => k ht hy)
          (List.filter_sublist (p := fun w : Term S => !w.isNever)))
  | p, .prim g, y, z, h, hx, hy => typed_meetSRight (fun _ => typed_famPrim g) y p z h hx hy
  | p, .set a, y, z, h, hx, hy =>
      typed_meetSRight (fun q => typed_famSet a (fun u w hw => typed_meet q a u w hw))
        y p z h hx hy
  | p, .opaq, y, z, h, hx, hy => typed_meetSRight (fun _ => typed_famOpaq) y p z h hx hy
  | p, .list pre sp suf, y, z, h, hx, hy => by
      cases sp with
      | none =>
          exact typed_meetSRight (fun q => typed_famList (pre := pre) (sp := none) (suf := suf)
            (typed_meetSTs q pre) (Or.inl ⟨rfl, rfl⟩) (typed_meetSTs q suf)) y p z h hx hy
      | some t =>
          exact typed_meetSRight (fun q => typed_famList (pre := pre) (sp := some t)
            (suf := suf) (typed_meetSTs q pre)
            (Or.inr ⟨t, Term.meet q t, rfl, rfl, fun u w hw => typed_meet q t u w hw⟩)
            (typed_meetSTs q suf)) y p z h hx hy
  | p, .object (.mk fs f none), y, z, h, hx, hy =>
      typed_meetSRight (fun q => typed_famObj (a := .mk fs f none)
        (fun k fl fm hm => typed_Field_meet q (f k) fl fm hm)
        (fun _ _ hz _ _ => by
          simp only [Option.some.injEq] at hz; subst hz; exact ⟨_, _, Typed.never⟩))
        y p z h hx hy
  | p, .object (.mk fs f (some t)), y, z, h, hx, hy =>
      typed_meetSRight (fun q => typed_famObj (a := .mk fs f (some t))
        (fun k fl fm hm => typed_Field_meet q (f k) fl fm hm)
        (fun u w hw => typed_meet q t u w hw)) y p z h hx hy
termination_by structural _ x => x

/-- The union row's options, lifted pointwise at the fixed partner. -/
theorem typed_meetL [Leaf S] : ∀ (p : Pairing) (os : List (Term S)) (y : Term S)
    (zs : List (Term S)),
    List.Forall₂ (fun t w => Term.meet p t y = some w) os zs →
    List.Forall₂ (fun t w => (∃ T μ, Typed t T μ) → (∃ T μ, Typed y T μ) →
      ∃ T μ, Typed w T μ) os zs
  | _, [], _, _, h => by cases h; exact .nil
  | p, t :: ts, y, _, h => by
      cases h with
      | cons hh ht =>
          exact .cons (fun hx hy => typed_meet p t y _ hh hx hy) (typed_meetL p ts y _ ht)
termination_by structural _ os => os

/-- Every position of a tuple carries the meet at that position. -/
theorem typed_meetSTs [Leaf S] : ∀ (p : Pairing) (ts : List (Term S)),
    List.Forall₂ TypedSound ts (Term.meetSTs p ts)
  | _, [] => .nil
  | p, t :: ts => .cons (fun u w hw => typed_meet p t u w hw) (typed_meetSTs p ts)
termination_by structural _ ts => ts

/-- Two fields at one name carry two terms that meet. -/
theorem typed_Field_meet [Leaf S] : ∀ (p : Pairing) (f fl : ObjectSlot S) (fm : ObjectSlot S),
    ObjectSlot.meet p f fl = some fm →
    (∃ T μ, Typed (ObjectSlot.termOf f) T μ) → (∃ T μ, Typed (ObjectSlot.termOf fl) T μ) →
    ∃ T μ, Typed (ObjectSlot.termOf fm) T μ
  | p, .req x, .req y, _, h, hx, hy => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact typed_meet p x y tz hz hx hy
  | p, .req x, .optional y, _, h, hx, hy => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact typed_meet p x y tz hz hx hy
  | p, .optional x, .req y, _, h, hx, hy => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact typed_meet p x y tz hz hx hy
  | p, .optional x, .optional y, _, h, hx, hy => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact typed_meet p x y tz hz hx hy
termination_by structural _ f => f
end

end Calculus.Alg
