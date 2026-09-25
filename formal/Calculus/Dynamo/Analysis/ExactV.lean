import Calculus.Dynamo.Witness.Discharge
import Calculus.Alg.Rows
import Calculus.Dynamo.Lang.Soundness

/-!
# §5 — exactness on the value side

§5 used to state admission as a family of per-aspect tables, and every one of them was an
**over**-approximation. `⊤` is sound for every term, so a row that claims nothing can never
fail, and every defect caught in those tables was an imprecision rather than an
unsoundness. `Adm` is admission as a *domain* instead: exact at every constructor.
-/

namespace Calculus

open Alg (ObjectSlot.isReq Term.depth)

noncomputable section

/-! ## The rows a term's subterms hand up

`Adm t` is a *predicate*, and every container row below is a combinator on the predicates its
subterms compute — which is what `denote` does with codecs one level down. The shape is not a
matter of taste: `Term.object`'s field table is a **function**, `sizeOf` is blind to functions,
and a well-founded recursion therefore cannot reach a field's term. A structural recursion can,
and a structural recursion is what this shape buys — the same reason `denote` is structural and
`fieldSem`/`wildSem` are its companions rather than its arguments.
-/

/-- A value-side row, once the subterms' rows are known. -/
abbrev VP := Value → Bool

/-- `entryCodec`'s row: the slot a name declares, or else the open block's. `none` is an
    undeclared name in a body that declares no open block, and both sides refuse it. -/
def entryP {α : Type} (fs : MapOf (α → Bool)) (rp : Option (α → Bool)) (k : Name) :
    Option (α → Bool) :=
  match fs.at k with | some P => some P | none => rp

/-- `objWrite`'s traversal and `objRead`'s traversal, as a row: every entry goes through the
    codec its name names. -/
def objAdmV {α : Type} (fs : MapOf (α → Bool)) (rp : Option (α → Bool)) (keys : Finset Name)
    (g : {k // k ∈ keys} → α) : Bool :=
  decide (∀ k : {k // k ∈ keys}, (entryP fs rp k.1).any (· (g k)) = true)

/-- `valPresentB`'s guard, read off the *term*'s field table: only `optional` may be absent.
    Decidable over a `Finset Name`, which is why the excuse that named it never held. -/
def valPresentT (fields : Finset Name) (fld : {k // k ∈ fields} → ObjectSlot)
    (keys : Finset Name) : Bool :=
  decide (∀ k : {k // k ∈ fields},
    (match fld k with | .optional _ => true | _ => decide (k.1 ∈ keys)) = true)

/-- What the literal codec **writes**, exactly.

    **This was `inL` conjoined with `Numeral.WF`, and the conjunct is now the carrier's.**
    The second conjunct existed because at `number` an alternative outside §1's `D` was *held*
    and not *written*, so membership alone over-claimed — the same (B) failure ~~LiteralD~~
    forbade in a derivable term, stated here as a fact about the codec, which had no premise to
    lean on. `GroundKind.number.Carrier` is `WFNumeral`, so `inL`'s own row splits on the gate
    and there is no alternative left for the conjunct to catch.

    The retired per-aspect row was always `inL`
    and was therefore inexact at `number` by exactly this conjunct, while the joint row carried
    it and so `Adm_exact` covered the literal. The defect is closed rather than patched:
    nothing was added to make the two agree. -/
noncomputable def AdmLit (k : GroundKind) (x : k.Carrier) (v : Value) : Bool :=
  inL k x v

/-! ## The rows that ask their own codec

    `opaque` and `mu` are the two recursive terms, and their rows below **do not describe a
    set at all**. Each asks the codec it denotes:

        Adm  .opaq    v = ((muCodec opaqStep).e v).isSome
        Adm  (.mu b)  v = ((denote (.mu b)).e v).isSome

    and the read rows do the same with `p`. Three things follow.

    *It is exact by construction.* `denote`'s row is that codec, so the row and `dom(e)` are
    the same function, and `ExactV`/`ExactA` at the term is `Iff.rfl`. That is not a sharp
    analysis of a recursive term; it is the analysis *declining* to be one, and the exactness
    is the codec's, borrowed.

    *It is as precise as the semantics is.* `muCodec` recurses on the *input's own depth*,
    and a row over the term cannot see past the top constructor. Deferring sees all of it,
    because it does not look. `opaque`'s domain is every value (`opaq_total`).

    *Nothing here knows anything about the implementation.* Swap the body of `opaque` — a
    different numeric policy, a different set of options — and every theorem downstream is
    still true and still proved, because none of them mentions what the codec answers.

    A variable is read closed, as the bottom, so its row is `false`. A variable reads its
    binder's stage only inside `muCodec`, and no row reaches inside it.

    ### The warranty behind the row

    `opaque` carries no premise. `Obligations .opaq = True`, and it is `True` because the
    laws are *theorems* here: `lawful_opaq` and `carrier_opaq` (`Opaque.lean`), from the
    guard of its body. A `mu` owes the premises of its body at each stage, and `soundnessIn`
    turns them into the laws of the limit. The row asks a codec **the calculus warrants**.

    ### What "unanalysable" turned out to mean

    `held` was on the unanalysable list because it carries Lean functions, and
    a function is not something a reader can look inside. But a row is not a reader: it is a
    function with the term in hand, and the term *carries* `f` and `g` as data. It can
    apply them. `(c.through f g).e v = c.e (f v)` holds by `Iff.rfl`, so `held`'s writable
    set is the subterm's pulled back along `f` and cut by the caller-side term's row, with no
    appeal to `held`'s iso obligation.

    Three senses had been running together: (i) the term does not carry the information —
    true of nothing here; (ii) the domain cannot be computed without running the codec — true
    of `opaq`, and the reason the row *does* run it, at the price of being
    `noncomputable`; (iii) a reader cannot see through it — true of `held` and
    `opaq`, and not a property of the calculus. -/

mutual

/-- **The joint admission predicate.** One structural recursion over the term, with the
    containers recursing through *this* — which is exactly what the retired per-aspect rows
    failed to do.

    **Every row is exact.** This said `union` was "still a sound over-approximation and
    claims no exactness, and it is now the only one" — true when written and false from the
    commit that proved `ExactV_union` and made `Adm_exact` unconditional, which rewrote the
    header of this file and missed the sentence eleven lines below it. One more description
    that nothing was keeping honest. -/
noncomputable def Adm : Term → Value → Bool
  | .base k   => inBase k
  | .literal k ls => AdmLit k ls
  -- the bottom admits nothing, and the row is that sentence
  | .never => fun _ => false
  | .refine t p => fun v => Adm t v && p.eval v
  | .held t P f _ => fun v => Adm t (f v) && Adm P v
  -- `select` attempts every option, so the row is the disjunction of the options' rows
  | .union opts => fun v => anyP (AdmList opts) v
  -- **`set` asks its own codec**, as `opaq` and `mu` do. A row over the elements alone is exact
  -- only where the element writes injectively and at one member, and an arbitrary element term
  -- does neither: a `held` can collide two elements, and a `union` can mix `S` and `N`. Below
  -- `opaque` both hold, and the meet reads the row element by element there.
  | .set t      => fun v => ((setCodec (denote t)).e v).isSome
  -- **One row for the one positional container.** `array` and `tuple` were two rows that
  -- computed different things (`allP` and `alignP`) on shapes that are now the same term,
  -- so the first would have shadowed the second in silence. `alignPL` is the row both
  -- shapes reduce to.
  | .list pre sp suf => fun v =>
      match v with
      | .arr vs => alignPL (AdmList pre) (AdmOptT sp) (AdmList suf) vs
      | _ => false
  | .object b => AdmBody b
  -- **The second row that asks its own codec**, as the section above sets out:
  -- `denote .opaq` *is* `muCodec opaqStep`, so this is `dom(e)` rather than a
  -- description of it, and `ExactV_opaq` is `Iff.rfl`.
  --
  -- It replaces a hand-written recursion over the value (~~AdmOpaqV~~) that computed the
  -- same set. That recursion was correct and cost ~120 lines of proof, and it was the
  -- wrong shape for one reason: it stated `opaque`'s domain a *second* time, so a change
  -- to `opaque`'s body — a new option, a different numeric policy — meant editing two
  -- definitions that had to agree. Deferring leaves one.
  | .opaq => fun v => ((muCodec opaqStep).e v).isSome
  -- a closed variable is the bottom
  | .var _ => fun _ => false
  -- the second recursive term asks its own codec, for the reason `opaq` does
  | .mu b => fun v => ((denote (.mu b)).e v).isSome

/-- The payload's row: the declared names are present, and every present name's value is
    admitted by its slot or by the open block. The companion `AdmField` and `AdmWild`
    were missing — `Adm`'s object row inlined it, so the one place that says what an object
    payload admits was a row of a table rather than a definition. -/
noncomputable def AdmBody : Body → VP
  | .mk fields fld wild => fun v =>
      match v with
      | .map keys g =>
          valPresentT fields fld keys &&
          objAdmV ⟨fields, fun k => AdmField (fld k)⟩ (AdmWild wild) keys g
      | _ => false

/-- A slot's row is its term's. The presence marker is `valPresentT`'s business, so it does
    not reach this row. Mirrors `fieldSem`, and for the same reason: the recursion has to be
    passed *applied*. -/
noncomputable def AdmField : ObjectSlot → VP
  | .req t => Adm t
  | .optional t => Adm t

/-- The open block's row, where the body has one — `rcOf`'s mirror. A body with no open
    block refuses, so an undeclared name is refused on the way *out* as well. -/
noncomputable def AdmWild : Option Term → Option VP
  | none => none
  | some t => some (Adm t)

/-- The options' rows, in order — `denoteList`'s mirror. -/
noncomputable def AdmList : List Term → List VP
  | [] => []
  | t :: ts => Adm t :: AdmList ts

noncomputable def AdmOptT : Option Term → Option VP
  | none => none
  | some t => some (Adm t)


end

/-- `valPresentT` in the form the object row uses: a declared name that must be present is
    present. -/
theorem valPresentT_req (fields : Finset Name) (fld : {k // k ∈ fields} → ObjectSlot)
    (keys : Finset Name) :
    valPresentT fields fld keys
      = decide (∀ k : {k // k ∈ fields}, ObjectSlot.isReq (fld k) = true → k.1 ∈ keys) := by
  unfold valPresentT
  refine decide_eq_decide.mpr ⟨fun hh k hreq => ?_, fun hh k => ?_⟩
  · have hk := hh k
    cases hf : fld k with
    | req t => rw [hf] at hk; exact of_decide_eq_true hk
    | optional t => rw [hf] at hreq; exact absurd hreq (by simp [ObjectSlot.isReq])
  · cases hf : fld k with
    | optional t => rfl
    | req t => exact decide_eq_true (hh k (by rw [hf]; rfl))


/-- A declared name that must be present is present, read off the admission. -/
theorem mem_keys_of_isReq {c : Body} {keys : Finset Name}
    (hv : valPresentT c.fields c.at keys = true) {k : Name} (hc : k ∈ c.fields)
    (hreq : ObjectSlot.isReq (c.at ⟨k, hc⟩) = true) : k ∈ keys := by
  rw [valPresentT_req] at hv
  exact of_decide_eq_true hv ⟨k, hc⟩ hreq

/-- A body admits a map by two tests: the declared names that must be present are, and every present name passes its row. -/
theorem AdmBody_map (c : Body) (keys : Finset Name) (g : {k // k ∈ keys} → Value) :
    AdmBody c (.map keys g)
      = (valPresentT c.fields c.at keys
         && objAdmV ⟨c.fields, fun k => AdmField (c.at k)⟩ (AdmWild c.wild) keys g) := by
  cases c; rfl

/-- A present name that the body declares goes through that name's field. -/
theorem objAdmV_row {c : Body} {keys : Finset Name} {g : {k // k ∈ keys} → Value}
    (hB : objAdmV ⟨c.fields, fun k => AdmField (c.at k)⟩ (AdmWild c.wild) keys g = true)
    {k : Name} (hk : k ∈ keys) (hc : k ∈ c.fields) :
    AdmField (c.at ⟨k, hc⟩) (g ⟨k, hk⟩) = true := by
  unfold objAdmV at hB
  have hh := of_decide_eq_true hB ⟨k, hk⟩
  rwa [entryP, MapOf.at, dif_pos hc] at hh

/-- A present name the body does not declare goes through the open block: an open body claims
    the name, and the block's row admits the name's value. -/
theorem objAdmV_wild {c : Body} {keys : Finset Name} {g : {k // k ∈ keys} → Value}
    (hB : objAdmV ⟨c.fields, fun k => AdmField (c.at k)⟩ (AdmWild c.wild) keys g = true)
    {k : Name} (hk : k ∈ keys) (hnc : k ∉ c.fields) {w : Term}
    (hw : c.wild = some w) : Adm w (g ⟨k, hk⟩) = true := by
  unfold objAdmV at hB
  have hh := of_decide_eq_true hB ⟨k, hk⟩
  rwa [entryP, MapOf.at, dif_neg hnc, hw, AdmWild] at hh

@[simp] theorem AdmList_eq : ∀ ts : List Term, AdmList ts = ts.map Adm
  | [] => rfl
  | t :: ts => by simp only [AdmList, List.map]; rw [AdmList_eq ts]



/-- `⋁` of `Adm` over a union's options, named — sound, and *not* exact. -/
noncomputable def AdmAny (ts : List Term) (v : Value) : Bool := anyP (AdmList ts) v

@[simp] theorem AdmAny_nil (v : Value) : AdmAny [] v = false := rfl

@[simp] theorem AdmAny_cons (t : Term) (ts : List Term) (v : Value) :
    AdmAny (t :: ts) v = (Adm t v || AdmAny ts v) := rfl

theorem Adm_union (opts : List Term) (v : Value) :
    Adm (.union opts) v = AdmAny opts v := rfl

/-- An option that admits makes the disjunction true. -/
theorem AdmAny_of_mem {t : Term} {ts : List Term} {v : Value} (ht : t ∈ ts)
    (h : Adm t v = true) : AdmAny ts v = true := by
  induction ts with
  | nil => exact absurd ht (by simp)
  | cons t0 ts ih =>
    rcases List.mem_cons.mp ht with rfl | h'
    · simp [AdmAny_cons, h]
    · simp [AdmAny_cons, ih h']

/-- A list admits a value exactly when one of its terms does. -/
theorem AdmAny_iff : ∀ {os : List Term} {v : Value},
    AdmAny os v = true ↔ ∃ t ∈ os, Adm t v = true
  | [], v => by simp
  | t :: ts, v => by
      rw [AdmAny_cons, Bool.or_eq_true, AdmAny_iff]
      constructor
      · rintro (h | ⟨u, hu, h⟩)
        · exact ⟨t, by simp, h⟩
        · exact ⟨u, by simp [hu], h⟩
      · rintro ⟨u, hu, h⟩
        rcases List.mem_cons.mp hu with rfl | hu'
        · exact Or.inl h
        · exact Or.inr ⟨u, hu', h⟩

/-- `Adm`'s literal row, named.

    Nothing should `simp [Adm]` at a literal: the row's pattern is *dependent* — `ls`'s type
    mentions `k` — so generating the table's equation lemmas across it is expensive enough to
    exhaust the heartbeat budget in proofs that used to close in one step. Stating the row once
    contains that cost, and every literal proof below rewrites with this instead. -/
@[simp] theorem Adm_literal (k : GroundKind) (x : k.Carrier) (v : Value) :
    Adm (.literal k x) v = AdmLit k x v := by unfold Adm; rfl

/-- §5's converse direction: the row is `dom(e)`, not merely a bound on it. -/
def ExactV (t : Term) : Prop := ∀ v, Adm t v = true ↔ ((denote t).e v).isSome

def ExactVL : List Term → Prop
  | [] => True
  | t :: ts => ExactV t ∧ ExactVL ts

def ExactVO : Option Term → Prop
  | none => True
  | some t => ExactV t

def ExactVW : Option Term → Prop
  | none => True
  | some t => ExactV t

theorem exactVL_mem : ∀ (ts : List Term), ExactVL ts → ∀ t ∈ ts, ExactV t
  | [], _, t, ht => absurd ht (by simp)
  | t0 :: ts, h, t, ht => by
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact h.1
      · exact exactVL_mem ts h.2 t ht'

theorem exactVO_mem : ∀ (tail : Option Term), ExactVO tail → ∀ t ∈ tail, ExactV t
  | none, _, t, ht => absurd ht (by simp)
  | some t0, h, t, ht => by
      have heq : t0 = t := by simpa using ht
      subst heq; exact h

theorem exactVW_codec : ∀ (wild : Option Term), ExactVW wild →
    ∀ t, wild = some t → ExactV t
  | none, _, t, h => nomatch h
  | some t0, h, t, hc => by
      simp only [Option.some.injEq] at hc
      exact hc ▸ h

/-- A traversal succeeds exactly when every entry does. -/
theorem traverse_isSome_iff {α β : Type} (f : α → Option β) : ∀ xs : List α,
    (traverse f xs).isSome = true ↔ ∀ x ∈ xs, (f x).isSome = true := by
  intro xs
  induction xs with
  | nil => simp [traverse]
  | cons x xs ih =>
    simp only [traverse, List.mem_cons]
    cases hx : f x with
    | none => simp [hx]
    | some y =>
      cases htr : traverse f xs with
      | none =>
        have hno : ¬ (∀ z ∈ xs, (f z).isSome = true) := by
          intro hall; have := ih.mpr hall; rw [htr] at this; simp at this
        constructor
        · intro hc; simp at hc
        · intro hall; exact absurd (fun z hz => hall z (Or.inr hz)) hno
      | some ys =>
        have hall : ∀ z ∈ xs, (f z).isSome = true := ih.mp (by rw [htr]; rfl)
        simp only [Option.isSome_some, true_iff]
        rintro z (rfl | hz)
        · rw [hx]; rfl
        · exact hall z hz

/-- `allP` transported across the element's exactness. -/
theorem AdmAll_iff {c : Term} (h : ExactV c) : ∀ xs : List Value,
    allP (Adm c) xs = true ↔ ∀ x ∈ xs, ((denote c).e x).isSome = true := by
  intro xs; induction xs with
  | nil => simp [allP]
  | cons x xs ih => simp [allP, ih, h x]

theorem traverse_cons_isSome {α β : Type} (f : α → Option β) (x : α) (xs : List α) :
    (traverse f (x :: xs)).isSome = ((f x).isSome && (traverse f xs).isSome) := by
  simp only [traverse]
  cases hx : f x <;> cases hxs : traverse f xs <;> simp

/-- `alignP` is `align`'s row: the same length discipline, the same per-position test. -/
theorem alignP_iff (tail : Option Term) (htl : ∀ t ∈ tail, ExactV t) :
    ∀ (ts : List Term) (vs : List Value), (∀ t ∈ ts, ExactV t) →
      (alignP (AdmList ts) (AdmOptT tail) vs = true ↔
        ((align (denoteList ts) (denoteOpt tail) vs).bind
          (traverse fun cv => cv.1.e cv.2)).isSome = true)
  | [], [], _ => by
      cases tail <;> simp [alignP, AdmList, AdmOptT, align, denoteList, denoteOpt, traverse]
  | [], v :: vs, _ => by
      cases htail : tail with
      | none => simp [alignP, AdmList, AdmOptT, align, denoteList, denoteOpt]
      | some t =>
        have ht : ExactV t := htl t (by simp [htail])
        have ih := alignP_iff tail htl [] vs (by simp)
        rw [htail] at ih
        simp only [AdmList, AdmOptT, denoteList, denoteOpt] at ih
        simp only [alignP, AdmList, AdmOptT, align, denoteList, denoteOpt,
          Bool.and_eq_true]
        cases hal : align [] (some (denote t)) vs with
        | none =>
          rw [hal] at ih
          simp at ih
          simp [ih]
        | some ps =>
          rw [hal] at ih
          simp only [Option.map_some, Option.bind_some] at ih ⊢
          rw [traverse_cons_isSome, Bool.and_eq_true, ← ht v, ← ih]
  | t :: ts, [], _ => by
      cases tail <;> simp [alignP, AdmList, AdmOptT, align, denoteList, denoteOpt]
  | t :: ts, v :: vs, h => by
      have ht : ExactV t := h t (by simp)
      have ih := alignP_iff tail htl ts vs (fun t' ht' => h t' (by simp [ht']))
      simp only [alignP, AdmList, align, denoteList, Bool.and_eq_true]
      cases hal : align (denoteList ts) (denoteOpt tail) vs with
      | none =>
        simp only [hal, Option.map_none, Option.bind_none, Option.isSome_none] at ih ⊢
        simp at ih
        simp [ih]
      | some ps =>
        simp only [hal, Option.map_some, Option.bind_some] at ih ⊢
        rw [traverse_cons_isSome, Bool.and_eq_true, ← ht v, ← ih]


/-- The suffix's row, transported across its positions' exactness.

    The length premise is load bearing: `List.zip` TRUNCATES, so a row longer than the
    suffix would traverse the short zip and answer `true` where `zipP` answers `false`.
    `alignL` only ever hands this a row of exactly the suffix's length. -/
theorem zipP_iff : ∀ (suf : List Term), (∀ t ∈ suf, ExactV t) → ∀ (back : List Value),
    back.length = suf.length →
    (zipP (AdmList suf) back = true ↔
      (traverse (fun cv : Codec × Value => cv.1.e cv.2)
        ((denoteList suf).zip back)).isSome = true)
  | [], _, [], _ => by simp [zipP, AdmList, denoteList]
  | [], _, _ :: _, h => by
      exact absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  | _ :: _, _, [], h => by
      exact absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  | t :: ts, h, v :: vs, hlen => by
      simp only [AdmList, denoteList, zipP, List.zip_cons_cons, Bool.and_eq_true,
        traverse_cons_isSome]
      rw [zipP_iff ts (fun t' ht' => h t' (List.mem_cons_of_mem _ ht')) vs
          (by simp only [List.length_cons] at hlen; omega),
        h t List.mem_cons_self v]

/-- **`alignPL` is `alignL`'s row.** The suffix splits off the right end on both sides, so
    this is `alignP_iff` beside `zipP_iff` and nothing new. -/
theorem alignPL_iff (pre : List Term) (sp : Option Term) (suf : List Term)
    (hpre : ∀ t ∈ pre, ExactV t) (hsp : ∀ t ∈ sp, ExactV t) (hsuf : ∀ t ∈ suf, ExactV t)
    (vs : List Value) :
    alignPL (AdmList pre) (AdmOptT sp) (AdmList suf) vs = true ↔
      ((alignL (denoteList pre) (denoteOpt sp) (denoteList suf) vs).bind
        (traverse fun cv => cv.1.e cv.2)).isSome = true := by
  have hlenA : (AdmList suf).length = suf.length := by simp
  have hlenD : (denoteList suf).length = suf.length := by simp
  unfold alignPL
  rw [hlenA]
  rcases Nat.lt_or_ge vs.length suf.length with hlt | hge
  · rw [alignL_short _ _ _ _ (by omega)]
    have h0 : vs.length - suf.length = 0 := by omega
    rw [h0, List.drop_zero]
    refine ⟨fun hc => ?_, fun hc => nomatch hc⟩
    have := zipP_length _ _ (Bool.and_eq_true .. ▸ hc |>.2)
    rw [hlenA] at this
    omega
  · rw [alignL_eq_split _ _ _ _ (by omega), hlenD]
    rw [Bool.and_eq_true, alignP_iff sp hsp pre (vs.take (vs.length - suf.length)) hpre,
      zipP_iff suf hsuf _ (by simp; omega)]
    cases hal : align (denoteList pre) (denoteOpt sp) (vs.take (vs.length - suf.length)) with
    | none => simp
    | some ps => simp [traverse_append_isSome]

/-- **`list` is exact** once its three parts are. -/
theorem ExactV_list {pre : List Term} {sp : Option Term} {suf : List Term}
    (hpre : ∀ t ∈ pre, ExactV t) (hsp : ∀ t ∈ sp, ExactV t) (hsuf : ∀ t ∈ suf, ExactV t) :
    ExactV (.list pre sp suf) := by
  intro v
  cases v
  case arr vs =>
    show alignPL (AdmList pre) (AdmOptT sp) (AdmList suf) vs = true ↔
      (((alignL (denoteList pre) (denoteOpt sp) (denoteList suf) vs).bind
        (traverse fun cv => cv.1.e cv.2)).map Attr.l).isSome = true
    rw [alignPL_iff pre sp suf hpre hsp hsuf vs]
    cases (alignL (denoteList pre) (denoteOpt sp) (denoteList suf) vs).bind
      (traverse fun cv => cv.1.e cv.2) <;> simp
  all_goals simp [Adm, denote, listCodec, Alg.listCodec, carriedCodec, arrV, lA]

/-- **`tuple` is exact** once its components are: the `list` with no suffix. -/
theorem ExactV_tuple {ts : List Term} {tail : Option Term}
    (h : ∀ t ∈ ts, ExactV t) (htl : ∀ t ∈ tail, ExactV t) : ExactV (.tuple ts tail) :=
  ExactV_list h htl (by simp)

/-- **`array` is exact** once its element is: the `list` with one spread. -/
theorem ExactV_array {c : Term} (hc : ExactV c) : ExactV (.array c) :=
  ExactV_list (by simp) (by simpa using hc) (by simp)

/-- A slot's row is exact when the term it carries is. -/
def ExactField (fd : ObjectSlot) : Prop :=
  ∀ v, AdmField fd v = true ↔ (((fieldSem fd).codec).e v).isSome

theorem valPresentT_eq (fields : Finset Name) (fld : {k // k ∈ fields} → ObjectSlot)
    (keys : Finset Name) :
    valPresentT fields fld keys = valPresentB ⟨fields, fun k => fieldSem (fld k)⟩ keys := by
  simp only [valPresentT, valPresentB]
  congr 1
  apply propext
  constructor <;> intro h k <;> have := h k <;>
    (cases hfd : fld k with
      | req t => simp_all [valPresentAt, fieldSem]
      | optional t => simp_all [valPresentAt, fieldSem])

theorem entry_iff {fields : Finset Name} {fld : {k // k ∈ fields} → ObjectSlot}
    {wild : Option Term}
    (hf : ∀ k : {k // k ∈ fields}, ExactField (fld k))
    (hr : ∀ t, wild = some t → ExactV t) (k : Name) (v : Value) :
    (entryP ⟨fields, fun k => AdmField (fld k)⟩ (AdmWild wild) k).any (· v) = true ↔
    ((entryCodec ⟨fields, fun k => fieldSem (fld k)⟩ (rcOf (wildSem wild)) k).bind
      (fun c => c.e v)).isSome = true := by
  simp only [entryP, entryCodec, MapOf.at]
  by_cases hk : k ∈ fields
  · rw [dif_pos hk, dif_pos hk]
    simpa using hf ⟨k, hk⟩ v
  · rw [dif_neg hk, dif_neg hk]
    cases wild with
    | none => simp [AdmWild, wildSem, rcOf]
    | some pt => simpa [AdmWild, wildSem, rcOf] using hr pt rfl v

/-- **`object` is exact** once its slots and its open block are. -/
theorem ExactV_object {fields : Finset Name} {fld : {k // k ∈ fields} → ObjectSlot}
    {wild : Option Term}
    (hf : ∀ k : {k // k ∈ fields}, ExactField (fld k))
    (hr : ∀ t, wild = some t → ExactV t) :
    ExactV (.object (.mk fields fld wild)) := by
  intro v
  cases v
  case map keys g =>
    show (valPresentT fields fld keys &&
        objAdmV ⟨fields, fun k => AdmField (fld k)⟩ (AdmWild wild) keys g) = true ↔
      ((objectCodec ⟨fields, fun k => fieldSem (fld k)⟩ (wildSem wild)).e (.map keys g)).isSome
        = true
    rw [valPresentT_eq]
    simp only [objectCodec, Alg.objectCodec, Alg.objectCodecCore, carriedCodec, mapV, objWrite,
      objAdmV, Bool.and_eq_true, decide_eq_true_eq, Option.isSome_map,
      Option.bind_some]
    by_cases hv : valPresentB ⟨fields, fun k => fieldSem (fld k)⟩ keys = true
    · rw [if_pos hv]
      simp only [hv, true_and, Option.isSome_map, funImage_isSome_iff]
      exact forall_congr' fun k => entry_iff hf hr k.1 (g k)
    · rw [if_neg hv]
      simp [hv]
  all_goals
    simp [Adm, AdmBody, denote, bodySem, objectCodec, Alg.objectCodec, Alg.objectCodecCore,
        carriedCodec, mapV]

theorem setImage_isSome_of_inj {α β : Type} [DecidableEq β] {f : α → Option β} {S : Finset α}
    (hall : ∀ x ∈ S, (f x).isSome = true)
    (hinj : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y) : (setImage f S).isSome = true := by
  unfold setImage
  rw [dif_pos hall]
  have hnd : (S.attach.val.map (fun x => (f x.1).get (hall x.1 x.2))).Nodup := by
    refine Multiset.Nodup.map_on ?_ S.attach.nodup
    intro x hx y hy hxy
    apply Subtype.ext
    refine hinj x.1 x.2 y.1 y.2 ?_
    rw [← Option.some_get (hall x.1 x.2), ← Option.some_get (hall y.1 y.2), hxy]
  rw [dif_pos hnd]
  rfl

theorem setImage_none_of_fail {α β : Type} [DecidableEq β] {f : α → Option β} {S : Finset α}
    {x : α} (hx : x ∈ S) (h : f x = none) : setImage f S = none := by
  unfold setImage
  rw [dif_neg]
  intro hall
  have := hall x hx
  rw [h] at this
  exact absurd this (by simp)

theorem neSetImage_isSome_of_inj {α β : Type} [DecidableEq β] {f : α → Option β}
    {S : NEFinset α} (hall : ∀ x ∈ S.1, (f x).isSome = true)
    (hinj : ∀ x ∈ S.1, ∀ y ∈ S.1, f x = f y → x = y) : (neSetImage f S).isSome = true := by
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp (setImage_isSome_of_inj hall hinj)
  have h2 := (neSetImage_eq_setImage (f := f) (S := S)
    (T := ⟨T, setImage_nonempty hT S.2⟩)).mpr hT
  rw [h2]
  rfl

/-- **`opaque` writes exactly what its row says — definitionally.**

    Read the proof before the statement: it is `Iff.rfl`, and that is the whole of what is
    being claimed. `Adm .opaq` is `((muCodec opaqStep).e ·).isSome` and
    `denote .opaq` is `muCodec opaqStep`, so the two sides of the `↔` are the same
    Boolean and there is nothing to prove.

    This is exactness **earned by deferring**, not by a clever row: as a claim about the
    analysis it says the analysis of an escape hatch is that hatch's own answer, and
    nothing about what the answer is.
    What it replaced was a 120-line induction (~~AdmOpaqV_iff~~) proving a hand-written
    recursion over the value agreed with the codec at every budget that sees the value.
    That was a real theorem about the stages of `opaque`; this is not one, and does not
    pretend to be.

    What is bought instead is decoupling: change the body of `opaque` and this still holds,
    still by `rfl`. `mu` has the same row for the same reason.

    The codec the row asks is warranted by the calculus:
    `Obligations .opaq = True`, because `lawful_opaq` and `carrier_opaq`
    (`Opaque.lean`) are proved. The deferral costs the writer of the term nothing. -/
theorem ExactV_opaq : ExactV .opaq := fun _ => Iff.rfl


/-- **`set` writes exactly what its row says**, because the row asks the set's codec. -/
theorem ExactV_set (t : Term) : ExactV (.set t) := fun _ => Iff.rfl

/-- Each option's row *is* its attempt — given that option's exactness, which is where the
    exactness hypothesis is spent. -/
theorem isSome_e_eq_Adm {t : Term} (h : ExactV t) (v : Value) :
    ((denote t).e v).isSome = Adm t v := by
  exact Bool.coe_iff_coe.mp (by simpa using (h v).symm)

/-- **The option list's filter is the term list's, mapped.** It is an induction rather than a
    rewrite because the agreement above is per-option and hypothesis-bearing. -/
theorem filter_AdmList {opts : List Term} (h : ∀ t ∈ opts, ExactV t) (v : Value) :
    (denoteList opts).filter (fun c => (c.e v).isSome)
      = (opts.filter (fun t => Adm t v)).map denote := by
  induction opts with
  | nil => rfl
  | cons t ts ih =>
    have ht : ExactV t := h t (by simp)
    have hts : ∀ t' ∈ ts, ExactV t' := fun t' h' => h t' (by simp [h'])
    simp only [denoteList, List.filter_cons, isSome_e_eq_Adm ht, ih hts]
    cases hb : Adm t v <;> simp []

/-- **A union writes exactly where one of its options writes.** -/
theorem select_isSome_attempt (os : List Codec) (v : Value) :
    (select os (·.e) v).isSome = true ↔ ∃ o ∈ os, (o.e v).isSome = true := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨o, ho, -, he⟩ := select_admits ha
    exact ⟨o, ho, by rw [he]; rfl⟩
  · rintro ⟨o, ho, he⟩
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp he
    obtain ⟨o', hf⟩ := find?_attempt_V ho ha
    unfold select; rw [hf]; exact acts_of_find?_V hf

/-- **`union` writes exactly what its row says**: the options are exact, and a union writes
    where one of them writes. -/
theorem ExactV_union {opts : List Term} (h : ∀ t ∈ opts, ExactV t) : ExactV (.union opts) := by
  intro v
  rw [denote_union_sems]
  show AdmAny opts v = true ↔ (select (denoteList opts) (·.e) v).isSome
  rw [select_isSome_attempt, denoteList_eq]
  simp only [List.mem_map, exists_exists_and_eq_and]
  constructor
  · intro ha
    induction opts with
    | nil => exact absurd ha (by simp)
    | cons t ts ih =>
      rw [AdmAny_cons, Bool.or_eq_true] at ha
      rcases ha with ha | ha
      · exact ⟨t, List.mem_cons_self, (h t List.mem_cons_self v).mp ha⟩
      · obtain ⟨t', ht', he⟩ := ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht')) ha
        exact ⟨t', List.mem_cons_of_mem _ ht', he⟩
  · rintro ⟨t, ht, he⟩
    exact AdmAny_of_mem ht ((h t ht v).mpr he)

mutual
/-- **Every row is exact.** Not a bound on `dom(e)` — `dom(e)`, at every constructor and
    with no hypothesis.

    The `held` case is the one worth reading: it appeals to the subterm at `f v`, which is
    the pullback, and to the caller-side term at `v`, which is the restriction. It is short
    because `(c.through f g).e v = c.e (f v)` holds by `Iff.rfl`. The `list` case is the
    repair of §5's container rows.

    **There is no hypothesis to discharge**, which is the whole of what the last two rows
    bought: `Adm_sound` is now `(Adm_exact t v).mpr`, and a new `Term` constructor cannot be
    added without a case here.

    Mutual with the list, option, slot and open-block companions, for the same reason
    `denote` is: a list's positions and a union's options are reached through a `List Term`
    and an object's slots through a *function*, and a single recursion on the term cannot
    follow either. -/
theorem Adm_exact : ∀ (t : Term), ExactV t
  -- the rows §5 excused, and not one of them needed excusing
  | .list pre sp suf =>
      ExactV_list (exactVL_mem pre (Adm_exactL pre)) (exactVO_mem sp (Adm_exactO sp))
        (exactVL_mem suf (Adm_exactL suf))
  | .object b => Adm_exactB b
  | .opaq => ExactV_opaq
  -- both recursive rows ask their own codec, and a closed variable is the bottom
  | .var _ => fun _ => Iff.rfl
  | .mu _ => fun _ => Iff.rfl
  -- both sides are empty, so the equivalence is `False ↔ False`
  | .never => fun _ => Iff.rfl
  -- the row the *constructor* made exact, rather than a sharper analysis of the old one
  | .set t => ExactV_set t
  -- the disjunction is exact given the options' exactness, which is the hypothesis this
  -- recursion hands it. See `ExactV_union`.
  | .union opts => ExactV_union (exactVL_mem opts (Adm_exactL opts))

  | .base k => by
      intro v; cases k <;> cases v <;> simp [Adm, inBase, denote, stringCodec, numberCodec,
        booleanCodec, binaryCodec, nullCodec]
  -- three rows into one, and `numberCodec` is read through `numberCodec_e_isSome` rather
  -- than unfolded: its `dite` is a string parser, and `simp` inside it runs out of heartbeats.
  | .literal k ls => by
      intro v
      cases k <;> cases v <;>
        simp [AdmLit, denote, denote, literalCodec, baseCodec, inL,
              stringCodec, booleanCodec, binaryCodec, nullCodec, inD]
  | .refine c p => by
      have hc := Adm_exact c
      intro v; cases hq : p.eval v <;> simp [Adm, denote, denote, Alg.Codec.restrict, hq, hc v]
  | .held c P f g => by
      have hc := Adm_exact c
      have hP := Adm_exact P
      intro v
      rw [show Adm (.held c P f g) v = (Adm c (f v) && Adm P v) from rfl, denote_held,
        restrict_e_isSome, Bool.and_eq_true, Bool.and_eq_true, hc (f v), hP v]
      exact And.comm

/-- The payload's own exactness, as a companion. An object's slots are reached through a
    function, so the recursion needs to land on a `Body` rather than on the `Term` that wraps
    one — the same reason the slot and open-block companions exist. -/
theorem Adm_exactB : ∀ (b : Body), ExactV (.object b)
  | .mk _ fld wild =>
      ExactV_object (fun k => Adm_exactF (fld k)) (exactVW_codec wild (Adm_exactW wild))

/-- The options' exactness, in the shape the recursion can produce it: a `∀ t ∈ ts` needs a
    membership hypothesis the structural checker cannot follow back to the constructor's
    argument, and this does not. -/
theorem Adm_exactL : ∀ (ts : List Term), ExactVL ts
  | [] => trivial
  | t0 :: ts => ⟨Adm_exact t0, Adm_exactL ts⟩

theorem Adm_exactO : ∀ (tail : Option Term), ExactVO tail
  | none => trivial
  | some t0 => Adm_exact t0

/-- A slot's row is exact when its term's is. -/
theorem Adm_exactF : ∀ (fd : ObjectSlot), ExactField fd
  | .req t0 => fun v => Adm_exact t0 v
  | .optional t0 => fun v => Adm_exact t0 v

theorem Adm_exactW : ∀ (wild : Option Term), ExactVW wild
  | none => trivial
  | some t0 => Adm_exact t0
end

/-- §5's empty-container argument, **derived**: the exact row still admits `[]`. -/
theorem Adm_array_nil (c : Term) : Adm (.array c) (.arr []) = true := by
  simp [Term.array, Adm, alignPL, alignP, zipP, AdmList, AdmOptT]

/-- …and it is strictly sharper than the `⊤` that was standing in for it. -/
theorem Adm_array_sharp : Adm (.array (.literal .string "A")) (.arr [.str "B"]) = false := by
  simp [Term.array, Adm, alignPL, alignP, zipP, AdmList, AdmOptT, AdmLit, inL]

/-- Nested, which the old row could not see at any depth. -/
theorem Adm_array_nested :
    Adm (.array (.array (.literal .string "A"))) (.arr [.arr [.str "B"]]) = false := by
  simp [Term.array, Adm, alignPL, alignP, zipP, AdmList, AdmOptT, AdmLit, inL]



/-- Soundness of every row — **now a corollary.**

    This was a hundred-and-twenty-line recursion on `Term.depth`, separate from `Adm_exact`
    because exactness was proved *given* the subterms' exactness and soundness could assume no
    such thing: `set` and `union` were loose, so a row over them had to be argued monotone
    instead. Both rows are exact now, `Adm_exact` carries no hypothesis, and the
    separate proof was proving the weaker half of something already available.

    The scaffolding it needed — ~~SoundV~~, ~~alignP_sound~~ and the per-constructor soundness
    lemmas — goes with it. -/
theorem Adm_sound (t : Term) {v a} (he : (denote t).e v = some a) : Adm t v = true :=
  (Adm_exact t v).mpr (by rw [he]; rfl)

/-! ### No escape hatch

**No row may be `false`, and there is nowhere to put an excuse.** An earlier apparatus —
~~Analysable~~, ~~Excuse~~ and their twins — forced a row per constructor and made adding a `false`
row cost a counterexample. `Adm_exact : ∀ t, ExactV t`, exhaustive over `Term` with no
hypothesis, forces a *proof* per constructor instead, which is the stronger form of the same
discipline: a new constructor cannot be added without one. -/

end

end Calculus
