import Calculus.Discharge
import Calculus.Soundness

/-!
# §5 — exactness on the value side

§5 used to state admission as a family of per-aspect tables, and every one of them was an
**over**-approximation. `⊤` is sound for every term, so a row that claims nothing can never
fail, and every defect caught in those tables was an imprecision rather than an
unsoundness. `Adm` is admission as a *domain* instead: exact at every constructor.
-/

namespace Calculus

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

/-- `⋀` over a container's elements. -/
def allP (P : VP) : List Value → Bool
  | [] => true
  | x :: xs => P x && allP P xs

/-- `⋁` over a union's options. -/
def anyP : List VP → Value → Bool
  | [], _ => false
  | P :: Ps, v => P v || anyP Ps v

/-- `align`'s row: the same length discipline — fixed head positionally, tail uniformly, a
    mismatch refused — asked of the rows rather than of the codecs. §5's `⊤` on any `.arr`
    ignored all three of those things. -/
def alignP : List VP → Option VP → List Value → Bool
  | [], none, [] => true
  | [], none, _ :: _ => false
  | [], some _, [] => true
  | [], some P, v :: vs => P v && alignP [] (some P) vs
  | _ :: _, _, [] => false
  | P :: Ps, tail, v :: vs => P v && alignP Ps tail vs

/-- The suffix's row: position for position, and a length mismatch refused. -/
def zipP : List VP → List Value → Bool
  | [], [] => true
  | P :: Ps, v :: vs => P v && zipP Ps vs
  | _, _ => false

/-- `alignL`'s row: the suffix splits off the right end, and what is left is `alignP`'s
    prefix-and-spread. A row shorter than the suffix takes `0` off the end, and `zipP`
    refuses it on the length, so no guard is owed. -/
def alignPL (pre : List VP) (sp : Option VP) (suf : List VP) (vs : List Value) : Bool :=
  alignP pre sp (vs.take (vs.length - suf.length))
    && zipP suf (vs.drop (vs.length - suf.length))

/-- `entryCodec`'s row: the slot a name declares, or else the open block's. `none` is an
    undeclared name in a body that declares no open block, and both sides refuse it. -/
def entryP (fs : MapOf VP) (rp : Option VP) (k : Name) : Option VP :=
  match fs.at k with | some P => some P | none => rp

/-- `objWrite`'s traversal, as a row: every entry goes through the codec its name names. -/
def objAdmV (fs : MapOf VP) (rp : Option VP) (keys : Finset Name)
    (g : {k // k ∈ keys} → Value) : Bool :=
  decide (∀ k : {k // k ∈ keys},
    (match entryP fs rp k.1 with | some P => P (g k) | none => false) = true)

/-- `valPresentB`'s guard, read off the *term*'s field table: only `optional` may be absent.
    Decidable over a `Finset Name`, which is why the excuse that named it never held. -/
def valPresentT (fields : Finset Name) (fld : {k // k ∈ fields} → ObjectSlot)
    (keys : Finset Name) : Bool :=
  decide (∀ k : {k // k ∈ fields},
    (match fld k with | .optional _ => true | _ => decide (k.1 ∈ keys)) = true)

/-- A `union` option's own admission. Every option decides by *attempt*, which is its row
    exactly when its row is exact — `admitOptV (specOf t,
    Adm t) v` reduces to `Adm t v`. `o.1` (`specOf`) goes unread here. -/
def admitOptV (o : Option (BodySpec) × VP) (v : Value) : Bool := o.2 v

/-- `select` at a `union`, as a row: the union admits where one of its options admits. -/
def selOptV (os : List (Option (BodySpec) × VP)) (v : Value) : Bool :=
  os.any (fun o => admitOptV o v)

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

/-! ## The one row that asks its own codec

    `opaque` is the language's escape hatch, and it is the row below that **does not
    describe a set at all**. It asks the codec it denotes:

        Adm  .opaq    v = ((opaqCodecω).e v).isSome
        AdmA .opaq    a = ((opaqCodecω).p a).isSome

    Three things follow.

    *It is exact by construction.* `denote`'s row sets `e := (opaqCodecω).e`, by
    `denote_opaq`, so the row and `dom(e)` are the same function, and `ExactV`/`ExactA` at
    the term is `Iff.rfl`. That is not a sharp analysis of an escape hatch; it is the
    analysis *declining* to be one, and the exactness is the codec's, borrowed.

    *It is as precise as the semantics is.* `opaqCodecω` recurses on the *input's own
    depth*, and a row over the term cannot see past the top constructor. Deferring sees all
    of it, because it does not look. The domain is every value (`opaq_total`).

    *Nothing here knows anything about the implementation.* Swap `opaqCodecω` for a
    different `opaque` — a different numeric policy, a different set of options, a different
    fuel discipline — and every theorem downstream is still true and still proved, because
    none of them mentions what the codec answers.

    ### The warranty behind the row

    `opaque` carries no premise. `Obligations .opaq = True`, and it is `True` because the
    laws are *theorems* here: `lawful_opaqCodecω` and `carrier_opaqCodecω`
    (`Opaque.lean`), off the stabilization and depth-preservation lemmas. The row asks a
    codec **the calculus warrants**, and owes nothing to whoever writes the term.

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
    `opaq`, and not a property of the calculus.

    ### And `lazy` is transparent, on both sides

    `denote (.lazy t) = { denote t with μ := none }`: the pair is the subterm's and only the
    member is erased, so both rows below pass straight through. The specification's §5
    lists `lazy` as unanalysable, and that is inherited from the document's
    thunk, which is `∗ → term`. `Term.lazy` carries a plain `Term` — a deliberate change,
    made because a closure adds no constructible term and defeats the termination checker
    (`Term.lean`) — so the model answers a question the document's `lazy` cannot be asked.
    The two constructors are not the same object and the section is right about its own. -/

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
  | .string   => fun v => match v with | .str _ => true | _ => false
  | .boolean  => fun v => match v with | .bool _ => true | _ => false
  | .binary   => fun v => match v with | .bin _ => true | _ => false
  | .null     => fun v => match v with | .null => true | _ => false
  | .number   => inD
  | .literal k ls => AdmLit k ls
  -- the bottom admits nothing, and the row is that sentence
  | .never => fun _ => false
  | .refine t p => fun v => Adm t v && p.eval v
  | .lazy t     => Adm t
  | .held t P f _ => fun v => Adm t (f v) && Adm P v
  -- `select`'s first admitter, mirrored: the row is the disjunction over `AdmSpecs`, so it
  -- mirrors `denoteList`'s pairing with `specOf`
  | .union opts => fun v => selOptV (AdmSpecs opts) v
  -- **`set` is a leaf, and exact.** Its base's row is `SetBase.adm` — the four ground rows
  -- of this table, indexed — and the set's row is that row over whichever payload the value
  -- carries. All three wire families are matched rather than gated on kind: a base admits at
  -- most one of them, and `℘⁺fin` has no empty inhabitant, so the other two answer `false`
  -- element by element. Homogeneity is the value type's and non-emptiness is `℘⁺fin`'s;
  -- what used to be missing was **injectivity**, and indexing supplies it — every base's
  -- element map is injective, so `encSet`'s collision guard never fires (`encSet_base_iff`).
  | .set b      => fun v =>
      match v with
      | .strSet S => decide (∀ s ∈ S.1, b.adm (.str s) = true)
      | .numSet S => decide (∀ d ∈ S.1, b.adm (.num d) = true)
      | .binSet S => decide (∀ y ∈ S.1, b.adm (.bin y) = true)
      | _ => false
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
  -- `denote .opaq` *is* `opaqCodecω`, so this is `dom(e)` rather than a
  -- description of it, and `ExactV_opaq` is `Iff.rfl`.
  --
  -- It replaces a hand-written recursion over the value (~~AdmOpaqV~~) that computed the
  -- same set. That recursion was correct and cost ~120 lines of proof, and it was the
  -- wrong shape for one reason: it stated `opaque`'s domain a *second* time, so a change
  -- to `opaqCodec` — a new option, a different numeric policy — meant editing two
  -- definitions that had to agree. Deferring leaves one.
  | .opaq => fun v => ((opaqCodecω).e v).isSome

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


/-- Each `union` option paired with its name spec — `denoteList`' mirror, the way
    ~~AdmTagged~~ mirrored ~~denoteTagged~~. `specOf` is what tells an object option from the
    rest, and it is a function of the term. -/
noncomputable def AdmSpecs : List Term → List (Option (BodySpec) × VP)
  | [] => []
  | t :: ts => (specOf t, Adm t) :: AdmSpecs ts

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

/-- A present name the body does not declare goes through the open block. `mem_fields_of_adm`'s
    twin: where that lemma reads a closed body's refusal, this reads an open body's claim. -/
theorem objAdmV_wild {c : Body} {keys : Finset Name} {g : {k // k ∈ keys} → Value}
    (hB : objAdmV ⟨c.fields, fun k => AdmField (c.at k)⟩ (AdmWild c.wild) keys g = true)
    {k : Name} (hk : k ∈ keys) (hnc : k ∉ c.fields) {w : Term}
    (hw : c.wild = some w) : Adm w (g ⟨k, hk⟩) = true := by
  unfold objAdmV at hB
  have hh := of_decide_eq_true hB ⟨k, hk⟩
  rwa [entryP, MapOf.at, dif_neg hnc, hw, AdmWild] at hh

/-- Every present name is declared, where the rest refuses an undeclared one. -/
theorem mem_fields_of_adm {b : Body} (hr : AdmWild b.wild = none)
    {keys : Finset Name} {g : {k // k ∈ keys} → Value}
    (h : AdmBody b (.map keys g) = true) : ∀ k ∈ keys, k ∈ b.fields := by
  rw [AdmBody_map, Bool.and_eq_true] at h
  have h2 := h.2
  unfold objAdmV at h2
  intro k hk
  refine Decidable.byContradiction (fun hnb => ?_)
  have hh := of_decide_eq_true h2 ⟨k, hk⟩
  rw [entryP, MapOf.at, dif_neg hnb, hr] at hh
  exact absurd hh (by simp)

/-- A field's row carries its literal alternatives, where it has any. -/
theorem altsOkV_of_AdmField {f : ObjectSlot} {v : Value} (h : AdmField f v = true) :
    altsOkV (altsOfField f) v = true := by
  cases f with
  | req t => cases t <;> first | rfl | exact h
  | optional t => cases t <;> first | rfl | exact h

/-- A term's row carries its literal alternatives, where it has any. `altsOkV_of_AdmField`'s
    twin at the term level, which is what an open block needs: the block carries a term and
    no mark. -/
theorem altsOkV_of_Adm {t : Term} {v : Value} (h : Adm t v = true) :
    altsOkV (altsOfTerm t) v = true := by
  cases t <;> first | rfl | exact h

/-- **An object's structural test is its row, open block and all.** A value the body admits
    passes `keysOk` and `literalsOk`.

    **No closedness premise, and none is needed.** `keysOk`'s first conjunct is free under an
    open block, so the claim that every present name is declared is owed by a closed body alone.
    `literalsOk` reads the block's alternatives at an undeclared name, and the block's own row
    is `Adm` of the block's term, which carries those alternatives. -/
theorem structural_of_AdmBody {b : Body}
    {keys : Finset Name} {g : {k // k ∈ keys} → Value}
    (h : AdmBody b (.map keys g) = true) :
    (keysOk b.spec keys && literalsOk b.spec keys g) = true := by
  have h' := h
  rw [AdmBody_map, Bool.and_eq_true] at h'
  cases hb : b with
  | mk fields fld wild =>
    subst hb
    refine Bool.and_eq_true _ _ |>.mpr ⟨?_, ?_⟩
    · refine keysOk_of_names ?_ (fun k hreq => ?_) (fun k hforbid hk => ?_)
      · cases hw : wild with
        | none => exact Or.inr (mem_fields_of_adm (by simp [Body.wild, hw, AdmWild]) h)
        | some _ => exact Or.inl rfl
      · cases hf : fld k with
        | req t =>
          apply mem_keys_of_isReq h'.1 k.2
          simp [Body.at, ObjectSlot.isReq, hf]
        | optional t =>
          rw [hf] at hreq
          cases t <;> simp [ObjectSlot.presence, Term.isNever] at hreq
      · have hrow := objAdmV_row h'.2 hk k.2
        change AdmField (fld k) (g ⟨k.1, hk⟩) = true at hrow
        cases hf : fld k with
        | req t =>
          rw [hf] at hforbid
          have ht : t = .never := by
            cases t <;> simp [ObjectSlot.presence, ObjectSlot.isReq, Term.isNever] at hforbid ⊢
          subst t
          rw [hf] at hrow
          simp [AdmField, Adm] at hrow
        | optional t =>
          rw [hf] at hforbid
          have ht : t = .never := by
            cases t <;> simp [ObjectSlot.presence, ObjectSlot.isReq, Term.isNever] at hforbid ⊢
          subst t
          rw [hf] at hrow
          simp [AdmField, Adm] at hrow
    · refine decide_eq_true (fun k => ?_)
      show litOkV _ k.1 (g k) = true
      cases hkf : decide (k.1 ∈ fields) with
      | true =>
        have hd := of_decide_eq_true hkf
        rw [litOkV, show (Body.spec (.mk fields fld wild)).names.at k.1
              = some ⟨_, altsOfField (fld ⟨k.1, hd⟩)⟩ from dif_pos hd]
        exact altsOkV_of_AdmField (objAdmV_row h'.2 k.2 hd)
      | false =>
        have hnd := of_decide_eq_false hkf
        cases hw : wild with
        | none =>
          exact absurd (mem_fields_of_adm (by simp [Body.wild, hw, AdmWild]) h k.1 k.2) hnd
        | some w =>
          have hat : (Body.spec (.mk fields fld (some w))).names.at k.1 = none := dif_neg hnd
          have hws : (Body.spec (.mk fields fld (some w))).wild = some (altsOfTerm w) := by
            simp [Body.spec]
          simp only [litOkV, hat, hws]
          exact altsOkV_of_Adm (objAdmV_wild h'.2 k.2 hnd hw)

@[simp] theorem AdmList_eq : ∀ ts : List Term, AdmList ts = ts.map Adm
  | [] => rfl
  | t :: ts => by simp only [AdmList, List.map]; rw [AdmList_eq ts]


@[simp] theorem AdmSpecs_eq : ∀ opts : List Term,
    AdmSpecs opts = opts.map fun t => (specOf t, Adm t)
  | [] => rfl
  | t :: ts => by simp only [AdmSpecs, List.map]; rw [AdmSpecs_eq ts]

/-- `⋁` of `Adm` over a union's options, named — sound, and *not* exact. -/
noncomputable def AdmAny (ts : List Term) (v : Value) : Bool := anyP (AdmList ts) v

@[simp] theorem AdmAny_nil (v : Value) : AdmAny [] v = false := rfl

@[simp] theorem AdmAny_cons (t : Term) (ts : List Term) (v : Value) :
    AdmAny (t :: ts) v = (Adm t v || AdmAny ts v) := rfl

theorem Adm_union (opts : List Term) (v : Value) :
    Adm (.union opts) v = selOptV (AdmSpecs opts) v := rfl

/-- An option that admits makes the disjunction true. -/
theorem AdmAny_of_mem {t : Term} {ts : List Term} {v : Value} (ht : t ∈ ts)
    (h : Adm t v = true) : AdmAny ts v = true := by
  induction ts with
  | nil => exact absurd ht (by simp)
  | cons t0 ts ih =>
    rcases List.mem_cons.mp ht with rfl | h'
    · simp [AdmAny_cons, h]
    · simp [AdmAny_cons, ih h']

/-- **The row is the disjunction**: a union admits where one of its options admits. -/
theorem selOptV_eq_AdmAny (opts : List Term) (v : Value) :
    selOptV (AdmSpecs opts) v = AdmAny opts v := by
  rw [AdmSpecs_eq]
  induction opts with
  | nil => rfl
  | cons t ts ih => simp only [selOptV, List.map_cons, List.any_cons] at ih ⊢; rw [ih]; rfl

/-- …read as the implication the containments need. -/
theorem selOptV_le_AdmAny {opts : List Term} {v : Value}
    (h : selOptV (AdmSpecs opts) v = true) : AdmAny opts v = true :=
  selOptV_eq_AdmAny opts v ▸ h

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


/-- A suffix row that holds pins the length. -/
theorem zipP_length : ∀ (Ps : List VP) (vs : List Value), zipP Ps vs = true → Ps.length = vs.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [zipP] at h
  | _ :: _, [], h => by simp [zipP] at h
  | _ :: Ps, _ :: vs, h => by
      simp only [zipP, Bool.and_eq_true] at h
      simp [zipP_length Ps vs h.2]

/-- A row of the wrong length holds nothing. -/
theorem zipP_false_of_length_ne (Ps : List VP) (ws : List Value) (h : Ps.length ≠ ws.length) :
    zipP Ps ws = false := by
  cases hz : zipP Ps ws with
  | false => rfl
  | true => exact absurd (zipP_length Ps ws hz) h

/-- Two rows of matching heads split. -/
theorem zipP_append : ∀ (a₁ b₁ : List VP) (a₂ b₂ : List Value), a₁.length = a₂.length →
    zipP (a₁ ++ b₁) (a₂ ++ b₂) = (zipP a₁ a₂ && zipP b₁ b₂)
  | [], _, [], _, _ => by simp [zipP]
  | P :: Ps, b₁, v :: vs, b₂, h => by
      simp only [List.cons_append, zipP, zipP_append Ps b₁ vs b₂ (by simpa using h)]
      exact (Bool.and_assoc _ _ _).symm

/-- With no spread, `alignP` IS the positionwise row: both refuse a length mismatch. -/
theorem alignP_none_eq_zipP : ∀ (pre : List VP) (ws : List Value),
    alignP pre none ws = zipP pre ws
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | _ :: Ps, _ :: vs => by simp only [alignP, zipP, alignP_none_eq_zipP Ps vs]

/-- A spread pads the row out to the value's length. -/
theorem alignP_some_eq_zipP : ∀ (pre : List VP) (c : VP) (ws : List Value),
    pre.length ≤ ws.length →
    alignP pre (some c) ws = zipP (pre ++ List.replicate (ws.length - pre.length) c) ws
  | [], _, [], _ => rfl
  | [], c, _ :: vs, _ => by
      have ih := alignP_some_eq_zipP [] c vs (Nat.zero_le _)
      simp only [List.length_nil, Nat.sub_zero, List.nil_append] at ih ⊢
      simp only [alignP, List.length_cons, List.replicate_succ, zipP, ih]
  | _ :: _, _, [], h => by simp at h
  | _ :: Ps, c, _ :: vs, h => by
      have ih := alignP_some_eq_zipP Ps c vs (by simpa using h)
      simp only [alignP, List.cons_append, zipP, List.length_cons,
        Nat.succ_sub_succ_eq_sub, ih]

/-- …and refuses a row shorter than its declared positions. -/
theorem alignP_short : ∀ (pre : List VP) (sp : Option VP) (ws : List Value),
    ws.length < pre.length → alignP pre sp ws = false
  | [], _, _, h => by simp at h
  | _ :: _, sp, [], _ => by cases sp <;> rfl
  | _ :: Ps, sp, _ :: vs, h => by
      simp only [alignP, alignP_short Ps sp vs (by simpa using h), Bool.and_false]

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
  all_goals simp [Adm, denote, listCodec]

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
    (match entryP ⟨fields, fun k => AdmField (fld k)⟩ (AdmWild wild) k with
      | some P => P v | none => false) = true ↔
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
    simp only [objectCodec, objectCodecCore, carriedCodec, mapV, objWrite,
      objAdmV, Bool.and_eq_true, decide_eq_true_eq, Option.isSome_map,
      Option.bind_some]
    by_cases hv : valPresentB ⟨fields, fun k => fieldSem (fld k)⟩ keys = true
    · rw [if_pos hv]
      simp only [hv, true_and, Option.isSome_map, funImage_isSome_iff]
      exact forall_congr' fun k => entry_iff hf hr k.1 (g k)
    · rw [if_neg hv]
      simp [hv]
  all_goals
    simp [Adm, AdmBody, denote, bodySem, objectCodec, objectCodecCore, carriedCodec, mapV]

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
    being claimed. `Adm .opaq` is `((opaqCodecω).e ·).isSome` and
    `denote .opaq` is `opaqCodecω`, so the two sides of the `↔` are the same
    Boolean and there is nothing to prove.

    This is exactness **earned by deferring**, not by a clever row: as a claim about the
    analysis it says the analysis of an escape hatch is that hatch's own answer, and
    nothing about what the answer is.
    What it replaced was a 120-line induction (~~AdmOpaqV_iff~~) proving a hand-written
    recursion over the value agreed with the codec at every budget that sees the value.
    That was a real theorem about `opaqCodec`; this is not one, and does not pretend to be.

    What is bought instead is decoupling: change `opaqCodecω` and this still holds, still
    by `rfl`. `opaq` is the one term for which that is true.

    The codec the row asks is warranted by the calculus:
    `Obligations .opaq = True`, because `lawful_opaqCodecω` and `carrier_opaqCodecω`
    (`Opaque.lean`) are proved. The deferral costs the writer of the term nothing. -/
theorem ExactV_opaq : ExactV .opaq := fun _ => Iff.rfl


/-- **`set` writes exactly what its row says**, which the constructor's old shape made
    false.

    Both directions run through `encSet_base_iff`, and the direction that used to fail is
    the interesting one: `encSet` refuses a *collision*, and a row over the elements cannot
    see one. At a base there is none to see — every base's element map is injective, by
    the host's round trip at `number` and by construction at the other three — so the guard
    never fires and the element conjunction is the whole domain.

    The three wire families are three cases rather than one because the payload types
    differ; the argument is the same in each. -/
theorem ExactV_set (b : SetBase) : ExactV (.set b) := by
  intro v
  cases v
  case strSet S =>
    show decide (∀ s ∈ S.1, b.adm (.str s) = true) = true
      ↔ (encSet b.elem Value.str S).isSome = true
    rw [decide_eq_true_eq, encSet_base_iff b (fun _ _ h => by injection h) S]
  case numSet S =>
    show decide (∀ d ∈ S.1, b.adm (.num d) = true) = true
      ↔ (encSet b.elem Value.num S).isSome = true
    rw [decide_eq_true_eq, encSet_base_iff b (fun _ _ h => by injection h) S]
  case binSet S =>
    show decide (∀ y ∈ S.1, b.adm (.bin y) = true) = true
      ↔ (encSet b.elem Value.bin S).isSome = true
    rw [decide_eq_true_eq, encSet_base_iff b (fun _ _ h => by injection h) S]
  all_goals exact Iff.intro (fun h => nomatch h) (fun h => nomatch h)

/-- Each option's row *is* its attempt — given that option's exactness, which is where the
    exactness hypothesis is spent. -/
theorem admitOptV_eq {t : Term} (h : ExactV t) (v : Value) :
    ((denote t).e v).isSome = admitOptV (specOf t, Adm t) v := by
  unfold admitOptV
  exact Bool.coe_iff_coe.mp (by simpa using (h v).symm)

/-- **The option list's filter is the term list's, mapped.** It is an induction rather than a
    rewrite because the agreement above is per-option and hypothesis-bearing. -/
theorem filter_AdmSpecs {opts : List Term} (h : ∀ t ∈ opts, ExactV t) (v : Value) :
    (denoteList opts).filter (fun c => (c.e v).isSome)
      = (opts.filter (fun t => admitOptV (specOf t, Adm t) v)).map denote := by
  induction opts with
  | nil => rfl
  | cons t ts ih =>
    have ht : ExactV t := h t (by simp)
    have hts : ∀ t' ∈ ts, ExactV t' := fun t' h' => h t' (by simp [h'])
    simp only [denoteList, List.filter_cons, admitOptV_eq ht, ih hts]
    cases hb : admitOptV (specOf t, Adm t) v <;> simp []

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
  show selOptV (AdmSpecs opts) v = true ↔ (select (denoteList opts) (·.e) v).isSome
  rw [selOptV_eq_AdmAny, select_isSome_attempt, denoteList_eq]
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
  -- both sides are empty, so the equivalence is `False ↔ False`
  | .never => fun _ => Iff.rfl
  -- the row the *constructor* made exact, rather than a sharper analysis of the old one
  | .set b => ExactV_set b
  -- the disjunction is exact given the options' exactness, which is the hypothesis this
  -- recursion hands it. See `ExactV_union`.
  | .union opts => ExactV_union (exactVL_mem opts (Adm_exactL opts))

  | .string => by intro v; cases v <;> simp [Adm, denote, denote, stringCodec]
  | .boolean => by intro v; cases v <;> simp [Adm, denote, denote, booleanCodec]
  | .binary => by intro v; cases v <;> simp [Adm, denote, denote, binaryCodec]
  | .null => by intro v; cases v <;> simp [Adm, denote, denote, nullCodec]
  | .number => by intro v; cases v <;> simp [Adm, denote, denote, inD]
  -- three rows into one, and `numberCodec` is read through `numberCodec_e_isSome` rather
  -- than unfolded: its `dite` is a string parser, and `simp` inside it runs out of heartbeats.
  | .literal k ls => by
      intro v
      cases k <;> cases v <;>
        simp [AdmLit, denote, denote, literalCodec, baseCodec, inL,
              stringCodec, booleanCodec, binaryCodec, nullCodec, inD]
  | .refine c p => by
      have hc := Adm_exact c
      intro v; cases hq : p.eval v <;> simp [Adm, denote, denote, Codec.restrict, hq, hc v]
  | .lazy c => by
      have hc := Adm_exact c
      intro v; simpa [Adm, denote] using hc v
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
