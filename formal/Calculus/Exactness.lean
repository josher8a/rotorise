import Calculus.Discharge
import Calculus.Soundness

/-!
# §5 — exactness: what `κ` and `adm` were computing between them

`κ`, `ident`, `adm` and `admA` are **over**-approximations, and that is the whole of the
problem this file exists to fix. `⊤` is sound for every term, so a row that claims nothing
is a row that can never fail, and every one of the defects in `docs/codec-formalization.md`
§4 is an imprecision rather than an unsoundness. A soundness obligation attached to each row
would have caught none of them: `fun _ => true` discharges it with `rfl`.

What catches them is the **converse** direction, and stating it turns up three things the
per-table form obscured.

* **Exactness is a property of the row, not of `adm`.** `adm .string` is `⊤`; it is `κ` that
  carries the kind. Neither is exact alone, and their conjunction is.
* **The conjunction does not survive `held`.** `f` may change a value's kind, so
  `κ (held t f g)` must be `none`, and there is no `κ` left to pair the subterm's `adm`
  with. The gate has to be absorbed into the row — `Adm (.held t f _) v = Adm t (f v)`.
* **The list rows were recursing on the wrong thing.** `array`, `record` and `union` took
  `⋀`/`⋁` of `adm` alone, where exactness needs `⋀`/`⋁` of the *joint* predicate. That is
  one defect with three faces, and it is why §5 could justify `⊤` at a container with an
  argument (the empty array) that is true and proves far less than it was asked to.

`Adm` below is that joint predicate as a single recursion. It is exact for nineteen of the
twenty-one constructors (`Adm_exact`); the other two are `Analysable`'s `false` rows, each
for a stated reason, and each with a witness here.

**Four of those `false` rows were never forced.** `tuple`, `object`, `dunion` and `opaq` were
excused on the strength of a reading — depth recursion, name admission, "the matched option's
own admission" — and in every case the exact row was expressible and simply unwritten. The
rows below are those four, and the deletions in the hatch are what they cost the excuses. The
one row that resisted is `union`, and it resisted for a reason no reading had reached: see the
note on `uniqueAdmission`.
-/

namespace Calculus

noncomputable section

/-! ## The rows a term's subterms hand up

`Adm t` is a *predicate*, and every container row below is a combinator on the predicates its
subterms compute — which is what `denote` does with codecs one level down. The shape is not a
matter of taste: `Term.object`'s field table is a **function**, `sizeOf` is blind to functions,
and a well-founded recursion therefore cannot reach a field's term. A structural recursion can,
and a structural recursion is what this shape buys — the same reason `denote` is structural and
`fieldSem`/`restSem` are its companions rather than its arguments.
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

/-- `entryCodec`'s row: the field a name declares, or else the rest policy's. `none` is an
    undeclared name under `drop` or `refuse` — which the *write* side refuses, `drop` being a
    read-side filter. -/
def entryP (fs : MapOf VP) (rp : Option VP) (k : Name) : Option VP :=
  match fs.at k with | some P => some P | none => rp

/-- `objWrite`'s traversal, as a row: every entry goes through the codec its name names. -/
def objAdmV (fs : MapOf VP) (rp : Option VP) (keys : Finset Name)
    (g : {k // k ∈ keys} → Value) : Bool :=
  decide (∀ k : {k // k ∈ keys},
    (match entryP fs rp k.1 with | some P => P (g k) | none => false) = true)

/-- `valPresentB`'s guard, read off the *term*'s field table: only `optional` may be absent.
    Decidable over a `Finset Name`, which is why the excuse that named it never held. -/
def valPresentT (fields : Finset Name) (fld : {k // k ∈ fields} → Field)
    (keys : Finset Name) : Bool :=
  decide (∀ k : {k // k ∈ fields},
    (match fld k with | .optional _ => true | _ => decide (k.1 ∈ keys)) = true)

/-- `select` at a `dunion`, as a row. The tag filter is **syntactic** — `tagsOf` is a function
    of the term — so the counting `select` does is available here, and the option the count
    lands on then answers for itself. The old row stopped at `allTags`, which is the *union* of
    the tag sets and so cannot see a tag two options answer to. -/
def selTagV (d : Name) (os : List (Finset String × VP)) (v : Value) : Bool :=
  match tagOfV d v with
  | none => false
  | some tag =>
    match os.filter (fun o => decide (tag ∈ o.1)) with
    | [o] => o.2 v
    | _ => false

/-- What the literal codec **writes**, exactly.

    `inL` is the prism, and at `number` that is not the whole story: with `Attr.n` carrying
    §1's `Numerals`, an alternative outside `D` is *held* and not *written*, so a row testing
    membership alone would over-claim. The second conjunct is that gap — the same (B) failure
    `LiteralD` exists to forbid in a derivable term, stated here as a fact about the codec,
    which has no premise to lean on.

    Uniform in the base rather than a case per base: `inL k ls (.num d)` can only hold at
    `k = .number`, so the numeral conjunct is `true` wherever it is not the point. -/
noncomputable def AdmLit (k : GroundKind) (ls : NEFinset k.Carrier) (v : Value) : Bool :=
  inL k ls v && (match v with | .num d => Numeral.WF d.toDec | _ => true)

mutual

/-- **The joint admission predicate.** What `κ` and `adm` compute between them, as one
    structural recursion — and the containers recurse with *this*, which is exactly what
    the old rows failed to do.

    One row is still a sound over-approximation and claims no exactness: `union`. `set` and
    `nullable` are the other two `Analysable`-false shapes, and their rows are the subterm
    recursion and the disjunction they always were. -/
noncomputable def Adm : Term → Value → Bool
  | .string   => fun v => match v with | .str _ => true | _ => false
  | .boolean  => fun v => match v with | .bool _ => true | _ => false
  | .binary   => fun v => match v with | .bin _ => true | _ => false
  | .null     => fun v => match v with | .null => true | _ => false
  | .number   => inD
  | .decimal  => isStored
  | .literal k ls => AdmLit k ls
  | .custom ce _ => fun v => (ce v).isSome
  | .array c  => fun v => match v with | .arr xs => allP (Adm c) xs | _ => false
  -- `record` needs no list companion either: `M`'s entries are a function on the key
  -- set, so "every entry admits" is one `decide` over that set, the way the three `set`
  -- rows are one `decide` over theirs.
  | .record c => fun v =>
      match v with | .map _ f => decide (∀ k, Adm c (f k) = true) | _ => false
  | .refine t q => fun v => Adm t v && q v
  | .legacy t _ => Adm t
  | .lazy t     => Adm t
  | .held t f _ => fun v => Adm t (f v)
  | .nullable t => fun v => Adm t v || (match v with | .null => true | _ => false)
  -- `union` is the one row that stays a disjunction, and the reason is `select`'s
  -- **anti-monotonicity** rather than any missing vocabulary — see `Excuse.uniqueAdmission`.
  | .union opts => fun v => anyP (AdmList opts) v
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
  | .tuple ts tail => fun v =>
      match v with | .arr vs => alignP (AdmList ts) (AdmOptT tail) vs | _ => false
  | .object fields fld rest => fun v =>
      match v with
      | .map keys g =>
          valPresentT fields fld keys &&
          objAdmV ⟨fields, fun k => AdmField (fld k)⟩ (AdmRest rest) keys g
      | _ => false
  | .dunion d opts => fun v => selTagV d (AdmTagged d opts) v
  -- **The second row that asks its own codec**, and the same row `adm` has
  -- (`Discharge.lean`): `denote (.opaq lossy)` *is* `opaqCodecω lossy`, so this is
  -- `dom(e)` rather than a description of it, and `ExactV_opaq` is `Iff.rfl`.
  --
  -- It replaces a hand-written recursion over the value (`AdmOpaqV`) that computed the
  -- same set. That recursion was correct and cost ~120 lines of proof, and it was the
  -- wrong shape for one reason: it stated `opaque`'s domain a *second* time, so a change
  -- to `opaqCodec` — a new option, a different numeric policy — meant editing two
  -- definitions that had to agree. Deferring leaves one.
  | .opaq lossy => fun v => ((opaqCodecω lossy).e v).isSome

/-- A field's row is its term's; the presence marker is `valPresentT`'s business, not this
    one's. Mirrors `fieldSem`, and for the same reason: the recursion has to be passed
    *applied*. -/
noncomputable def AdmField : Field → VP
  | .req t => Adm t
  | .optional t => Adm t
  | .fallback t _ => Adm t

/-- The rest policy's row, where it has one — `rcOf`'s mirror. `drop` and `refuse` have
    none, and an undeclared name is therefore refused on the way *out* under both. -/
noncomputable def AdmRest : Rest → Option VP
  | .drop => none
  | .refuse => none
  | .codec t => some (Adm t)

/-- The options' rows, in order — `denoteList`'s mirror. -/
noncomputable def AdmList : List Term → List VP
  | [] => []
  | t :: ts => Adm t :: AdmList ts

noncomputable def AdmOptT : Option Term → Option VP
  | none => none
  | some t => some (Adm t)

/-- Each `dunion` option paired with the tags it answers to — `denoteTagged`'s mirror. -/
noncomputable def AdmTagged (d : Name) : List Term → List (Finset String × VP)
  | [] => []
  | t :: ts => (tagsOf d t, Adm t) :: AdmTagged d ts

end

@[simp] theorem AdmList_eq : ∀ ts : List Term, AdmList ts = ts.map Adm
  | [] => rfl
  | t :: ts => by simp only [AdmList, List.map]; rw [AdmList_eq ts]

@[simp] theorem AdmTagged_eq : ∀ (d : Name) (opts : List Term),
    AdmTagged d opts = opts.map fun t => (tagsOf d t, Adm t)
  | _, [] => rfl
  | d, t :: ts => by simp only [AdmTagged, List.map]; rw [AdmTagged_eq d ts]

/-- `⋁` of `Adm` over a union's options, named — sound, and *not* exact. -/
noncomputable def AdmAny (ts : List Term) (v : Value) : Bool := anyP (AdmList ts) v

@[simp] theorem AdmAny_nil (v : Value) : AdmAny [] v = false := rfl

@[simp] theorem AdmAny_cons (t : Term) (ts : List Term) (v : Value) :
    AdmAny (t :: ts) v = (Adm t v || AdmAny ts v) := rfl

theorem Adm_union (opts : List Term) (v : Value) :
    Adm (.union opts) v = AdmAny opts v := rfl

/-- `Adm`'s literal row, named.

    Nothing should `simp [Adm]` at a literal: the row's pattern is *dependent* — `ls`'s type
    mentions `k` — so generating the table's equation lemmas across it is expensive enough to
    exhaust the heartbeat budget in proofs that used to close in one step. Stating the row once
    contains that cost, and every literal proof below rewrites with this instead. -/
@[simp] theorem Adm_literal (k : GroundKind) (ls : NEFinset k.Carrier) (v : Value) :
    Adm (.literal k ls) v = AdmLit k ls v := by unfold Adm; rfl

/-- §5's converse direction: the row is `dom(e)`, not merely a bound on it. -/
def ExactV (t : Term) : Prop := ∀ v, Adm t v = true ↔ ((denote t).e v).isSome

mutual
/-- The terms whose rows carry an exactness proof, subterms included. Three `false` rows are
    left, and each has a reason:

    * `union` — `select` admits only where **exactly one** option does, and the count is taken
      over `Adm`'s own answers, which over-approximate at the shape below. Sharpening the
      row to that count would make it *unsound* — see `Excuse.uniqueAdmission`.
    * `nullable` — `ownsNull` is a disjunction over *both* halves, so a read that reaches the
      null point suppresses the wrapper while the write still refuses it
      (`not_ExactV_nullable`).

    `tuple`, `object`, `dunion` and `opaq` used to be here. Nothing about their *shapes* put
    them here: the rows are written now, and the four excuses are deleted rather than
    re-argued. **`set` used to be here too**, and it left by a different door: not a sharper
    row over the same constructor, but a narrower constructor. `encSet` demands the element
    map be injective and no row of an arbitrary element *term* says so; a `SetBase` says it,
    at all four bases, so the row that was excused is now provable as written.

    This list is the escape hatch, and it is closed: a row cannot be left vague by
    accident, only by being added here, in the open. -/
def Analysable : Term → Bool
  | .string | .boolean | .binary | .null | .number | .decimal
  | .literal _ _ | .custom _ _ | .opaq _ => true
  | .array c | .record c | .refine c _ | .legacy c _ | .lazy c
  | .held c _ _ => Analysable c
  | .tuple ts tail => AnalysableL ts && AnalysableO tail
  | .dunion _ opts => AnalysableL opts
  | .object fields fld rest =>
      decide (∀ k : {k // k ∈ fields}, AnalysableF (fld k) = true) && AnalysableR rest
  | .set _ => true
  | .union _ | .nullable _ => false

def AnalysableL : List Term → Bool
  | [] => true
  | t :: ts => Analysable t && AnalysableL ts

def AnalysableO : Option Term → Bool
  | none => true
  | some t => Analysable t

def AnalysableF : Field → Bool
  | .req t => Analysable t
  | .optional t => Analysable t
  | .fallback t _ => Analysable t

def AnalysableR : Rest → Bool
  | .drop | .refuse => true
  | .codec t => Analysable t
end

def ExactVL : List Term → Prop
  | [] => True
  | t :: ts => ExactV t ∧ ExactVL ts

def ExactVO : Option Term → Prop
  | none => True
  | some t => ExactV t

def ExactVR : Rest → Prop
  | .drop | .refuse => True
  | .codec t => ExactV t

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

theorem exactVR_codec : ∀ (rest : Rest), ExactVR rest → ∀ t, rest = .codec t → ExactV t
  | .drop, _, t, h => nomatch h
  | .refuse, _, t, h => nomatch h
  | .codec t0, h, t, hc => by
      have : t = t0 := by injection hc.symm
      subst this; exact h

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

/-- A filter whose predicate never fires is empty. Written out rather than taken from
    `List.filter_eq_nil_iff`, which is proved classically — see `Calculus/Axioms.lean`, where
    that exact lemma is the example of how the base gets widened by accident. -/
theorem filter_eq_nil_of_all_false {α : Type} (p : α → Bool) (l : List α)
    (h : ∀ x, p x = false) : l.filter p = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.filter_cons, h a, ih]

theorem filter_map_comm {α β : Type} (f : α → β) (p : β → Bool) (l : List α) :
    (l.map f).filter p = (l.filter (fun a => p (f a))).map f := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p (f a) <;> simp [List.filter_cons, h, ih]

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
          simp [hal, ih]
        | some ps =>
          rw [hal] at ih
          simp only [hal, Option.map_some', Option.some_bind, Option.bind_some] at ih ⊢
          rw [traverse_cons_isSome, Bool.and_eq_true, ← ht v, ← ih]
  | t :: ts, [], _ => by
      cases tail <;> simp [alignP, AdmList, AdmOptT, align, denoteList, denoteOpt]
  | t :: ts, v :: vs, h => by
      have ht : ExactV t := h t (by simp)
      have ih := alignP_iff tail htl ts vs (fun t' ht' => h t' (by simp [ht']))
      simp only [alignP, AdmList, AdmOptT, align, denoteList, denoteOpt, Bool.and_eq_true]
      cases hal : align (denoteList ts) (denoteOpt tail) vs with
      | none =>
        simp only [hal, Option.map_none', Option.bind_none, Option.isSome_none] at ih ⊢
        simp at ih
        simp [ih]
      | some ps =>
        simp only [hal, Option.map_some', Option.some_bind, Option.bind_some] at ih ⊢
        rw [traverse_cons_isSome, Bool.and_eq_true, ← ht v, ← ih]



/-- **`tuple` is exact** once its components are. -/
theorem ExactV_tuple {ts : List Term} {tail : Option Term}
    (h : ∀ t ∈ ts, ExactV t) (htl : ∀ t ∈ tail, ExactV t) : ExactV (.tuple ts tail) := by
  intro v
  cases v
  case arr vs =>
    show alignP (AdmList ts) (AdmOptT tail) vs = true ↔
      (((align (denoteList ts) (denoteOpt tail) vs).bind
        (traverse fun cv => cv.1.e cv.2)).map Attr.l).isSome = true
    rw [alignP_iff tail htl ts vs h]
    cases (align (denoteList ts) (denoteOpt tail) vs).bind (traverse fun cv => cv.1.e cv.2) <;>
      simp
  all_goals simp [Adm, denote, tupleCodec]

/-- **`dunion` is exact** once its options are: the tag filter is syntactic, and the one
    option it lands on answers for itself. -/
theorem ExactV_dunion {d : Name} {opts : List Term}
    (h : ∀ t ∈ opts, ExactV t) : ExactV (.dunion d opts) := by
  intro v
  show selTagV d (AdmTagged d opts) v = true ↔
    (select ((denoteTagged d opts).map fun o => OptionSem.byTag d o.1 o.2)
      (·.admitV) (·.c.e) v).isSome = true
  simp only [selTagV, denoteTagged_eq, AdmTagged_eq, List.map_map, select]
  cases htag : tagOfV d v with
  | none =>
    have hz : ∀ t : Term, (OptionSem.byTag d (tagsOf d t) (denote t)).admitV v = false := by
      intro t; simp [OptionSem.byTag, htag]
    rw [filter_map_comm]
    simp only [Function.comp_def]
    rw [filter_eq_nil_of_all_false _ opts hz]
    simp
  | some tag =>
    have hfil : ((opts.map fun t => (OptionSem.byTag d (tagsOf d t) (denote t))).filter
        (·.admitV v))
        = (opts.filter (fun t => decide (tag ∈ tagsOf d t))).map
            (fun t => OptionSem.byTag d (tagsOf d t) (denote t)) := by
      have hpred : (fun a => (OptionSem.byTag d (tagsOf d a) (denote a)).admitV v)
          = (fun t => decide (tag ∈ tagsOf d t)) := by
        funext t; simp [OptionSem.byTag, htag]
      rw [filter_map_comm, hpred]
    have hfil2 : ((opts.map fun t => (tagsOf d t, Adm t)).filter
        (fun o => decide (tag ∈ o.1)))
        = (opts.filter (fun t => decide (tag ∈ tagsOf d t))).map
            (fun t => (tagsOf d t, Adm t)) := by
      rw [filter_map_comm]
    simp only [Function.comp_def, hfil, hfil2]
    cases hL : opts.filter (fun t => decide (tag ∈ tagsOf d t)) with
    | nil => simp
    | cons t rest =>
      cases rest with
      | nil =>
        have ht : t ∈ opts := List.mem_of_mem_filter (by rw [hL]; simp)
        simp only [List.map_cons, List.map_nil]
        exact h t ht v
      | cons t2 rest2 => simp

/-- A field's row is exact when the term it carries is. -/
def ExactField (fd : Field) : Prop :=
  ∀ v, AdmField fd v = true ↔ (((fieldSem fd).codec).e v).isSome

theorem valPresentT_eq (fields : Finset Name) (fld : {k // k ∈ fields} → Field)
    (keys : Finset Name) :
    valPresentT fields fld keys = valPresentB ⟨fields, fun k => fieldSem (fld k)⟩ keys := by
  simp only [valPresentT, valPresentB]
  congr 1
  apply propext
  constructor <;> intro h k <;> have := h k <;> cases hfd : fld k <;>
    simp_all [valPresentAt, fieldSem]

theorem entry_iff {fields : Finset Name} {fld : {k // k ∈ fields} → Field} {rest : Rest}
    (hf : ∀ k : {k // k ∈ fields}, ExactField (fld k))
    (hr : ∀ t, rest = .codec t → ExactV t) (k : Name) (v : Value) :
    (match entryP ⟨fields, fun k => AdmField (fld k)⟩ (AdmRest rest) k with
      | some P => P v | none => false) = true ↔
    ((entryCodec ⟨fields, fun k => fieldSem (fld k)⟩ (rcOf (restSem rest)) k).bind
      (fun c => c.e v)).isSome = true := by
  simp only [entryP, entryCodec, MapOf.at]
  by_cases hk : k ∈ fields
  · rw [dif_pos hk, dif_pos hk]
    simpa using hf ⟨k, hk⟩ v
  · rw [dif_neg hk, dif_neg hk]
    cases rest with
    | drop => simp [AdmRest, restSem, rcOf]
    | refuse => simp [AdmRest, restSem, rcOf]
    | codec t => simpa [AdmRest, restSem, rcOf] using hr t rfl v

/-- **`object` is exact** once its fields and its rest policy are. -/
theorem ExactV_object {fields : Finset Name} {fld : {k // k ∈ fields} → Field} {rest : Rest}
    (hf : ∀ k : {k // k ∈ fields}, ExactField (fld k))
    (hr : ∀ t, rest = .codec t → ExactV t) : ExactV (.object fields fld rest) := by
  intro v
  cases v
  case map keys g =>
    show (valPresentT fields fld keys &&
        objAdmV ⟨fields, fun k => AdmField (fld k)⟩ (AdmRest rest) keys g) = true ↔
      ((objectCodec ⟨fields, fun k => fieldSem (fld k)⟩ (restSem rest)).e (.map keys g)).isSome
        = true
    rw [valPresentT_eq]
    simp only [objectCodec, objectCodecCore, carriedCodec, mapV, Ctor.out, objWrite,
      objAdmV, Bool.and_eq_true, decide_eq_true_eq, Option.isSome_map',
      Option.some_bind, Option.bind_some]
    by_cases hv : valPresentB ⟨fields, fun k => fieldSem (fld k)⟩ keys = true
    · rw [if_pos hv]
      simp only [hv, true_and, Option.isSome_map', funImage_isSome_iff]
      exact forall_congr' fun k => entry_iff hf hr k.1 (g k)
    · rw [if_neg hv]
      simp [hv]
  all_goals
    simp [Adm, denote, objectCodec, objectCodecCore, carriedCodec, mapV, Ctor.out]

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
    being claimed. `Adm (.opaq lossy)` is `((opaqCodecω lossy).e ·).isSome` and
    `denote (.opaq lossy)` is `opaqCodecω lossy`, so the two sides of the `↔` are the same
    Boolean and there is nothing to prove.

    This is exactness **earned by deferring**, not by a clever row: as a claim about the
    analysis it is exactly the `custom` row's claim, which is to say it says the analysis
    of an escape hatch is the hatch's own answer, and nothing about what that answer is.
    What it replaced was a 120-line induction (`AdmOpaqV_iff`) proving a hand-written
    recursion over the value agreed with the codec at every budget that sees the value.
    That was a real theorem about `opaqCodec`; this is not one, and does not pretend to be.

    What is bought instead is decoupling: change `opaqCodecω` and this still holds, still
    by `rfl`. `custom` and `opaq` are exactly the terms for which that is true.

    They are **not** interchangeable, and the difference is on the other side of the row.
    `custom`'s codec is warranted by its user — `Obligations (.custom ce cp)` is a `Lawful`
    premise nothing here discharges. `opaque`'s is warranted by the calculus:
    `Obligations (.opaq _) = True`, because `lawful_opaqCodecω` and `carrier_opaqCodecω`
    (`Opaque.lean`) are proved. Same deferral, opposite warranty; `opaque` is the member of
    the pair that owes nothing. -/
theorem ExactV_opaq (lossy : Bool) : ExactV (.opaq lossy) := fun _ => Iff.rfl


/-- **`set` writes exactly what its row says**, which the constructor's old shape made
    false.

    Both directions run through `encSet_base_iff`, and the direction that used to fail is
    the interesting one: `encSet` refuses a *collision*, and a row over the elements cannot
    see one. At a base there is none to see — every base's element map is injective, by
    `Double.roundtrip` at `number` and by construction at the other three — so the guard
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

mutual
/-- **Nineteen of the twenty-one rows are exact.** Not a bound on `dom(e)` — `dom(e)`.

    The `held` case is the one worth reading: it appeals to the subterm at `f v`, which is
    the pullback, and it is one line because `(c.through f g).e v = c.e (f v)` holds by
    `Iff.rfl`. The `array` and `record` cases are the repair of §5's container rows, and the
    four cases after them are the rows the hatch used to hold.

    Mutual with the list, option, field and rest companions, for the same reason `denote` is:
    a tuple's components and a `dunion`'s options are reached through a `List Term` and an
    object's fields through a *function*, and a single recursion on the term cannot follow
    either. -/
theorem Adm_exact : ∀ (t : Term), Analysable t = true → ExactV t
  -- the four rows §5 excused, and none of them needed excusing
  | .tuple ts tail => by
      intro ha
      simp only [Analysable, Bool.and_eq_true] at ha
      exact ExactV_tuple (exactVL_mem ts (Adm_exactL ts ha.1))
        (exactVO_mem tail (Adm_exactO tail ha.2))
  | .dunion d opts => by
      intro ha
      exact ExactV_dunion
        (exactVL_mem opts (Adm_exactL opts (by simpa [Analysable] using ha)))
  | .object fields fld rest => by
      intro ha
      simp only [Analysable, Bool.and_eq_true, decide_eq_true_eq] at ha
      exact ExactV_object (fun k => Adm_exactF (fld k) (ha.1 k))
        (exactVR_codec rest (Adm_exactR rest ha.2))
  | .opaq lossy => fun _ => ExactV_opaq lossy
  -- the row the *constructor* made exact, rather than a sharper analysis of the old one
  | .set b => fun _ => ExactV_set b
  -- the two that are genuinely inexact, refuted by the hypothesis
  | .union _ => by intro ha; simp [Analysable] at ha
  | .nullable _ => by intro ha; simp [Analysable] at ha

  | .string => by intro _ v; cases v <;> simp [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, stringCodec]
  | .boolean => by intro _ v; cases v <;> simp [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, booleanCodec]
  | .binary => by intro _ v; cases v <;> simp [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, binaryCodec]
  | .null => by intro _ v; cases v <;> simp [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, nullCodec]
  | .number => by intro _ v; cases v <;> simp [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, inD]
  | .decimal => by intro _ v; cases v <;> simp [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, isStored]
  -- three rows into one, and `numberCodec` is read through `numberCodec_e_isSome` rather
  -- than unfolded: its `dite` is a string parser, and `simp` inside it runs out of heartbeats.
  | .literal k ls => by
      intro _ v
      cases k <;> cases v <;>
        simp [AdmLit, denote, denote, literalCodec, baseCodec, inL,
              stringCodec, booleanCodec, binaryCodec, nullCodec, inD]
  | .custom ce cp => by intro _ v; simp [Adm, denote, denote]
  | .array c => by
      intro ha
      have hc := Adm_exact c (by simpa [Analysable] using ha)
      intro v
      cases v
      case arr xs =>
        simp only [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, arrayCodec, Option.isSome_map]
        rw [AdmAll_iff hc, ← traverse_isSome_iff]
        cases traverse (denote c).e xs <;> simp
      all_goals simp [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, arrayCodec]
  | .record c => by
      intro ha
      have hc := Adm_exact c (by simpa [Analysable] using ha)
      intro v
      cases v
      -- The entry-key transport is gone with the traversal: `funImage` is defined
      -- exactly where every entry's `e` is, which is the row verbatim.
      case map keys f =>
        simp only [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, recordCodec, Option.isSome_map', decide_eq_true_eq,
          funImage_isSome_iff]
        exact forall_congr' fun k => hc (f k)
      -- the other nine rows are refused on both sides, and unfolding `recordCodec`'s
      -- `funImage` to see it is more work than reading it off the two `false`s
      all_goals simp only [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, recordCodec, Option.map_none',
        Option.isSome_none, Bool.false_eq_true]
  | .refine c q => by
      intro ha
      have hc := Adm_exact c (by simpa [Analysable] using ha)
      intro v; cases hq : q v <;> simp [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, Codec.restrict, hq, hc v]
  | .legacy c r => by
      intro ha
      have hc := Adm_exact c (by simpa [Analysable] using ha)
      intro v; simpa [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, Codec.extendRead] using hc v
  | .lazy c => by
      intro ha
      have hc := Adm_exact c (by simpa [Analysable] using ha)
      intro v; simpa [Adm, denote] using hc v
  | .held c f g => by
      intro ha
      have hc := Adm_exact c (by simpa [Analysable] using ha)
      intro v; simpa [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, Codec.through] using hc (f v)

/-- The options' exactness, in the shape the recursion can produce it: a `∀ t ∈ ts` needs a
    membership hypothesis the structural checker cannot follow back to the constructor's
    argument, and this does not. -/
theorem Adm_exactL : ∀ (ts : List Term), AnalysableL ts = true → ExactVL ts
  | [] => fun _ => trivial
  | t0 :: ts => by
      intro ha
      simp only [AnalysableL, Bool.and_eq_true] at ha
      exact ⟨Adm_exact t0 ha.1, Adm_exactL ts ha.2⟩

theorem Adm_exactO : ∀ (tail : Option Term), AnalysableO tail = true → ExactVO tail
  | none => fun _ => trivial
  | some t0 => by
      intro ha
      exact Adm_exact t0 (by simpa [AnalysableO] using ha)

/-- A field's row is exact when its term's is — the marker plays no part, which is what
    `valPresentT` being a separate conjunct records. -/
theorem Adm_exactF : ∀ (fd : Field), AnalysableF fd = true → ExactField fd
  | .req t0 => by intro ha v; exact Adm_exact t0 (by simpa [AnalysableF] using ha) v
  | .optional t0 => by intro ha v; exact Adm_exact t0 (by simpa [AnalysableF] using ha) v
  | .fallback t0 _ => by intro ha v; exact Adm_exact t0 (by simpa [AnalysableF] using ha) v

theorem Adm_exactR : ∀ (rest : Rest), AnalysableR rest = true → ExactVR rest
  | .drop => fun _ => trivial
  | .refuse => fun _ => trivial
  | .codec t0 => by
      intro ha
      exact Adm_exact t0 (by simpa [AnalysableR] using ha)
end

/-- §5's empty-container argument, **derived**: the exact row still admits `[]`. -/
theorem Adm_array_nil (c : Term) : Adm (.array c) (.arr []) = true := by
  simp [Adm, allP]

/-- …and it is strictly sharper than the `⊤` that was standing in for it. -/
theorem Adm_array_sharp : Adm (.array (.literal .string (.of "A" ∅))) (.arr [.str "B"]) = false := by
  simp [Adm, allP, AdmLit, inL, NEFinset.of]

/-- Nested, which the old row could not see at any depth. -/
theorem Adm_array_nested :
    Adm (.array (.array (.literal .string (.of "A" ∅)))) (.arr [.arr [.str "B"]]) = false := by
  simp [Adm, allP, AdmLit, inL, NEFinset.of]

/-- A migration whose *read* reaches the null point while its write does not. -/
def rNull : Attr → Option Value := fun a => match a with | .null => some (.str "x") | _ => none

/-- **Why `nullable` is in the hatch**, with a witness rather than an assertion.
    `ownsNull` is `(e null).isSome || (p null).isSome` — a disjunction over *both* halves.
    A `legacy` that reads the null point makes the guard fire, so `withNull` adds nothing,
    and the wrapper's `e` still refuses `null` — while any row of the shape
    `Adm t v || v = null` claims it. -/
theorem not_ExactV_nullable : ¬ ExactV (.nullable (.legacy .string rNull)) := by
  intro h
  have hadm : Adm (.nullable (.legacy .string rNull)) .null = true := by simp [Adm]
  have := (h .null).mp hadm
  simp only [denote, Codec.withNull, Codec.extendRead] at this
  simp [denote, Codec.withNull, Codec.ownsNull, Codec.extendRead, stringCodec, rNull] at this


/-! ## The hatch, made expensive

`Analysable`'s `false` rows are the last place a vague row can hide. The three exhaustive
recursions above already force a *row* per constructor, so a new `Term` constructor cannot
be added silently. What they do not force is a **reason**: the two `false` rows could be
three, and the third would cost one identifier and a docstring nobody has to write.

So the excuses are a type. `Excuse.covers` says which term shapes each one may be invoked
for, and `analysable_excused` — exhaustive over `Term` — says every `Analysable`-false term
has one. Filing `array` under `opaqueDepth` is then a type error, and adding a row to the
hatch means naming which of these four things is true of it, in the open, where a reviewer
reads the reason rather than trusting that one existed.

The type is three constructors shorter than it was. `opaqueDepth` and `nameAdmission` covered
`opaq`, `tuple` and `object`, all three of which are exact above, and `payloadShape` covered
`set`, whose *constructor* narrowed; an excuse with no user is an excuse with no content, so
all three are deleted rather than left standing over rows that no longer decline. `excuse_witnessed` could not have caught this — it asks for *some* term of a
covered shape on which exactness fails, and once the row is written there is none — which is
the residual softness its own docstring concedes, seen from the other side.

`covers`' catch-all is the one place a catch-all is right, and the polarity is why: it
answers **`false`** — *no excuse covers this* — so a new `Term` constructor lands in "no
excuse available" and `analysable_excused` forces `Analysable` to call it analysable, which
forces `Adm_exact` to prove it. The failure mode of every other catch-all in this
development was that it silently said yes. -/

/-- The two reasons a row may decline to be exact. There is no `other`, deliberately.

    There were four. `valueUnderRead` — "`q` tests the value a read *produces*, and no
    syntactic set of attributes bounds that" — covered `refine` on the attribute side, and
    was deleted when the row it excused turned out to be writable: a row may decode and then
    apply `q` (`refineReads`), so `refine` is exact on both sides and needs no reason. The
    sentence the excuse was named for is still true; it was never a reason.

    **`payloadShape` is the third deletion, and it went a different way.** It covered `set`
    on both sides, and its docstring gave one reason — "`encSet` demands the element map be
    **injective**, and no row of the elements alone says so". That was the *write* side's
    reason and it was only ever half the story: the read-side witness `not_ExactA_set` was
    `set(string)`, a typed, `Obligations`-discharged term whose inexactness had nothing to do
    with injectivity. Its cause was `AdmA (.set _)`, which admitted `.ss`, `.ns` and `.bs`
    whatever the element term was, because `setMember` sends one value kind to three
    attribute members and a row over an element term cannot say which. Two causes, one
    excuse, one of them unstated.

    Both die at the constructor rather than at the row. Indexing `set` by a `SetBase` makes
    every element map injective — so `encSet`'s collision guard cannot fire — and makes the
    wire family a function of the index — so the read row names one of the three. Neither
    row was sharpened; the shape they were excusing stopped existing. -/
inductive Excuse where
  /-- `select` admits only where **exactly one** option does, and the count that decides it
      is taken over the *rows*, not over `dom(e)`.

      This is **not** the obligation (U): (U) is what the laws need, and a row needs only
      counting — `(opts.filter (Adm · v)).length = 1` is written as easily as `⋁` is. What
      forbids it is that `Adm` must stay **sound at every term**, and at `set` and `nullable`
      it over-approximates. An over-counted filter is a filter that is *not* a singleton, so
      the sharper row would answer `false` where the union writes: sharpening `union` breaks
      soundness rather than improving precision. `dunion` escapes exactly because its filter
      is by *tag* and does not consult a row at all. The anti-monotonicity is `Continuity`'s,
      and this is where it bites. -/
  | uniqueAdmission
  /-- `ownsNull` is a disjunction over **both** halves, so a read that reaches the null
      point suppresses the wrapper while the write still refuses it. -/
  | nullOwnership
  deriving DecidableEq

/-- Which term shapes each excuse may be invoked for. The catch-all answers `false`, so a
    new constructor is *not* excusable by default — see the note above. -/
def Excuse.covers : Excuse → Term → Bool
  | .uniqueAdmission, .union _     => true
  | .nullOwnership,   .nullable _  => true
  | _, _ => false

/-- The answer a propagating row inherits: its children's, conjoined. The catch-all is
    `true` — "nothing to inherit" — so a new constructor must justify itself at the root
    rather than quietly borrowing a subterm's excuse.

    A `Term → Option Term` said this while every propagating row had exactly one subterm.
    `tuple`, `dunion` and `object` propagate too now, and their children are a list, a list
    and a *function on a `Finset`*; naming one of them would need a choice the axiom base does
    not have (`Finset.toList` is `Classical.choice`), so the row conjoins them instead. -/
def childrenAnalysable : Term → Bool
  | .array c | .record c | .refine c _ | .legacy c _ | .lazy c | .held c _ _ => Analysable c
  | .tuple ts tail => AnalysableL ts && AnalysableO tail
  | .dunion _ opts => AnalysableL opts
  | .object fields fld rest =>
      decide (∀ k : {k // k ∈ fields}, AnalysableF (fld k) = true) && AnalysableR rest
  | _ => true

/-- **Every row that declines exactness either names a reason of the right shape, or
    inherits the refusal from a subterm.** Exhaustive over `Term`, so growing the hatch
    means either producing an `Excuse` that covers the new shape — which requires extending
    `covers`, a visible act — or leaving this proof unclosed. There is no third branch and
    no `other` constructor to reach for. -/
theorem analysable_excused : ∀ (t : Term), Analysable t = false →
    (∃ e : Excuse, e.covers t = true) ∨ childrenAnalysable t = false
  | .union _, _     => .inl ⟨.uniqueAdmission, rfl⟩
  | .nullable _, _  => .inl ⟨.nullOwnership, rfl⟩
  -- The propagating rows decline only by inheritance, and say so — the four that used to
  -- name an excuse are here now, which is the whole of the change.
  | .array c, h | .record c, h | .refine c _, h | .legacy c _, h | .lazy c, h
  | .held c _ _, h => .inr (by simpa [childrenAnalysable, Analysable] using h)
  | .tuple _ _, h | .dunion _ _, h | .object _ _ _, h =>
      .inr (by simpa [childrenAnalysable, Analysable] using h)
  -- The exact rows: the hypothesis refutes them, which is the point — a term cannot both
  -- carry an exactness proof and claim an excuse.
  | .string, h | .boolean, h | .binary, h | .null, h | .number, h | .decimal, h
  | .literal _ _, h | .custom _ _, h | .opaq _, h | .set _, h => nomatch h

/-- **No excuse names an exact row.** The hatch cannot be used as a shortcut past an
    obligation that is provable: a covered shape really does decline. -/
theorem excuse_shapes (e : Excuse) (t : Term) (h : e.covers t = true) :
    Analysable t = false := by
  cases e <;> cases t <;> simp_all [Excuse.covers, Analysable]

/-- …stated the way a reviewer wants it: an exact row has no excuse available to it, so
    the two halves of `analysable_excused` are exclusive as well as exhaustive. -/
theorem not_excused_of_analysable {t : Term} (h : Analysable t = true) :
    ¬ ∃ e : Excuse, e.covers t = true := by
  rintro ⟨e, he⟩
  rw [excuse_shapes e t he] at h
  exact absurd h (by simp)

/-- Entrywise soundness lifted to a container's traversal. Generalised over the codec so
    the fueled and fuel-free forms share it. -/
theorem AdmAll_sound_aux {c : Term} {C : Codec}
    (hc : ∀ {v a}, C.e v = some a → Adm c v = true) :
    ∀ {xs : List Value} {ys}, traverse C.e xs = some ys → allP (Adm c) xs = true
  | [], _, _ => by simp [allP]
  | x :: xs, ys, h => by
      simp only [traverse] at h
      cases hx : C.e x with
      | none => rw [hx] at h; exact nomatch h
      | some y =>
        cases hxs : traverse C.e xs with
        | none => rw [hx, hxs] at h; exact nomatch h
        | some ys' => simp [allP, hc hx, AdmAll_sound_aux hc hxs]

/-! ### Soundness of the four repaired rows, and why it is a separate proof

Exactness was proved *given* the subterms' exactness. `Adm_sound` may assume no such thing —
it holds at every term, and at `set`, `nullable` and anything containing them the subterm's
row is loose. What carries the four rows across that gap is that each is **monotone** in the
rows it is built from: a conjunction of subterm answers (`tuple`, `object`), or one option's
answer behind a filter that does not consult a row at all (`dunion`), or no subterm at all
(`opaq`). Loosen a subterm and the row only loosens.

`union` is exactly the row that fails this test, which is why it keeps its excuse: its
`select` is a *count*, and a loosened option is one more admitting option, so the count that
would make it exact makes it refuse where the codec writes. That is `Continuity`'s
anti-monotonicity, arriving as a soundness obligation. -/

/-- The soundness half, as a predicate on a term. -/
def SoundV (t : Term) : Prop := ∀ v, ((denote t).e v).isSome = true → Adm t v = true

def SoundField (fd : Field) : Prop :=
  ∀ v, (((fieldSem fd).codec).e v).isSome = true → AdmField fd v = true

theorem alignP_sound (tail : Option Term) (htl : ∀ t ∈ tail, SoundV t) :
    ∀ (ts : List Term) (vs : List Value), (∀ t ∈ ts, SoundV t) →
      ((align (denoteList ts) (denoteOpt tail) vs).bind
        (traverse fun cv => cv.1.e cv.2)).isSome = true →
      alignP (AdmList ts) (AdmOptT tail) vs = true
  | [], [], _, _ => by cases tail <;> simp [alignP, AdmList, AdmOptT]
  | [], v :: vs, _, h => by
      cases htail : tail with
      | none => rw [htail] at h; simp [align, denoteOpt, denoteList] at h
      | some t =>
        have ht : SoundV t := htl t (by simp [htail])
        have ih := alignP_sound tail htl [] vs (by simp)
        rw [htail] at ih h
        simp only [AdmList, AdmOptT, denoteList, denoteOpt] at ih h ⊢
        simp only [alignP, Bool.and_eq_true]
        cases hal : align [] (some (denote t)) vs with
        | none =>
          simp only [align] at h
          rw [hal] at h
          simp at h
        | some ps =>
          rw [hal] at ih
          simp only [align, hal, Option.map_some', Option.some_bind, Option.bind_some] at h
          rw [traverse_cons_isSome, Bool.and_eq_true] at h
          exact ⟨ht v h.1, ih (by simp [h.2])⟩
  | t :: ts, [], _, h => by cases tail <;> simp [align, denoteList, denoteOpt] at h
  | t :: ts, v :: vs, hall, h => by
      have ht : SoundV t := hall t (by simp)
      have ih := alignP_sound tail htl ts vs (fun t' ht' => hall t' (by simp [ht']))
      simp only [alignP, AdmList, AdmOptT, Bool.and_eq_true]
      simp only [denoteList, align] at h
      cases hal : align (denoteList ts) (denoteOpt tail) vs with
      | none => rw [hal] at h; simp at h
      | some ps =>
        rw [hal] at ih
        simp only [hal, Option.map_some', Option.some_bind, Option.bind_some] at h
        rw [traverse_cons_isSome, Bool.and_eq_true] at h
        exact ⟨ht v h.1, ih (by simp [h.2])⟩

theorem entry_sound {fields : Finset Name} {fld : {k // k ∈ fields} → Field} {rest : Rest}
    (hf : ∀ k : {k // k ∈ fields}, SoundField (fld k))
    (hr : ∀ t, rest = .codec t → SoundV t) (k : Name) (v : Value)
    (h : ((entryCodec ⟨fields, fun k => fieldSem (fld k)⟩ (rcOf (restSem rest)) k).bind
      (fun c => c.e v)).isSome = true) :
    (match entryP ⟨fields, fun k => AdmField (fld k)⟩ (AdmRest rest) k with
      | some P => P v | none => false) = true := by
  simp only [entryP, entryCodec, MapOf.at] at h ⊢
  by_cases hk : k ∈ fields
  · rw [dif_pos hk] at h ⊢
    simpa using hf ⟨k, hk⟩ v (by simpa using h)
  · rw [dif_neg hk] at h ⊢
    cases rest with
    | drop => simp [rcOf, restSem] at h
    | refuse => simp [rcOf, restSem] at h
    | codec t => simpa [AdmRest, restSem, rcOf] using hr t rfl v (by simpa [rcOf, restSem] using h)

theorem Adm_tuple_sound {ts : List Term} {tail : Option Term}
    (h : ∀ t ∈ ts, SoundV t) (htl : ∀ t ∈ tail, SoundV t) : SoundV (.tuple ts tail) := by
  intro v hv
  cases v
  case arr vs =>
    show alignP (AdmList ts) (AdmOptT tail) vs = true
    refine alignP_sound tail htl ts vs h ?_
    replace hv : (((align (denoteList ts) (denoteOpt tail) vs).bind
      (traverse fun cv => cv.1.e cv.2)).map Attr.l).isSome = true := hv
    rwa [Option.isSome_map'] at hv
  all_goals simp [denote, tupleCodec] at hv

theorem Adm_object_sound {fields : Finset Name} {fld : {k // k ∈ fields} → Field} {rest : Rest}
    (hf : ∀ k : {k // k ∈ fields}, SoundField (fld k))
    (hr : ∀ t, rest = .codec t → SoundV t) : SoundV (.object fields fld rest) := by
  intro v hv
  cases v
  case map keys g =>
    show (valPresentT fields fld keys &&
      objAdmV ⟨fields, fun k => AdmField (fld k)⟩ (AdmRest rest) keys g) = true
    replace hv : ((objectCodec ⟨fields, fun k => fieldSem (fld k)⟩
      (restSem rest)).e (.map keys g)).isSome = true := hv
    rw [valPresentT_eq]
    simp only [objectCodec, objectCodecCore, carriedCodec, mapV, Ctor.out, objWrite,
      objAdmV, Bool.and_eq_true, decide_eq_true_eq, Option.isSome_map',
      Option.some_bind, Option.bind_some] at hv ⊢
    by_cases hvp : valPresentB ⟨fields, fun k => fieldSem (fld k)⟩ keys = true
    · rw [if_pos hvp] at hv
      rw [Option.isSome_map', funImage_isSome_iff] at hv
      exact ⟨hvp, fun k => entry_sound hf hr k.1 (g k) (hv k)⟩
    · rw [if_neg hvp] at hv; simp at hv
  all_goals
    simp [denote, objectCodec, objectCodecCore, carriedCodec, mapV, Ctor.out] at hv

theorem Adm_dunion_sound {d : Name} {opts : List Term}
    (h : ∀ t ∈ opts, SoundV t) : SoundV (.dunion d opts) := by
  intro v hv
  show selTagV d (AdmTagged d opts) v = true
  replace hv : (select ((denoteTagged d opts).map fun o => OptionSem.byTag d o.1 o.2)
      (·.admitV) (·.c.e) v).isSome = true := hv
  simp only [selTagV, denoteTagged_eq, AdmTagged_eq, List.map_map, select] at hv ⊢
  cases htag : tagOfV d v with
  | none =>
    have hz : ∀ t : Term, (OptionSem.byTag d (tagsOf d t) (denote t)).admitV v = false := by
      intro t; simp [OptionSem.byTag, htag]
    rw [filter_map_comm] at hv
    simp only [Function.comp_def] at hv
    rw [filter_eq_nil_of_all_false _ opts hz] at hv
    simp at hv
  | some tag =>
    have hpred : (fun t => (OptionSem.byTag d (tagsOf d t) (denote t)).admitV v)
        = (fun t => decide (tag ∈ tagsOf d t)) := by
      funext t; simp [OptionSem.byTag, htag]
    have hfil : ((opts.map fun t => (OptionSem.byTag d (tagsOf d t) (denote t))).filter
        (·.admitV v))
        = (opts.filter (fun t => decide (tag ∈ tagsOf d t))).map
            (fun t => OptionSem.byTag d (tagsOf d t) (denote t)) := by
      rw [filter_map_comm, hpred]
    have hfil2 : ((opts.map fun t => (tagsOf d t, Adm t)).filter
        (fun o => decide (tag ∈ o.1)))
        = (opts.filter (fun t => decide (tag ∈ tagsOf d t))).map
            (fun t => (tagsOf d t, Adm t)) := by
      rw [filter_map_comm]
    simp only [Function.comp_def, hfil, hfil2] at hv ⊢
    cases hL : opts.filter (fun t => decide (tag ∈ tagsOf d t)) with
    | nil => rw [hL] at hv; simp at hv
    | cons t rest =>
      cases rest with
      | nil =>
        have ht : t ∈ opts := List.mem_of_mem_filter (by rw [hL]; simp)
        rw [hL] at hv
        simp only [List.map_cons, List.map_nil] at hv ⊢
        exact h t ht v hv
      | cons t2 rest2 => rw [hL] at hv; simp at hv

theorem Adm_opaq_sound (lossy : Bool) : SoundV (.opaq lossy) :=
  fun v hv => (ExactV_opaq lossy v).mpr hv

set_option maxHeartbeats 1000000 in
-- the shared `term_depth_wf` block has alternatives this theorem's goals do not use
set_option linter.unreachableTactic false in
/-- Soundness of every row. The recursion is on `Term.depth`, which
    is what `κ_sound` and `adm_sound` do: a term recursion here makes the equation compiler
    elaborate all twenty-one heavy cases as one well-founded definition, and it does not
    finish. The heartbeat bump is for the twenty-one-way `cases`, not for any one case. -/
theorem Adm_sound : ∀ (t : Term) {v a},
    (denote t).e v = some a → Adm t v = true
  | t, v, a, he => by
    cases t
    case string => cases v <;> simp_all [Adm, denote, stringCodec]
    case boolean => cases v <;> simp_all [Adm, denote, booleanCodec]
    case binary => cases v <;> simp_all [Adm, denote, binaryCodec]
    case null => cases v <;> simp_all [Adm, denote, nullCodec]
    -- read off the write's `isSome` rather than unfolding the gate: the decision inside
    -- it is `Numeral.WF`'s parser
    case number =>
      have hs : (numberCodec.e v).isSome = true := by
        have h' : numberCodec.e v = some a := he
        rw [h']; rfl
      rw [numberCodec_e_isSome] at hs
      simpa [Adm] using hs
    case decimal =>
      have hs : (decimalCodec.e v).isSome = true := by
        have h' : decimalCodec.e v = some a := he
        rw [h']; rfl
      rw [decimalCodec_e_isSome] at hs
      simpa [Adm] using hs
    -- Three cases into one, and the numeric base no longer needs its own `show`: the codec
    -- **is** `(baseCodec k).restrict (inL k ls)`, so `restrict_e_isSome` and
    -- `numberCodec_e_isSome` answer it without `Codec.restrict` being unfolded into an `if`
    -- over `Numeral.WF`'s parser.
    case literal k ls =>
      have hs : ((denote (.literal k ls)).e v).isSome = true := by rw [he]; rfl
      clear he
      cases k <;> cases v <;>
        simp_all [AdmLit, denote, literalCodec, baseCodec, inL, stringCodec, inD,
                  booleanCodec, binaryCodec, nullCodec]
    case custom ce cp => simp_all [Adm, denote]
    -- the four repaired rows are sound because they are **exact** given the subterms'
    -- soundness, and each row is monotone in those — which is what `union` is not.
    case opaq lossy => exact Adm_opaq_sound lossy v (by rw [he]; rfl)
    -- the row is exact now, so soundness is one half of the `Iff` rather than a traversal
    case set b => exact (ExactV_set b v).mpr (by rw [he]; rfl)
    case tuple ts tl =>
      refine Adm_tuple_sound (fun t' ht' w hw => ?_) (fun t' ht' w hw => ?_) v (by rw [he]; rfl)
      · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hw
        exact Adm_sound t' hb
      · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hw
        exact Adm_sound t' hb
    -- `objectCodecCore` is `carriedCodec` now, so the non-`map` rows are refused by the
    -- value prism rather than by a traversal: `mapV.out` is what says so.
    case object fields fld rest =>
      have hf : ∀ k : {k // k ∈ fields}, SoundField (fld k) := by
        intro k w hw
        obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hw
        cases hfd : fld k with
        | req t0 => rw [hfd] at hb; exact Adm_sound t0 hb
        | optional t0 => rw [hfd] at hb; exact Adm_sound t0 hb
        | fallback t0 v0 => rw [hfd] at hb; exact Adm_sound t0 hb
      have hr : ∀ t0, rest = .codec t0 → SoundV t0 := by
        intro t0 hrest w hw
        obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hw
        exact Adm_sound t0 hb
      exact Adm_object_sound hf hr v (by rw [he]; rfl)
    case array c =>
      cases v
      case arr xs =>
        simp only [Adm]
        simp only [denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, arrayCodec] at he
        obtain ⟨ys, hys, -⟩ := Option.map_eq_some'.mp he
        exact AdmAll_sound_aux (fun {v a} h => Adm_sound c h) hys
      all_goals (simp only [denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, arrayCodec] at he; exact nomatch he)
    case record c =>
      cases v
      case map keys f =>
        simp only [Adm, decide_eq_true_eq]
        simp only [denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, recordCodec] at he
        obtain ⟨g, hg, -⟩ := Option.map_eq_some'.mp he
        exact fun k => Adm_sound c (funImage_some hg k)
      all_goals (simp only [denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, recordCodec] at he; exact nomatch he)
    case refine c q =>
      obtain ⟨hq, hc⟩ := restrict_e.mp he
      simp [Adm, Adm_sound c hc, hq]
    case legacy c r => simpa [Adm] using Adm_sound c (extendRead_e.mp he)
    case lazy c => simpa [Adm] using Adm_sound c he
    case held c f g => simpa [Adm] using Adm_sound c he
    case nullable c =>
      cases hw : (denote c).ownsNull with
      | true =>
        rw [show (denote (.nullable c)).e = (denote c).e from
          withNull_e_of_owns hw] at he
        simp [Adm, Adm_sound c he]
      | false =>
        rw [show denote (.nullable c) = (denote c).orNull from
          withNull_eq_orNull hw] at he
        rcases orNull_e.mp he with ⟨rfl, -⟩ | ⟨-, hc⟩
        · simp [Adm]
        · simp [Adm, Adm_sound c hc]
    case dunion d opts =>
      refine Adm_dunion_sound (fun t' ht' w hw => ?_) v (by rw [he]; rfl)
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hw
      exact Adm_sound t' hb
    case union opts =>
      simp only [denote, optionSems_eq] at he
      obtain ⟨o, ho, -, hoe⟩ := altCodec_e_admits he
      simp only [List.mem_map] at ho
      obtain ⟨tx, htx, rfl⟩ := ho
      rw [optionSemOf_c] at hoe
      -- the recursive call is taken **here**, before the generalisation: `key` quantifies over
      -- an arbitrary list containing `tx`, and a measure on the term cannot bound a call made
      -- inside that. With fuel it did not have to.
      have htx' : Adm tx v = true := Adm_sound tx hoe
      have key : ∀ (ts : List Term), tx ∈ ts → AdmAny ts v = true := by
        intro ts hts
        induction ts with
        | nil => exact absurd hts (by simp)
        | cons t0 ts ih =>
          rcases List.mem_cons.mp hts with rfl | h'
          · simp [AdmAny_cons, htx']
          · simp [AdmAny_cons, ih h']
      exact key opts htx

termination_by t _ _ => Term.depth t
decreasing_by term_depth_wf

/-! **Every row is a sound over-approximation, the hatch included.**

    `Adm_exact` binds the nineteen analysable rows to `dom(e)` in both directions. The other
    two had, until this theorem, *no* obligation at all: nothing stopped a hatch row being
    written `fun _ => false`, which would have been an outright unsoundness rather than the
    imprecision every defect in the log so far has been. A hatch row may be **loose**; it
    may not be **wrong**, and that is now checked. -/
/-! ### Every excuse earned

`Excuse` and `covers` say which rows may decline exactness. Nothing so far said the
declining was *warranted*: a constructor could be added naming a shape that is secretly
provable, and the hatch would absorb a row that ought to carry a proof.

So each excuse owes a witness — a term of a shape it covers, for which exactness genuinely
fails. `excuse_witnessed` collects them. Adding an excuse now costs a counterexample, and
for a shape that is exact there is none to be had.

**What this does not claim**, because the stronger reading is false: *not* every covered
term is inexact. `union []` is covered by `uniqueAdmission` and is perfectly exact — `Adm`
is `false` and so is admission, there being no option to admit. The obligation is that an
excuse names a real phenomenon, not that it is tight on every term of that shape. Widening
`covers` to a shape that is always exact is still caught; widening it to one that is
sometimes exact is not, and that is the residual softness.

**And that softness had already cost something.** `opaqueDepth` and `nameAdmission` each had
a witness here and were each covering a shape whose row is now exact: the witnesses were
terms on which the *old, loose* row over-claimed, not evidence that no exact row existed. A
witnessed excuse says the row as written is loose; it never said the row had to be. Both
constructors are deleted above, and the two witnesses (`not_ExactV_tuple`, `not_ExactV_opaq`
and their read-side twins) with them. -/

/-! `not_ExactV_set` stood here. It was `set(held(string, collapse, id))` — an element
adapter merging `"a"` and `"b"`, so every element writes and `encSet` refuses the collision —
and it is **unstatable** now: `Term.set` takes a `SetBase`, and no base has a colliding
element map. The witness is gone because the shape it witnessed is. -/

/-- **The counting failing in its purest form.** `select` writes only where *exactly one*
    option admits, so two copies of one option admit everything and write nothing — while `⋁`
    says yes. No arithmetic, no `Double`, just the counting `select` does.

    This is the row a count *would* fix and may not: see `Excuse.uniqueAdmission`. -/
theorem not_ExactV_union : ¬ ExactV (.union [.string, .string]) := by
  intro h
  have := (h (.str "a")).mp (by simp [Adm, anyP, AdmList])
  simp [denote, denote, optionSems, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, specOf, optionSemOf, altCodec, select,
    stringCodec] at this

/-- **Every excuse is earned.** Exhaustive over `Excuse`, so a new constructor must come
    with a term of a shape it covers on which exactness actually fails — which, for a shape
    that is exact, cannot be produced. -/
theorem excuse_witnessed : ∀ (e : Excuse) (t : Term), e.covers t = true →
    ∃ t' : Term, e.covers t' = true ∧ ¬ ExactV t'
  | .uniqueAdmission, _, _ => ⟨.union [.string, .string], rfl, not_ExactV_union⟩
  | .nullOwnership, _, _   => ⟨.nullable (.legacy .string rNull), rfl, not_ExactV_nullable⟩

/-! ## The attribute side

`Adm` is the value half. `admA` is the attribute half of §5's tables, and it has no
`Adm`-shaped counterpart — which is the first reason the analysis tables cannot simply be
renamed onto `Adm`. `AdmA` below is that counterpart's definition and its soundness proof.

The mirror is not symmetric, and the asymmetry that remains is §1's rather than this
file's: the numeric rows go through `Double.ofDec`, and `legacy` widens a read. `refine`
was listed here as a third — "cannot narrow a read" — and is not one: the row decodes and
then applies `q`. Each is a row here rather than a remark. -/

/-! ### The attribute side's rows, and the three that are not the value side's

The combinators below mirror the value side's one for one, with one genuine difference:
`objRead` filters the *stored* names through `keepB` before traversing — `drop` is a read-side
policy — so `objAdmA` carries the filter and `objAdmV` does not. The filter is written as an
implication over the key set rather than as a `Finset.filter` on the subtype, because the two
predicates (`keepB` on the denoted table, `keepT` on the term's) are equal and not
*definitionally* equal, and a filtered subtype would make that difference a transport. -/

/-- An attribute-side row, once the subterms' rows are known. -/
abbrev AP := Attr → Bool

def allPA (P : AP) : List Attr → Bool
  | [] => true
  | x :: xs => P x && allPA P xs

def anyPA : List AP → Attr → Bool
  | [], _ => false
  | P :: Ps, a => P a || anyPA Ps a

def alignPA : List AP → Option AP → List Attr → Bool
  | [], none, [] => true
  | [], none, _ :: _ => false
  | [], some _, [] => true
  | [], some P, a :: as => P a && alignPA [] (some P) as
  | _ :: _, _, [] => false
  | P :: Ps, tail, a :: as => P a && alignPA Ps tail as

def entryPA (fs : MapOf AP) (rp : Option AP) (k : Name) : Option AP :=
  match fs.at k with | some P => some P | none => rp

/-- `objRead`'s traversal, as a row: every *kept* entry goes through its name's codec. -/
def objAdmA (fs : MapOf AP) (rp : Option AP) (kn : Name → Bool) (keys : Finset Name)
    (g : {k // k ∈ keys} → Attr) : Bool :=
  decide (∀ k : {k // k ∈ keys}, kn k.1 = true →
    (match entryPA fs rp k.1 with | some P => P (g k) | none => false) = true)

/-- `reqPresentB`'s guard off the term's table: `fb` reads to its stand-in, so only `req`
    must be present. -/
def reqPresentT (fields : Finset Name) (fld : {k // k ∈ fields} → Field)
    (keys : Finset Name) : Bool :=
  decide (∀ k : {k // k ∈ fields},
    (match fld k with | .req _ => decide (k.1 ∈ keys) | _ => true) = true)

/-- `keepB`'s row: `drop` keeps declared names, the other two keep everything. -/
def keepT (rest : Rest) (fields : Finset Name) : Name → Bool :=
  match rest with
  | .drop => fun k => decide (k ∈ fields)
  | _ => fun _ => true

/-- `select` at a `dunion`, read side. -/
def selTagA (d : Name) (os : List (Finset String × AP)) (a : Attr) : Bool :=
  match tagOfA d a with
  | none => false
  | some tag =>
    match os.filter (fun o => decide (tag ∈ o.1)) with
    | [o] => o.2 a
    | _ => false

/-- What the literal codec **reads**, exactly.

    Three rows into one, and the `number` row is the only one that is not simply membership:
    the read goes through `Double.ofDec`, and `&& WF` is there because the base's own read is
    `number`'s restricted, so it refuses a numeral whose double re-spells outside `D` even when
    that double is in `ℓ`.

    §5's table row (`admALit` in `Discharge`) used to be `⊤` here, on the ground that a
    *syntactic* set of attributes does not bound a read through `Double.ofDec`. True, and it
    never made the row unwritable: `ofDec` is a function the row may call, exactly as this one
    does. The table's row now asks its codec, so the two rows **agree at every base**, and
    `AdmA_le_admA`'s numeric cases are `AdmA_exact` rather than the `rfl` a `⊤` used to make
    them. -/
noncomputable def AdmALit : (k : GroundKind) → NEFinset k.Carrier → Attr → Bool
  | .string,  ls, .s s    => decide (s ∈ ls.1)
  | .boolean, ls, .bool b => decide (b ∈ ls.1)
  | .binary,  ls, .b b    => decide (b ∈ ls.1)
  | .null,    _,  .null   => true
  | .number,  ls, .n x    => (match Double.ofDec x.1 with
                              | some d => decide (d ∈ ls.1) && Numeral.WF d.toDec
                              | none => false)
  | _, _, _ => false

/-- **What a set base reads.**

    Three bases answer concretely: `string` reads `SS` and nothing else, `binary` `BS`,
    `decimal` an `NS` every numeral of which is `Stored`. `number` **asks its codec** — the
    same move `admALit .number` (`Discharge.lean`) makes at the same base, and for a related
    but different reason.

    The reason is worth stating, because it is the one residue the re-indexing does *not*
    remove and it is not injectivity of `e`. `numberCodec.p` goes through `Double.ofDec`,
    which **rounds** (`Combinators.lean`), so two distinct stored numerals can read to the
    same double and `decSet`'s `Nodup` gate then refuses an `NS` every element of which
    reads. That is `e ∘ p ≠ id`, not `e` non-injective, and `numericHost` says nothing about
    whether it ever fires — it is decidable, through `Double.decEq`, and not describable
    syntactically, so the exact row is the codec's own answer. `AdmA` is already
    `noncomputable`, so this costs nothing it had not already spent. -/
noncomputable def AdmASet : SetBase → Attr → Bool
  | .string,  .ss _ => true
  | .binary,  .bs _ => true
  | .decimal, .ns S => decide (∀ x ∈ S.1, Numeral.Stored x.1 = true)
  | .number,  .ns S => (decSet numberCodec Attr.n S).isSome
  | _, _ => false

mutual

/-- **The joint admission predicate, attribute side.** The mirror of `Adm` across §1's
    asymmetry, and it is not a symmetric mirror — three rows differ in kind, not degree.

    * `number`, `literalN` and a numeric `literal` go through `Double.ofDec`, which is
      axiomatized. The domain is still *expressible* — `ofDec` is a function and this row
      may call it — at the cost of being `noncomputable`, which `adm` already was. These rows
      used to be sharper than §5's `⊤`; they are now equal to it, because the observation in
      the previous sentence is exactly the one §5's numeric rows were missing.
    * `refine` **does** narrow here, and the row that said it could not was wrong in the
      same way the numeric `⊤`s were. "`q` tests the value a read *produces*, and no
      syntactic set of attributes bounds that" is true of syntax and says nothing about a
      row, which may decode and then ask `q` (`refineReads`). Sound, and exact whenever the
      subterm's row is: `dom((c.restrict q).p)` is precisely `{a | ∃ v, c.p a = some v ∧ q v}`.
    * `legacy` is the read-side alternative: `p` is the subterm's channel falling back to
      `r`'s, and `r` is data the term carries — the asymmetry `not_admA_legacy` records, and
      the reason `adm` and `admA` split at all. -/
noncomputable def AdmA : Term → Attr → Bool
  | .string   => fun a => match a with | .s _ => true | _ => false
  | .boolean  => fun a => match a with | .bool _ => true | _ => false
  | .binary   => fun a => match a with | .b _ => true | _ => false
  | .null     => fun a => match a with | .null => true | _ => false
  | .number   => fun a =>
      match a with
      | .n x => (match Double.ofDec x.1 with
                 | some d => Numeral.WF d.toDec
                 | none => false)
      | _ => false
  | .decimal  => fun a => match a with | .n x => Numeral.Stored x.1 | _ => false
  | .literal k ls => AdmALit k ls
  | .custom _ cp => fun a => (cp a).isSome
  | .array c  => fun a => match a with | .l as => allPA (AdmA c) as | _ => false
  | .record c => fun a =>
      match a with | .m _ g => decide (∀ k, AdmA c (g k) = true) | _ => false
  | .held t _ _ => AdmA t
  | .lazy t   => AdmA t
  | .refine t q => fun a => AdmA t a && refineReads t q a
  -- hatch
  | .legacy t r => fun a => AdmA t a || (r a).isSome
  | .nullable t => fun a => AdmA t a || (match a with | .null => true | _ => false)
  | .union opts => fun a => anyPA (AdmAList opts) a
  -- **the row that used to admit all three wire families whatever the element term was.**
  -- With the base an index the family is a function of it, so this names one — and at
  -- `number` defers to the codec, for the rounding residue `AdmASet` documents.
  | .set b    => AdmASet b
  | .tuple ts tail => fun a =>
      match a with | .l as => alignPA (AdmAList ts) (AdmAOptT tail) as | _ => false
  | .object fields fld rest => fun a =>
      match a with
      | .m keys g =>
          reqPresentT fields fld keys &&
          objAdmA ⟨fields, fun k => AdmAField (fld k)⟩ (AdmARest rest)
            (keepT rest fields) keys g
      | _ => false
  | .dunion d opts => fun a => selTagA d (AdmATagged d opts) a
  -- the read side of the same deferral; see the `Adm` row and `ExactA_opaq`
  | .opaq lossy => fun a => ((opaqCodecω lossy).p a).isSome

noncomputable def AdmAField : Field → AP
  | .req t => AdmA t
  | .optional t => AdmA t
  | .fallback t _ => AdmA t

noncomputable def AdmARest : Rest → Option AP
  | .drop => none
  | .refuse => none
  | .codec t => some (AdmA t)

noncomputable def AdmAList : List Term → List AP
  | [] => []
  | t :: ts => AdmA t :: AdmAList ts

noncomputable def AdmAOptT : Option Term → Option AP
  | none => none
  | some t => some (AdmA t)

noncomputable def AdmATagged (d : Name) : List Term → List (Finset String × AP)
  | [] => []
  | t :: ts => (tagsOf d t, AdmA t) :: AdmATagged d ts

end

@[simp] theorem AdmAList_eq : ∀ ts : List Term, AdmAList ts = ts.map AdmA
  | [] => rfl
  | t :: ts => by simp only [AdmAList, List.map]; rw [AdmAList_eq ts]

@[simp] theorem AdmATagged_eq : ∀ (d : Name) (opts : List Term),
    AdmATagged d opts = opts.map fun t => (tagsOf d t, AdmA t)
  | _, [] => rfl
  | d, t :: ts => by simp only [AdmATagged, List.map]; rw [AdmATagged_eq d ts]

/-- `⋁` of `AdmA` over a union's options; sound, and inexact for the reason the value side
    gives. -/
noncomputable def AdmAAny (ts : List Term) (a : Attr) : Bool := anyPA (AdmAList ts) a

@[simp] theorem AdmAAny_nil (a : Attr) : AdmAAny [] a = false := rfl

@[simp] theorem AdmAAny_cons (t : Term) (ts : List Term) (a : Attr) :
    AdmAAny (t :: ts) a = (AdmA t a || AdmAAny ts a) := rfl

theorem AdmA_union (opts : List Term) (a : Attr) :
    AdmA (.union opts) a = AdmAAny opts a := rfl

/-- `AdmA`'s literal row, named — for the reason `Adm_literal` gives. -/
@[simp] theorem AdmA_literal (k : GroundKind) (ls : NEFinset k.Carrier) (a : Attr) :
    AdmA (.literal k ls) a = AdmALit k ls a := by unfold AdmA; rfl

/-! Two bases stated as standalone lemmas, with their carriers written out.

`GroundKind.Carrier` is reducible, so `NEFinset k.Carrier` at a *constructor* `k` is the same
type as `NEFinset Bytes` — but it is not the same *expression*, and `simp` inside the goal
re-derives that on every rewrite. At `binary` (`List UInt8`) and `null` (`Unit`) that was
enough to exhaust the heartbeat budget. Taking the carrier as a plain type in the statement
does the reduction once, at elaboration. -/

theorem AdmALit_binary_exact (ls : NEFinset Bytes) (a : Attr) :
    AdmA (.literal .binary ls) a = true ↔ ((denote (Term.literal .binary ls)).p a).isSome = true := by
  cases a <;>
    simp [AdmA_literal, AdmALit, denote, denote, literalCodec, baseCodec, Codec.restrict, inL,
          binaryCodec]

theorem AdmALit_null_exact (ls : NEFinset Unit) (a : Attr) :
    AdmA (.literal .null ls) a = true ↔ ((denote (Term.literal .null ls)).p a).isSome = true := by
  cases a <;>
    simp [AdmA_literal, AdmALit, denote, denote, literalCodec, baseCodec, Codec.restrict, inL,
          nullCodec]


/-- The converse direction on the attribute side: the row is `dom(p)`, not a bound on it. -/
def ExactA (t : Term) : Prop := ∀ a, AdmA t a = true ↔ ((denote t).p a).isSome

/-- **`set` reads exactly what its row says.**

    Four bases, eleven attribute constructors, and the argument is the same three moves in
    each cell: `decSet` succeeds on the branch the base's `p` lands in, and fails at the
    first element that base refuses (`decSet_isSome_false`). `number` is the cell that is
    `rfl`, because its row *is* the codec's answer — see `AdmASet` for why it has to be. -/
theorem ExactA_set (b : SetBase) : ExactA (.set b) := by
  intro a
  show AdmASet b a = true ↔ ((setCodec b.elem).p a).isSome = true
  cases a
  case ss S =>
    cases b
    case string =>
      have h : (decSet stringCodec Attr.s S).isSome = true :=
        decSet_isSome_str (fun _ _ => rfl) (fun _ _ _ _ _ h1 h2 => by
          simp only [stringCodec, Option.some_bind, vStr] at h1 h2
          exact (Option.some.inj h1).trans (Option.some.inj h2).symm)
      exact Iff.intro (fun _ => h) (fun _ => rfl)
    all_goals
      obtain ⟨x, hx⟩ := S.2
      simp only [AdmASet, SetBase.elem, setCodec]
      rw [decSet_isSome_false hx rfl]
  case ns S =>
    cases b
    case number => exact Iff.rfl
    case decimal =>
      show decide (∀ x ∈ S.1, Numeral.Stored x.1 = true) = true
        ↔ (decSet decimalCodec Attr.n S).isSome = true
      rw [decide_eq_true_eq]
      constructor
      · intro hst
        have hp : ∀ x ∈ S.1, (decimalCodec.p (Attr.n x)).bind vStr = some x.1 := by
          intro x hx
          show ((if Numeral.Stored x.1 then some (Value.str x.1) else none).bind vStr)
            = some x.1
          rw [if_pos (hst x hx)]; rfl
        refine decSet_isSome_str (fun x hx => by rw [hp x hx]; rfl) ?_
        intro x₁ h₁ x₂ h₂ y e₁ e₂
        rw [hp x₁ h₁] at e₁; rw [hp x₂ h₂] at e₂
        exact Subtype.ext ((Option.some.inj e₁).trans (Option.some.inj e₂).symm)
      · intro hd x hx
        by_contra hc
        have hn : decimalCodec.p (Attr.n x) = none := by
          show (if Numeral.Stored x.1 then some (Value.str x.1) else none) = none
          rw [if_neg hc]
        rw [decSet_isSome_false hx hn] at hd
        exact nomatch hd
    all_goals
      obtain ⟨x, hx⟩ := S.2
      simp only [AdmASet, SetBase.elem, setCodec]
      rw [decSet_isSome_false hx rfl]
  case bs S =>
    cases b
    case binary =>
      obtain ⟨x₀, hx₀⟩ := S.2
      have h : (decSet binaryCodec Attr.b S).isSome = true :=
        decSet_isSome_bin hx₀ rfl rfl (fun _ _ => rfl) (fun _ _ _ _ _ h1 h2 => by
          simp only [binaryCodec, Option.some_bind, vBin] at h1 h2
          exact (Option.some.inj h1).trans (Option.some.inj h2).symm)
      exact Iff.intro (fun _ => h) (fun _ => rfl)
    all_goals
      obtain ⟨x, hx⟩ := S.2
      simp only [AdmASet, SetBase.elem, setCodec]
      rw [decSet_isSome_false hx rfl]
  all_goals cases b <;> exact Iff.intro (fun h => nomatch h) (fun h => nomatch h)

theorem alignPA_iff (tail : Option Term) (htl : ∀ t ∈ tail, ExactA t) :
    ∀ (ts : List Term) (as : List Attr), (∀ t ∈ ts, ExactA t) →
      (alignPA (AdmAList ts) (AdmAOptT tail) as = true ↔
        ((align (denoteList ts) (denoteOpt tail) as).bind
          (traverse fun ca => ca.1.p ca.2)).isSome = true)
  | [], [], _ => by
      cases tail <;> simp [alignPA, AdmAList, AdmAOptT, align, denoteList, denoteOpt, traverse]
  | [], a :: as, _ => by
      cases htail : tail with
      | none => simp [alignPA, AdmAList, AdmAOptT, align, denoteList, denoteOpt]
      | some t =>
        have ht : ExactA t := htl t (by simp [htail])
        have ih := alignPA_iff tail htl [] as (by simp)
        rw [htail] at ih
        simp only [AdmAList, AdmAOptT, denoteList, denoteOpt] at ih
        simp only [alignPA, AdmAList, AdmAOptT, align, denoteList, denoteOpt,
          Bool.and_eq_true]
        cases hal : align [] (some (denote t)) as with
        | none =>
          rw [hal] at ih
          simp at ih
          simp [hal, ih]
        | some ps =>
          rw [hal] at ih
          simp only [hal, Option.map_some', Option.some_bind, Option.bind_some] at ih ⊢
          rw [traverse_cons_isSome, Bool.and_eq_true, ← ht a, ← ih]
  | t :: ts, [], _ => by
      cases tail <;> simp [alignPA, AdmAList, AdmAOptT, align, denoteList, denoteOpt]
  | t :: ts, a :: as, h => by
      have ht : ExactA t := h t (by simp)
      have ih := alignPA_iff tail htl ts as (fun t' ht' => h t' (by simp [ht']))
      simp only [alignPA, AdmAList, AdmAOptT, align, denoteList, denoteOpt, Bool.and_eq_true]
      cases hal : align (denoteList ts) (denoteOpt tail) as with
      | none =>
        simp only [hal, Option.map_none', Option.bind_none, Option.isSome_none] at ih ⊢
        simp at ih
        simp [ih]
      | some ps =>
        simp only [hal, Option.map_some', Option.some_bind, Option.bind_some] at ih ⊢
        rw [traverse_cons_isSome, Bool.and_eq_true, ← ht a, ← ih]

theorem ExactA_tuple {ts : List Term} {tail : Option Term}
    (h : ∀ t ∈ ts, ExactA t) (htl : ∀ t ∈ tail, ExactA t) : ExactA (.tuple ts tail) := by
  intro a
  cases a
  case l as =>
    show alignPA (AdmAList ts) (AdmAOptT tail) as = true ↔
      (((align (denoteList ts) (denoteOpt tail) as).bind
        (traverse fun ca => ca.1.p ca.2)).map Value.arr).isSome = true
    rw [alignPA_iff tail htl ts as h]
    cases (align (denoteList ts) (denoteOpt tail) as).bind (traverse fun ca => ca.1.p ca.2) <;>
      simp
  all_goals simp [AdmA, denote, tupleCodec]

theorem ExactA_dunion {d : Name} {opts : List Term}
    (h : ∀ t ∈ opts, ExactA t) : ExactA (.dunion d opts) := by
  intro a
  show selTagA d (AdmATagged d opts) a = true ↔
    (select ((denoteTagged d opts).map fun o => OptionSem.byTag d o.1 o.2)
      (·.admitA) (·.c.p) a).isSome = true
  simp only [selTagA, denoteTagged_eq, AdmATagged_eq, List.map_map, select]
  cases htag : tagOfA d a with
  | none =>
    have hz : ∀ t : Term, (OptionSem.byTag d (tagsOf d t) (denote t)).admitA a = false := by
      intro t; simp [OptionSem.byTag, htag]
    rw [filter_map_comm]
    simp only [Function.comp_def]
    rw [filter_eq_nil_of_all_false _ opts hz]
    simp
  | some tag =>
    have hpred : (fun t => (OptionSem.byTag d (tagsOf d t) (denote t)).admitA a)
        = (fun t => decide (tag ∈ tagsOf d t)) := by
      funext t; simp [OptionSem.byTag, htag]
    have hfil : ((opts.map fun t => (OptionSem.byTag d (tagsOf d t) (denote t))).filter
        (·.admitA a))
        = (opts.filter (fun t => decide (tag ∈ tagsOf d t))).map
            (fun t => OptionSem.byTag d (tagsOf d t) (denote t)) := by
      rw [filter_map_comm, hpred]
    have hfil2 : ((opts.map fun t => (tagsOf d t, AdmA t)).filter
        (fun o => decide (tag ∈ o.1)))
        = (opts.filter (fun t => decide (tag ∈ tagsOf d t))).map
            (fun t => (tagsOf d t, AdmA t)) := by
      rw [filter_map_comm]
    simp only [Function.comp_def, hfil, hfil2]
    cases hL : opts.filter (fun t => decide (tag ∈ tagsOf d t)) with
    | nil => simp
    | cons t rest =>
      cases rest with
      | nil =>
        have ht : t ∈ opts := List.mem_of_mem_filter (by rw [hL]; simp)
        simp only [List.map_cons, List.map_nil]
        exact h t ht a
      | cons t2 rest2 => simp

def ExactAField (fd : Field) : Prop :=
  ∀ a, AdmAField fd a = true ↔ (((fieldSem fd).codec).p a).isSome

theorem reqPresentT_eq (fields : Finset Name) (fld : {k // k ∈ fields} → Field)
    (keys : Finset Name) :
    reqPresentT fields fld keys = reqPresentB ⟨fields, fun k => fieldSem (fld k)⟩ keys := by
  simp only [reqPresentT, reqPresentB]
  congr 1
  apply propext
  constructor <;> intro h k <;> have := h k <;> cases hfd : fld k <;>
    simp_all [reqPresentAt, fieldSem]

theorem keepB_eq (fields : Finset Name) (fld : {k // k ∈ fields} → Field) (rest : Rest)
    (k : Name) :
    keepB (restSem rest) ⟨fields, fun k => fieldSem (fld k)⟩ k = keepT rest fields k := by
  cases rest with
  | drop =>
    simp only [keepB, keepT, restSem, MapOf.at]
    by_cases hk : k ∈ fields <;> simp [hk]
  | refuse => rfl
  | codec t => rfl

theorem entryA_iff {fields : Finset Name} {fld : {k // k ∈ fields} → Field} {rest : Rest}
    (hf : ∀ k : {k // k ∈ fields}, ExactAField (fld k))
    (hr : ∀ t, rest = .codec t → ExactA t) (k : Name) (a : Attr) :
    (match entryPA ⟨fields, fun k => AdmAField (fld k)⟩ (AdmARest rest) k with
      | some P => P a | none => false) = true ↔
    ((entryCodec ⟨fields, fun k => fieldSem (fld k)⟩ (rcOf (restSem rest)) k).bind
      (fun c => c.p a)).isSome = true := by
  simp only [entryPA, entryCodec, MapOf.at]
  by_cases hk : k ∈ fields
  · rw [dif_pos hk, dif_pos hk]
    simpa using hf ⟨k, hk⟩ a
  · rw [dif_neg hk, dif_neg hk]
    cases rest with
    | drop => simp [AdmARest, restSem, rcOf]
    | refuse => simp [AdmARest, restSem, rcOf]
    | codec t => simpa [AdmARest, restSem, rcOf] using hr t rfl a

theorem ExactA_object {fields : Finset Name} {fld : {k // k ∈ fields} → Field} {rest : Rest}
    (hf : ∀ k : {k // k ∈ fields}, ExactAField (fld k))
    (hr : ∀ t, rest = .codec t → ExactA t) : ExactA (.object fields fld rest) := by
  intro a
  cases a
  case m keys g =>
    show (reqPresentT fields fld keys &&
        objAdmA ⟨fields, fun k => AdmAField (fld k)⟩ (AdmARest rest)
          (keepT rest fields) keys g) = true ↔
      ((objectCodec ⟨fields, fun k => fieldSem (fld k)⟩ (restSem rest)).p (.m keys g)).isSome
        = true
    rw [reqPresentT_eq]
    simp only [objectCodec, objectCodecCore, carriedCodec, mA, Ctor.out, objRead,
      objAdmA, Bool.and_eq_true, decide_eq_true_eq, Option.isSome_map',
      Option.some_bind, Option.bind_some]
    by_cases hv : reqPresentB ⟨fields, fun k => fieldSem (fld k)⟩ keys = true
    · rw [if_pos hv]
      simp only [hv, true_and, Option.isSome_map', funImage_isSome_iff]
      constructor
      · intro h k
        refine (entryA_iff hf hr k.1 _).mp ?_
        refine h ⟨k.1, (Finset.mem_filter.mp k.2).1⟩ ?_
        rw [← keepB_eq fields fld rest]
        exact (Finset.mem_filter.mp k.2).2
      · intro h k hk
        refine (entryA_iff hf hr k.1 (g k)).mpr ?_
        have hmem : k.1 ∈ keys.filter (keepB (restSem rest) ⟨fields, fun k => fieldSem (fld k)⟩ ·) :=
          Finset.mem_filter.mpr ⟨k.2, by rw [keepB_eq fields fld rest]; exact hk⟩
        exact h ⟨k.1, hmem⟩
    · rw [if_neg hv]
      simp [hv]
  all_goals
    simp [AdmA, denote, objectCodec, objectCodecCore, carriedCodec, mA, Ctor.out]

/-- **`opaque` reads exactly what its row says**, definitionally, and for the reason
    `ExactV_opaq` gives at length: `p := (opaqCodecω lossy).p`, so the row and `dom(p)` are
    one function. `AdmOpaqA_iff` — a second induction, this one carrying an injectivity
    clause about `Double.ofDec` that `decSet` needs — is deleted rather than moved. The
    clause was true and is still true; it is now the codec's business, where it was always
    stated (`decSet`, `Combinators.lean`), instead of being restated here in a form that had
    to be kept in step by hand. -/
theorem ExactA_opaq (lossy : Bool) : ExactA (.opaq lossy) := fun _ => Iff.rfl

def SoundA (t : Term) : Prop := ∀ a, ((denote t).p a).isSome = true → AdmA t a = true

def SoundAField (fd : Field) : Prop :=
  ∀ a, (((fieldSem fd).codec).p a).isSome = true → AdmAField fd a = true

theorem alignPA_sound (tail : Option Term) (htl : ∀ t ∈ tail, SoundA t) :
    ∀ (ts : List Term) (as : List Attr), (∀ t ∈ ts, SoundA t) →
      ((align (denoteList ts) (denoteOpt tail) as).bind
        (traverse fun ca => ca.1.p ca.2)).isSome = true →
      alignPA (AdmAList ts) (AdmAOptT tail) as = true
  | [], [], _, _ => by cases tail <;> simp [alignPA, AdmAList, AdmAOptT]
  | [], a :: as, _, h => by
      cases htail : tail with
      | none => rw [htail] at h; simp [align, denoteOpt, denoteList] at h
      | some t =>
        have ht : SoundA t := htl t (by simp [htail])
        have ih := alignPA_sound tail htl [] as (by simp)
        rw [htail] at ih h
        simp only [AdmAList, AdmAOptT, denoteList, denoteOpt] at ih h ⊢
        simp only [alignPA, Bool.and_eq_true]
        cases hal : align [] (some (denote t)) as with
        | none =>
          simp only [align] at h
          rw [hal] at h
          simp at h
        | some ps =>
          rw [hal] at ih
          simp only [align, hal, Option.map_some', Option.some_bind, Option.bind_some] at h
          rw [traverse_cons_isSome, Bool.and_eq_true] at h
          exact ⟨ht a h.1, ih (by simp [h.2])⟩
  | t :: ts, [], _, h => by cases tail <;> simp [align, denoteList, denoteOpt] at h
  | t :: ts, a :: as, hall, h => by
      have ht : SoundA t := hall t (by simp)
      have ih := alignPA_sound tail htl ts as (fun t' ht' => hall t' (by simp [ht']))
      simp only [alignPA, AdmAList, AdmAOptT, Bool.and_eq_true]
      simp only [denoteList, align] at h
      cases hal : align (denoteList ts) (denoteOpt tail) as with
      | none => rw [hal] at h; simp at h
      | some ps =>
        rw [hal] at ih
        simp only [hal, Option.map_some', Option.some_bind, Option.bind_some] at h
        rw [traverse_cons_isSome, Bool.and_eq_true] at h
        exact ⟨ht a h.1, ih (by simp [h.2])⟩

theorem entryA_sound {fields : Finset Name} {fld : {k // k ∈ fields} → Field} {rest : Rest}
    (hf : ∀ k : {k // k ∈ fields}, SoundAField (fld k))
    (hr : ∀ t, rest = .codec t → SoundA t) (k : Name) (a : Attr)
    (h : ((entryCodec ⟨fields, fun k => fieldSem (fld k)⟩ (rcOf (restSem rest)) k).bind
      (fun c => c.p a)).isSome = true) :
    (match entryPA ⟨fields, fun k => AdmAField (fld k)⟩ (AdmARest rest) k with
      | some P => P a | none => false) = true := by
  simp only [entryPA, entryCodec, MapOf.at] at h ⊢
  by_cases hk : k ∈ fields
  · rw [dif_pos hk] at h ⊢
    simpa using hf ⟨k, hk⟩ a (by simpa using h)
  · rw [dif_neg hk] at h ⊢
    cases rest with
    | drop => simp [rcOf, restSem] at h
    | refuse => simp [rcOf, restSem] at h
    | codec t =>
      simpa [AdmARest, restSem, rcOf] using hr t rfl a (by simpa [rcOf, restSem] using h)

theorem AdmA_tuple_sound {ts : List Term} {tail : Option Term}
    (h : ∀ t ∈ ts, SoundA t) (htl : ∀ t ∈ tail, SoundA t) : SoundA (.tuple ts tail) := by
  intro a ha
  cases a
  case l as =>
    show alignPA (AdmAList ts) (AdmAOptT tail) as = true
    refine alignPA_sound tail htl ts as h ?_
    replace ha : (((align (denoteList ts) (denoteOpt tail) as).bind
      (traverse fun ca => ca.1.p ca.2)).map Value.arr).isSome = true := ha
    rwa [Option.isSome_map'] at ha
  all_goals simp [denote, tupleCodec] at ha

theorem AdmA_object_sound {fields : Finset Name} {fld : {k // k ∈ fields} → Field} {rest : Rest}
    (hf : ∀ k : {k // k ∈ fields}, SoundAField (fld k))
    (hr : ∀ t, rest = .codec t → SoundA t) : SoundA (.object fields fld rest) := by
  intro a ha
  cases a
  case m keys g =>
    show (reqPresentT fields fld keys &&
      objAdmA ⟨fields, fun k => AdmAField (fld k)⟩ (AdmARest rest)
        (keepT rest fields) keys g) = true
    replace ha : ((objectCodec ⟨fields, fun k => fieldSem (fld k)⟩
      (restSem rest)).p (.m keys g)).isSome = true := ha
    rw [reqPresentT_eq]
    simp only [objectCodec, objectCodecCore, carriedCodec, mA, Ctor.out, objRead,
      objAdmA, Bool.and_eq_true, decide_eq_true_eq, Option.isSome_map',
      Option.some_bind, Option.bind_some] at ha ⊢
    by_cases hrp : reqPresentB ⟨fields, fun k => fieldSem (fld k)⟩ keys = true
    · rw [if_pos hrp] at ha
      rw [Option.isSome_map', funImage_isSome_iff] at ha
      refine ⟨hrp, fun k hk => ?_⟩
      have hmem : k.1 ∈ keys.filter
          (keepB (restSem rest) ⟨fields, fun k => fieldSem (fld k)⟩ ·) :=
        Finset.mem_filter.mpr ⟨k.2, by rw [keepB_eq fields fld rest]; exact hk⟩
      exact entryA_sound hf hr k.1 (g k) (ha ⟨k.1, hmem⟩)
    · rw [if_neg hrp] at ha; simp at ha
  all_goals
    simp [denote, objectCodec, objectCodecCore, carriedCodec, mA, Ctor.out] at ha

theorem AdmA_dunion_sound {d : Name} {opts : List Term}
    (h : ∀ t ∈ opts, SoundA t) : SoundA (.dunion d opts) := by
  intro a ha
  show selTagA d (AdmATagged d opts) a = true
  replace ha : (select ((denoteTagged d opts).map fun o => OptionSem.byTag d o.1 o.2)
      (·.admitA) (·.c.p) a).isSome = true := ha
  simp only [selTagA, denoteTagged_eq, AdmATagged_eq, List.map_map, select] at ha ⊢
  cases htag : tagOfA d a with
  | none =>
    have hz : ∀ t : Term, (OptionSem.byTag d (tagsOf d t) (denote t)).admitA a = false := by
      intro t; simp [OptionSem.byTag, htag]
    rw [filter_map_comm] at ha
    simp only [Function.comp_def] at ha
    rw [filter_eq_nil_of_all_false _ opts hz] at ha
    simp at ha
  | some tag =>
    have hpred : (fun t => (OptionSem.byTag d (tagsOf d t) (denote t)).admitA a)
        = (fun t => decide (tag ∈ tagsOf d t)) := by
      funext t; simp [OptionSem.byTag, htag]
    have hfil : ((opts.map fun t => (OptionSem.byTag d (tagsOf d t) (denote t))).filter
        (·.admitA a))
        = (opts.filter (fun t => decide (tag ∈ tagsOf d t))).map
            (fun t => OptionSem.byTag d (tagsOf d t) (denote t)) := by
      rw [filter_map_comm, hpred]
    have hfil2 : ((opts.map fun t => (tagsOf d t, AdmA t)).filter
        (fun o => decide (tag ∈ o.1)))
        = (opts.filter (fun t => decide (tag ∈ tagsOf d t))).map
            (fun t => (tagsOf d t, AdmA t)) := by
      rw [filter_map_comm]
    simp only [Function.comp_def, hfil, hfil2] at ha ⊢
    cases hL : opts.filter (fun t => decide (tag ∈ tagsOf d t)) with
    | nil => rw [hL] at ha; simp at ha
    | cons t rest =>
      cases rest with
      | nil =>
        have ht : t ∈ opts := List.mem_of_mem_filter (by rw [hL]; simp)
        rw [hL] at ha
        simp only [List.map_cons, List.map_nil] at ha ⊢
        exact h t ht a ha
      | cons t2 rest2 => rw [hL] at ha; simp at ha

theorem AdmA_opaq_sound (lossy : Bool) : SoundA (.opaq lossy) :=
  fun a ha => (ExactA_opaq lossy a).mpr ha

/-- Entrywise soundness lifted to a container's traversal, attribute side. -/
theorem AdmAAll_sound_aux {c : Term} {C : Codec}
    (hc : ∀ {a v}, C.p a = some v → AdmA c a = true) :
    ∀ {as : List Attr} {vs}, traverse C.p as = some vs → allPA (AdmA c) as = true
  | [], _, _ => by simp [allPA]
  | x :: as, vs, h => by
      simp only [traverse] at h
      cases hx : C.p x with
      | none => rw [hx] at h; exact nomatch h
      | some y =>
        cases hxs : traverse C.p as with
        | none => rw [hx, hxs] at h; exact nomatch h
        | some vs' => simp [allPA, hc hx, AdmAAll_sound_aux hc hxs]

set_option maxHeartbeats 1000000 in
-- the shared `term_depth_wf` block has alternatives this theorem's goals do not use
set_option linter.unreachableTactic false in
/-- Soundness of every attribute row; recursion on `Term.depth`, as on the value side. The
-/
theorem AdmA_sound : ∀ (t : Term) {a v},
    (denote t).p a = some v → AdmA t a = true
  | t, a, v, hp => by
    cases t
    case string => cases a <;> simp_all [AdmA, denote, stringCodec]
    case boolean => cases a <;> simp_all [AdmA, denote, booleanCodec]
    case binary => cases a <;> simp_all [AdmA, denote, binaryCodec]
    case null => cases a <;> simp_all [AdmA, denote, nullCodec]
    case number =>
      cases a
      case n x =>
        simp only [denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, numberCodec] at hp
        cases hx : Double.ofDec x.1 <;> rw [hx] at hp <;> simp_all [AdmA]
      all_goals (simp only [denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, numberCodec] at hp; exact nomatch hp)
    case decimal => cases a <;> simp_all [AdmA, denote, decimalCodec]
    -- One case where there were three, and the shape of the argument is now visible: the
    -- `number` base is the only one whose read goes through `Double.ofDec`, so it is the only
    -- one where the exact row and §5's table row differ. The other four coincide, and
    -- `admA_sound` carries them.
    case literal k ls =>
      cases k
      case number =>
        cases a
        case n x =>
          simp only [denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, literalCodec, baseCodec, Codec.restrict, numberCodec, inL] at hp
          cases hx : Double.ofDec x.1 with
          | none => rw [hx] at hp; simp at hp
          | some d =>
            rw [hx] at hp
            by_cases hw : Numeral.WF d.toDec = true <;> simp_all [AdmALit]
        all_goals
          (simp only [denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, literalCodec, baseCodec, Codec.restrict, numberCodec, inL] at hp
           exact nomatch hp)
      all_goals
        (rw [show AdmA (.literal _ ls) a = admA (.literal _ ls) a from by
              cases a <;> simp [AdmALit, admA, admALit]]
         exact admA_sound _ hp)
    case custom ce cp => simp_all [AdmA, denote]
    -- the four repaired rows, sound for the reason the value side gives
    case opaq lossy => exact AdmA_opaq_sound lossy a (by rw [hp]; rfl)
    case legacy c r =>
      simp only [denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, Codec.extendRead] at hp
      cases hc : (denote c).p a with
      | some w => rw [hc] at hp; simp [AdmA, AdmA_sound c hc]
      | none => rw [hc] at hp; simp [AdmA, hp]
    -- exact, so soundness is one half of the `Iff`
    case set b => exact (ExactA_set b a).mpr (by rw [hp]; rfl)
    case tuple ts tl =>
      refine AdmA_tuple_sound (fun t' ht' b hb => ?_) (fun t' ht' b hb => ?_) a (by rw [hp]; rfl)
      · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hb
        exact AdmA_sound t' hw
      · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hb
        exact AdmA_sound t' hw
    case object fields fld rest =>
      have hf : ∀ k : {k // k ∈ fields}, SoundAField (fld k) := by
        intro k b hb
        obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hb
        cases hfd : fld k with
        | req t0 => rw [hfd] at hw; exact AdmA_sound t0 hw
        | optional t0 => rw [hfd] at hw; exact AdmA_sound t0 hw
        | fallback t0 v0 => rw [hfd] at hw; exact AdmA_sound t0 hw
      have hr : ∀ t0, rest = .codec t0 → SoundA t0 := by
        intro t0 hrest b hb
        obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hb
        exact AdmA_sound t0 hw
      exact AdmA_object_sound hf hr a (by rw [hp]; rfl)
    case array c =>
      cases a
      case l as =>
        simp only [AdmA]
        simp only [denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, arrayCodec] at hp
        obtain ⟨vs, hvs, -⟩ := Option.map_eq_some'.mp hp
        exact AdmAAll_sound_aux (fun {a v} h => AdmA_sound c h) hvs
      all_goals (simp only [denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, arrayCodec] at hp; exact nomatch hp)
    case record c =>
      cases a
      case m keys g =>
        simp only [AdmA, decide_eq_true_eq]
        simp only [denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, recordCodec] at hp
        obtain ⟨f, hf, -⟩ := Option.map_eq_some'.mp hp
        exact fun k => AdmA_sound c (funImage_some hf k)
      all_goals (simp only [denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, recordCodec] at hp; exact nomatch hp)
    case refine c q =>
      obtain ⟨hp', hq⟩ := restrict_p.mp hp
      rw [AdmA, Bool.and_eq_true]
      exact ⟨AdmA_sound c hp', by rw [refineReads_some hp']; exact hq⟩
    case lazy c => simpa [AdmA] using AdmA_sound c hp
    case held c f g =>
      obtain ⟨w, hw, -⟩ := through_p.mp hp
      simpa [AdmA] using AdmA_sound c hw
    case nullable c =>
      cases hw : (denote c).ownsNull with
      | true =>
        rw [show (denote (.nullable c)).p = (denote c).p from
          withNull_p_of_owns hw] at hp
        simp [AdmA, AdmA_sound c hp]
      | false =>
        rw [show denote (.nullable c) = (denote c).orNull from
          withNull_eq_orNull hw] at hp
        rcases orNull_p.mp hp with ⟨rfl, -⟩ | ⟨-, hc⟩
        · simp [AdmA]
        · simp [AdmA, AdmA_sound c hc]
    case dunion d opts =>
      refine AdmA_dunion_sound (fun t' ht' b hb => ?_) a (by rw [hp]; rfl)
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hb
      exact AdmA_sound t' hw
    case union opts =>
      simp only [denote, optionSems_eq] at hp
      obtain ⟨o, ho, -, hop⟩ := altCodec_p_admits hp
      simp only [List.mem_map] at ho
      obtain ⟨tx, htx, rfl⟩ := ho
      rw [optionSemOf_c] at hop
      -- hoisted for the reason the value side gives: the recursive call cannot live inside a
      -- generalisation over an arbitrary list
      have htx' : AdmA tx a = true := AdmA_sound tx hop
      have key : ∀ (ts : List Term), tx ∈ ts → AdmAAny ts a = true := by
        intro ts hts
        induction ts with
        | nil => exact absurd hts (by simp)
        | cons t0 ts ih =>
          rcases List.mem_cons.mp hts with rfl | h'
          · simp [AdmAAny_cons, htx']
          · simp [AdmAAny_cons, ih h']
      exact key opts htx

termination_by t _ _ => Term.depth t
decreasing_by term_depth_wf

/-! **Every attribute row is a sound over-approximation, the hatch included** — the
    attribute-side counterpart of `Adm_sound`, and the same obligation for the same reason.

    Exactness now has a mirror here (`AdmA_exact`), so both sides of the pair carry two
    obligations rather than one and a half, and the analysis tables can be read off either. -/

mutual
/-- The attribute-side hatch, and it is now **the value side's, exactly** — `union`, `set`
    and `nullable`, for the value side's reasons.

    `refine` used to be the fourth, and the one asymmetry: "`q` tests the value a read
    *produces*; no syntactic set of attributes bounds that". The sentence is true and the
    inference from it was not — a row is free to decode and then ask `q` (`refineReads`),
    which is what `AdmA`'s row now does, so `refine` propagates on both sides. The claim
    that this row is why `adm` and `admA` are two functions rather than one is likewise
    retracted; `legacy` is why, and `legacy` alone (`not_admA_legacy`).

    `legacy` left this list when its row became the union of the two channels; `tuple`,
    `object`, `dunion` and `opaq` left it next; `refine` leaves it now. -/
def AnalysableA : Term → Bool
  | .string | .boolean | .binary | .null | .number | .decimal
  | .literal _ _ | .custom _ _ | .opaq _ => true
  | .array c | .record c | .held c _ _ | .lazy c | .legacy c _ | .refine c _ =>
      AnalysableA c
  | .tuple ts tail => AnalysableAL ts && AnalysableAO tail
  | .dunion _ opts => AnalysableAL opts
  | .object fields fld rest =>
      decide (∀ k : {k // k ∈ fields}, AnalysableAF (fld k) = true) && AnalysableAR rest
  | .set _ => true
  | .nullable _ | .union _ => false

def AnalysableAL : List Term → Bool
  | [] => true
  | t :: ts => AnalysableA t && AnalysableAL ts

def AnalysableAO : Option Term → Bool
  | none => true
  | some t => AnalysableA t

def AnalysableAF : Field → Bool
  | .req t => AnalysableA t
  | .optional t => AnalysableA t
  | .fallback t _ => AnalysableA t

def AnalysableAR : Rest → Bool
  | .drop | .refuse => true
  | .codec t => AnalysableA t
end

def ExactAL : List Term → Prop
  | [] => True
  | t :: ts => ExactA t ∧ ExactAL ts

def ExactAO : Option Term → Prop
  | none => True
  | some t => ExactA t

def ExactAR : Rest → Prop
  | .drop | .refuse => True
  | .codec t => ExactA t

theorem exactAL_mem : ∀ (ts : List Term), ExactAL ts → ∀ t ∈ ts, ExactA t
  | [], _, t, ht => absurd ht (by simp)
  | t0 :: ts, h, t, ht => by
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact h.1
      · exact exactAL_mem ts h.2 t ht'

theorem exactAO_mem : ∀ (tail : Option Term), ExactAO tail → ∀ t ∈ tail, ExactA t
  | none, _, t, ht => absurd ht (by simp)
  | some t0, h, t, ht => by
      have heq : t0 = t := by simpa using ht
      subst heq; exact h

theorem exactAR_codec : ∀ (rest : Rest), ExactAR rest → ∀ t, rest = .codec t → ExactA t
  | .drop, _, t, h => nomatch h
  | .refuse, _, t, h => nomatch h
  | .codec t0, h, t, hc => by
      have heq : t = t0 := by injection hc.symm
      subst heq; exact h

/-- `allPA` transported across the entry's exactness. -/
theorem AdmAAll_iff {c : Term} (h : ExactA c) : ∀ as : List Attr,
    allPA (AdmA c) as = true ↔ ∀ a ∈ as, ((denote c).p a).isSome = true := by
  intro as; induction as with
  | nil => simp [allPA]
  | cons a as ih => simp [allPA, ih, h a]

mutual
/-- **Nineteen of the twenty-one attribute rows are exact** — the same nineteen as the value
    side, and the two that decline are the same two. `refine` was the last difference between
    the two sides and is exact now: its row decodes and then applies `q`. `legacy`,
    which used to be the other half of that asymmetry, is exact here because its row is the
    union of the two channels it reads on.

    The numeric rows are the interesting ones: they reach `dom(p)` through `Double.ofDec`,
    which is axiomatized, and are exact anyway — a row may *call* an axiomatized function
    even though no finite set of numerals describes its domain. §5 wrote `⊤` there. -/
theorem AdmA_exact : ∀ (t : Term), AnalysableA t = true → ExactA t
  -- the four rows §5 excused on this side too
  | .tuple ts tail => by
      intro ha
      simp only [AnalysableA, Bool.and_eq_true] at ha
      exact ExactA_tuple (exactAL_mem ts (AdmA_exactL ts ha.1))
        (exactAO_mem tail (AdmA_exactO tail ha.2))
  | .dunion d opts => by
      intro ha
      exact ExactA_dunion
        (exactAL_mem opts (AdmA_exactL opts (by simpa [AnalysableA] using ha)))
  | .object fields fld rest => by
      intro ha
      simp only [AnalysableA, Bool.and_eq_true, decide_eq_true_eq] at ha
      exact ExactA_object (fun k => AdmA_exactF (fld k) (ha.1 k))
        (exactAR_codec rest (AdmA_exactR rest ha.2))
  | .opaq lossy => fun _ => ExactA_opaq lossy
  -- exact because the constructor narrowed, not because the row sharpened
  | .set b => fun _ => ExactA_set b
  -- the two that decline, refuted by the hypothesis
  | .nullable _ => by intro ha; simp [AnalysableA] at ha
  | .union _ => by intro ha; simp [AnalysableA] at ha

  | .string => by intro _ a; cases a <;> simp [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, stringCodec]
  | .boolean => by intro _ a; cases a <;> simp [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, booleanCodec]
  | .binary => by intro _ a; cases a <;> simp [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, binaryCodec]
  | .null => by intro _ a; cases a <;> simp [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, nullCodec]
  | .number => by
      intro _ a
      cases a
      case n x =>
        simp only [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, numberCodec]
        cases hx : Double.ofDec x.1 <;> simp [hx]
      all_goals simp [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, numberCodec]
  | .decimal => by intro _ a; cases a <;> simp [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, decimalCodec]
  -- Three rows into one. The `number` base is the only one needing `Double.ofDec`, and it is
  -- also the only one where unfolding `numberCodec` is safe here: the `simp only` fixes the
  -- shape before `Numeral.WF`'s parser can be reached.
  | .literal k ls => by
      intro _ a
      cases k
      case number =>
        cases a
        case n x =>
          -- through the named shape lemmas, not by unfolding `numberCodec`: its `p` is a
          -- `bind` over `Double.ofDec` guarded by `Numeral.WF`, and `simp` inside that gate
          -- reaches the parser and runs out of heartbeats
          rw [show (denote (Term.literal .number ls)).p (.n x)
                 = (literalCodec .number ls).p (.n x) from rfl,
             literalNCodec_p_n, numberCodec_p_n]
          cases hx : Double.ofDec x.1 with
          | none => simp [hx, AdmALit]
          | some d =>
            by_cases hw : Numeral.WF d.toDec = true <;>
              simp [hx, hw, AdmALit, inL]
        -- for every other attribute the base's own read is `none` by a match, so this is
        -- `rfl` once `AdmA`'s recursion is unfolded — no `numberCodec` in the simp set
        all_goals (simp only [AdmA_literal, AdmALit]; rfl)
      -- the four bases whose stored attribute *is* the value, one tight simp set each: a
      -- shared set has to mention every base's codec, and one of those is `number`
      case string =>
        cases a <;> simp [AdmALit, denote, denote, literalCodec, baseCodec, Codec.restrict,
                          inL, stringCodec]
      case boolean =>
        cases a <;> simp [AdmALit, denote, denote, literalCodec, baseCodec, Codec.restrict,
                          inL, booleanCodec]
      case binary => exact AdmALit_binary_exact ls a
      case null => exact AdmALit_null_exact ls a
  | .custom ce cp => by intro _ a; simp [AdmA, denote, denote]
  | .array c => by
      intro ha
      have hc := AdmA_exact c (by simpa [AnalysableA] using ha)
      intro a
      cases a
      case l as =>
        simp only [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, arrayCodec]
        rw [AdmAAll_iff hc, ← traverse_isSome_iff]
        cases traverse (denote c).p as <;> simp
      all_goals simp [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, arrayCodec]
  | .record c => by
      intro ha
      have hc := AdmA_exact c (by simpa [AnalysableA] using ha)
      intro a
      cases a
      case m keys g =>
        simp only [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, recordCodec, Option.isSome_map', decide_eq_true_eq,
          funImage_isSome_iff]
        exact forall_congr' fun k => hc (g k)
      all_goals simp only [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, recordCodec, Option.map_none',
        Option.isSome_none, Bool.false_eq_true]
  | .held c f g => by
      intro ha
      have hc := AdmA_exact c (by simpa [AnalysableA] using ha)
      intro a
      simp only [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, Codec.through]
      rw [hc a]
      cases (denote c).p a <;> simp
  -- **the row this file said could not exist.** `restrict`'s `p` is the base's `bind`ed
  -- through `q`, so `dom(p)` is `dom` of the base's intersected with `q` of what it decodes
  -- to — and that is what the row computes, term for term.
  | .refine c q => by
      intro ha
      have hc := AdmA_exact c (by simpa [AnalysableA] using ha)
      intro a
      simp only [AdmA, refineReads, denote_refine, Codec.restrict, Bool.and_eq_true, hc a]
      cases hx : (denote c).p a <;> simp [hx]
  | .lazy c => by
      intro ha
      have hc := AdmA_exact c (by simpa [AnalysableA] using ha)
      intro a; simpa [AdmA, denote] using hc a
  | .legacy c r => by
      intro ha
      have hc := AdmA_exact c (by simpa [AnalysableA] using ha)
      intro a
      simp only [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, Codec.extendRead]
      cases hx : (denote c).p a <;> simp [hc a, hx]

theorem AdmA_exactL : ∀ (ts : List Term), AnalysableAL ts = true → ExactAL ts
  | [] => fun _ => trivial
  | t0 :: ts => by
      intro ha
      simp only [AnalysableAL, Bool.and_eq_true] at ha
      exact ⟨AdmA_exact t0 ha.1, AdmA_exactL ts ha.2⟩

theorem AdmA_exactO : ∀ (tail : Option Term), AnalysableAO tail = true → ExactAO tail
  | none => fun _ => trivial
  | some t0 => by
      intro ha
      exact AdmA_exact t0 (by simpa [AnalysableAO] using ha)

theorem AdmA_exactF : ∀ (fd : Field), AnalysableAF fd = true → ExactAField fd
  | .req t0 => by intro ha a; exact AdmA_exact t0 (by simpa [AnalysableAF] using ha) a
  | .optional t0 => by intro ha a; exact AdmA_exact t0 (by simpa [AnalysableAF] using ha) a
  | .fallback t0 _ => by intro ha a; exact AdmA_exact t0 (by simpa [AnalysableAF] using ha) a

theorem AdmA_exactR : ∀ (rest : Rest), AnalysableAR rest = true → ExactAR rest
  | .drop => fun _ => trivial
  | .refuse => fun _ => trivial
  | .codec t0 => by
      intro ha
      exact AdmA_exact t0 (by simpa [AnalysableAR] using ha)
end

/-! ### The attribute side's excuses, and their witnesses

The value side's two reasons apply here too, and they are now the whole list. A fourth —
`refine`, "which cannot narrow a read because `q` tests the value a read *produces*" — was
here until the row was written: `AdmA` decodes with the base and applies `q`, so the shape
is exact and the reason is deleted rather than restated. `excuse_witnessed` keeps the
covering as a hypothesis anyway: an excuse must be witnessed **on the side it is used on**,
and a future asymmetry should not have to re-derive that.

`legacy` used to be the second such reason and is exact on both sides now; `tuple` and
`opaq` used to be witnessed here and are exact too. -/

/-! `not_ExactA_set` stood here: `set(string)` admitted an `NS` because `AdmA`'s `set` row
answered `true` at all three wire families whatever the element term was. That row is gone —
the family is a function of the base — and with it the witness. It was the *read* side's
half of `payloadShape`, and the half that excuse's docstring never mentioned. -/

/-- (U) failing, read side: two options admit and `select` reads nothing. -/
theorem not_ExactA_union : ¬ ExactA (.union [.string, .string]) := by
  intro h
  have := (h (.s "a")).mp (by simp [AdmA, anyPA, AdmAList])
  simp [denote, denote, optionSems, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, specOf, optionSemOf, altCodec, select,
    stringCodec] at this

/-- Writes the null point — half of a pair whose write reaches it and whose read does not,
    the mirror of `rNull`, and the reason `nullable` is in both hatches rather than one. -/
def ceNull : Value → Option Attr := fun v => match v with | .null => some .null | _ => none
/-- …and reads nothing at all. -/
def cpNone : Attr → Option Value := fun _ => none

theorem not_ExactA_nullable : ¬ ExactA (.nullable (.custom ceNull cpNone)) := by
  intro h
  have h2 := (h .null).mp (by simp [AdmA])
  simp [denote, denote, Codec.withNull, Codec.ownsNull, ceNull, cpNone] at h2

/-- **The witness that is now a theorem the other way.** `refine(string, ⊥)` reads nothing,
    and `AdmA` says so: the row decodes with `stringCodec` and applies `⊥`. This used to be
    `not_ExactA_refine`, stated as "`AdmA` cannot see it". -/
theorem AdmA_refine_bot (a : Attr) : AdmA (.refine .string (fun _ => false)) a = false := by
  simp [AdmA, refineReads]
  cases a <;> simp [denote, stringCodec]

/-- Which shapes each excuse may be invoked for **on the attribute side**. It is now the
    value side's table, row for row — `refine` was the last entry that differed — and the
    catch-all answers `false` for the same reason it does there: a new constructor is not
    excusable by default. The two tables are kept separate anyway: nothing makes them agree,
    and a future asymmetry should be able to appear in one of them. -/
def Excuse.coversA : Excuse → Term → Bool
  | .uniqueAdmission, .union _     => true
  | .nullOwnership,   .nullable _  => true
  | _, _ => false

/-- The answer a propagating **attribute** row inherits, conjoined as on the value side.
    `refine` is here now rather than excused, which closes the last shape at which the two
    hatches differed: `coversA` and `covers` are the same table. -/
def childrenAnalysableA : Term → Bool
  | .array c | .record c | .held c _ _ | .lazy c | .legacy c _ | .refine c _ =>
      AnalysableA c
  | .tuple ts tail => AnalysableAL ts && AnalysableAO tail
  | .dunion _ opts => AnalysableAL opts
  | .object fields fld rest =>
      decide (∀ k : {k // k ∈ fields}, AnalysableAF (fld k) = true) && AnalysableAR rest
  | _ => true

/-- Every attribute row that declines exactness names a covering reason or inherits one. -/
theorem analysableA_excused : ∀ (t : Term), AnalysableA t = false →
    (∃ e : Excuse, e.coversA t = true) ∨ childrenAnalysableA t = false
  | .union _, _     => .inl ⟨.uniqueAdmission, rfl⟩
  | .nullable _, _  => .inl ⟨.nullOwnership, rfl⟩
  | .array c, h | .record c, h | .held c _ _, h | .lazy c, h | .legacy c _, h
  | .refine c _, h =>
      .inr (by simpa [childrenAnalysableA, AnalysableA] using h)
  | .tuple _ _, h | .dunion _ _, h | .object _ _ _, h =>
      .inr (by simpa [childrenAnalysableA, AnalysableA] using h)
  | .string, h | .boolean, h | .binary, h | .null, h | .number, h | .decimal, h
  | .literal _ _, h | .custom _ _, h | .opaq _, h | .set _, h => nomatch h

/-- No attribute-side excuse names an exact row. -/
theorem excuseA_shapes (e : Excuse) (t : Term) (h : e.coversA t = true) :
    AnalysableA t = false := by
  cases e <;> cases t <;> simp_all [Excuse.coversA, AnalysableA]

/-- **Every attribute-side excuse is earned**, on the side it is used on. -/
theorem excuseA_witnessed : ∀ (e : Excuse) (t : Term), e.coversA t = true →
    ∃ t' : Term, e.coversA t' = true ∧ ¬ ExactA t'
  | .uniqueAdmission, _, _ => ⟨.union [.string, .string], rfl, not_ExactA_union⟩
  | .nullOwnership, _, _   => ⟨.nullable (.custom ceNull cpNone), rfl, not_ExactA_nullable⟩

/-! ## Re-deriving §5's separations on the pair

`SepV` and `SepA` are what the discharge machinery actually consumes, and they are stated
on `κ`/`adm`/`admA`. Before any of that can move to `Adm`/`AdmA`, two things have to be
true: the joint predicate must be at least as tight as the row it replaces, and every
discharge §5 already has must survive.

`Adm_le_adm` and `AdmA_le_admA` are the first. `sepJV_of_sepV` and `sepJA_of_sepA` are the
second — nothing is lost.

The interesting result is that the two sides do **not** re-derive the same way. On the value
side `κ`'s disjunct is subsumed: `Adm` folds the kind gate into its own rows and
`Adm_kind` proves it lands where `κ` says, so `SepJV` is a single clause. On the attribute
side the member disjunct survives, because `setMember` sends one value kind to three
attribute members and `AdmA`'s `set` row admits all three. `sepJA_needs_member` is the pair
that shows it doing work. -/

/-- `⋁` of `Adm` refines `⋁` of `adm`, option by option. -/
theorem AdmAny_le_admList : ∀ (ts : List Term) (v : Value),
    (∀ t ∈ ts, Adm t v = true → adm t v = true) →
    AdmAny ts v = true → admList ts v = true
  | [], _, _, h => by simp [AdmAny_nil] at h
  | t :: ts, v, hall, h => by
      simp only [AdmAny_cons, Bool.or_eq_true] at h
      simp only [admList, Bool.or_eq_true]
      rcases h with h | h
      · exact Or.inl (hall t (by simp) h)
      · exact Or.inr (AdmAny_le_admList ts v (fun t' ht' => hall t' (by simp [ht'])) h)

/-- The tag a `dunion`'s row lands on is one of the pooled tags. The row is sharper than
    `allTags` — it counts, where `allTags` unions — so the containment needs saying. -/
theorem selTagV_mem {d : Name} {opts : List Term} {v : Value}
    (h : selTagV d (AdmTagged d opts) v = true) :
    ∃ tag, tagOfV d v = some tag ∧ tag ∈ allTags d opts := by
  simp only [selTagV, AdmTagged_eq] at h
  cases htag : tagOfV d v with
  | none => rw [htag] at h; simp at h
  | some tag =>
    rw [htag] at h
    refine ⟨tag, rfl, ?_⟩
    replace h : (match (opts.map fun t => (tagsOf d t, Adm t)).filter
        (fun o => decide (tag ∈ o.1)) with
      | [o] => o.2 v | _ => false) = true := h
    rw [filter_map_comm] at h
    cases hL : opts.filter (fun t => decide (tag ∈ tagsOf d t)) with
    | nil => rw [hL] at h; simp at h
    | cons t rest =>
      have hmem : t ∈ opts.filter (fun t => decide (tag ∈ tagsOf d t)) := by
        rw [hL]; simp
      exact mem_allTags (List.mem_of_mem_filter hmem) (by simpa using List.of_mem_filter hmem)

/-- **`Adm` refines `adm`.** Every row of the joint predicate is at least as tight as the
    row it replaces, which is what lets every existing discharge carry over unchanged. -/
theorem Adm_le_adm : ∀ (t : Term) (v : Value), Adm t v = true → adm t v = true
  | .string, _, _ => rfl
  | .boolean, _, _ => rfl
  | .binary, _, _ => rfl
  | .null, _, _ => rfl
  | .set _, _, _ => rfl
  | .tuple _ _, _, _ => rfl
  | .object _ _ _, _, _ => rfl
  | .array _, _, _ => rfl
  | .record _, _, _ => rfl
  -- the two rows are now the **same** row — both ask `(opaqCodecω lossy).e` — so the
  -- containment is the identity, exactly as it is at `custom`. It was three lines while
  -- `Adm` recursed over the value and `adm` matched on the top constructor.
  | .opaq _, _, h => by rw [adm]; rw [Adm] at h; exact h
  | .number, v, h => by simpa [adm] using (by simpa [Adm] using h : inD v = true)
  | .decimal, v, h => by simpa [adm] using (by simpa [Adm] using h : isStored v = true)
  -- `Adm` is *strictly* stronger at the numeric base: it carries `WF`, which §5's table does
  -- not, so the containment drops a conjunct there rather than being `exact`. At the other
  -- four the two rows are the same predicate — `inL` — which is what one rule makes visible.
  | .literal k ls, v, h => by
      rw [adm]
      rw [Adm_literal] at h
      exact (Bool.and_eq_true _ _ ▸ h : inL k ls v = true ∧ _).1
  | .custom ce cp, v, h => by rw [adm]; rw [Adm] at h; exact h
  -- the sharpened row: `select`'s filter lands on an option whose tags are pooled into
  -- `allTags`, which is all §5's row ever said
  | .dunion d opts, v, h => by
      obtain ⟨tag, htag, hmem⟩ := selTagV_mem h
      rw [adm]
      simp only [htag, decide_eq_true_eq]
      exact hmem
  | .refine t q, v, h => by
      rw [Adm, Bool.and_eq_true] at h
      rw [adm, Bool.and_eq_true]
      exact ⟨Adm_le_adm t v h.1, h.2⟩
  | .legacy t r, v, h => by
      rw [adm]; exact Adm_le_adm t v (by rw [Adm] at h; exact h)
  | .lazy t, v, h => by
      rw [adm]; exact Adm_le_adm t v (by rw [Adm] at h; exact h)
  | .held t f g, v, h => by
      rw [adm]; exact Adm_le_adm t (f v) (by rw [Adm] at h; exact h)
  | .nullable t, v, h => by
      rw [Adm, Bool.or_eq_true] at h
      rw [adm, Bool.or_eq_true]
      rcases h with h | h
      · exact Or.inl (Adm_le_adm t v h)
      · exact Or.inr h
  | .union opts, v, h => by
      rw [adm]
      exact AdmAny_le_admList opts v (fun t' _ => Adm_le_adm t' v) (by rw [Adm] at h; exact h)


/-- …and lands in `⋃ κ`, which is what `union`'s kind row claims. -/
theorem AdmAny_kind : ∀ (ts : List Term) (ks : List Kind) (v : Value),
    κList ts = some ks →
    (∀ t ∈ ts, ∀ ks', κ t = some ks' → Adm t v = true → v.kind ∈ ks') →
    AdmAny ts v = true → v.kind ∈ ks
  | [], _, _, _, _, h => by simp [AdmAny_nil] at h
  | t :: ts, ks, v, hk, hall, h => by
      simp only [AdmAny_cons, Bool.or_eq_true] at h
      rcases h with h | h
      · obtain ⟨ks', hks', hsub⟩ := κList_mem hk t (by simp)
        exact hsub _ (hall t (by simp) ks' hks' h)
      · have : ∀ t' ∈ ts, ∀ ks', κ t' = some ks' → Adm t' v = true → v.kind ∈ ks' :=
          fun t' ht' => hall t' (by simp [ht'])
        replace hk : (match κ t, κList ts with
          | some k0, some k1 => some (k0 ++ k1) | _, _ => none) = some ks := hk
        cases h0 : κ t with
        | none => rw [h0] at hk; exact nomatch hk
        | some k0 =>
          cases h1 : κList ts with
          | none => rw [h0, h1] at hk; exact nomatch hk
          | some k1 =>
            rw [h0, h1] at hk
            have hks : ks = k0 ++ k1 := by simpa using hk.symm
            subst hks
            exact List.mem_append.mpr (Or.inr (AdmAny_kind ts k1 v h1 this h))

/-- **`Adm` lands in `κ`.** Wherever `κ` names a kind list at all, an `Adm`-admitted value
    has one of those kinds — so the kind gate `Adm` folds in really is `κ`'s, and `SepV`'s
    first disjunct is subsumed by its second. -/
theorem Adm_kind : ∀ (t : Term) (ks : List Kind) (v : Value),
    κ t = some ks → Adm t v = true → v.kind ∈ ks
  | .string, _, v, rfl, h => by cases v <;> simp_all [Adm, Value.kind]
  | .boolean, _, v, rfl, h => by cases v <;> simp_all [Adm, Value.kind]
  | .binary, _, v, rfl, h => by cases v <;> simp_all [Adm, Value.kind]
  | .null, _, v, rfl, h => by cases v <;> simp_all [Adm, Value.kind]
  | .number, _, v, rfl, h => by cases v <;> simp_all [Adm, inD, Value.kind]
  | .decimal, _, v, rfl, h => by cases v <;> simp_all [Adm, isStored, Value.kind]
  | .literal k _, _, v, rfl, h => by
      cases k <;> cases v <;> simp_all [Adm_literal, AdmLit, inL, Value.kind]
  | .set _, _, v, rfl, h => by cases v <;> simp_all [Adm, Value.kind]
  | .array _, _, v, rfl, h => by cases v <;> simp_all [Adm, Value.kind]
  | .tuple _ _, _, v, rfl, h => by cases v <;> simp_all [Adm, Value.kind]
  | .record _, _, v, rfl, h => by cases v <;> simp_all [Adm, Value.kind]
  | .object _ _ _, _, v, rfl, h => by cases v <;> simp_all [Adm, Value.kind]
  | .dunion d opts, _, v, rfl, h => by
      obtain ⟨tag, htag, -⟩ := selTagV_mem h
      cases v <;> simp_all [tagOfV, Value.kind]
  | .refine t q, ks, v, hk, h => by
      rw [Adm, Bool.and_eq_true] at h
      exact Adm_kind t ks v (by rw [κ] at hk; exact hk) h.1
  | .legacy t r, ks, v, hk, h => by
      exact Adm_kind t ks v (by rw [κ] at hk; exact hk) (by rw [Adm] at h; exact h)
  | .lazy t, ks, v, hk, h => by
      exact Adm_kind t ks v (by rw [κ] at hk; exact hk) (by rw [Adm] at h; exact h)
  | .nullable t, ks, v, hk, h => by
      rw [κ] at hk
      obtain ⟨ks', hks', rfl⟩ := Option.map_eq_some'.mp hk
      rw [Adm, Bool.or_eq_true] at h
      rcases h with h | h
      · exact List.mem_cons_of_mem _ (Adm_kind t ks' v hks' h)
      · cases v <;> simp_all [Value.kind]
  | .union opts, ks, v, hk, h => by
      exact AdmAny_kind opts ks v (by rw [κ] at hk; exact hk)
        (fun t' _ ks' hk' h' => Adm_kind t' ks' v hk' h') (by rw [Adm] at h; exact h)
  | .held _ _ _, ks, v, hk, h => by rw [κ] at hk; exact nomatch hk
  | .custom _ _, ks, v, hk, h => by rw [κ] at hk; exact nomatch hk
  | .opaq _, ks, v, hk, h => by rw [κ] at hk; exact nomatch hk


/-- `⋁` of `AdmA` refines `⋁` of `admA`. -/
theorem AdmAAny_le_admAList : ∀ (ts : List Term) (a : Attr),
    (∀ t ∈ ts, AdmA t a = true → admA t a = true) →
    AdmAAny ts a = true → admAList ts a = true
  | [], _, _, h => by simp [AdmAAny_nil] at h
  | t :: ts, a, hall, h => by
      simp only [AdmAAny_cons, Bool.or_eq_true] at h
      simp only [admAList, Bool.or_eq_true]
      rcases h with h | h
      · exact Or.inl (hall t (by simp) h)
      · exact Or.inr (AdmAAny_le_admAList ts a (fun t' ht' => hall t' (by simp [ht'])) h)

/-- The read-side mirror of `selTagV_mem`. -/
theorem selTagA_mem {d : Name} {opts : List Term} {a : Attr}
    (h : selTagA d (AdmATagged d opts) a = true) :
    ∃ tag, tagOfA d a = some tag ∧ tag ∈ allTags d opts := by
  simp only [selTagA, AdmATagged_eq] at h
  cases htag : tagOfA d a with
  | none => rw [htag] at h; simp at h
  | some tag =>
    rw [htag] at h
    refine ⟨tag, rfl, ?_⟩
    replace h : (match (opts.map fun t => (tagsOf d t, AdmA t)).filter
        (fun o => decide (tag ∈ o.1)) with
      | [o] => o.2 a | _ => false) = true := h
    rw [filter_map_comm] at h
    cases hL : opts.filter (fun t => decide (tag ∈ tagsOf d t)) with
    | nil => rw [hL] at h; simp at h
    | cons t rest =>
      have hmem : t ∈ opts.filter (fun t => decide (tag ∈ tagsOf d t)) := by
        rw [hL]; simp
      exact mem_allTags (List.mem_of_mem_filter hmem) (by simpa using List.of_mem_filter hmem)

/-- **`AdmA` refines `admA`**, the attribute-side counterpart of `Adm_le_adm`. -/
theorem AdmA_le_admA : ∀ (t : Term) (a : Attr), AdmA t a = true → admA t a = true
  | .string, _, _ => rfl
  | .boolean, _, _ => rfl
  | .binary, _, _ => rfl
  | .null, _, _ => rfl
  | .set _, _, _ => rfl
  | .tuple _ _, _, _ => rfl
  | .object _ _ _, _, _ => rfl
  | .array _, _, _ => rfl
  | .record _, _, _ => rfl
  | .legacy _ _, _, _ => rfl
  -- as on the value side: one row, so the containment is the identity
  | .opaq _, a, h => by rw [admA]; rw [AdmA] at h; exact h
  | .custom _ _, a, h => by rw [admA]; rw [AdmA] at h; exact h
  | .decimal, a, h => by rw [admA]; rw [AdmA] at h; exact h
  | .dunion d opts, a, h => by
      obtain ⟨tag, htag, hmem⟩ := selTagA_mem h
      rw [admA]
      simp only [htag, decide_eq_true_eq]
      exact hmem
  -- **`number` and a numeric `literal` are no longer containments.** §5's rows at these two
  -- terms used to be `⊤`, so the containment was `rfl`; they now ask the same codec `AdmA`
  -- asks, so the two analyses *coincide* and `AdmA_exact` is what says so.
  | .number, a, h => by
      show ((denote Term.number).p a).isSome = true
      exact (AdmA_exact .number rfl a).mp h
  | .literal k ls, a, h => by
      cases k
      case number =>
        show ((denote (Term.literal .number ls)).p a).isSome = true
        exact (AdmA_exact (.literal .number ls) rfl a).mp h
      all_goals cases a <;> simp_all [AdmA_literal, AdmALit, admA, admALit]
  -- the two rows are the *same* gate now — `refineReads` verbatim on both sides — so this
  -- is the containment of the base's, conjoined with a shared conjunct
  | .refine t q, a, h => by
      rw [AdmA, Bool.and_eq_true] at h
      rw [admA, Bool.and_eq_true]
      exact ⟨AdmA_le_admA t a h.1, h.2⟩
  | .held t _ _, a, h => by
      rw [admA]; exact AdmA_le_admA t a (by rw [AdmA] at h; exact h)
  | .lazy t, a, h => by
      rw [admA]; exact AdmA_le_admA t a (by rw [AdmA] at h; exact h)
  | .nullable t, a, h => by
      rw [AdmA, Bool.or_eq_true] at h
      rw [admA, Bool.or_eq_true]
      rcases h with h | h
      · exact Or.inl (AdmA_le_admA t a h)
      · exact Or.inr h
  | .union opts, a, h => by
      rw [admA]
      exact AdmAAny_le_admAList opts a (fun t' _ => AdmA_le_admA t' a)
        (by rw [AdmA] at h; exact h)

/-- **Separation on the joint predicate, value side — one clause.** §5's `SepV` offers a
    choice between disjoint kinds and disjoint admissible sets; `Adm` carries the kind gate
    in its own rows, so the first disjunct is subsumed (`Adm_kind`) and the definition
    collapses. -/
def SepJV (x y : Term) : Prop := ∀ v, Adm x v = true → Adm y v = false

/-- **…and attribute side, which does *not* collapse.** The member disjunct stays, because
    `AdmA` does not bound `μSyn`.

    The reason used to be `setMember`'s — one value kind, three attribute members, so a
    `set` row admitted `SS`, `NS` and `BS` whatever its element term was. That reason is
    **gone**: `set` is indexed by its base, so its wire family is a function of the index
    and its row names one member. The clause survives anyway, because the phenomenon was
    never `set`'s alone. `legacy` widens a read past the member its own term claims — `p`
    falls back to a channel the term carries as data — so `AdmA` still fails to bound
    `μSyn`, and `sepJA_needs_member` is now witnessed there. -/
def SepJA (x y : Term) : Prop :=
  (∃ μx μy, μSyn x = some μx ∧ μSyn y = some μy ∧ μx ≠ μy) ∨
  (∀ a, AdmA x a = true → AdmA y a = false)

/-- **Every §5 value-side discharge carries over**, from either disjunct. -/
theorem sepJV_of_sepV {x y : Term} (h : SepV x y) : SepJV x y := by
  intro v hv
  cases hy : Adm y v with
  | false => rfl
  | true =>
    exfalso
    rcases h with ⟨kx, ky, hkx, hky, hdisj⟩ | hd
    · exact hdisj _ (Adm_kind x kx v hkx hv) (Adm_kind y ky v hky hy)
    · have := hd v (Adm_le_adm x v hv)
      rw [Adm_le_adm y v hy] at this
      exact absurd this (by simp)

/-- …and every attribute-side one. -/
theorem sepJA_of_sepA {x y : Term} (h : SepA x y) : SepJA x y := by
  rcases h with hμ | hd
  · exact Or.inl hμ
  · refine Or.inr fun a ha => ?_
    cases hy : AdmA y a with
    | false => rfl
    | true =>
      exfalso
      have := hd a (AdmA_le_admA x a ha)
      rw [AdmA_le_admA y a hy] at this
      exact absurd this (by simp)

/-- A read channel that fires at `N` and nowhere else — `legacy`'s widening, minimal. -/
def rNum : Attr → Option Value := fun a => match a with | .n _ => some (.str "x") | _ => none

/-- **The member disjunct is load-bearing, and the witness moved.**

    It used to be `set(string)` against `set(number)`: they differ in `μSyn` and were
    indistinguishable to `AdmA`, which admitted `NS` at both. Indexing `set` killed that
    pair — the wire family is now a function of the base, so `AdmA` separates those two on
    its own — and it did **not** kill the disjunct, because `set` was never the only way to
    have a read that outruns `μSyn`.

    `legacy` is. `legacy(string, r)` stores `S`, and `r` reading an `.n` widens `p` past the
    member the term claims; `decimal` stores `N` and admits the same attribute. So the two
    are separated by `μSyn` and not by `AdmA`, which is exactly what the first clause of
    `SepJA` is for. -/
theorem sepJA_needs_member :
    ¬ (∀ a, AdmA (.legacy .string rNum) a = true → AdmA .decimal a = false) := by
  intro h
  exact absurd (h (.n (.of "1")) (by simp [AdmA, rNum])) (by simp [AdmA]; decide)

/-- …and the pair really is separated — by the member disjunct alone, which is what makes
    `SepJA`'s two clauses independent rather than redundant. -/
theorem sepJA_legacy_decimal : SepJA (.legacy .string rNum) .decimal :=
  Or.inl ⟨.S, .N, rfl, rfl, by decide⟩

/-! ## `ident`, and why the pair does not replace it

`ident` is §5's third auxiliary: *the term decides its own membership*. The question the
migration has to answer is whether the joint predicate subsumes it. It does not, and the
reason is worth stating precisely, because it is the one place where `Adm` carries **less**
than the three functions it replaces.

`ident` is not a function of `Adm` — nor of `adm`. `string` and `refine(string, ⊤)` denote
the same pair, have the same `Adm` and the same `adm`, and differ in `ident`, which is
`false` for the bare base and `true` for any `refine`. `ident` is a fact about *how a term
is written*, not about which values it admits, and no predicate on values can recover it.

That is not a gap, because nothing consumes it. `ident` appears in no discharge: none of the
seventeen `uAtCan_*` theorems mentions it. What it does is carry §5's **(K)** — the rule
that was stated as `κ(cᵢ) ∩ κ(cⱼ) = ∅ ∨ ident(cᵢ) ∨ ident(cⱼ)`, found unsound, and replaced
by `SepV`. `ident_of_adm` pins it, `admDisj_ident` recovers the repaired form, and
`not_uAtCan_literal_string` / the two-sided refutation record why the withdrawn form was
wrong.

So `ident` stays where it is, defined on `adm`, and `adm` stays with it. The pair supersedes
`κ`/`adm`/`admA` **for the discharge**; it does not supersede the transcription of §5, and
deleting that would delete the record of what §5 got wrong. -/

/-- A refinement by the trivially-true predicate: same pair, same `Adm`, different `ident`. -/
def qTop : Value → Bool := fun _ => true

/-- The two terms agree on the joint predicate… -/
theorem Adm_string_eq_refine : Adm .string = Adm (.refine .string qTop) := by
  funext v; simp [Adm, qTop]

/-- …and disagree on `ident`. -/
theorem ident_string_ne_refine :
    ident .string ≠ ident (.refine .string qTop) := by
  simp [ident]

/-- **`ident` is not a function of `Adm`.** Two terms with the *same* joint predicate and
    different `ident`, so no definition on the pair can recover it. -/
theorem ident_not_determined_by_Adm :
    ∃ x y : Term, Adm x = Adm y ∧ ident x ≠ ident y :=
  ⟨.string, .refine .string qTop, Adm_string_eq_refine, ident_string_ne_refine⟩

/-- They agree on `adm` too, so this is not an artefact of folding in the kind gate. -/
theorem adm_string_eq_refine : adm .string = adm (.refine .string qTop) := by
  funext v; simp [adm, qTop]

/-- …so `ident` is not a function of `adm` either, by the same pair. -/
theorem ident_not_determined_by_adm :
    ∃ x y : Term, adm x = adm y ∧ ident x ≠ ident y :=
  ⟨.string, .refine .string qTop, adm_string_eq_refine, ident_string_ne_refine⟩

/-- **`SepJV` suffices for the discharge.** This is what "nothing is lost" means: the joint
    predicate is tighter than the rows it replaces, so `SepJV` is a *weaker* statement — but
    `Adm_sound` connects it straight to the denotation, and that is all the discharge needs.
    Where `x` writes, `y` refuses. -/
theorem admitV_of_sepJV {x y : Term} (h : SepJV x y) (v : Value) (a : Attr)
    (hx : (denote x).e v = some a) : ((denote y).e v).isSome = false := by
  have hAx : Adm x v = true := Adm_sound x hx
  have hAy : Adm y v = false := h v hAx
  cases hy : (denote y).e v with
  | none => rfl
  | some b => exact absurd (Adm_sound y hy) (by simp [hAy])

/-- …and on the attribute side, from `SepJA`'s second disjunct. -/
theorem admitA_of_sepJA {x y : Term} (h : ∀ a, AdmA x a = true → AdmA y a = false)
    (a : Attr) (v : Value) (hx : (denote x).p a = some v) :
    ((denote y).p a).isSome = false := by
  have hAx : AdmA x a = true := AdmA_sound x hx
  have hAy : AdmA y a = false := h a hAx
  cases hy : (denote y).p a with
  | none => rfl
  | some w => exact absurd (AdmA_sound y hy) (by simp [hAy])

/-! ### `ident`, pinned from below

The section above concluded that `ident` cannot be recovered from the pair and should
therefore be left alone. That was the wrong conclusion from a correct observation. `ident`
is a table like the other three, it had never been pinned from below either, and the reason
it resists the pair is not that it carries something the pair lacks — it is that it carries
something **nothing** justifies.

`Decides` below is the semantic notion §5's prose describes: two values of the same kind,
one written and one refused, so that the kind does not settle admission and an admission is
therefore evidence. Against it, `ident` is neither an over- nor an under-approximation:

* **Too generous.** `refine(string, ⊤)` is `ident` and decides nothing — `q` is checked on
  both halves and always passes. `ident` cannot see this, because it never looks at `q`.
* **Too stingy.** `object` with a required field refuses the empty map and writes a
  populated one, which is deciding by any reading, and `ident` calls it `false`.

And the `refine` row is not an oversight but an artifact: `ident (refine t q) = true`
unconditionally is what makes `ident_of_adm` go through, since `adm (refine t q)` can refuse
on `q` alone while `ident t` is `false`. The row exists to satisfy the pinning lemma, not
because refinements decide.

`ident` cannot be made exact — whether an arbitrary `q : Value → Bool` narrows anything is
not a syntactic question. What it can be is *honest about which side it errs on*, and at
present it errs on both. Nothing live depends on it: no `uAtCan_*` consumes it, and
`admDisj_ident` derives it rather than assuming it. -/

/-- **What "decides its own membership" actually says.** Two values of the *same kind*, one
    written and one refused: the kind does not settle admission, so an admission is
    evidence. This is the content §5's `ident` gestures at, stated on the denotation. -/
def Decides (t : Term) : Prop :=
  ∃ v w, ((denote t).e v).isSome = true ∧ v.kind = w.kind ∧ ((denote t).e w).isSome = false

/-- `literalS` decides, as §5 says. -/
theorem decides_literalS : Decides (.literal .string (.of "A" ∅)) :=
  ⟨.str "A", .str "B",
   by simp [denote, denote, literalCodec, baseCodec, Codec.restrict, inL, stringCodec,
         NEFinset.of],
   rfl,
   by simp [denote, denote, literalCodec, baseCodec, Codec.restrict, inL, stringCodec,
         NEFinset.of]⟩

/-- `string` does not, as §5 also says. -/
theorem not_decides_string : ¬ Decides .string := by
  rintro ⟨v, w, hv, hk, hw⟩
  simp only [denote, denote] at hv hw
  cases v <;> cases w <;> simp_all [denote, stringCodec, Value.kind]

/-- **`ident` is too generous.** A refinement by the trivially-true predicate is `ident`,
    and decides nothing: `q` is checked on both halves and always passes, so admission is
    no evidence at all. `ident` cannot see this, because it does not look at `q`. -/
theorem ident_refine_top : ident (.refine .string qTop) = true := rfl

theorem not_decides_refine_top : ¬ Decides (.refine .string qTop) := by
  rintro ⟨v, w, hv, hk, hw⟩
  simp only [denote, denote] at hv hw
  cases v <;> cases w <;>
    simp_all [denote, Codec.restrict, stringCodec, qTop, Value.kind]

/-- **And too stingy.** An object with a required field refuses the empty map and writes a
    populated one — two `map`s differing in admission — while `ident` calls it `false`. -/
theorem decides_object :
    Decides (.object {"k"} (fun _ => .req .string) .refuse) := by
  refine ⟨.map {"k"} (fun _ => .str "a"),
          .map ∅ (fun k => absurd k.2 (Finset.not_mem_empty k.1)), ?_, rfl, ?_⟩
  · simp [denote, denote, fieldTable, restSem, fieldSem, restSem,
          objectCodec, objectCodecCore, stringCodec,
          valPresentB, valPresentAt, fieldSem, rcOf, FieldSem.codec, carriedCodec,
          mapV, mA, Ctor.out, Ctor.into, objWrite, entryCodec, MapOf.at, funImage,
          Subtype.forall]
  · simp [denote, denote, fieldTable, restSem, fieldSem, restSem,
          objectCodec, objectCodecCore, stringCodec,
          valPresentB, valPresentAt, fieldSem, rcOf, FieldSem.codec, carriedCodec,
          mapV, mA, Ctor.out, Ctor.into, objWrite, MapOf.at, Subtype.forall]

theorem ident_object : ident (.object {"k"} (fun _ => .req .string) .refuse) = false := rfl

/-! ### …and the two errors are the same combinator

`refine` and `held` are not unrelated rows that happen to be wrong in opposite directions.
They are **one combinator with two adapters**: `Codec.adapt` generalises both, `held` taking
the total `some ∘ f` (`through_e_adapt`) and `refine` the partial identity `partialId q`
(`restrict_e_adapt`). The doc says as much — "the *same* combinator, weaker adapter".

`ident` gives them opposite rows. `refine` is `true` unconditionally; `held` propagates.
So the over-claim and the under-claim are the same mistake seen from two sides, and the
witnesses are duals:

* `refine(string, ⊤)` — the adapter narrows nothing, and `ident` says it decides.
* `held(string, fSplit, _)` — the adapter narrows to one string, and `ident` says it does
  not.

`Adm` has no such split. `Adm_refine_adapt` and `Adm_held_adapt` show it doing the one
thing `adapt` describes on both rows — apply the adapter, then ask the subterm — which is
why it carries `q` and `f` where `ident` carries neither. -/

/-- An adapter that sends one string to itself and everything else off `string`'s carrier.
    Total, so this is a `held` and not a `refine` — and it narrows exactly as a refinement
    would. -/
def fSplit : Value → Value := fun v => match v with | .str "A" => .str "A" | _ => .bool true

/-- **The dual gap.** `held(string, fSplit, _)` writes `"A"` and refuses `"B"` — two values
    of one kind, differing in admission — so it decides. `ident` says `false`. -/
theorem decides_held : Decides (.held .string fSplit (fun v => v)) := by
  refine ⟨.str "A", .str "B", ?_, rfl, ?_⟩
  · simp [denote, denote, Codec.through, stringCodec, fSplit]
  · simp [denote, denote, Codec.through, stringCodec, fSplit]

theorem ident_held_false : ident (.held .string fSplit (fun v => v)) = false := rfl

/-- `Adm` treats the two adapters uniformly: apply it, then ask the subterm. -/
theorem Adm_refine_adapt (t : Term) (q : Value → Bool) (v : Value) :
    Adm (.refine t q) v = ((partialId q v).elim false (Adm t)) := by
  cases hq : q v <;> simp [Adm, partialId, hq]

theorem Adm_held_adapt (t : Term) (f g : Value → Value) (v : Value) :
    Adm (.held t f g) v = ((some (f v)).elim false (Adm t)) := by
  simp [Adm]

/-! ### Adapters and alternatives, and why `legacy` was in the wrong family

`held` and `refine` are `Codec.adapt` with different adapters. `legacy` is **not** an
adapter at all, and asking whether it was is what found the row above.

An adapter *composes*: `adapt`'s read is `(c.p a).bind g`, so it can only lose attributes —
`adapt_p_le`. `legacy`'s read *gains* them: `extendRead`'s `p` is the subterm's channel
falling back to `r`'s, which is a **choice**, not a composition. That is the family
`nullable` belongs to as well (`orNull` adjoins the null point on both sides) and `union`
(`altCodec`, n-ary, both sides). `legacy` is the one-sided member: it reads on two channels
and writes on one.

Placing it correctly is what makes the row exact. §5 called `admA(legacy)` `⊤` because
`extendRead` widens past the subterm's set — true, and the wrong conclusion, because the
thing it widens *by* is `r`, which the term carries. The domain is
`dom(p) ∪ dom(r)`, both halves named, and `AdmA` can apply `r` for the same reason it can
apply `held`'s `f` and `custom`'s `cp`.

So `legacy` leaves the attribute hatch, and the `widenedRead` excuse is deleted rather than
witnessed: it was covering a row that did not need excusing. What survives untouched is
`not_admA_legacy` — §5's *passthrough* really is unsound, and the union is not the
passthrough. -/

/-- An adapter never widens the read domain. -/
theorem adapt_p_le {c : Codec} {f g : Value → Option Value} {a : Attr} :
    ((c.adapt f g).p a).isSome = true → (c.p a).isSome = true := by
  intro h
  simp only [Codec.adapt] at h
  cases hc : c.p a with
  | none => rw [hc] at h; simp at h
  | some _ => rfl

/-- `legacy` is the read-side alternative: the subterm's channel, falling back to `r`'s. -/
theorem legacy_p_alt (t : Term) (r : Attr → Option Value) (a : Attr) :
    (denote (.legacy t r)).p a
      = (match (denote t).p a with | some v => some v | none => r a) := rfl

/-- …so its read domain is the union of the two channels, and both are named. -/
theorem legacy_p_isSome (t : Term) (r : Attr → Option Value) (a : Attr) :
    ((denote (.legacy t r)).p a).isSome = (((denote t).p a).isSome || (r a).isSome) := by
  simp only [legacy_p_alt]
  cases (denote t).p a <;> simp

/-- Which is exactly `AdmA`'s row, so `legacy` widens the read side and is exact anyway. -/
theorem AdmA_legacy_union (t : Term) (r : Attr → Option Value) (a : Attr) :
    AdmA (.legacy t r) a = (AdmA t a || (r a).isSome) := by
  simp [AdmA]

/-- **A discharge §5 could not state.** Two sets over disjoint literals separate, because
    `℘⁺fin` has no empty inhabitant and so the two options share none. The non-emptiness
    is the *type's*, which is why every branch here ends at `S.2`.

    The terms are `refine(set(string), liftQ …)` where they were `set(literal …)`, and that
    is the whole of what the re-indexing cost this discharge: with `set` taking a base, a
    literal element is a **restriction of the set**, and `setCodec_restrict` proves the two
    write the same attribute on the nose. Same separation, one spelling further out. -/
theorem sepJV_set_literals :
    SepJV (.refine (.set .string) (liftQ (inL .string (.of "A" ∅))))
          (.refine (.set .string) (liftQ (inL .string (.of "B" ∅)))) := by
  intro v hv
  cases v
  case strSet S =>
    obtain ⟨x, hx⟩ := S.2
    simp only [Adm, Bool.and_eq_true, liftQ, decide_eq_true_eq] at hv
    have hxA : x = "A" := by
      have h1 := hv.2 x hx
      simpa [inL, NEFinset.of] using h1
    simp only [Adm, liftQ, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    refine Or.inr (fun hall => ?_)
    have h2 := hall x hx
    rw [hxA] at h2
    simp [inL, NEFinset.of] at h2
  -- the other two wire families are refused by the *set* row, element by element: a
  -- `string` base admits no number and no byte string, and `℘⁺fin` supplies the element
  case numSet S =>
    obtain ⟨x, hx⟩ := S.2
    simp only [Adm, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    exact Or.inl (fun hall => by have h := hall x hx; simp [SetBase.adm] at h)
  case binSet S =>
    obtain ⟨x, hx⟩ := S.2
    simp only [Adm, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    exact Or.inl (fun hall => by have h := hall x hx; simp [SetBase.adm] at h)
  all_goals simp [Adm, liftQ]

/-- …and the contrast that shows what the non-emptiness is doing: the *array* pair does not
    separate, because both options admit `[]`. This is §5's empty-container argument in its
    correct scope — it is a fact about `array`, `record` and `object`, not about `set`. -/
theorem not_sepJV_array_literals :
    ¬ SepJV (.array (.literal .string (.of "A" ∅))) (.array (.literal .string (.of "B" ∅))) := by
  intro h
  exact absurd (h (.arr []) (by simp [Adm, allP])) (by simp [Adm, allP])

/-! ### What `set` is, structurally — and the defect that closed

Three readings were worth separating. Two were right and the third found a defect; the
defect is now fixed by the type, and these are the witnesses that it is.

**Not a `union`.** A union is a choice among *codecs*, resolved by (U); a set's elements all
go through **one** codec, so no uniqueness obligation arises. That is why `set` needs no (U)
and `union` does.

**Not `array` with a wrapper either, any more.** It was, while both were lists: the two
shared `traverse c.e vs` and differed only in how the payload list was presented. With the
sets typed there is no shared list to share — `array` traverses a `List Value`, `set` images
a `Finset` — and what survives of the old observation is that the *element* codec is the
same in both.

**And "order does not matter" is now true of the model**, where it was not. §1 types `SS` as
`℘⁺fin(String)` and the reference says the order of a set's values is not preserved and each
value is unique. Three theorems recorded that the model disagreed. They are replaced by the
three below, which say the disagreement is over: an ordering is not a distinction a `Finset`
can make, and a repeat is not an inhabitant it can hold. -/

/-- Two "orderings" of one set are the same value — there is nothing to quotient. -/
theorem set_order_irrelevant :
    (Value.strSet (.of "a" {"b"})) = (Value.strSet (.of "b" {"a"})) :=
  congrArg Value.strSet (Subtype.ext (Finset.ext fun x => by
    simp only [NEFinset.of, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun h => h.elim (fun e => Or.inr e) (fun e => Or.inl e),
           fun h => h.elim (fun e => Or.inr e) (fun e => Or.inl e)⟩))

/-- …and the same attribute. -/
theorem wireSet_order_irrelevant :
    (Attr.ss (.of "a" {"b"})) = (Attr.ss (.of "b" {"a"})) :=
  congrArg Attr.ss (Subtype.ext (Finset.ext fun x => by
    simp only [NEFinset.of, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun h => h.elim (fun e => Or.inr e) (fun e => Or.inl e),
           fun h => h.elim (fun e => Or.inr e) (fun e => Or.inl e)⟩))

/-- A repeat is not an inhabitant: `℘⁺fin` has no multiplicities, and neither does the
    model now. -/
theorem set_no_duplicates :
    (Value.strSet (.of "a" {"a"})) = (Value.strSet (.of "a" ∅)) :=
  congrArg Value.strSet (Subtype.ext (Finset.ext fun x => by
    simp only [NEFinset.of, Finset.mem_insert, Finset.mem_singleton,
      Finset.not_mem_empty, or_false]
    exact ⟨fun h => h.elim id id, fun h => Or.inl h⟩))

/-! ### What (R) would have forced, had the type not settled it

The repair was once going to be a canonical form over lists, and (R) constrained it hard:
retraction is to the *same* value, not an agreeing one, so a codec whose `e` collapsed two
orderings would owe one attribute two readings. `e` could not normalise; it would have had
to accept exactly one representative per set and refuse the rest, with `p` normalising so
that `ker p` collapsed the orderings — §2's sentence, made true by construction.

None of that is needed. `Finset` has one representative per set *as a type*, so there is
nothing for `e` to choose between and nothing for `p` to collapse; `ker p` is equality at
`setCodec` and that is now correct rather than a defect. The constraint is recorded because
it is what rules out the alternative design, not because anything here depends on it.

`Calculus/WireOrder.lean` — the canonical form and the axiom-free order it was built on — was
likewise no longer on the set path, and has been deleted; the `Classical.choice` hazard it
existed to route around is recorded beside `NEFinset` in `Domain.lean`. Nor, as the next section shows, on the map path: the
quotient the kernel refuses is `Finset (Name × Attr)`, and `M` does not need it. -/

/-! ### The reference, checked against the model

`docs/dynamo-datatypes.md` is the official datatype reference. Most of §1 survives it
exactly — `Numeral.WF`'s 38 digits and `-130 … 125` exponent range are the documented
bounds; binary compares unsigned; empty strings and empty binary are permitted, empty lists
and maps are permitted, empty sets are not, and the model already refuses the last.

Two things do not survive, and they are the same defect at two members.

**`SS`/`NS`/`BS`** — *"Each value within a set must be unique. The order of the values within
a set is not preserved."* Recorded above.

**`M`** — *"A map type attribute can store an **unordered** collection of name-value
pairs."* The model's `M` was a `List (Name × Attr)`, so two orderings of one map were two
attributes and a repeated key was writable, which no map has. Three theorems recorded the
disagreement; they are replaced by the three below.

This one was called sharper than the set case for two reasons, and only the first survives.
The model does *state* the intent elsewhere — `Agree` at `M` compares by key and ignores
order — so the two halves of the model disagreed with each other and not merely with the
reference. But the second reason, that maps cannot be repaired by typing, was wrong, and the
correction is the content of this section. `Finset (Name × Attr)` **is** rejected by the
kernel, exactly as `Finset Value` is, the element type being the one under declaration. What
does not follow is that `M` needs the well-formedness route. The pair need not be the
element: §1's `M` is a finite *partial function*, so the names go in a `Finset` over the
concrete type `Name` and the attributes go in a function's codomain — a strictly positive
position, which the kernel accepts:

    | m (keys : Finset Name) (f : {k // k ∈ keys} → Attr)

Unordered, unique-keyed and total-on-its-keys are now facts about the type. No canonical
order, no `Wire.canon`, and nothing for `e` to choose between. -/

/-- Two "orderings" of one map's names are one name set — there is nothing to quotient. -/
theorem mapKeys_order_irrelevant : ({"a", "b"} : Finset Name) = {"b", "a"} :=
  Finset.ext fun x => by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun h => h.elim (fun e => Or.inr e) (fun e => Or.inl e),
           fun h => h.elim (fun e => Or.inr e) (fun e => Or.inl e)⟩

/-- …so the codec has one answer where it used to have two. Equal key sets and
    pointwise-equal entries are one attribute (`MapOf.ext`), and one attribute is one
    reading — the order-sensitivity had nowhere left to live. -/
theorem record_p_order_irrelevant
    (g : {k // k ∈ ({"a", "b"} : Finset Name)} → Attr)
    (g' : {k // k ∈ ({"b", "a"} : Finset Name)} → Attr)
    (h : ∀ k (h₁ : k ∈ ({"a", "b"} : Finset Name)) (h₂ : k ∈ ({"b", "a"} : Finset Name)),
      g ⟨k, h₁⟩ = g' ⟨k, h₂⟩) :
    (recordCodec stringCodec).p (.m {"a", "b"} g)
      = (recordCodec stringCodec).p (.m {"b", "a"} g') :=
  congrArg (fun p : MapOf Attr => (recordCodec stringCodec).p (.m p.1 p.2))
    (MapOf.ext (p := ⟨{"a", "b"}, g⟩) (q := ⟨{"b", "a"}, g'⟩) mapKeys_order_irrelevant h)

/-- A repeated key is not an inhabitant: the map that was supposed to carry `"a"` twice is
    the map that carries it once. -/
theorem mapKeys_no_duplicates : ({"a", "a"} : Finset Name) = {"a"} :=
  Finset.ext fun x => by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun h => h.elim id id, fun h => Or.inr h⟩

end
end Calculus

