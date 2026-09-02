import Calculus.Discharge
import Calculus.Soundness

/-!
# §5 — exactness: what `κ` and `adm` were computing between them

`κ`, `ident`, `adm` and `admA` are **over**-approximations, and that is the whole of the
problem this file exists to fix. `⊤` is sound for every term, so a row that claims nothing
is a row that can never fail, and every defect this development has caught in §5's tables was
an imprecision rather than an unsoundness. A soundness obligation attached to each row
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

`Adm` below is that joint predicate as a single recursion, exact at **all twenty-one
constructors**: `Adm_exact : ∀ t, ExactV t`, no hypothesis and no escape hatch.

**`union` is the one row whose looseness was about something real, and its reason is why
`ExactV_union` takes a hypothesis.** `select` admits where *exactly one* option does, and a
count is anti-monotone: loosen an option and you add an admitting option, so the count refuses
where the codec writes. That makes the count unsound *while any row is loose*. Once no row is
loose there is nothing left to loosen, and the count is exact given the options' exactness —
the hypothesis every other container row already takes. See `selOptV` and `ExactV_union`.

`nullable` is the row worth copying: `Codec.ownsNull` is a computable `Bool`, so the row
**asks** it rather than describing a disjunction over both halves of the pair.
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

/-- A `union` option's own admission, as `optionSemOf` builds it — and the two builders are
    **not** the same test. An *object* option decides by `keysOk`: which names the map carries,
    not what they hold. Every other option decides by *attempt*, which is its row exactly when
    its row is exact.

    That asymmetry is the whole of why this is not `Adm`. A row that counted `Adm` would count
    an object option by its fields' contents, where `select` counts it by its names — so the
    two would disagree on any union of objects, in both directions.

    Taking `(spec, row)` rather than the term is what keeps the recursion structural, the same
    shape `selTagV` takes; `specOf` is a function of the term, so the distinction is available
    here without consulting a codec. -/
def admitOptV (o : Option (MapOf Bool) × VP) (v : Value) : Bool :=
  match o.1 with
  | some spec => match v with | .map keys _ => keysOk spec keys | _ => false
  | none => o.2 v

/-- `select` at a `union`, as a row: filter the options by the admission each one reads, and
    the option that answers **alone** answers for the union.

    **This is the row ~~Excuse.uniqueAdmission~~ said would be unsound**, and the excuse was
    right about the calculus it was written in. A count is anti-monotone — loosen an option and
    you add an admitting option, which turns a singleton into a pair and makes the row refuse
    where the codec writes — so while any row was loose, sharpening `union` traded imprecision
    for unsoundness. What the argument did not reach is that the count is *exact given the
    options' exactness*, which is the hypothesis every other container row already carries; and
    once `set` (a narrower constructor) and `nullable` (a row that asks `ownsNull`) stopped
    being loose, there was nothing left to loosen. The excuse was a fact about the state of the
    table, recorded as a fact about the row. -/
def selOptV (os : List (Option (MapOf Bool) × VP)) (v : Value) : Bool :=
  match os.filter (fun o => admitOptV o v) with
  | [o] => o.2 v
  | _ => false

/-- What the literal codec **writes**, exactly.

    **This was `inL` conjoined with `Numeral.WF`, and the conjunct is now the carrier's.**
    The second conjunct existed because at `number` an alternative outside §1's `D` was *held*
    and not *written*, so membership alone over-claimed — the same (B) failure ~~LiteralD~~
    forbade in a derivable term, stated here as a fact about the codec, which had no premise to
    lean on. `GroundKind.number.Carrier` is `WFDouble`, so `inL`'s own row splits on the gate
    and there is no alternative left for the conjunct to catch.

    What that closes is §8's third open question. `adm`'s literal row (`Discharge.lean`) was
    always `inL` and was therefore inexact at `number` by exactly this conjunct; the joint row
    carried it and so `Adm_exact` covered the literal. The two rows are now the *same
    function* — `adm_literal_eq_Adm` — so the older generation is exact at this row for free.
    The defect is closed rather than patched: nothing was added to `adm`. -/
noncomputable def AdmLit (k : GroundKind) (ls : NEFinset k.Carrier) (v : Value) : Bool :=
  inL k ls v

mutual

/-- **The joint admission predicate.** What `κ` and `adm` compute between them, as one
    structural recursion — and the containers recurse with *this*, which is exactly what
    the old rows failed to do.

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
  -- **`ownsNull` is asked, not assumed.** The row was `Adm t v || v = null`, which claims
  -- the wrapper always adds the point. §3's `withNull` adds it *unless the subterm already
  -- owns it*, and `ownsNull` is a disjunction over **both** halves — so a subterm whose
  -- *read* reaches null (a `legacy` widening) suppresses the wrapper while its write still
  -- refuses null, and the old row admitted a value the codec does not write
  -- (~~not_ExactV_nullable~~, deleted with the excuse it witnessed).
  --
  -- The conjunct is the sixth row to **ask its codec** rather than describe it, and the
  -- cheapest of them: `Codec.ownsNull` is a computable `Bool` off the subterm's pair, so
  -- this needs no mutual recursion and no new vocabulary — only the question the old row
  -- answered from a reading.
  | .nullable t => fun v =>
      Adm t v || ((match v with | .null => true | _ => false) && !(denote t).ownsNull)
  -- **`select`'s count, mirrored** — where this was `⋁` over the options. The `⋁` was
  -- inexact with perfectly exact options (`union [string, string]`: two admit, so the union
  -- writes nothing while `⋁` says yes), and the count that fixes it was refused on
  -- anti-monotonicity grounds that held only while some other row was loose. None is.
  --
  -- The count is over `AdmSpecs`, not over `Adm`: an object option is admitted by its
  -- **names** and not by its fields' contents, so the row must mirror `optionSems` rather
  -- than count rows. See `admitOptV`.
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
  | .tuple ts tail => fun v =>
      match v with | .arr vs => alignP (AdmList ts) (AdmOptT tail) vs | _ => false
  | .object b => AdmBody b
  | .dunion d opts => fun v => selTagV d (AdmTagged d opts) v
  -- **The second row that asks its own codec**, and the same row `adm` has
  -- (`Discharge.lean`): `denote (.opaq lossy)` *is* `opaqCodecω lossy`, so this is
  -- `dom(e)` rather than a description of it, and `ExactV_opaq` is `Iff.rfl`.
  --
  -- It replaces a hand-written recursion over the value (~~AdmOpaqV~~) that computed the
  -- same set. That recursion was correct and cost ~120 lines of proof, and it was the
  -- wrong shape for one reason: it stated `opaque`'s domain a *second* time, so a change
  -- to `opaqCodec` — a new option, a different numeric policy — meant editing two
  -- definitions that had to agree. Deferring leaves one.
  | .opaq lossy => fun v => ((opaqCodecω lossy).e v).isSome

/-- The payload's row: the declared names are present, and every present name's value is
    admitted by its field or by the rest policy. The companion `AdmField` and `AdmRest`
    were missing — `Adm`'s object row inlined it, so the one place that says what an object
    payload admits was a row of a table rather than a definition. -/
noncomputable def AdmBody : Body → VP
  | .mk fields fld rest => fun v =>
      match v with
      | .map keys g =>
          valPresentT fields fld keys &&
          objAdmV ⟨fields, fun k => AdmField (fld k)⟩ (AdmRest rest) keys g
      | _ => false

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

/-- Each `union` option paired with its name spec — `optionSems`' mirror, the way
    `AdmTagged` mirrors `denoteTagged`. `specOf` is what tells an object option from the
    rest, and it is a function of the term. -/
noncomputable def AdmSpecs : List Term → List (Option (MapOf Bool) × VP)
  | [] => []
  | t :: ts => (specOf t, Adm t) :: AdmSpecs ts

end

@[simp] theorem AdmList_eq : ∀ ts : List Term, AdmList ts = ts.map Adm
  | [] => rfl
  | t :: ts => by simp only [AdmList, List.map]; rw [AdmList_eq ts]

@[simp] theorem AdmTagged_eq : ∀ (d : Name) (opts : List Term),
    AdmTagged d opts = opts.map fun t => (tagsOf d t, Adm t)
  | _, [] => rfl
  | d, t :: ts => by simp only [AdmTagged, List.map]; rw [AdmTagged_eq d ts]

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

/-- **The count implies the disjunction**, which is the direction the containments need: the
    option that answers *alone* is in particular an option that answers.

    The converse is exactly what fails, and `union [string, string]` is the witness — which is
    why the row is the count and not the `⋁` it used to be. -/
theorem selOptV_le_AdmAny {opts : List Term} {v : Value}
    (h : selOptV (AdmSpecs opts) v = true) : AdmAny opts v = true := by
  simp only [selOptV, AdmSpecs_eq] at h
  cases hf : (opts.map fun t => (specOf t, Adm t)).filter (fun o => admitOptV o v) with
  | nil => rw [hf] at h; exact absurd h (by simp)
  | cons o rest =>
    cases rest with
    | cons _ _ => rw [hf] at h; exact absurd h (by simp)
    | nil =>
      rw [hf] at h
      have hmem : o ∈ opts.map fun t => (specOf t, Adm t) :=
        (mem_of_filter_eq_singleton hf).1
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hmem
      exact AdmAny_of_mem ht h

/-- `Adm`'s literal row, named.

    Nothing should `simp [Adm]` at a literal: the row's pattern is *dependent* — `ls`'s type
    mentions `k` — so generating the table's equation lemmas across it is expensive enough to
    exhaust the heartbeat budget in proofs that used to close in one step. Stating the row once
    contains that cost, and every literal proof below rewrites with this instead. -/
@[simp] theorem Adm_literal (k : GroundKind) (ls : NEFinset k.Carrier) (v : Value) :
    Adm (.literal k ls) v = AdmLit k ls v := by unfold Adm; rfl

/-- §5's converse direction: the row is `dom(e)`, not merely a bound on it. -/
def ExactV (t : Term) : Prop := ∀ v, Adm t v = true ↔ ((denote t).e v).isSome

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
        have ht : t ∈ opts := (mem_of_filter_eq_singleton hL).1
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
    (hr : ∀ t, rest = .codec t → ExactV t) :
    ExactV (.object (.mk fields fld rest)) := by
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
    simp [Adm, AdmBody, denote, bodySem, objectCodec, objectCodecCore, carriedCodec, mapV,
      Ctor.out]

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
    of an escape hatch is that hatch's own answer, and nothing about what the answer is.
    What it replaced was a 120-line induction (~~AdmOpaqV_iff~~) proving a hand-written
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

/-- Each option's row *is* the admission `optionSemOf` builds for it — given that option's
    exactness, which is where the exactness hypothesis is spent.

    Two cases and they are not symmetric. At an **object** option both sides are `keysOk`,
    definitionally, and the hypothesis is not used at all: `select` never attempts an object
    option, and neither does the row. Everywhere else the admission *is* `(c.e ·).isSome`, and
    the hypothesis is exactly what identifies it with the row. -/
theorem admitOptV_eq {t : Term} (h : ExactV t) (v : Value) :
    (optionSemOf (denote t) (specOf t)).admitV v = admitOptV (specOf t, Adm t) v := by
  unfold admitOptV
  cases hs : specOf t with
  | some spec => rfl
  | none =>
    simp only [hs, optionSemOf, OptionSem.byAttempt]
    exact Bool.coe_iff_coe.mp (by simpa using (h v).symm)

/-- The row's own filter, pushed through the map — the plain commutation, no hypothesis. -/
theorem filter_map_AdmSpecs (opts : List Term) (v : Value) :
    (opts.map fun t => (specOf t, Adm t)).filter (fun o => admitOptV o v)
      = (opts.filter fun t => admitOptV (specOf t, Adm t) v).map
          fun t => (specOf t, Adm t) := by
  induction opts with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, List.filter_cons, ih]
    cases hb : admitOptV (specOf t, Adm t) v <;> simp [hb]

/-- **The option list's filter is the term list's, mapped.** This is the step that lets a row
    count terms where `select` counts semantics, and it is an induction rather than a rewrite
    because the agreement above is per-option and hypothesis-bearing. -/
theorem filter_AdmSpecs {opts : List Term} (h : ∀ t ∈ opts, ExactV t) (v : Value) :
    (optionSems opts).filter (·.admitV v)
      = (opts.filter (fun t => admitOptV (specOf t, Adm t) v)).map
          (fun t => optionSemOf (denote t) (specOf t)) := by
  induction opts with
  | nil => rfl
  | cons t ts ih =>
    have ht : ExactV t := h t (by simp)
    have hts : ∀ t' ∈ ts, ExactV t' := fun t' h' => h t' (by simp [h'])
    simp only [optionSems, List.filter_cons, admitOptV_eq ht, ih hts]
    cases hb : admitOptV (specOf t, Adm t) v <;> simp [hb]

/-- **`union` writes exactly what its row says**, and this is the row ~~Excuse.uniqueAdmission~~
    said could not be written soundly.

    The excuse's argument was correct and its scope was the table, not the row: a count is
    anti-monotone, so while any option's row could be loose the count could refuse where the
    codec writes. The hypothesis here is the same one `ExactV_tuple`, `ExactV_object` and
    `ExactV_dunion` all take — the options are exact — and once `set` and `nullable` stopped
    declining there is no term at which it is unavailable. `Adm_exact` supplies it by
    structural recursion, exactly as it does at every other container.

    What the proof spends it on is narrower than the excuse suggested: the *filter*, not the
    count. `select` filters `optionSems` and the row filters terms; identifying the two needs
    each option's admission to be its row, which at an object option is free and everywhere
    else is exactness. The count itself is then a `cases` on a list. -/
theorem ExactV_union {opts : List Term} (h : ∀ t ∈ opts, ExactV t) : ExactV (.union opts) := by
  intro v
  rw [denote_union_sems]
  show selOptV (AdmSpecs opts) v = true ↔ (select (optionSems opts) (·.admitV) (·.c.e) v).isSome
  rw [AdmSpecs_eq]
  unfold select selOptV
  -- both sides become a match over the *same* filtered term list: the row's by
  -- `filter_map_AdmSpecs`, `select`'s by `filter_AdmSpecs`
  rw [filter_map_AdmSpecs opts v, filter_AdmSpecs h v]
  cases hf : opts.filter (fun t => admitOptV (specOf t, Adm t) v) with
  | nil => simp
  | cons t rest =>
    cases rest with
    | nil =>
      have ht : ExactV t := h t (mem_of_filter_eq_singleton hf).1
      simpa [optionSemOf_c] using ht v
    | cons t2 r2 => simp

/-- **`nullable` writes exactly what its row says**, once the row asks `ownsNull`.

    The proof is the definition of `withNull` in two cases, and each case is where the old
    row went wrong or did not:

    * `ownsNull = true` — the wrapper is *suppressed*, `e` is the subterm's, and the row
      collapses to the subterm's row. The old row still offered `null`, and at
      `nullable(legacy(string, ⟨NULL⟩))` that was a value the pair refuses to write: the
      read side owns the point, so the guard fires, and the write side is `string`'s.
    * `ownsNull = false` — the wrapper is `orNull`, and the point really is added.

    So the conjunct is not a repair of an approximation. It is the guard §3 already has,
    stated on the side of the analysis that had been reading it as unconditional. -/
theorem ExactV_nullable {t : Term} (h : ExactV t) : ExactV (.nullable t) := by
  intro v
  rw [denote_nullable]
  simp only [Adm, Codec.withNull]
  cases hw : (denote t).ownsNull with
  | true => simp [hw, h v]
  | false =>
    simp only [hw, Bool.not_false, Bool.and_true, if_false, Bool.false_eq_true, addPoint]
    cases v <;> simp [h _]

-- `unnecessarySeqFocus` fires on `Adm_exact`'s `literal` case and is wrong there: `try split`
-- leaves two goals at `decimal`, and the `;` it suggests would reach only the first.
-- Suppressed at the block, as the three `term_depth_wf` recursions already do.
set_option linter.unnecessarySeqFocus false in
mutual
/-- **Every row is exact.** Not a bound on `dom(e)` — `dom(e)`, at all twenty-one
    constructors and with no hypothesis.

    The `held` case is the one worth reading: it appeals to the subterm at `f v`, which is
    the pullback, and it is one line because `(c.through f g).e v = c.e (f v)` holds by
    `Iff.rfl`. The `array` and `record` cases are the repair of §5's container rows.

    **There is no hypothesis to discharge**, which is the whole of what the last two rows
    bought: `Adm_sound` is now `(Adm_exact t v).mpr`, and a new `Term` constructor cannot be
    added without a case here.

    Mutual with the list, option, field and rest companions, for the same reason `denote` is:
    a tuple's components and a `dunion`'s options are reached through a `List Term` and an
    object's fields through a *function*, and a single recursion on the term cannot follow
    either. -/
theorem Adm_exact : ∀ (t : Term), ExactV t
  -- the rows §5 excused, and not one of them needed excusing
  | .tuple ts tail =>
      ExactV_tuple (exactVL_mem ts (Adm_exactL ts)) (exactVO_mem tail (Adm_exactO tail))
  | .dunion _ opts => ExactV_dunion (exactVL_mem opts (Adm_exactL opts))
  | .object (.mk fields fld rest) =>
      ExactV_object (fun k => Adm_exactF (fld k)) (exactVR_codec rest (Adm_exactR rest))
  | .opaq lossy => ExactV_opaq lossy
  -- the row the *constructor* made exact, rather than a sharper analysis of the old one
  | .set b => ExactV_set b
  -- the row that asks `ownsNull`
  | .nullable c => ExactV_nullable (Adm_exact c)
  -- the count is exact given the options' exactness, which is the hypothesis this
  -- recursion hands it. See `ExactV_union`.
  | .union opts => ExactV_union (exactVL_mem opts (Adm_exactL opts))

  | .string => by intro v; cases v <;> simp [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, stringCodec]
  | .boolean => by intro v; cases v <;> simp [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, booleanCodec]
  | .binary => by intro v; cases v <;> simp [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, binaryCodec]
  | .null => by intro v; cases v <;> simp [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, nullCodec]
  | .number => by intro v; cases v <;> simp [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, inD]
  | .decimal => by intro v; cases v <;> simp [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, isStored]
  -- three rows into one, and `numberCodec` is read through `numberCodec_e_isSome` rather
  -- than unfolded: its `dite` is a string parser, and `simp` inside it runs out of heartbeats.
  --
  -- `unnecessarySeqFocus` fires on the `<;>` before `simp_all` below and is wrong: `try split`
  -- leaves two goals at `decimal` and `;` would reach only the first. Suppressed at the
  -- declaration rather than restructured, the way the `term_depth_wf` recursions already do.
  | .literal k ls => by
      intro v
      cases k <;> cases v <;>
        simp [AdmLit, denote, denote, literalCodec, baseCodec, inL,
              stringCodec, booleanCodec, binaryCodec, nullCodec, inD, decimalCodec] <;>
        -- `decimal` alone leaves a goal: its `inL` is a `dite` on the gate, and splitting it is
        -- what shows the alternatives already carry `Stored` — the base's whole point.
        (try split) <;> simp_all [isStored]
  | .custom ce cp => by intro v; simp [Adm, denote, denote]
  | .array c => by
      have hc := Adm_exact c
      intro v
      cases v
      case arr xs =>
        simp only [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, arrayCodec, Option.isSome_map]
        rw [AdmAll_iff hc, ← traverse_isSome_iff]
        cases traverse (denote c).e xs <;> simp
      all_goals simp [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, arrayCodec]
  | .record c => by
      have hc := Adm_exact c
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
      have hc := Adm_exact c
      intro v; cases hq : q v <;> simp [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, Codec.restrict, hq, hc v]
  | .legacy c r => by
      have hc := Adm_exact c
      intro v; simpa [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, Codec.extendRead] using hc v
  | .lazy c => by
      have hc := Adm_exact c
      intro v; simpa [Adm, denote] using hc v
  | .held c f g => by
      have hc := Adm_exact c
      intro v; simpa [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, Codec.through] using hc (f v)

/-- The options' exactness, in the shape the recursion can produce it: a `∀ t ∈ ts` needs a
    membership hypothesis the structural checker cannot follow back to the constructor's
    argument, and this does not. -/
theorem Adm_exactL : ∀ (ts : List Term), ExactVL ts
  | [] => trivial
  | t0 :: ts => ⟨Adm_exact t0, Adm_exactL ts⟩

theorem Adm_exactO : ∀ (tail : Option Term), ExactVO tail
  | none => trivial
  | some t0 => Adm_exact t0

/-- A field's row is exact when its term's is — the marker plays no part, which is what
    `valPresentT` being a separate conjunct records. -/
theorem Adm_exactF : ∀ (fd : Field), ExactField fd
  | .req t0 => fun v => Adm_exact t0 v
  | .optional t0 => fun v => Adm_exact t0 v
  | .fallback t0 _ => fun v => Adm_exact t0 v

theorem Adm_exactR : ∀ (rest : Rest), ExactVR rest
  | .drop => trivial
  | .refuse => trivial
  | .codec t0 => Adm_exact t0
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

/-- **§8's third open question, closed — and closed by deletion, not by a patch.**

    `adm (.literal .number ls)` was the one inexact row in the older generation: it is `inL`,
    and `inL` was missing §1's `WF` gate, so the row admitted a `.num d` the codec refuses to
    write. The joint row `AdmLit` carried the gate as a second conjunct, which is why
    `Adm_exact` covered the literal while `adm` did not.

    Nothing was added to `adm`. `GroundKind.number.Carrier` became `WFDouble`, `inL`'s `number`
    row now splits on the element's own gate, and the two generations' literal rows are the
    same function on the nose. -/
theorem adm_literal_eq_Adm (k : GroundKind) (ls : NEFinset k.Carrier) :
    adm (.literal k ls) = Adm (.literal k ls) := rfl

/-- …so §5's own row is exact at every base, including `number`. -/
theorem adm_literal_exact (k : GroundKind) (ls : NEFinset k.Carrier) (v : Value) :
    adm (.literal k ls) v = true ↔ ((denote (.literal k ls)).e v).isSome := by
  rw [adm_literal_eq_Adm]
  exact Adm_exact (.literal k ls) v

/-- Soundness of every row — **now a corollary.**

    This was a hundred-and-twenty-line recursion on `Term.depth`, separate from `Adm_exact`
    because exactness was proved *given* the subterms' exactness and soundness could assume no
    such thing: `set`, `nullable` and `union` were loose, so a row over them had to be argued
    monotone instead. All three rows are exact now, `Adm_exact` carries no hypothesis, and the
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

/-- …and on the attribute side, where `byNames` reads the same name test off an `.m`. -/
def admitOptA (o : Option (MapOf Bool) × AP) (a : Attr) : Bool :=
  match o.1 with
  | some spec => match a with | .m keys _ => keysOk spec keys | _ => false
  | none => o.2 a

/-- …and the same count. -/
def selOptA (os : List (Option (MapOf Bool) × AP)) (a : Attr) : Bool :=
  match os.filter (fun o => admitOptA o a) with
  | [o] => o.2 a
  | _ => false

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
  -- **The `&& Numeral.WF d.toDec` conjunct used to be written out here**, and it was the
  -- reason this row was exact while the table's `adm` row was not (§8). It is now the
  -- carrier's: `ls : NEFinset WFDouble`, so the gate is what names the alternative.
  | .number,  ls, .n x    => (match Double.ofDec x.1 with
                              | some d =>
                                  if h : Numeral.WF d.toDec = true then
                                    decide ((⟨d, h⟩ : WFDouble) ∈ ls.1)
                                  else false
                              | none => false)
  -- `decimal` asks its codec, which is what `admALit` does at this base too — so the joint row
  -- and the table row are the *same function* here rather than two spellings that have to be
  -- proved equal. `number` cannot do this and spells the `ofDec` lookup out, because its answer
  -- depends on the host's numeric type; `decimal`'s does not.
  | .decimal, ls, a       => ((literalCodec .decimal ls).p a).isSome
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

    * `number` and a numeric `literal` go through `Double.ofDec`, which is
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
  -- the read side of the same question; see the `Adm` row. `withNull` guards *both* halves
  -- on the same `ownsNull`, so the conjunct is identical rather than a mirror of it.
  | .nullable t => fun a =>
      AdmA t a || ((match a with | .null => true | _ => false) && !(denote t).ownsNull)
  -- the read side of the same count; `byNames` reads the name test off an `.m`
  | .union opts => fun a => selOptA (AdmASpecs opts) a
  -- **the row that used to admit all three wire families whatever the element term was.**
  -- With the base an index the family is a function of it, so this names one — and at
  -- `number` defers to the codec, for the rounding residue `AdmASet` documents.
  | .set b    => AdmASet b
  | .tuple ts tail => fun a =>
      match a with | .l as => alignPA (AdmAList ts) (AdmAOptT tail) as | _ => false
  | .object b => AdmABody b
  | .dunion d opts => fun a => selTagA d (AdmATagged d opts) a
  -- the read side of the same deferral; see the `Adm` row and `ExactA_opaq`
  | .opaq lossy => fun a => ((opaqCodecω lossy).p a).isSome

/-- The read side's payload row; `AdmBody`'s mirror. -/
noncomputable def AdmABody : Body → AP
  | .mk fields fld rest => fun a =>
      match a with
      | .m keys g =>
          reqPresentT fields fld keys &&
          objAdmA ⟨fields, fun k => AdmAField (fld k)⟩ (AdmARest rest)
            (keepT rest fields) keys g
      | _ => false

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

/-- `optionSems`' mirror on the attribute side. -/
noncomputable def AdmASpecs : List Term → List (Option (MapOf Bool) × AP)
  | [] => []
  | t :: ts => (specOf t, AdmA t) :: AdmASpecs ts

end

@[simp] theorem AdmAList_eq : ∀ ts : List Term, AdmAList ts = ts.map AdmA
  | [] => rfl
  | t :: ts => by simp only [AdmAList, List.map]; rw [AdmAList_eq ts]

@[simp] theorem AdmATagged_eq : ∀ (d : Name) (opts : List Term),
    AdmATagged d opts = opts.map fun t => (tagsOf d t, AdmA t)
  | _, [] => rfl
  | d, t :: ts => by simp only [AdmATagged, List.map]; rw [AdmATagged_eq d ts]

@[simp] theorem AdmASpecs_eq : ∀ opts : List Term,
    AdmASpecs opts = opts.map fun t => (specOf t, AdmA t)
  | [] => rfl
  | t :: ts => by simp only [AdmASpecs, List.map]; rw [AdmASpecs_eq ts]

/-- `⋁` of `AdmA` over a union's options; sound, and inexact for the reason the value side
    gives. -/
noncomputable def AdmAAny (ts : List Term) (a : Attr) : Bool := anyPA (AdmAList ts) a

@[simp] theorem AdmAAny_nil (a : Attr) : AdmAAny [] a = false := rfl

@[simp] theorem AdmAAny_cons (t : Term) (ts : List Term) (a : Attr) :
    AdmAAny (t :: ts) a = (AdmA t a || AdmAAny ts a) := rfl

theorem AdmA_union (opts : List Term) (a : Attr) :
    AdmA (.union opts) a = selOptA (AdmASpecs opts) a := rfl

/-- An option that admits makes the disjunction true. -/
theorem AdmAAny_of_mem {t : Term} {ts : List Term} {a : Attr} (ht : t ∈ ts)
    (h : AdmA t a = true) : AdmAAny ts a = true := by
  induction ts with
  | nil => exact absurd ht (by simp)
  | cons t0 ts ih =>
    rcases List.mem_cons.mp ht with rfl | h'
    · simp [AdmAAny_cons, h]
    · simp [AdmAAny_cons, ih h']

/-- The count implies the disjunction — see `selOptV_le_AdmAny`. -/
theorem selOptA_le_AdmAAny {opts : List Term} {a : Attr}
    (h : selOptA (AdmASpecs opts) a = true) : AdmAAny opts a = true := by
  simp only [selOptA, AdmASpecs_eq] at h
  cases hf : (opts.map fun t => (specOf t, AdmA t)).filter (fun o => admitOptA o a) with
  | nil => rw [hf] at h; exact absurd h (by simp)
  | cons o rest =>
    cases rest with
    | cons _ _ => rw [hf] at h; exact absurd h (by simp)
    | nil =>
      rw [hf] at h
      have hmem : o ∈ opts.map fun t => (specOf t, AdmA t) :=
        (mem_of_filter_eq_singleton hf).1
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hmem
      exact AdmAAny_of_mem ht h

/-- `AdmA`'s literal row, named — for the reason `Adm_literal` gives. -/
@[simp] theorem AdmA_literal (k : GroundKind) (ls : NEFinset k.Carrier) (a : Attr) :
    AdmA (.literal k ls) a = AdmALit k ls a := by unfold AdmA; rfl

/-! The four bases whose stored attribute *is* the value, stated as standalone lemmas with
their carriers written out.

`GroundKind.Carrier` is reducible, so `NEFinset k.Carrier` at a *constructor* `k` is the same
type as `NEFinset Bytes` — but it is not the same *expression*, and `simp` inside the goal
re-derives that on every rewrite. At `binary` (`List UInt8`) and `null` (`Unit`) that was
enough to exhaust the heartbeat budget. Taking the carrier as a plain type in the statement
does the reduction once, at elaboration.

`string` and `boolean` are here for the same reason and not because they failed: inline in
`AdmA_exact` they were re-derived inside a twenty-case fan, and the row each one needs is a
statement about *one* base. `AdmA_exact` cites all four and unfolds none. -/

theorem AdmALit_binary_exact (ls : NEFinset Bytes) (a : Attr) :
    AdmA (.literal .binary ls) a = true ↔ ((denote (Term.literal .binary ls)).p a).isSome = true := by
  cases a <;>
    simp [AdmA_literal, AdmALit, denote, denote, literalCodec, baseCodec,
          binaryCodec]

theorem AdmALit_null_exact (ls : NEFinset Unit) (a : Attr) :
    AdmA (.literal .null ls) a = true ↔ ((denote (Term.literal .null ls)).p a).isSome = true := by
  cases a <;>
    simp [AdmA_literal, AdmALit, denote, denote, literalCodec, baseCodec,
          nullCodec]

/-- `(literal)` at `string`, read side. `NEFinset String` and not `NEFinset k.Carrier`: the
    carrier reduces once here instead of on every rewrite. -/
theorem AdmALit_string_exact (ls : NEFinset String) (a : Attr) :
    AdmA (.literal .string ls) a = true ↔ ((denote (Term.literal .string ls)).p a).isSome = true := by
  cases a <;>
    simp [AdmA_literal, AdmALit, denote, denote, literalCodec, baseCodec,
          stringCodec]

/-- `(literal)` at `boolean`, read side. Same shape as `AdmALit_string_exact`, and the two
    cannot share a `simp` set — one of them would have to name the other's codec. -/
theorem AdmALit_boolean_exact (ls : NEFinset Bool) (a : Attr) :
    AdmA (.literal .boolean ls) a = true ↔ ((denote (Term.literal .boolean ls)).p a).isSome = true := by
  cases a <;>
    simp [AdmA_literal, AdmALit, denote, denote, literalCodec, baseCodec,
          booleanCodec]


/-- The converse direction on the attribute side: the row is `dom(p)`, not a bound on it. -/
def ExactA (t : Term) : Prop := ∀ a, AdmA t a = true ↔ ((denote t).p a).isSome

/-- The read-side agreement, option by option — `admitOptV_eq`'s twin. -/
theorem admitOptA_eq {t : Term} (h : ExactA t) (a : Attr) :
    (optionSemOf (denote t) (specOf t)).admitA a = admitOptA (specOf t, AdmA t) a := by
  unfold admitOptA
  cases hs : specOf t with
  | some spec => rfl
  | none =>
    simp only [hs, optionSemOf, OptionSem.byAttempt]
    exact Bool.coe_iff_coe.mp (by simpa using (h a).symm)

/-- The row's own filter, pushed through the map. -/
theorem filter_map_AdmASpecs (opts : List Term) (a : Attr) :
    (opts.map fun t => (specOf t, AdmA t)).filter (fun o => admitOptA o a)
      = (opts.filter fun t => admitOptA (specOf t, AdmA t) a).map
          fun t => (specOf t, AdmA t) := by
  induction opts with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, List.filter_cons, ih]
    cases hb : admitOptA (specOf t, AdmA t) a <;> simp [hb]

/-- `select`'s filter is the term list's, mapped — `filter_AdmSpecs`'s twin. -/
theorem filter_AdmASpecs {opts : List Term} (h : ∀ t ∈ opts, ExactA t) (a : Attr) :
    (optionSems opts).filter (·.admitA a)
      = (opts.filter (fun t => admitOptA (specOf t, AdmA t) a)).map
          (fun t => optionSemOf (denote t) (specOf t)) := by
  induction opts with
  | nil => rfl
  | cons t ts ih =>
    have ht : ExactA t := h t (by simp)
    have hts : ∀ t' ∈ ts, ExactA t' := fun t' h' => h t' (by simp [h'])
    simp only [optionSems, List.filter_cons, admitOptA_eq ht, ih hts]
    cases hb : admitOptA (specOf t, AdmA t) a <;> simp [hb]

/-- **`union` reads exactly what its row says** — `ExactV_union` on the other side of the
    pair, and the same two rewrites. `select` is stated once over both halves
    (`Combinators.lean`), which is why this proof is the value side's verbatim. -/
theorem ExactA_union {opts : List Term} (h : ∀ t ∈ opts, ExactA t) : ExactA (.union opts) := by
  intro a
  rw [denote_union_sems]
  show selOptA (AdmASpecs opts) a = true ↔ (select (optionSems opts) (·.admitA) (·.c.p) a).isSome
  rw [AdmASpecs_eq]
  unfold select selOptA
  rw [filter_map_AdmASpecs opts a, filter_AdmASpecs h a]
  cases hf : opts.filter (fun t => admitOptA (specOf t, AdmA t) a) with
  | nil => simp
  | cons t rest =>
    cases rest with
    | nil =>
      have ht : ExactA t := h t (mem_of_filter_eq_singleton hf).1
      simpa [optionSemOf_c] using ht a
    | cons t2 r2 => simp

/-- **`nullable` reads exactly what its row says.** The same two cases as `ExactV_nullable`,
    against the same guard: `withNull` gates *both* halves of the pair on one `ownsNull`, so
    the read side needs no separate argument and gets none. -/
theorem ExactA_nullable {t : Term} (h : ExactA t) : ExactA (.nullable t) := by
  intro a
  rw [denote_nullable]
  simp only [AdmA, Codec.withNull]
  cases hw : (denote t).ownsNull with
  | true => simp [hw, h a]
  | false =>
    simp only [hw, Bool.not_false, Bool.and_true, if_false, Bool.false_eq_true, addPoint]
    cases a <;> simp [h _]

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
        have ht : t ∈ opts := (mem_of_filter_eq_singleton hL).1
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
    (hr : ∀ t, rest = .codec t → ExactA t) :
    ExactA (.object (.mk fields fld rest)) := by
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
    simp [AdmA, AdmABody, denote, bodySem, objectCodec, objectCodecCore, carriedCodec, mA,
      Ctor.out]

/-- **`opaque` reads exactly what its row says**, definitionally, and for the reason
    `ExactV_opaq` gives at length: `p := (opaqCodecω lossy).p`, so the row and `dom(p)` are
    one function. ~~AdmOpaqA_iff~~ — a second induction, this one carrying an injectivity
    clause about `Double.ofDec` that `decSet` needs — is deleted rather than moved. The
    clause was true and is still true; it is now the codec's business, where it was always
    stated (`decSet`, `Combinators.lean`), instead of being restated here in a form that had
    to be kept in step by hand. -/
theorem ExactA_opaq (lossy : Bool) : ExactA (.opaq lossy) := fun _ => Iff.rfl


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
/-- **Every attribute row is exact** — all twenty-one, as on the value side, and nothing
    declines on either. `refine` was the last difference between
    the two sides and is exact now: its row decodes and then applies `q`. `legacy`,
    which used to be the other half of that asymmetry, is exact here because its row is the
    union of the two channels it reads on.

    The numeric rows are the interesting ones: they reach `dom(p)` through `Double.ofDec`,
    which is axiomatized, and are exact anyway — a row may *call* an axiomatized function
    even though no finite set of numerals describes its domain. §5 wrote `⊤` there. -/
theorem AdmA_exact : ∀ (t : Term), ExactA t
  -- the rows §5 excused on this side too
  | .tuple ts tail =>
      ExactA_tuple (exactAL_mem ts (AdmA_exactL ts)) (exactAO_mem tail (AdmA_exactO tail))
  | .dunion _ opts => ExactA_dunion (exactAL_mem opts (AdmA_exactL opts))
  | .object (.mk fields fld rest) =>
      ExactA_object (fun k => AdmA_exactF (fld k)) (exactAR_codec rest (AdmA_exactR rest))
  | .opaq lossy => ExactA_opaq lossy
  -- exact because the constructor narrowed, not because the row sharpened
  | .set b => ExactA_set b
  -- the row that asks `ownsNull`; see `ExactA_nullable`
  | .nullable c => ExactA_nullable (AdmA_exact c)
  -- see `ExactA_union`
  | .union opts => ExactA_union (exactAL_mem opts (AdmA_exactL opts))

  | .string => by intro a; cases a <;> simp [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, stringCodec]
  | .boolean => by intro a; cases a <;> simp [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, booleanCodec]
  | .binary => by intro a; cases a <;> simp [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, binaryCodec]
  | .null => by intro a; cases a <;> simp [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, nullCodec]
  | .number => by
      intro a
      cases a
      case n x =>
        simp only [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, numberCodec]
        cases hx : Double.ofDec x.1 <;> simp [hx]
      all_goals simp [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, numberCodec]
  | .decimal => by intro a; cases a <;> simp [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, decimalCodec]
  -- Three rows into one. The `number` base is the only one needing `Double.ofDec`, and it is
  -- also the only one where unfolding `numberCodec` is safe here: the `simp only` fixes the
  -- shape before `Numeral.WF`'s parser can be reached.
  | .literal k ls => by
      intro a
      cases k
      -- the row asks the codec, so the biconditional is the row read twice
      case decimal => simp [AdmA, AdmALit, denote]
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
      case string => exact AdmALit_string_exact ls a
      case boolean => exact AdmALit_boolean_exact ls a
      case binary => exact AdmALit_binary_exact ls a
      case null => exact AdmALit_null_exact ls a
  | .custom ce cp => by intro a; simp [AdmA, denote, denote]
  | .array c => by
      have hc := AdmA_exact c
      intro a
      cases a
      case l as =>
        simp only [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, arrayCodec]
        rw [AdmAAll_iff hc, ← traverse_isSome_iff]
        cases traverse (denote c).p as <;> simp
      all_goals simp [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, arrayCodec]
  | .record c => by
      have hc := AdmA_exact c
      intro a
      cases a
      case m keys g =>
        simp only [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, recordCodec, Option.isSome_map', decide_eq_true_eq,
          funImage_isSome_iff]
        exact forall_congr' fun k => hc (g k)
      all_goals simp only [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, recordCodec, Option.map_none',
        Option.isSome_none, Bool.false_eq_true]
  | .held c f g => by
      have hc := AdmA_exact c
      intro a
      simp only [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, Codec.through]
      rw [hc a]
      cases (denote c).p a <;> simp
  -- **the row this file said could not exist.** `restrict`'s `p` is the base's `bind`ed
  -- through `q`, so `dom(p)` is `dom` of the base's intersected with `q` of what it decodes
  -- to — and that is what the row computes, term for term.
  | .refine c q => by
      have hc := AdmA_exact c
      intro a
      simp only [AdmA, refineReads, denote_refine, Codec.restrict, Bool.and_eq_true, hc a]
      cases hx : (denote c).p a <;> simp [hx]
  | .lazy c => by
      have hc := AdmA_exact c
      intro a; simpa [AdmA, denote] using hc a
  | .legacy c r => by
      have hc := AdmA_exact c
      intro a
      simp only [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, Codec.extendRead]
      cases hx : (denote c).p a <;> simp [hc a, hx]

theorem AdmA_exactL : ∀ (ts : List Term), ExactAL ts
  | [] => trivial
  | t0 :: ts => ⟨AdmA_exact t0, AdmA_exactL ts⟩

theorem AdmA_exactO : ∀ (tail : Option Term), ExactAO tail
  | none => trivial
  | some t0 => AdmA_exact t0

theorem AdmA_exactF : ∀ (fd : Field), ExactAField fd
  | .req t0 => fun a => AdmA_exact t0 a
  | .optional t0 => fun a => AdmA_exact t0 a
  | .fallback t0 _ => fun a => AdmA_exact t0 a

theorem AdmA_exactR : ∀ (rest : Rest), ExactAR rest
  | .drop => trivial
  | .refuse => trivial
  | .codec t0 => AdmA_exact t0
end

/-- Soundness of every attribute row — a corollary, as on the value side. The
    hundred-and-thirty-line depth recursion this was, and the ~~SoundA~~ scaffolding it needed,
    are deleted: `AdmA_exact` carries no hypothesis, so the weaker half comes free. -/
theorem AdmA_sound (t : Term) {a v} (hp : (denote t).p a = some v) : AdmA t a = true :=
  (AdmA_exact t a).mpr (by rw [hp]; rfl)

/-- **The witness that is now a theorem the other way.** `refine(string, ⊥)` reads nothing,
    and `AdmA` says so: the row decodes with `stringCodec` and applies `⊥`. This used to be
    ~~not_ExactA_refine~~, stated as "`AdmA` cannot see it". -/
theorem AdmA_refine_bot (a : Attr) : AdmA (.refine .string (fun _ => false)) a = false := by
  simp [AdmA, refineReads]
  cases a <;> simp [denote, stringCodec]

/-! ## Two of the twenty-one constructors are derivable

`array` is the degenerate `tuple` — empty fixed part, uniform tail — and `record` the
degenerate `object`: no declared names, `codec` rest. Both rows agree with their general
form *pointwise*, on both sides, so nothing in the analysis depends on them existing.

They are kept anyway, and the reason is the shape of the row rather than the size of the
language. `array`'s row is `allP`, one fold; the `tuple` it expands to is `alignP`, which
carries a length discipline that at `([], some c)` can never fire. `record`'s row is one
`decide` over the key set; the `object` it expands to is `valPresentT && objAdmV`, a
presence guard over an empty field table — vacuous — conjoined with a traversal that
consults `entryP` at every name only to be handed the rest policy back. So the narrow
constructor buys a row a reader can check by eye, and that is the **opposite** trade from
`set`, where a narrower constructor bought *exactness*: `set b` cannot be spelled as a
`refine` of anything, and indexing by the base is what made `encSet`'s collision guard
provably dead. Convenience here, necessity there.

### …and `union` is not a congruence for codec equivalence

`record c` and `object ∅ noFields (.codec c)` have identical rows on both sides, hence —
by `Adm_exact`/`AdmA_exact`, which take no hypothesis — identical domains on both sides.
They are the same codec as far as anything observable through `e` and `p` can tell.

`union` still distinguishes them, and `union_not_congruent` is the pair. An option's
admission is `admitOptV`, which matches the **constructor**: `specOf (.record c) = none`,
so the option is admitted *by attempt*, while `specOf (.object (.mk ∅ noFields (.codec c)))` is
`some ⟨∅, _⟩`, so the option is admitted *by names* — and an empty name spec admits no map
that carries a name. On `{"a" ↦ "x"}` the first option answers `true` and the second
`false`, with equal domains behind both.

This is not a defect in the rows and not one in `select`; it is the price of deciding an
object option syntactically, which `docs/codec-calculus.md:713` argues for on other
grounds ("an open object that must be an option should declare what it means to keep").
What that passage does not observe is this consequence: **term equivalence is not a
congruence for `union`**, so no rewrite that replaces a subterm by a domain-equal one is
sound inside a `union`. Anything that wants to normalize `record` to `object` — or `array`
to `tuple`, which is safe, both being `specOf = none` — has to check the spec, not the
domain. -/

/-- The empty field table. Not `by simp`: `simp`'s route to a vacuous `Finset ∅` goal reaches
    `Classical.choice`, and this is a *definition*, so it would put the axiom under every
    theorem below rather than under a proof. `Finset.not_mem_empty` is the direct term. -/
def noFields : {k // k ∈ (∅ : Finset Name)} → Field :=
  fun k => absurd k.2 (Finset.not_mem_empty k.1)

/-- `array`'s fold is its `tuple`'s alignment. The induction is on the value's list, not the
    term: `alignP [] (some P)` recurses with the same `(([], some P))`, so there is nothing
    structural to follow on the term side. -/
theorem arrayRow (c : Term) (v : Value) : Adm (.array c) v = Adm (.tuple [] (some c)) v := by
  cases v with
  | arr xs =>
    simp only [Adm, AdmList, AdmOptT]
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [allP, alignP, ih]
  | _ => rfl

/-- The same on the read side; `allPA`/`alignPA` are the same two shapes over `Attr`. -/
theorem arrayRowA (c : Term) (a : Attr) : AdmA (.array c) a = AdmA (.tuple [] (some c)) a := by
  cases a with
  | l as =>
    simp only [AdmA, AdmAList, AdmAOptT]
    induction as with
    | nil => rfl
    | cons x as ih => simp [allPA, alignPA, ih]
  | _ => rfl

/-- `record`'s one `decide` is its `object`'s guard-and-traverse, with both extra pieces
    dead: the presence guard quantifies over an empty field table, and `entryP` finds no
    declaration at any name and hands back the rest policy.

    Spelled out rather than left to `simp`. The one-line `simp [Adm, valPresentT, objAdmV,
    entryP, AdmRest, noFields, MapOf.at]` proves it and reaches `Classical.choice` — the
    `decide` over a `Finset` subtype is where simp picks up a classical instance — which
    `#assert_axioms_all` rejects. `decide_eq_true` and `dif_neg` are the two facts actually
    needed. -/
theorem recordRow (c : Term) (v : Value) :
    Adm (.record c) v = Adm (.object (.mk ∅ noFields (.codec c))) v := by
  cases v with
  | map keys f =>
    have hv : valPresentT ∅ noFields keys = true :=
      decide_eq_true (fun k => absurd k.2 (Finset.not_mem_empty k.1))
    have he : ∀ k : Name, entryP ⟨∅, fun k => AdmField (noFields k)⟩ (some (Adm c)) k
        = some (Adm c) := fun k => by
      simp only [entryP, MapOf.at, dif_neg (Finset.not_mem_empty k)]
    simp only [Adm, AdmBody, hv, Bool.true_and, objAdmV, AdmRest, he]
  | _ => rfl

/-- The read side, with one extra dead piece: `keepT (.codec c) ∅` is the constant `true`,
    an open rest keeping every name, so `objAdmA`'s guard discharges by `true_implies`. -/
theorem recordRowA (c : Term) (a : Attr) :
    AdmA (.record c) a = AdmA (.object (.mk ∅ noFields (.codec c))) a := by
  cases a with
  | m keys g =>
    have hv : reqPresentT ∅ noFields keys = true :=
      decide_eq_true (fun k => absurd k.2 (Finset.not_mem_empty k.1))
    have he : ∀ k : Name, entryPA ⟨∅, fun k => AdmAField (noFields k)⟩ (some (AdmA c)) k
        = some (AdmA c) := fun k => by
      simp only [entryPA, MapOf.at, dif_neg (Finset.not_mem_empty k)]
    simp only [AdmA, AdmABody, hv, Bool.true_and, objAdmA, AdmARest, keepT, he, true_implies]
  | _ => rfl

/-! ### Row equality is domain equality, for free

Each of the four above becomes a statement about `e` and `p` with no further work, which is
what an unconditional `Adm_exact`/`AdmA_exact` buys: the row *is* the domain, so a proof
that two rows agree is a proof that two codecs' domains agree. Under the old exactness —
a hypothesis to discharge per term — each of these would have needed its own discharge. -/

theorem arrayDom (c : Term) (v : Value) :
    ((denote (.array c)).e v).isSome = ((denote (.tuple [] (some c))).e v).isSome :=
  Bool.coe_iff_coe.mp
    ((Adm_exact (.array c) v).symm.trans (arrayRow c v ▸ Adm_exact (.tuple [] (some c)) v))

theorem arrayDomA (c : Term) (a : Attr) :
    ((denote (.array c)).p a).isSome = ((denote (.tuple [] (some c))).p a).isSome :=
  Bool.coe_iff_coe.mp
    ((AdmA_exact (.array c) a).symm.trans (arrayRowA c a ▸ AdmA_exact (.tuple [] (some c)) a))

theorem recordDom (c : Term) (v : Value) :
    ((denote (.record c)).e v).isSome = ((denote (.object (.mk ∅ noFields (.codec c)))).e v).isSome :=
  Bool.coe_iff_coe.mp
    ((Adm_exact (.record c) v).symm.trans
      (recordRow c v ▸ Adm_exact (.object (.mk ∅ noFields (.codec c))) v))

theorem recordDomA (c : Term) (a : Attr) :
    ((denote (.record c)).p a).isSome = ((denote (.object (.mk ∅ noFields (.codec c)))).p a).isSome :=
  Bool.coe_iff_coe.mp
    ((AdmA_exact (.record c) a).symm.trans
      (recordRowA c a ▸ AdmA_exact (.object (.mk ∅ noFields (.codec c))) a))

/-- `record` is admitted by attempt… -/
theorem specOf_record (c : Term) : specOf (.record c) = none := rfl

/-- …and the `object` with its domain is admitted by names. -/
theorem specOf_object_isSome (c : Term) :
    (specOf (.object (.mk ∅ noFields (.codec c)))).isSome = true := rfl

/-- **`union` is not a congruence for domain equality.** `recordDom` and `recordDomA` say
    these two terms have the same `e` and the same `p` at every point. As *options* they
    disagree at `{"a" ↦ "x"}`: the first is attempted and admits, the second is asked for
    its names and refuses, because its spec is empty and the map is not.

    So a normalization pass over `Term` may not replace `record c` by its `object` inside a
    `union` — nor, in general, replace any subterm by a domain-equal one there. See the
    section note above; `docs/codec-calculus.md:713` gives the reason `ρ` goes unread and
    does not draw this corollary. -/
theorem union_not_congruent :
    admitOptV (specOf (.record .string), Adm (.record .string))
        (.map {"a"} (fun _ => .str "x")) = true
      ∧ admitOptV (specOf (.object (.mk ∅ noFields (.codec .string))),
          Adm (.object (.mk ∅ noFields (.codec .string)))) (.map {"a"} (fun _ => .str "x")) = false :=
  ⟨rfl, rfl⟩

/-! ## Re-deriving §5's separations on the pair

`SepV` and `SepA` are what the discharge machinery actually consumes, and they are stated
on `κ`/`adm`/`admA`. Before any of that can move to `Adm`/`AdmA`, two things have to be
true: the joint predicate must be at least as tight as the row it replaces, and every
discharge §5 already has must survive.

`Adm_le_adm` and `AdmA_le_admA` are the first. `sepJV_of_sepV` and `sepJA_of_sepA` are the
second — nothing is lost.

**And that is not enough to move `uAtCan_of_separated`, which is the third thing.** Both
bridges run from `SepV` to `SepJV`, the direction a *producer* wants; a consumer needs the
opposite, and at an `object` option it is unavailable — `not_uAtCan_of_sepJ`, at the end of
this section, is the discharger restated on the pair and refuted. The migration this section
was written to prepare does not go through.

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
      exact mem_allTags (List.mem_filter.mp hmem).1 (by simpa using (List.mem_filter.mp hmem).2)

/-- **`Adm` refines `adm`.** Every row of the joint predicate is at least as tight as the
    row it replaces, which is what lets every existing discharge carry over unchanged. -/
theorem Adm_le_adm : ∀ (t : Term) (v : Value), Adm t v = true → adm t v = true
  | .string, _, _ => rfl
  | .boolean, _, _ => rfl
  | .binary, _, _ => rfl
  | .null, _, _ => rfl
  | .set _, _, _ => rfl
  | .tuple _ _, _, _ => rfl
  | .object _, _, _ => rfl
  | .array _, _, _ => rfl
  | .record _, _, _ => rfl
  -- the two rows are now the **same** row — both ask `(opaqCodecω lossy).e` — so the
  -- containment is the identity, exactly as it is at `custom`. It was three lines while
  -- `Adm` recursed over the value and `adm` matched on the top constructor.
  | .opaq _, _, h => by rw [adm]; rw [Adm] at h; exact h
  | .number, v, h => by simpa [adm] using (by simpa [Adm] using h : inD v = true)
  | .decimal, v, h => by simpa [adm] using (by simpa [Adm] using h : isStored v = true)
  -- **The two rows are now the same predicate at every base**, `inL`. `Adm` used to be
  -- strictly stronger at `number` — it carried `WF` where §5's table did not — so this case
  -- dropped a conjunct rather than being the hypothesis. The gate is `WFDouble`'s now.
  | .literal k ls, v, h => by rw [adm]; rw [Adm_literal, AdmLit] at h; exact h
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
      -- `Adm`'s null disjunct carries the `ownsNull` guard and `adm`'s does not, so the
      -- containment drops it. `adm` is the discharger's row and may be loose; that it is
      -- loose *here* is now visible rather than incidental.
      · refine Or.inr ?_
        revert h; cases v <;> simp
  | .union opts, v, h => by
      rw [adm]
      -- `Adm` counts and `adm` disjoins, so the containment goes through
      -- `selOptV_le_AdmAny`: the option that answers alone is an option that answers
      exact AdmAny_le_admList opts v (fun t' _ => Adm_le_adm t' v)
        (selOptV_le_AdmAny (by rw [Adm] at h; exact h))


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
  | .object (.mk _ _ _), _, v, rfl, h => by cases v <;> simp_all [Adm, AdmBody, Value.kind]
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
        (fun t' _ ks' hk' h' => Adm_kind t' ks' v hk' h')
        (selOptV_le_AdmAny (by rw [Adm] at h; exact h))
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
      exact mem_allTags (List.mem_filter.mp hmem).1 (by simpa using (List.mem_filter.mp hmem).2)

/-- **`AdmA` refines `admA`**, the attribute-side counterpart of `Adm_le_adm`. -/
theorem AdmA_le_admA : ∀ (t : Term) (a : Attr), AdmA t a = true → admA t a = true
  | .string, _, _ => rfl
  | .boolean, _, _ => rfl
  | .binary, _, _ => rfl
  | .null, _, _ => rfl
  | .set _, _, _ => rfl
  | .tuple _ _, _, _ => rfl
  | .object _, _, _ => rfl
  | .array _, _, _ => rfl
  | .record _, _, _ => rfl
  -- **`legacy` stopped being `rfl` here, and that is the change working.** It held because
  -- `admA (.legacy _ _)` was `⊤`, so any `AdmA` implied it. The two rows are now the same
  -- union, `admA t a || (r a).isSome`, so the containment is the subterm's, disjunct-wise.
  | .legacy t r, a, h => by
      simp only [admA, Bool.or_eq_true]
      simp only [AdmA, Bool.or_eq_true] at h
      exact h.imp (AdmA_le_admA t a) id
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
      exact (AdmA_exact .number a).mp h
  | .literal k ls, a, h => by
      cases k
      case number =>
        show ((denote (Term.literal .number ls)).p a).isSome = true
        exact (AdmA_exact (.literal .number ls) a).mp h
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
      -- as on the value side: `admA`'s null disjunct is unguarded, so the guard is dropped
      · refine Or.inr ?_
        revert h; cases a <;> simp
  | .union opts, a, h => by
      rw [admA]
      exact AdmAAny_le_admAList opts a (fun t' _ => AdmA_le_admA t' a)
        (selOptA_le_AdmAAny (by rw [AdmA] at h; exact h))

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

/-- **`SepJV` suffices for the codec-level discharge.** The joint predicate is tighter than
    the rows it replaces, so `SepJV` is a *weaker* statement — but `Adm_sound` connects it
    straight to the denotation: where `x` writes, `y` refuses.

    This said "and that is all the discharge needs", which is where it over-claimed. What
    `uAtCan_of_separated` consumes is disjointness of the *options* `select` builds, and an
    object option is admitted by `keysOk` rather than by attempting its codec. The section
    below is that gap, with the pair that refutes the stronger reading. -/
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

/-! ### …and it does **not** suffice for the discharger, because of `adm`'s `object` row

The paragraph above says the discharge never needed `adm`'s extra strength. That is true of
the two theorems it is stated about and false of the theorem the migration exists to move,
and the difference is worth being precise about because the whole retirement of `adm` turns
on it.

`admitV_of_sepJV` is a claim about the **codec**: where `x`'s `e` writes, `y`'s `e` refuses.
`uAtCan_of_separated` is a claim about the **options `select` builds**, and at an `object`
those are not the same test. `admitOptV` records the asymmetry already — an object option is
admitted by `keysOk`, which reads which names a map carries and never what they hold — but
the corollary was not drawn: `Adm` is not an over-approximation of `OptionSem.admitV` at an
object, it is strictly *tighter*, and disjointness of a tighter predicate does not imply
disjointness of admission.

`adm (.object _) = ⊤` is what makes §5's generation sound here, and it is not slack. It is
exactly the over-approximation that turns `adm`-disjointness into admission-disjointness,
and it is why `SepV` cannot separate two objects at all: both `κ`s are `[map]` and both
`adm`s are `⊤`, so neither disjunct is available. Restate the discharger on `SepJV` and the
pair separates — while `select` attempts both options, so (U) genuinely fails. The premise
gets *stronger* and the theorem becomes *false*.

The witness is two objects with the same names and different field terms. Both are derivable
(`Typed.object`), both closed (`rest = drop`), and both lawful, so no other premise of
`uAtCan_of_separated` is what declines them — which is what makes `not_uAtCan_of_sepJ` a
refutation of the migration rather than a failure to find its proof.

And the `object` row is the *only* obstruction: `admitV_Adm_nonObject` and
`admitA_AdmA_nonObject` are the containments the discharger needs, and they hold, from
exactness alone, for every term whose `specOf` is `none` — which is every term but an
`object`. -/

/-- One required field, holding a string. -/
def bodyReqStr : Body := .mk {"a"} (fun _ => .req .string) .drop

/-- The same name, the same policy, a different field term. -/
def bodyReqNum : Body := .mk {"a"} (fun _ => .req .number) .drop

def objReqStr : Term := .object bodyReqStr
def objReqNum : Term := .object bodyReqNum

/-- A map the first object writes and the second refuses. -/
def mapReqStr : Value := .map {"a"} (fun _ => .str "x")

/-- `adm` at an object is `⊤`, at either of them — the row this section is about. -/
theorem adm_objReq (v : Value) : adm objReqStr v = true ∧ adm objReqNum v = true :=
  ⟨rfl, rfl⟩

theorem Adm_objReqStr : Adm objReqStr mapReqStr = true := by
  simp [objReqStr, bodyReqStr, mapReqStr, Adm, AdmBody, AdmField, AdmRest, objAdmV,
    valPresentT, entryP, MapOf.at]

theorem Adm_objReqNum : Adm objReqNum mapReqStr = false := by
  simp [objReqNum, bodyReqNum, mapReqStr, Adm, AdmBody, AdmField, AdmRest, objAdmV,
    valPresentT, entryP, MapOf.at, inD]

/-- **The joint predicate separates the pair on the writable side.** A map the first admits
    carries a string at `"a"`, which the second's field term refuses; and neither admits a
    value that is not a map. -/
theorem sepJV_objReq : SepJV objReqStr objReqNum := by
  intro v hv
  cases v with
  | map keys g =>
    simp only [objReqStr, bodyReqStr, Adm, AdmBody, valPresentT, objAdmV, entryP, MapOf.at,
      Bool.and_eq_true, decide_eq_true_eq] at hv
    simp only [objReqNum, bodyReqNum, Adm, AdmBody, valPresentT, objAdmV, entryP, MapOf.at,
      Bool.and_eq_true, decide_eq_true_eq, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    refine Or.inr fun h => ?_
    have ha : "a" ∈ keys := hv.1 ⟨"a", Finset.mem_singleton_self _⟩
    have h1 := hv.2 ⟨"a", ha⟩
    have h2 := h ⟨"a", ha⟩
    simp only [Finset.mem_singleton, dif_pos, AdmField] at h1 h2
    cases hg : g ⟨"a", ha⟩ <;> simp_all [Adm, inD]
  | _ => rfl

/-- …and on the readable side, on the `AdmA` disjunct: the member disjunct is no help,
    both objects being `⇝ M`. -/
theorem sepJA_objReq : SepJA objReqStr objReqNum := by
  refine Or.inr fun a ha => ?_
  cases a with
  | m keys g =>
    simp only [objReqStr, bodyReqStr, AdmA, AdmABody, reqPresentT, objAdmA, entryPA,
      MapOf.at, keepT, Bool.and_eq_true, decide_eq_true_eq] at ha
    simp only [objReqNum, bodyReqNum, AdmA, AdmABody, reqPresentT, objAdmA, entryPA,
      MapOf.at, keepT, Bool.and_eq_true, decide_eq_true_eq, Bool.and_eq_false_iff,
      decide_eq_false_iff_not]
    refine Or.inr fun h => ?_
    have ha' : "a" ∈ keys := ha.1 ⟨"a", Finset.mem_singleton_self _⟩
    have h1 := ha.2 ⟨"a", ha'⟩
    have h2 := h ⟨"a", ha'⟩
    simp only [Finset.mem_singleton, dif_pos, AdmAField, decide_true] at h1 h2
    cases hg : g ⟨"a", ha'⟩ <;> simp_all [AdmA]
  | _ => rfl

theorem typed_objReqStr :
    Typed objReqStr (HObject {"a"} (fun _ => (true, fun v => ∃ s, v = .str s)) none)
      (some .M) := .object (fun _ => .req .string) .drop

theorem typed_objReqNum :
    Typed objReqNum
      (HObject {"a"}
        (fun _ => (true, fun v => ∃ d, v = .num d ∧ Numeral.WF d.toDec = true)) none)
      (some .M) := .object (fun _ => .req .number) .drop

theorem lawful_objReqStr : Lawful (denote objReqStr) :=
  soundness typed_objReqStr ⟨fun _ => trivial, trivial⟩ ⟨fun _ => trivial, trivial⟩

theorem lawful_objReqNum : Lawful (denote objReqNum) :=
  soundness typed_objReqNum ⟨fun _ => trivial, trivial⟩ ⟨fun _ => trivial, trivial⟩

/-- **The pair is not uniquely admitting.** `select` counts an object option by its names,
    the two specs are the same spec, so a map the first option writes is admitted by both
    and the filter is not a singleton. -/
theorem not_uAtCan_objReq : ¬ UAtCan [objReqStr, objReqNum] := by
  intro h
  obtain ⟨a, ha⟩ :=
    Option.isSome_iff_exists.mp ((Adm_exact objReqStr mapReqStr).mp Adm_objReqStr)
  have hfil := (h (optionSemOf (denote objReqStr) (specOf objReqStr)) (by simp [semsOf])
    mapReqStr a (by rw [optionSemOf_c]; exact ha)).2
  simp [semsOf, objReqStr, objReqNum, bodyReqStr, bodyReqNum, specOf, Body.spec, optionSemOf,
    OptionSem.byNames, keysOk, mapReqStr] at hfil

/-- **`admitV_adm`'s analogue on the exact row is false**, which is the route the discharger
    would have to take. An object option admits by names; `Adm` asks the field terms. -/
theorem not_admitV_le_Adm :
    ¬ ∀ (t : Term) (v : Value),
      (optionSemOf (denote t) (specOf t)).admitV v = true → Adm t v = true := fun h =>
  absurd (h objReqNum mapReqStr rfl) (by simp [Adm_objReqNum])

/-- **`uAtCan_of_separated`, restated on the joint predicate, is false.** Every premise
    holds of `[objReqStr, objReqNum]` and the conclusion does not. This is the theorem that
    would have to survive for `adm`, `admA`, `SepV` and `SepA` to be retired in favour of
    `Adm`, `AdmA`, `SepJV` and `SepJA`; it does not, and the reason is a row rather than a
    proof — see the section note above. -/
theorem not_uAtCan_of_sepJ :
    ¬ ∀ (opts : List Term),
      (∀ t ∈ opts, Lawful (denote t)) →
      (∀ t ∈ opts, t.isOpenObject = false) →
      List.Pairwise SepJV opts →
      List.Pairwise SepJA opts →
      UAtCan opts := by
  intro h
  refine not_uAtCan_objReq (h [objReqStr, objReqNum] ?_ ?_ ?_ ?_)
  · intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact lawful_objReqStr
    · rcases List.mem_cons.mp ht with rfl | ht
      · exact lawful_objReqNum
      · exact nomatch ht
  · intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · exact nomatch ht
  · refine .cons (fun y hy => ?_) (.cons (by simp) .nil)
    rcases List.mem_singleton.mp hy with rfl
    exact sepJV_objReq
  · refine .cons (fun y hy => ?_) (.cons (by simp) .nil)
    rcases List.mem_singleton.mp hy with rfl
    exact sepJA_objReq

/-- **The containment the discharger needs, everywhere it holds.** Off an `object`, `specOf`
    is `none`, admission *is* attempted encoding, and exactness identifies it with the row.
    So the `object` row is the whole of the obstruction above. -/
theorem admitV_Adm_nonObject (t : Term) (hs : specOf t = none) {v : Value}
    (h : (optionSemOf (denote t) (specOf t)).admitV v = true) : Adm t v = true := by
  rw [hs] at h
  exact (Adm_exact t v).mpr h

/-- …and its twin on the readable side. -/
theorem admitA_AdmA_nonObject (t : Term) (hs : specOf t = none) {a : Attr}
    (h : (optionSemOf (denote t) (specOf t)).admitA a = true) : AdmA t a = true := by
  rw [hs] at h
  exact (AdmA_exact t a).mpr h

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

/-- A string `literal` decides, as §5 says. -/
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
    Decides (.object (.mk {"k"} (fun _ => .req .string) .refuse)) := by
  refine ⟨.map {"k"} (fun _ => .str "a"),
          .map ∅ (fun k => absurd k.2 (Finset.not_mem_empty k.1)), ?_, rfl, ?_⟩
  · simp [denote, denote, bodySem, fieldTable, restSem, fieldSem, restSem,
          objectCodec, objectCodecCore, stringCodec,
          valPresentB, valPresentAt, fieldSem, rcOf, FieldSem.codec, carriedCodec,
          mapV, mA, Ctor.out, Ctor.into, objWrite, entryCodec, MapOf.at, funImage,
          Subtype.forall]
  · simp [denote, denote, bodySem, fieldTable, restSem, fieldSem, restSem,
          objectCodec, objectCodecCore, stringCodec,
          valPresentB, valPresentAt, fieldSem, rcOf, FieldSem.codec, carriedCodec,
          mapV, mA, Ctor.out, Ctor.into, objWrite, MapOf.at, Subtype.forall]

theorem ident_object : ident (.object (.mk {"k"} (fun _ => .req .string) .refuse)) = false := rfl

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

So `legacy` leaves the attribute hatch, and the ~~widenedRead~~ excuse is deleted rather than
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
order, no ~~Wire.canon~~, and nothing for `e` to choose between. -/

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

