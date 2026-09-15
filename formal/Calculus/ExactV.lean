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

/-! `select` at a `dunion` is gone with the filtered sum. The variants are keyed by tag, so the
lookup reaches one variant or none: there is nothing to filter and no second match to rule out.
~~selTagV~~, ~~selTagA~~, ~~AdmTagged~~ and ~~AdmATagged~~ went with it. -/

/-- A `union` option's own admission, as `optionSemOf` builds it — and the two builders are
    **not** the same test. An *object* option decides by *structure*: the names the map carries
    lie in the spec's interval, and every present name whose field is a literal carries one of
    that literal's alternatives. Every other option decides by *attempt*, which is its row
    exactly when its row is exact.

    That asymmetry is the whole of why this is not `Adm`. Structure is weaker than `Adm`, which
    reads every field's contents through that field's codec; a row that counted `Adm` would
    disagree with `select` on any union of objects, in both directions.

    Taking `(spec, row)` rather than the term is what keeps the recursion structural, the same
    shape ~~selTagV~~ took; `specOf` is a function of the term, so the distinction is available
    here without consulting a codec. -/
def admitOptV (o : Option (MapOf NameSpec) × VP) (v : Value) : Bool :=
  match o.1 with
  | some spec =>
      match v with
      | .map keys f => keysOk spec keys && literalsOk spec keys f
      | _ => false
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
def selOptV (os : List (Option (MapOf NameSpec) × VP)) (v : Value) : Bool :=
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

    The retired per-aspect row was always `inL`
    and was therefore inexact at `number` by exactly this conjunct, while the joint row carried
    it and so `Adm_exact` covered the literal. The defect is closed rather than patched:
    nothing was added to make the two agree. -/
noncomputable def AdmLit (k : GroundKind) (ls : NEFinset k.Carrier) (v : Value) : Bool :=
  inL k ls v

/-! ## The two rows that ask their own codec

    `custom` and `opaque` are the language's two escape hatches, and they are the two rows
    below that **do not describe a set at all**. Each asks the codec it denotes:

        Adm  (.custom ce _)   v = (ce v).isSome
        Adm  (.opaq lossy)    v = ((opaqCodecω lossy).e v).isSome
        AdmA (.custom _ cp)   a = (cp a).isSome
        AdmA (.opaq lossy)    a = ((opaqCodecω lossy).p a).isSome

    Three things follow, and they are the same three for both.

    *They are exact by construction.* `denote`'s rows set `e := ce` and
    `e := (opaqCodecω lossy).e` — the `custom` row definitionally, `opaque` by `denote_opaq`
    — so the row and `dom(e)` are the same function, and `ExactV`/`ExactA` at either term is
    `Iff.rfl`. That is not a sharp analysis of an escape hatch; it is the analysis
    *declining* to be one, and the exactness is the codec's, borrowed.

    *They are as precise as the semantics is.* No syntactic set could name `opaqCodecω`'s
    domain: it recurses on the *input's own depth*, refusing a `numSet` of numerals the
    store will not take, or an array with one such numeral at any depth. A row over the term
    cannot see past the top constructor. Deferring sees all of it, because it does not look.

    *Nothing here knows anything about either implementation.* Swap `opaqCodecω` for a
    different `opaque` — a different numeric policy, a different set of options, a different
    fuel discipline — and every theorem downstream is still true and still proved, because
    none of them mentions what the codec answers.

    ### …and the one respect in which they are opposite

    The likeness is **the analysis, and only the analysis**. `opaque` is not a `custom`, and
    the difference is the warranty behind the codec each row asks:

    * `custom` carries a real premise. `Obligations (.custom ce cp)` (`Soundness.lean`) is
      `Lawful ⟨dom(ce), none, ce, cp⟩` — a proof obligation on whoever writes the term, and
      nothing in the calculus discharges it. The row asks a codec **the user warrants**.
    * `opaque` carries none. `Obligations (.opaq _) = True`, and it is `True` because the
      laws are *theorems* here: `lawful_opaqCodecω` and `carrier_opaqCodecω`
      (`Opaque.lean`), off the stabilization and depth-preservation lemmas. The row asks a
      codec **the calculus warrants**.

    So `opaque` is strictly the stronger of the two — same decoupling, no premise — and that
    is what "a *well-behaved* `custom`" means. A reading of these rows as "`opaque` is a
    `custom`" gets the obligation exactly backwards.

    ### What "unanalysable" turned out to mean

    `held` and `custom` were on the unanalysable list because they carry Lean functions, and
    a function is not something a reader can look inside. But a row is not a reader: it is a
    function with the term in hand, and the term *carries* `f`, `ce` and `cp` as data. It can
    apply them. `(c.through f g).e v = c.e (f v)` holds by `Iff.rfl`, so `held`'s writable
    set is the subterm's pulled back along `f`, with no appeal to `held`'s iso obligation.

    Three senses had been running together: (i) the term does not carry the information —
    true of nothing here; (ii) the domain cannot be computed without running the codec — true
    of `opaq` and of `custom`, and the reason both rows *do* run it, at the price of being
    `noncomputable`; (iii) a reader cannot see through it — true of `held`, `custom` and
    `opaq`, and not a property of the calculus.

    ### And `lazy` is transparent, on both sides

    `denote (.lazy t) = { denote t with μ := none }`: the pair is the subterm's and only the
    member is erased, so both rows below pass straight through. The specification's §5
    lists `lazy` with `custom` as unanalysable, and that is inherited from the document's
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
  | .decimal  => isStored
  | .literal k ls => AdmLit k ls
  | .custom ce _ => fun v => (ce v).isSome
  -- the bottom admits nothing, and the row is that sentence
  | .never => fun _ => false
  | .array c  => fun v => match v with | .arr xs => allP (Adm c) xs | _ => false
  -- `record` needs no list companion either: `M`'s entries are a function on the key
  -- set, so "every entry admits" is one `decide` over that set, the way the three `set`
  -- rows are one `decide` over theirs.
  | .record c => fun v =>
      match v with | .map _ f => decide (∀ k, Adm c (f k) = true) | _ => false
  | .refine t p => fun v => Adm t v && p.eval v
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
  -- the lookup: read the tag, index the table, ask that one variant. No filter, and no second
  -- match to rule out — the key set already did that
  | .dunion variants => fun v =>
      match tagOfV variants.ks.1 v with
      | some tag => if h : tag ∈ variants.keys then AdmBody (variants.get ⟨tag, h⟩) v else false
      | none => false
  -- **The second row that asks its own codec**, as the section above sets out:
  -- `denote (.opaq lossy)` *is* `opaqCodecω lossy`, so this is `dom(e)` rather than a
  -- description of it, and `ExactV_opaq` is `Iff.rfl`.
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


/-- Each `union` option paired with its name spec — `optionSems`' mirror, the way
    ~~AdmTagged~~ mirrored ~~denoteTagged~~. `specOf` is what tells an object option from the
    rest, and it is a function of the term. -/
noncomputable def AdmSpecs : List Term → List (Option (MapOf NameSpec) × VP)
  | [] => []
  | t :: ts => (specOf t, Adm t) :: AdmSpecs ts

end

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
theorem ExactV_dunion {variants : TagMap Body}
    (h : ∀ k, ExactV (.object (variants.get k))) : ExactV (.dunion variants) := by
  intro v
  show (match tagOfV variants.ks.1 v with
        | some tag => if hk : tag ∈ variants.keys then AdmBody (variants.get ⟨tag, hk⟩) v else false
        | none => false) = true ↔ _
  rw [denote_dunion_tags]
  cases htv : tagOfV variants.ks.1 v with
  | none => simp [dunionTable, htv]
  | some tag =>
    show (if hk : tag ∈ variants.keys then AdmBody (variants.get ⟨tag, hk⟩) v else false)
        = true ↔ _
    by_cases hk : tag ∈ variants.keys
    · rw [dif_pos hk]
      refine Iff.trans (h ⟨tag, hk⟩ v) (Iff.intro (fun hs => ?_) (fun hs => ?_))
      · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hs
        exact Option.isSome_iff_exists.mpr ⟨a, dunionTable_e.mpr ⟨tag, hk, htv, ha⟩⟩
      · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hs
        obtain ⟨tag', hk', ht, hve⟩ := dunionTable_e.mp ha
        rw [htv] at ht
        obtain rfl : tag' = tag := (Option.some.inj ht).symm
        exact Option.isSome_iff_exists.mpr ⟨a, hve⟩
    · rw [dif_neg hk]
      refine Iff.intro (fun hs => nomatch hs) (fun hs => ?_)
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨tag', hk', ht, -⟩ := dunionTable_e.mp ha
      rw [htv] at ht
      obtain rfl : tag' = tag := (Option.some.inj ht).symm
      exact absurd hk' hk

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

    Two cases and they are not symmetric. At an **object** option both sides are the same
    `keysOk && literalsOk`, definitionally, and the hypothesis is not used at all: `select`
    never attempts an object option, and neither does the row. Everywhere else the admission *is* `(c.e ·).isSome`, and
    the hypothesis is exactly what identifies it with the row. -/
theorem admitOptV_eq {t : Term} (h : ExactV t) (v : Value) :
    (optionSemOf (denote t) (specOf t)).admitV v = admitOptV (specOf t, Adm t) v := by
  unfold admitOptV
  cases hs : specOf t with
  | some spec => rfl
  | none =>
    simp only [optionSemOf, OptionSem.byAttempt]
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
    cases hb : admitOptV (specOf t, Adm t) v <;> simp []

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
    cases hb : admitOptV (specOf t, Adm t) v <;> simp []

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
  | true => simp [h v]
  | false =>
    simp only [Bool.not_false, Bool.and_true, if_false, Bool.false_eq_true, addPoint]
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
  | .dunion variants => ExactV_dunion fun k => Adm_exactB (variants.get k)
  | .object b => Adm_exactB b
  | .opaq lossy => ExactV_opaq lossy
  -- both sides are empty, so the equivalence is `False ↔ False`
  | .never => fun _ => Iff.rfl
  -- the row the *constructor* made exact, rather than a sharper analysis of the old one
  | .set b => ExactV_set b
  -- the row that asks `ownsNull`
  | .nullable c => ExactV_nullable (Adm_exact c)
  -- the count is exact given the options' exactness, which is the hypothesis this
  -- recursion hands it. See `ExactV_union`.
  | .union opts => ExactV_union (exactVL_mem opts (Adm_exactL opts))

  | .string => by intro v; cases v <;> simp [Adm, denote, denote, stringCodec]
  | .boolean => by intro v; cases v <;> simp [Adm, denote, denote, booleanCodec]
  | .binary => by intro v; cases v <;> simp [Adm, denote, denote, binaryCodec]
  | .null => by intro v; cases v <;> simp [Adm, denote, denote, nullCodec]
  | .number => by intro v; cases v <;> simp [Adm, denote, denote, inD]
  | .decimal => by intro v; cases v <;> simp [Adm, denote, denote, isStored]
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
              stringCodec, booleanCodec, binaryCodec, nullCodec, inD, decimalCodec]
  | .custom ce cp => by intro v; simp [Adm, denote, denote]
  | .array c => by
      have hc := Adm_exact c
      intro v
      cases v
      case arr xs =>
        simp only [Adm, denote, denote, denote, arrayCodec, Option.isSome_map]
        rw [AdmAll_iff hc, ← traverse_isSome_iff]
      all_goals simp [Adm, denote, denote, arrayCodec]
  | .record c => by
      have hc := Adm_exact c
      intro v
      cases v
      -- The entry-key transport is gone with the traversal: `funImage` is defined
      -- exactly where every entry's `e` is, which is the row verbatim.
      case map keys f =>
        simp only [Adm, denote, denote, denote, recordCodec, Option.isSome_map, decide_eq_true_eq,
          funImage_isSome_iff]
        exact forall_congr' fun k => hc (f k)
      -- the other nine rows are refused on both sides, and unfolding `recordCodec`'s
      -- `funImage` to see it is more work than reading it off the two `false`s
      all_goals simp only [Adm, denote, denote, denote, recordCodec, 
        Option.isSome_none, Bool.false_eq_true]
  | .refine c p => by
      have hc := Adm_exact c
      intro v; cases hq : p.eval v <;> simp [Adm, denote, denote, Codec.restrict, hq, hc v]
  | .legacy c r => by
      have hc := Adm_exact c
      intro v; simpa [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, Codec.extendRead] using hc v
  | .lazy c => by
      have hc := Adm_exact c
      intro v; simpa [Adm, denote] using hc v
  | .held c f g => by
      have hc := Adm_exact c
      intro v; simpa [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, Codec.through] using hc (f v)

/-- The payload's own exactness, as a companion. A `dunion`'s variants are `Body`s reached
    through a function, so the recursion needs to land on a `Body` rather than on the `Term` that
    wraps one — the same reason the field and rest companions exist. -/
theorem Adm_exactB : ∀ (b : Body), ExactV (.object b)
  | .mk _ fld rest =>
      ExactV_object (fun k => Adm_exactF (fld k)) (exactVR_codec rest (Adm_exactR rest))

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

end

end Calculus
