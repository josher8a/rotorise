import Calculus.Typing

/-!
# §5 — Soundness

The theorem. `Obligations t` collects the doc's *semantic* rule premises — `(legacy)`'s two
side conditions, `(held)`'s cancellation laws, `(fallback)`'s writable stand-in, `(custom)`'s
laws, `(union)`'s residual (U) at canonical inputs. **Neither fueled nor carrying
`(nullable)`'s null-honesty**, both of which this paragraph said: `Obligations : Term → Prop`
is structural, as its own docstring says in as many words, and the `nullable` row is
`Obligations t'` with no conjunct — `NullHonest` left `Obligations` when §3's guard made it
derivable (`Combinators.lean`'s `nullHonest_of_not_ownsNull`). `MPOk` marks a derivation
legacy-free — the doc's
(MP) exemption, as a predicate.

Statements:

* `soundness_core` — (R), (C), (W) for every derivable term.
* `soundness` — all four laws, legacy-free.

The ground-term cases are wrappers over the certified combinators (Combinators.lean),
where the per-construction lemmas — proved and open — now live.
-/

namespace Calculus

/-! ## Obligations -/

/-- The union options, denoted with their name specs — as in `denote`'s union case. -/
noncomputable def semsOf (opts : List Term) : List OptionSem :=
  opts.map fun t' => optionSemOf (denote t') (specOf t')

/-- §5 (U) at canonical inputs: every canonical attribute of an option is admitted by
    that option alone, on both sides. The strong form, and what the dischargers produce —
    `Calculus.Orthogonality`'s `uAtCan_of_orth` and `uAtCan_of_separated`, and the hand
    proofs in `Calculus.Discharge` that no phase of the classifier reaches. -/
def UAtCan (opts : List Term) : Prop :=
  UniqueAdmission (semsOf opts)

/-- **§5 (U) where the union acts** — the theorem's actual residue, and what `(union)`
    carries as an obligation.

    `UAtCan` quantifies over every canonical pair of every *option*; the laws only ever
    ask about inputs the *union* resolves, since `altCodec` declines everything else and
    a law quantified over `dom` cannot reach a declined input. `UAtAct` is that
    restriction (`UniqueBothWays`), and it is strictly weaker: the gap is where the
    working schemas sit — `union(array(literal "A"), array(literal "B"))` fails `UAtCan`
    at `[]` and meets `UAtAct`, because the union declines to write `[]`.

    Every discharger still discharges, through `uAtAct_of_uAtCan`. -/
def UAtAct (opts : List Term) : Prop :=
  UniqueBothWays (semsOf opts)

/-- The strong residue implies the one the laws need, so §5's dischargers are unaffected. -/
theorem uAtAct_of_uAtCan {opts} (h : UAtCan opts) : UAtAct opts :=
  uniqueBothWays_of_uniqueAdmission h

mutual

/-- The doc's semantic rule premises.

    **Structural**, and it means what the specification means: the premises hold. The list
    companions exist because `∀ t' ∈ ts, Obligations t'` is not a structural recursion and
    `ObligationsList` is. -/
def Obligations : Term → Prop
  -- `set` joins the leaves: its base is an index, so there is no subterm to carry premises.
  | .string | .number | .decimal | .boolean | .binary | .null
  | .literal _ _ | .opaq _ | .set _ => True
  | .array t' | .record t' | .refine t' _ => Obligations t'
  | .tuple ts tail => ObligationsList ts ∧ ObligationsOpt tail
  | .held t' f g => Obligations t' ∧ IsoCancels (denote t') f g
  | .legacy t' r => Obligations t' ∧ ReadsCoherently (denote t') r
  | .nullable t' => Obligations t'
  | .lazy t' => Obligations t'
  | .custom ce cp =>
    Lawful { T := fun v => (ce v).isSome, μ := none, e := ce, p := cp }
  | .object b => ObligationsBody b
  | .union opts => ObligationsList opts ∧ UAtAct opts
  -- one premise per variant, indexed by the key rather than by a list position
  | .dunion _ variants => ∀ k, ObligationsBody (variants.2 k)

/-- The payload's premises: every declared field's, and the rest policy's. The companion
    `Field` and `Rest` already had and the object row inlined. -/
def ObligationsBody : Body → Prop
  | .mk _ f rest => (∀ k, ObligationsField (f k)) ∧ ObligationsRest rest

/-- A field's premises: the subterm's, plus `fallback`'s own `v(∗) ∈ dom(e)`. -/
def ObligationsField : Field → Prop
  | .req t' => Obligations t'
  | .optional t' => Obligations t'
  | .fallback t' v => Obligations t' ∧ ((denote t').e v).isSome

def ObligationsRest : Rest → Prop
  | .codec t' => Obligations t'
  | .drop | .refuse => True

def ObligationsList : List Term → Prop
  | [] => True
  | t' :: ts => Obligations t' ∧ ObligationsList ts

def ObligationsOpt : Option Term → Prop
  | none => True
  | some t' => Obligations t'

end

mutual

/-- Legacy-free: where (MP) holds without exemption. Structural, for the same reason. -/
def MPOk : Term → Prop
  | .legacy _ _ => False
  | .literal _ _
  | .string | .number | .decimal | .boolean | .binary | .null
  | .opaq _ | .custom _ _ | .set _ => True
  | .array t' | .record t' | .refine t' _ | .nullable t'
  | .held t' _ _ => MPOk t'
  | .tuple ts tail => MPOkList ts ∧ MPOkOpt tail
  | .lazy t' => MPOk t'
  | .object b => MPOkBody b
  | .union opts => MPOkList opts
  | .dunion _ variants => ∀ k, MPOkBody (variants.2 k)

def MPOkBody : Body → Prop
  | .mk _ f rest => (∀ k, MPOkField (f k)) ∧ MPOkRest rest

def MPOkField : Field → Prop
  | .req t' | .optional t' => MPOk t'
  | .fallback t' _ => MPOk t'

def MPOkRest : Rest → Prop
  | .codec t' => MPOk t'
  | .drop | .refuse => True

def MPOkList : List Term → Prop
  | [] => True
  | t' :: ts => MPOk t' ∧ MPOkList ts

def MPOkOpt : Option Term → Prop
  | none => True
  | some t' => MPOk t'

end

/-! ### The companions, as the quantifiers the rest of the file speaks in

`ObligationsList` is what made the recursion structural; `∀ t ∈ ts, Obligations t` is what every
proof below wants. These are that bridge, and they are the entire cost of losing the fuel. -/

theorem obligationsList_iff : ∀ {ts : List Term},
    ObligationsList ts ↔ ∀ t ∈ ts, Obligations t
  | [] => by simp [ObligationsList]
  | t :: ts => by
      simp only [ObligationsList, List.mem_cons, forall_eq_or_imp]
      exact and_congr_right (fun _ => obligationsList_iff)

theorem obligationsOpt_iff : ∀ {tail : Option Term},
    ObligationsOpt tail ↔ ∀ t ∈ tail, Obligations t
  | none => by simp [ObligationsOpt]
  | some _ => by simp [ObligationsOpt]

theorem mpOkList_iff : ∀ {ts : List Term}, MPOkList ts ↔ ∀ t ∈ ts, MPOk t
  | [] => by simp [MPOkList]
  | t :: ts => by
      simp only [MPOkList, List.mem_cons, forall_eq_or_imp]
      exact and_congr_right (fun _ => mpOkList_iff)

theorem mpOkOpt_iff : ∀ {tail : Option Term}, MPOkOpt tail ↔ ∀ t ∈ tail, MPOk t
  | none => by simp [MPOkOpt]
  | some _ => by simp [MPOkOpt]

/-! ### The premises, per rule

`Obligations` is a recursion over the term, so at each rule it *is* the proposition that
rule's premises make — but only up to unfolding, and every case of the two inductions
below was re-stating that proposition to name it. These are that unfolding, once per
rule, and they read as the rule they belong to. Each is `:= h`. -/

namespace Obligations

theorem array {t} (h : Obligations (.array t)) : Obligations t := h
theorem record {t} (h : Obligations (.record t)) : Obligations t := h
theorem refine {t q} (h : Obligations (.refine t q)) : Obligations t := h
theorem lazy {t} (h : Obligations (.lazy t)) : Obligations t := h

theorem tuple {ts tail} (h : Obligations (.tuple ts tail)) :
    (∀ t ∈ ts, Obligations t) ∧ (∀ t ∈ tail, Obligations t) :=
  ⟨obligationsList_iff.mp h.1, obligationsOpt_iff.mp h.2⟩

/-- §3 `(held)`: the subterm's premises, and the iso cancelling on the carriers. -/
theorem held {t f g} (h : Obligations (.held t f g)) :
    Obligations t ∧ IsoCancels (denote t) f g := h

/-- §3 `(legacy)`: the subterm's premises, and the migration landing on writable values
    and agreeing with the current reading. -/
theorem legacy {t r} (h : Obligations (.legacy t r)) :
    Obligations t ∧ ReadsCoherently (denote t) r := h

/-- §3 `(nullable)`: the subterm's premises, and **nothing else**. Null-honesty was the
    other half of this until the wrapper's guard made it derivable
    (`nullHonest_of_not_ownsNull`) — one of the four premises §5's theorem levied, now
    paid by lawfulness instead. -/
theorem nullable {t} (h : Obligations (.nullable t)) :
    Obligations t := h

/-- §3 `(custom)`: the escape hatch proves §2's laws for itself. -/
theorem custom {ce cp} (h : Obligations (.custom ce cp)) :
    Lawful { T := fun v => (ce v).isSome, μ := none, e := ce, p := cp } := h

/-- §5 `(union)`: one premise per option, and (U) where the union acts. -/
theorem union {opts} (h : Obligations (.union opts)) :
    (∀ t ∈ opts, Obligations t) ∧ UAtAct opts :=
  ⟨obligationsList_iff.mp h.1, h.2⟩

/-- §5 `(dunion)`: one premise per variant. (U) is not a premise and is no longer a theorem
    either — a lookup reaches one variant by construction, so there is nothing to discharge. -/
theorem dunion {d} {variants : MapOf Body} (h : Obligations (.dunion d variants)) :
    ∀ k, ObligationsBody (variants.2 k) := h

/-- The `fallback` field's own premise, `v(∗) ∈ dom(e)`. -/
theorem fallback {t v} (h : ObligationsField (Field.fallback t v)) :
    Obligations t ∧ ((denote t).e v).isSome := h

end Obligations

/-! ## Ground-term lemmas -/

theorem lawful_string : Lawful (denote .string) := by
  simp only [denote]; exact lawful_stringCodec

theorem lawful_boolean : Lawful (denote .boolean) := by
  simp only [denote]; exact lawful_booleanCodec

theorem lawful_null : Lawful (denote .null) := by
  simp only [denote]; exact lawful_nullCodec

theorem lawful_binary : Lawful (denote .binary) := by
  simp only [denote]; exact lawful_binaryCodec

theorem lawful_decimal : Lawful (denote .decimal) := by
  simp only [denote]; exact lawful_decimalCodec

theorem lawful_number : Lawful (denote .number) := by
  simp only [denote]; exact lawful_numberCodec

/-- One where there were two, at every base rather than the two commonest. -/
theorem lawful_literal (k : GroundKind) (ls : NEFinset k.Carrier) :
    Lawful (denote (.literal k ls)) := by
  simp only [denote]; exact lawful_literalCodec k ls

/-! ## Inversion and dispatch helpers -/

theorem TypedList.forall : ∀ {ts Ts}, TypedList ts Ts → ∀ t ∈ ts, ∃ T μ, Typed t T μ
  | _, _, .nil, t, ht => absurd ht (by simp)
  | _, _, .cons h hs, t, ht => by
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact ⟨_, _, h⟩
      · exact TypedList.forall hs t ht'

theorem TypedListμ.forall : ∀ {ts Ts μs}, TypedListμ ts Ts μs →
    ∀ t ∈ ts, ∃ T μ, Typed t T μ
  | _, _, _, .nil, t, ht => absurd ht (by simp)
  | _, _, _, .cons h hs, t, ht => by
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact ⟨_, _, h⟩
      · exact TypedListμ.forall hs t ht'

theorem TypedListM.forall : ∀ {ts Ts}, TypedListM ts Ts →
    ∀ t ∈ ts, ∃ T, Typed t T (some .M)
  | _, _, .nil, t, ht => absurd ht (by simp)
  | _, _, .cons h hs, t, ht => by
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact ⟨_, h⟩
      · exact TypedListM.forall hs t ht'

theorem unanimous_spec : ∀ {l : List (Option Member)} {m},
    unanimous l = some m → ∀ x ∈ l, x = some m
  | [], _, h => nomatch h
  | μ :: μs, m, h => by
      replace h : (if μs.all (· == μ) then μ else none) = some m := h
      cases hall : μs.all (· == μ) with
      | false => rw [hall] at h; exact nomatch h
      | true =>
        rw [hall] at h
        replace h : μ = some m := h
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact h
        · have hbe := List.all_eq_true.mp hall x hx'
          have hxeq : x = μ := eq_of_beq hbe
          rw [hxeq, h]

theorem optionSemOf_c (c : Codec) : ∀ s?, (optionSemOf c s?).c = c
  | some _ => rfl
  | none => rfl


mutual

/-- Typing's member index is the syntactic one — exactly, both sides. -/
theorem typed_μSyn : ∀ {t T μ}, Typed t T μ → μSyn t = μ
  -- `rfl`, where this used to be the rule's `hμ`. The member is a function of the *index* on
  -- both sides now — `μSyn` reads `GroundKind.member`, and so does the rule.
  | _, _, _, .literal _ _ => rfl
  | _, _, _, .string => rfl
  | _, _, _, .number => rfl
  | _, _, _, .decimal => rfl
  | _, _, _, .boolean => rfl
  | _, _, _, .null => rfl
  | _, _, _, .binary => rfl
  | _, _, _, .set _ => rfl
  | _, _, _, .array _ => rfl
  | _, _, _, .tuple _ _ => rfl
  | _, _, _, .record _ => rfl
  | _, _, _, .held h' => by have ih := typed_μSyn h'; exact ih
  | _, _, _, .refine h' => by have ih := typed_μSyn h'; exact ih
  | _, _, _, .legacy h' => by have ih := typed_μSyn h'; exact ih
  | _, _, _, .nullable _ => rfl
  | _, _, _, .lazy _ => rfl
  | _, _, _, .custom _ _ => rfl
  | _, _, _, .opaq _ => rfl
  | _, _, _, .object _ _ => rfl
  | _, _, _, .union h _ => by
      show unanimous (μSynList _) = unanimous _
      rw [typedListμ_μSyn h]
  | _, _, _, .dunion _ _ => rfl

theorem typedListμ_μSyn : ∀ {ts Ts μs}, TypedListμ ts Ts μs → μSynList ts = μs
  | _, _, _, .nil => rfl
  | _, _, _, .cons h hs => by
      show μSyn _ :: μSynList _ = _
      rw [typed_μSyn h, typedListμ_μSyn hs]

end

/-! ## The `(dunion)` stamp -/

/-- Typing's nonempty-tags premise **is** a shape constraint: `tagsOf` is empty for
    everything except an object whose `d` field is a `req literal` at a base that names a tag, so
    a term with tags is one, and its tags are that literal's set. Stated once, it replaces the
    outer case analysis in `dunion_stamp` below.

    **Two bases name a tag, and the base stays existential.** `string` and `decimal`, because the
    host's tag reader accepts `S` or `N` and keys on the text either way, and a decimal literal
    holds its numeral as text. `number` does not, and the reason is not policy: `Double` is an
    axiom with no closed terms, so no numeric tag can appear in a term this development can state.
    The remaining three name no tag a lookup could reach.

    The conclusion is stated through `tagsOfField` rather than through the literal's own set,
    which is what lets the base stay existential: at `string` the set is `ls.1` and at `decimal`
    it is that set's texts, and no consumer needs to know which. -/
theorem tagsOf_ne_nil {d : Name} {t : Term} (h : (tagsOf d t).Nonempty) :
    ∃ (b : Body) (k : GroundKind) (ls : NEFinset k.Carrier), t = .object b ∧
      (k = .string ∨ k = .decimal) ∧
      b.map.at d = some (.req (.literal k ls)) ∧
      tagsOf d t = tagsOfField (some (.req (.literal k ls))) := by
  cases t
  case object body =>
    cases hlk : MapOf.at (α := Field) body.map d with
    | none => exact absurd h (by simp only [tagsOf, Body.tags]; rw [hlk]; simp [tagsOfField])
    | some fd =>
      cases fd with
      | optional _ => exact absurd h (by simp only [tagsOf, Body.tags]; rw [hlk]; simp [tagsOfField])
      | fallback _ _ => exact absurd h (by simp only [tagsOf, Body.tags]; rw [hlk]; simp [tagsOfField])
      | req tlit =>
        cases tlit
        case literal k ls =>
          cases k
          case string => exact ⟨body, .string, ls, rfl, Or.inl rfl, hlk, by
            simp only [tagsOf, Body.tags]; rw [hlk]⟩
          case decimal => exact ⟨body, .decimal, ls, rfl, Or.inr rfl, hlk, by
            simp only [tagsOf, Body.tags]; rw [hlk]⟩
          all_goals exact absurd h (by simp only [tagsOf, Body.tags]; rw [hlk]; simp [tagsOfField])
        all_goals exact absurd h (by simp only [tagsOf, Body.tags]; rw [hlk]; simp [tagsOfField])
  all_goals exact absurd h (by simp [tagsOf])

/-- **A literal at a tag base stamps its tag on both sides**, and the two bases are one lemma
    because the *readers* are uniform where the codecs are not.

    `tagOfV` reads a `.str` and `tagOfA` reads an `.s` or an `.n`, and both answer the text. A
    string literal writes `.str s` and stores `.s s`; a decimal literal writes `.str x.1` and
    stores `.n ⟨x.1, _⟩`. So the value side is one row for both bases and the stored side is the
    two rows `tagOfA` has, which is why `dunion_stamp` below no longer names a base. -/
theorem literalCodec_tag {k : GroundKind} (hk : k = .string ∨ k = .decimal)
    {ls : NEFinset k.Carrier} {v : Value} {a : Attr}
    (h : (literalCodec k ls).e v = some a) :
    ∃ tag ∈ tagsOfField (some (.req (.literal k ls))),
      v.tagText = some tag ∧ a.tagText = some tag := by
  rcases hk with rfl | rfl
  · cases v
    case str tagv =>
      replace h : (if tagv ∈ ls.1 then some (Attr.s tagv) else none) = some a := by
        simpa [literalCodec, baseCodec, Codec.restrict, inL, stringCodec] using h
      split at h
      · rename_i hin
        refine ⟨tagv, by simpa [tagsOfField] using hin, rfl, ?_⟩
        rw [← Option.some.inj h]; rfl
      · exact nomatch h
    all_goals exact absurd h (by
      simp [literalCodec, baseCodec, Codec.restrict, inL, stringCodec])
  · cases v
    case str tagv =>
      simp only [literalCodec, baseCodec, Codec.restrict, decimalCodec, inL] at h
      split at h
      · rename_i hst
        split at h
        · rename_i hin
          refine ⟨tagv, ?_, rfl, ?_⟩
          · simp only [tagsOfField, Finset.mem_map]
            exact ⟨⟨tagv, hst⟩, of_decide_eq_true hin, rfl⟩
          · rw [← Option.some.inj h]; rfl
        · exact nomatch h
      · exact nomatch h
    all_goals exact absurd h (by
      simp [literalCodec, baseCodec, Codec.restrict, inL, decimalCodec])

/-! ~~tagsOf_nonempty_of_card_one~~ bridged `(dunion)`'s old `card = 1` premise to the
nonemptiness the inversion wanted. The premise is now `tags d = {k.1}`, which gives the
nonemptiness directly and gives the tag's identity besides, so the bridge has nothing to cross. -/

/-- **A body with a tag stamps it on both sides of every canonical pair it writes.** Nonempty
    tags force the discriminator to be a `req` literal at a tag base, and object-encode writes a
    literal verbatim, so the attribute carries the tag the value does.

    Stated over a `Body` rather than over a list of options, because that is what a variant is. -/
theorem body_stamp {d : Name} {b : Body} (hne : (b.tags d).Nonempty)
    {t' : Value} {a : Attr} (he' : (bodySem b).e t' = some a) :
    ∃ tag ∈ b.tags d, tagOfA d a = some tag ∧ tagOfV d t' = some tag := by
  obtain ⟨body, kb, ls, hbe, hkb, hlk, htagsls⟩ :=
    tagsOf_ne_nil (t := Term.object b) hne
  obtain rfl : body = b := (Term.object.inj hbe).symm
  -- the payload's three components are what `objectCodecCore_e_inv` reads, so it is taken
  -- apart once, here, rather than threaded through the statement above
  obtain ⟨fields, ff, rest⟩ := body
  replace he' : (objectCodec ⟨fields, fun k => fieldSem (ff k)⟩ (restSem rest)).e t' = some a :=
    he'
  obtain ⟨keys, fv, g, rfl, rfl, hval, hfi⟩ := objectCodecCore_e_inv he'
  -- the discriminator is declared and non-`opt`, so the key set carries it. Denoting
  -- the table does not touch its key set, so the term's lookup *is* the semantics'.
  have hslk : MapOf.at (⟨fields, fun k => fieldSem (ff k)⟩ : MapOf FieldSem) d
      = some (FieldSem.req (denote (Term.literal kb ls))) := by
    obtain ⟨hdf, hfd⟩ := MapOf.at_eq_some.mp hlk
    replace hfd : ff ⟨d, hdf⟩ = Field.req (Term.literal kb ls) := hfd
    refine MapOf.at_eq_some.mpr ⟨hdf, ?_⟩
    show fieldSem (ff ⟨d, hdf⟩) = _
    rw [hfd]; rfl
  have hd : d ∈ keys :=
    valPresentB_spec hval hslk (fun _ h' => nomatch h')
  -- …and `literal` writes it verbatim, which is the stamp on both sides. The key set
  -- is shared by the two payloads, so one membership proof serves both projections —
  -- where the list representation had to find `d` in each row separately.
  have hw := funImage_some hfi ⟨d, hd⟩
  rw [show entryCodec ⟨fields, fun k => fieldSem (ff k)⟩
        (rcOf (restSem rest)) d = some (denote (Term.literal kb ls)) by
      simp only [entryCodec, hslk]; rfl] at hw
  replace hw : (literalCodec kb ls).e (fv ⟨d, hd⟩) = some (g ⟨d, hd⟩) := hw
  -- the base is existential from here: `literalCodec_tag` answers both of them, because the
  -- two *readers* are uniform where the two codecs are not
  obtain ⟨tag, htag, hv, ha⟩ := literalCodec_tag hkb hw
  -- `tagsOf` at an object *is* `Body.tags`, and the goal is stated at the payload
  replace htagsls : Body.tags d ⟨fields, ff, rest⟩
      = tagsOfField (some (.req (.literal kb ls))) := htagsls
  exact ⟨tag, htagsls ▸ htag,
    by simp only [tagOfA, dif_pos hd]; exact ha,
    by simp only [tagOfV, dif_pos hd]; exact hv⟩

/-- **The stamp a lookup needs**, from the one premise the table cannot carry. `hone` says a
    variant's own tag set is the singleton of its key, so the tag `body_stamp` produces *is* the
    key, and the lookup's two halves reach the same variant. -/
theorem dunion_stamp {d : Name} {variants : MapOf Body}
    (hone : ∀ k, (variants.2 k).tags d = {k.1}) :
    StampedAt d ⟨variants.1, fun k => bodySem (variants.2 k)⟩ := by
  intro k v a he
  have hne : ((variants.2 k).tags d).Nonempty := by
    rw [hone k]; exact ⟨k.1, Finset.mem_singleton_self _⟩
  obtain ⟨tag, htag, hA, hV⟩ := body_stamp hne he
  rw [hone k, Finset.mem_singleton] at htag
  subst htag
  exact ⟨hA, hV⟩

/-! ## The theorem

Both halves in one induction. `Sound` names what a case has to deliver, and three
helpers name the three shapes a case comes in: a ground pair, lawful outright; one
subterm, whose two combinator lemmas are applied to the two halves of the induction
hypothesis; and a list of subterms, where the hypothesis is read off the mapped list.
What is left in each case is the combinator lemmas it cites — which is the content. -/

/-- What one derivation has to deliver: the core laws unconditionally, and all four
    where it is legacy-free. -/
abbrev Sound (t : Term) : Prop :=
  LawfulCore (denote t) ∧ (MPOk t → Lawful (denote t))

/-- A ground case: the pair is lawful outright, so both halves are the same lemma. -/
theorem sound_ground {P : Prop} {c : Codec} (h : Lawful c) :
    LawfulCore c ∧ (P → Lawful c) :=
  ⟨h.core, fun _ => h⟩

/-- A one-subterm case: the subterm's core lemma and its full one, applied to the two
    halves of the induction hypothesis. (MP) passes through unchanged — every wrapper
    but `legacy` is transparent to it. -/
theorem sound_wrap {t : Term} {c : Codec} (ih : Sound t)
    (core : LawfulCore (denote t) → LawfulCore c)
    (full : Lawful (denote t) → Lawful c) :
    LawfulCore c ∧ (MPOk t → Lawful c) :=
  ⟨core ih.1, fun hmp => full (ih.2 hmp)⟩

/-- `(fallback)`'s premise `v(∗) ∈ dom(e)`, transported to the denoted field list —
    which is the shape `object`'s two lemmas ask for. Both walks of the derivation
    need it, so it is stated here rather than twice inside them. -/
theorem fieldSems_fb {fields : Finset Name}
    {f : {k // k ∈ fields} → Field}
    (hob : ∀ k, ObligationsField (f k)) :
    ∀ (k : {k // k ∈ fields}) c v, fieldSem (f k) = .fb c v → (c.e v).isSome := by
  intro k c v hcv
  have hobf := hob k
  cases hfk : f k with
  | req t' => rw [hfk] at hcv; exact nomatch hcv
  | optional t' => rw [hfk] at hcv; exact nomatch hcv
  | fallback t' v₀ =>
    rw [hfk] at hcv hobf
    replace hobf := Obligations.fallback hobf
    replace hcv : FieldSem.fb (denote t') v₀ = FieldSem.fb c v := hcv
    cases hcv
    exact hobf.2

-- the shared `term_depth_wf` block has alternatives this theorem's goals do not use
set_option linter.unreachableTactic false in
/-- Both halves of §5's theorem in one induction: the core laws unconditionally, and
    all four where the derivation is legacy-free. One walk of the derivation, one
    unpacking of the obligations; each case dispatches to its two combinator lemmas.
    The public statements are the projections below. -/
theorem soundness_both : ∀ {t T μ}, Typed t T μ → Obligations t → Sound t
  | t, T, μ, h, hob => by
    cases h with
    | literal k ls => exact sound_ground (lawful_literalCodec k ls)
    | string => exact sound_ground lawful_stringCodec
    | number => exact sound_ground lawful_numberCodec
    | decimal => exact sound_ground lawful_decimalCodec
    | boolean => exact sound_ground lawful_booleanCodec
    | null => exact sound_ground lawful_nullCodec
    | binary => exact sound_ground lawful_binaryCodec
    | opaq lossy => exact sound_ground (lawful_opaqCodecω lossy)
    | custom ce cp =>
      exact sound_ground hob.custom
    -- a leaf now: `setCodec` is lawful at each of the four bases, so `(set)` discharges the
    -- way the ground rules do rather than by wrapping a subterm's soundness
    | set b => exact sound_ground (lawful_setCodec (lawful_setBase b))
    | @array t' T' μ' h' =>
      exact sound_wrap (t := t') (soundness_both h' hob) lawfulCore_arrayCodec lawful_arrayCodec
    | @record t' T' μ' h' =>
      exact sound_wrap (t := t') (soundness_both h' hob) lawfulCore_recordCodec lawful_recordCodec
    | @refine t' T' μ' p h' =>
      exact sound_wrap (t := t') (soundness_both h' hob)
        (LawfulCore.restrict · p.eval) (Lawful.restrict · p.eval)
    | @lazy γ T' μ' h' =>
      exact sound_wrap (t := γ) (soundness_both h' hob) LawfulCore.μNone Lawful.μNone
    | @held t' I' μ' f g h' =>
      exact sound_wrap (t := t') (soundness_both h' hob.1) (LawfulCore.through · hob.2)
        (Lawful.through · hob.2)
    | @nullable t' T' μ' h' =>
      exact sound_wrap (t := t') (soundness_both h' hob) lawfulCore_withNull lawful_withNull
    | @legacy t' T' μ' r h' =>
      -- (MP) is off here by design: `MPOk` is `False` at a `legacy`, so the second
      -- half is vacuous and only the core laws survive. §5's first residue.
      exact ⟨LawfulCore.extendRead (soundness_both h' hob.1).1 hob.2.1, fun hmp => hmp.elim⟩
    | @tuple ts Ts tail Tt hlist hopt =>
      have ihs : ∀ t' ∈ ts, Sound t' := fun t' ht' => by
        obtain ⟨T', μ', hμ'⟩ := TypedList.forall hlist t' ht'
        exact soundness_both hμ' ((Obligations.tuple hob).1 t' ht')
      have iht : ∀ t' ∈ tail, Sound t' := fun t' ht' => by
        cases tail with
        | none => exact nomatch ht'
        | some tx =>
          replace ht' : some tx = some t' := ht'
          cases ht'
          cases hopt with
          | some hμ' => exact soundness_both hμ' ((Obligations.tuple hob).2 t' rfl)
      rw [Sound, denote_tuple, denoteList_eq, denoteOpt_eq]
      exact ⟨lawfulCore_tupleCodec (forall_mem_map fun t' ht' => (ihs t' ht').1)
          (forall_mem_map_option fun t' ht' => (iht t' ht').1),
        fun hmp => lawful_tupleCodec
          (forall_mem_map fun t' ht' => (ihs t' ht').2 (mpOkList_iff.mp hmp.1 t' ht'))
          (forall_mem_map_option fun t' ht' => (iht t' ht').2 (mpOkOpt_iff.mp hmp.2 t' ht'))⟩
    -- The field table is indexed by the declared names, so the induction hypothesis is
    -- read off at a key rather than at a membership, and ~~TypedFields.forall~~ — which
    -- existed to walk the row — is not needed. Nor is a `Nodup` to transport.
    | @object body bind R μs hfields hrest =>
      -- the payload is taken apart once, here: the field lemmas below read a key set and a
      -- function on it, and `objectCodec` is stated over those
      cases body with | mk fields ff rest =>
      simp only [Body.fields_mk, Body.at_mk, Body.rest_mk] at hfields hrest
      -- a field's codec is its term's denotation, and (MP) reaches it unchanged
      have ihf : ∀ k, LawfulCore (fieldSem (ff k)).codec ∧
          (MPOkField (ff k) → Lawful (fieldSem (ff k)).codec) := by
        intro k
        have hobf := hob.1 k
        obtain ⟨t', hty', hshape⟩ := TypedField.term (hfields k)
        rcases hshape with heq | heq | ⟨v, heq⟩ <;>
          rw [heq] at hobf ⊢ <;> simp only [MPOkField]
        · exact soundness_both hty' hobf
        · exact soundness_both hty' hobf
        · exact soundness_both hty' (Obligations.fallback hobf).1
      have hfb := fieldSems_fb hob.1
      have ihr : ∀ c, restSem rest = .codec c →
          LawfulCore c ∧ (MPOk (.object (.mk fields ff rest)) → Lawful c) := by
        intro c hcr
        cases hrest with
        | drop => exact nomatch hcr
        | refuse => exact nomatch hcr
        | @codec t' T' μ' hty =>
          replace hcr : RestSem.codec (denote t') = RestSem.codec c := hcr
          cases hcr
          exact ⟨(soundness_both hty hob.2).1, fun hmp => (soundness_both hty hob.2).2 hmp.2⟩
      rw [Sound, denote_object_table, fieldTable]
      exact ⟨lawfulCore_objectCodec (fun k => (ihf k).1) hfb
          (fun c hcr => (ihr c hcr).1),
        fun hmp => lawful_objectCodec (fun k => (ihf k).2 (hmp.1 k)) hfb
          (fun c hcr => (ihr c hcr).2 hmp)⟩
    | @union opts Ts μs hlist _ =>
      have ihs : ∀ t' ∈ opts, Sound t' := fun t' ht' => by
        obtain ⟨T', μ', hμ'⟩ := TypedListμ.forall hlist t' ht'
        exact soundness_both hμ' ((Obligations.union hob).1 t' ht')
      have hU : UniqueBothWays
          (opts.map fun t' => optionSemOf (denote t') (specOf t')) := hob.2
      have hW : ∀ m, unanimous (opts.map fun t' => (denote t').μ) = some m →
          ∀ o ∈ opts.map fun t' => optionSemOf (denote t') (specOf t'),
            ∀ t' a, o.c.e t' = some a → a.member = m := by
        intro m hm
        refine forall_mem_map fun tx htx t' a he' => ?_
        rw [optionSemOf_c] at he'
        exact (ihs tx htx).1.writes
          (unanimous_spec hm _ (List.mem_map.mpr ⟨tx, htx, rfl⟩)) he'
      rw [Sound, denote_union_sems, optionSems_eq, denoteμs_eq_map]
      exact ⟨lawfulCore_altCodec
          (forall_mem_map fun t' ht' => (optionSemOf_c _ _) ▸ (ihs t' ht').1) hU hW,
        fun hmp => lawful_altCodec
          (forall_mem_map fun t' ht' => (optionSemOf_c _ _) ▸ (ihs t' ht').2 (mpOkList_iff.mp hmp t' ht'))
          hU hW⟩
    | @dunion d variants Ts hty hone =>
      -- **no uniqueness premise.** A lookup reaches one variant by construction, so where the
      -- filtered sum needed `hdisj` and `UniqueAdmission`, there is nothing to supply
      have ihs : ∀ k, Sound (Term.object (variants.2 k)) := fun k =>
        soundness_both (hty k) (hob k)
      have hstamp := dunion_stamp hone
      rw [Sound, denote_dunion_tags]
      exact ⟨lawfulCore_dunionTable (fun k => (ihs k).1) hstamp,
        fun hmp => lawful_dunionTable (fun k => (ihs k).2 (hmp k)) hstamp⟩

termination_by t _ _ _ _ => Term.depth t
decreasing_by term_depth_wf
/-! ## The denotation's held set is the judgement's

    `Carrier` bounds `e` and `p` by the *codec's* `T`. `typed_TSub` bounds the codec's
    `T` by the *judgement's*, which is what makes §3's `⊢ c : T ⇝ μ` a claim about the
    denotation rather than a decoration. The two compose into `typed_e_mem` and
    `typed_p_mem` below.

    Each rule's held set is built by the same former the combinator's `T` field uses, so
    most cases are pointwise. Three are not: `tuple` (positional through `align`),
    `object` (name-dispatched) and `opaque` (a fixpoint), and each gets a helper. -/

/-- The uniform tail of a `(tuple-tail)`: every trailing position is the tail's. -/
theorem alignTail_TSub {c : Codec} {T' : Held} (ih : ∀ v, c.T v → T' v) :
    ∀ {vs ps}, align [] (some c) vs = some ps → (∀ p ∈ ps, p.1.T p.2) → ∀ x ∈ vs, T' x
  | [], _, _, _, x, hx => absurd hx (by simp)
  | v :: vs, ps, hal, hall, x, hx => by
      replace hal : ((align [] (some c) vs).map ((c, v) :: ·)) = some ps := hal
      cases hal' : align ([] : List Codec) (some c) vs with
      | none => rw [hal'] at hal; exact nomatch hal
      | some ps' =>
        rw [hal'] at hal
        replace hal : some ((c, v) :: ps') = some ps := hal
        cases hal
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact ih x (hall (c, x) (List.mem_cons_self))
        · exact alignTail_TSub ih hal'
            (fun p hp => hall p (List.mem_cons_of_mem _ hp)) x hx'

/-- …and the same tail, built rather than read. `alignTail_TSub` takes an `align` that
    already succeeded; the converse has to *produce* one, and that is the whole difference
    between the two directions here: on this side `align`'s success is a conclusion, not a
    hypothesis. It never fails at a tail, because a tail accepts any length. -/
theorem alignTail_T {c : Codec} {T' : Held} (ih : ∀ v, T' v → c.T v) :
    ∀ (vs : List Value), (∀ x ∈ vs, T' x) →
      ∃ ps, align [] (some c) vs = some ps ∧ ∀ p ∈ ps, p.1.T p.2
  | [], _ => ⟨[], rfl, by simp⟩
  | v :: vs, hall => by
      obtain ⟨ps, hal, hps⟩ :=
        alignTail_T ih vs (fun x hx => hall x (List.mem_cons_of_mem _ hx))
      refine ⟨(c, v) :: ps, ?_, ?_⟩
      · simp only [align, hal, Option.map_some]
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact ih v (hall v (List.mem_cons_self))
        · exact hps p hp'

/-- `align`'s positional pairing is §3's `T₁ × … × Tₙ`, one position at a time. -/
theorem align_TSub {tail Tt} (hopt : TypedOpt tail Tt)
    (ihTail : ∀ t' ∈ tail, ∀ (T' : Held) (μ' : Option Member),
      Typed t' T' μ' → ∀ v, (denote t').T v → T' v) :
    ∀ {ts Ts}, TypedList ts Ts →
      (∀ t' ∈ ts, ∀ (T' : Held) (μ' : Option Member),
        Typed t' T' μ' → ∀ v, (denote t').T v → T' v) → ∀ {vs ps},
      align (ts.map denote) (tail.map denote) vs = some ps →
      (∀ p ∈ ps, p.1.T p.2) → HTuple Ts Tt vs
  | _, _, .nil, _, vs, ps, hal, hall => by
      cases hopt with
      | none =>
        show HTuple [] none vs
        cases vs with
        | nil => rfl
        | cons _ _ => exact nomatch hal
      | @some t' T' μ' hty =>
        show HTuple [] (some T') vs
        exact alignTail_TSub (ihTail _ rfl _ _ hty) hal hall
  | _, _, .cons hty hs, ih, vs, ps, hal, hall => by
      cases vs with
      | nil => exact nomatch hal
      | cons v vs' =>
        replace hal : (((align _ (tail.map denote) vs')).map
          ((denote _, v) :: ·)) = some ps := hal
        cases hal' : align _ (tail.map denote) vs' with
        | none => rw [hal'] at hal; exact nomatch hal
        | some ps' =>
          rw [hal'] at hal
          replace hal : some ((denote _, v) :: ps') = some ps := hal
          cases hal
          refine ⟨ih _ (List.mem_cons_self) _ _ hty v (hall _ (List.mem_cons_self)), ?_⟩
          exact align_TSub hopt ihTail hs
            (fun t' ht' => ih t' (List.mem_cons_of_mem _ ht')) hal'
            (fun p hp => hall p (List.mem_cons_of_mem _ hp))

/-- …and the positional pairing built from the held sets instead of read off them.

    **`HTuple` is what makes `align` total here**, and that is the content of this direction:
    the head lists are the same length by construction, and a tail accepts whatever is left,
    so the `none` rows of `align` are unreachable under the hypothesis. `align_TSub` never
    has to know that — it is handed the `some`. -/
theorem align_T_of_HTuple {tail Tt} (hopt : TypedOpt tail Tt)
    (ihTail : ∀ t' ∈ tail, ∀ (T' : Held) (μ' : Option Member),
      Typed t' T' μ' → ∀ v, T' v → (denote t').T v) :
    ∀ {ts Ts}, TypedList ts Ts →
      (∀ t' ∈ ts, ∀ (T' : Held) (μ' : Option Member),
        Typed t' T' μ' → ∀ v, T' v → (denote t').T v) →
      ∀ (vs : List Value), HTuple Ts Tt vs →
      ∃ ps, align (ts.map denote) (tail.map denote) vs = some ps ∧ ∀ p ∈ ps, p.1.T p.2
  | _, _, .nil, _, vs, hall => by
      cases hopt with
      | none =>
        obtain rfl : vs = [] := hall
        exact ⟨[], rfl, by simp⟩
      | @some t' T' μ' hty =>
        exact alignTail_T (ihTail _ rfl _ _ hty) vs hall
  | _, _, @TypedList.cons tx tsx Tx Tsx μx hty hs, ih, vs, hall => by
      cases vs with
      | nil => exact nomatch hall
      | cons v vs' =>
        obtain ⟨ps, hal, hps⟩ :=
          align_T_of_HTuple hopt ihTail hs
            (fun x hx => ih x (List.mem_cons_of_mem _ hx)) vs' hall.2
        refine ⟨(denote tx, v) :: ps, ?_, ?_⟩
        · simp only [List.map_cons, align, hal, Option.map_some]
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact ih tx (List.mem_cons_self) _ _ hty v hall.1
          · exact hps p hp'

/-- `opaque`'s fixpoint carries §3's `Uν` at every fuel.

    **This fuel stays.** It is `Opaque.lean`'s budget on the *input's* depth, not `denote`'s on
    the term — a different recursion, and one this change does not touch. -/
theorem opaq_TSub : ∀ (fuel : Nat) (lossy : Bool) (v : Value),
    (opaqCodec fuel lossy).T v → HOpaque lossy v
  | 0, _, _, h => nomatch h
  | fuel+1, lossy, v, h => by
    obtain ⟨o, ho, hT⟩ := h
    have ih := opaq_TSub fuel lossy
    simp only [opaqOptions, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨s, rfl⟩ := hT; exact .str s
    · obtain ⟨b, rfl⟩ := hT; exact .bool b
    · obtain ⟨b, rfl⟩ := hT; exact .bin b
    · cases hT; exact .null
    · cases hl : lossy with
      | false => rw [hl] at hT; exact nomatch hT
      | true =>
        rw [hl] at hT
        obtain ⟨d, rfl, hw⟩ := hT
        exact .num d rfl hw
    · cases v <;> first
        | exact .strSet _ fun s hs => ih (Value.str s) (hT s hs)
        | exact .numSet _ fun d hd => ih (Value.num d) (hT d hd)
        | exact .binSet _ fun b hb => ih (Value.bin b) (hT b hb)
        | exact nomatch hT
    · cases v <;> first
        | exact .arr _ fun x hx => ih x (hT x hx)
        | exact nomatch hT
    · cases v <;> first
        | exact .map _ _ fun k => ih _ (hT k)
        | exact nomatch hT

/-- `opaqCodecω`'s held set — the union over all fuels — still lands in §3's `Uν`. -/
theorem opaq_TSubω (lossy : Bool) (v : Value) :
    (opaqCodecω lossy).T v → HOpaque lossy v := by
  intro h
  obtain ⟨n, hn⟩ := h
  exact opaq_TSub n lossy v hn

/-- A union option's held set is one of the rule's. -/
theorem TypedListμ.mem : ∀ {ts Ts μs}, TypedListμ ts Ts μs →
    ∀ t ∈ ts, ∃ T ∈ Ts, ∃ μ, Typed t T μ
  | _, _, _, .nil, t, ht => absurd ht (by simp)
  | _, _, _, .cons h hs, t, ht => by
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact ⟨_, List.mem_cons_self, _, h⟩
      · obtain ⟨T', hT', μ', hty⟩ := TypedListμ.mem hs t ht'
        exact ⟨T', List.mem_cons_of_mem _ hT', μ', hty⟩

theorem TypedListM.mem : ∀ {ts Ts}, TypedListM ts Ts →
    ∀ t ∈ ts, ∃ T ∈ Ts, Typed t T (some .M)
  | _, _, .nil, t, ht => absurd ht (by simp)
  | _, _, .cons h hs, t, ht => by
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact ⟨_, List.mem_cons_self, h⟩
      · obtain ⟨T', hT', hty⟩ := TypedListM.mem hs t ht'
        exact ⟨T', List.mem_cons_of_mem _ hT', hty⟩

/-- …and the option that answers for a held set, which is the lookup in the other direction.

    `TypedListμ.mem` goes from a *term* in the list to its held set; here a value is known to
    lie in one of the rule's held sets and the option holding it has to be produced. The two
    lists are built together by the same `cons`, so neither direction needs a premise — but
    membership in `Ts` names no term, so this cannot be `mem` applied backwards and is a
    recursion of its own. The denotation argument arrives as `ih` rather than being taken
    here, because the caller is the one with the depth measure. -/
theorem unionT_of_mem : ∀ {opts : List Term} {Ts μs}, TypedListμ opts Ts μs →
    (∀ t ∈ opts, ∀ (T : Held) (μ), Typed t T μ → ∀ v, T v → (denote t).T v) →
    ∀ (v : Value) (T : Held), T ∈ Ts → T v → ∃ t ∈ opts, (denote t).T v
  | _, _, _, .nil, _, _, _, hT, _ => nomatch hT
  | _, _, _, .cons hty hs, ih, v, T, hT, hv => by
    rcases List.mem_cons.mp hT with rfl | hT'
    · exact ⟨_, List.mem_cons_self, ih _ (List.mem_cons_self) _ _ hty v hv⟩
    · obtain ⟨t'', ht'', hd⟩ :=
        unionT_of_mem hs (fun x hx => ih x (List.mem_cons_of_mem _ hx)) v T hT' hv
      exact ⟨t'', List.mem_cons_of_mem _ ht'', hd⟩

/-- …and its `(dunion)` twin, where every option is at `M`. -/
theorem unionMT_of_mem : ∀ {opts : List Term} {Ts}, TypedListM opts Ts →
    (∀ t ∈ opts, ∀ (T : Held) (μ), Typed t T μ → ∀ v, T v → (denote t).T v) →
    ∀ (v : Value) (T : Held), T ∈ Ts → T v → ∃ t ∈ opts, (denote t).T v
  | _, _, .nil, _, _, _, hT, _ => nomatch hT
  | _, _, .cons hty hs, ih, v, T, hT, hv => by
    rcases List.mem_cons.mp hT with rfl | hT'
    · exact ⟨_, List.mem_cons_self, ih _ (List.mem_cons_self) _ _ hty v hv⟩
    · obtain ⟨t'', ht'', hd⟩ :=
        unionMT_of_mem hs (fun x hx => ih x (List.mem_cons_of_mem _ hx)) v T hT' hv
      exact ⟨t'', List.mem_cons_of_mem _ ht'', hd⟩

-- the shared `term_depth_wf` block has alternatives this theorem's goals do not use
set_option linter.unreachableTactic false in
/-- The denotation's held set is inside the judgement's, at every fuel. -/
theorem typed_TSub : ∀ {t T μ}, Typed t T μ → ∀ v, (denote t).T v → T v
  | t, T, μ, h, v, hv => by
    cases h with
    | string | number | decimal | boolean | binary | null => exact hv
    -- `exact hv`, where this was a five-way split guarding against `simp` unfolding
    -- `numberCodec` into `Numeral.WF`'s decision procedure. The denotation's held set and the
    -- rule's are the same expression now — `HLit k ls` — so there is nothing to prove.
    | literal _ _ => exact hv
    | custom _ _ => exact hv
    | opaq lossy => exact opaq_TSubω lossy v hv
    -- the base's codec holds exactly the base's held set (`SetBase.elem_T`), so the three
    -- wire families transport with no recursion left to do
    | set b =>
      cases b <;> cases v <;> first
        | exact Or.inl ⟨_, rfl, fun x hx => hv x hx⟩
        | exact Or.inr (Or.inl ⟨_, rfl, fun x hx => hv x hx⟩)
        | exact Or.inr (Or.inr ⟨_, rfl, fun x hx => hv x hx⟩)
        | exact nomatch hv
    | @array t' T' μ' h' =>
      cases v <;> first
        | exact ⟨_, rfl, fun x hx => typed_TSub h' x (hv x hx)⟩
        | exact nomatch hv
    | @record t' T' μ' h' =>
      cases v <;> first
        | exact ⟨_, _, rfl, fun k => typed_TSub h' _ (hv k)⟩
        | exact nomatch hv
    | @tuple ts Ts tail Tt hlist hopt =>
      rw [denote_tuple, denoteList_eq, denoteOpt_eq] at hv
      cases v
      case arr vs =>
        obtain ⟨ps, hal, hall⟩ := hv
        exact ⟨_, rfl, align_TSub hopt
          (fun t' _ _ _ hty v hv => typed_TSub hty v hv) hlist
          (fun t' _ _ _ hty v hv => typed_TSub hty v hv) hal hall⟩
      all_goals exact absurd hv (by simp only [tupleCodec]; exact id)
    | @held t' I' μ' f g h' =>
      exact typed_TSub h' (f v) hv
    | @refine t' T' μ' q h' => exact ⟨typed_TSub h' v hv.1, hv.2⟩
    | @legacy t' T' μ' r h' => exact typed_TSub h' v hv
    | @nullable t' T' μ' h' =>
      rcases hv with hv' | rfl
      · exact Or.inl (typed_TSub h' v hv')
      · exact Or.inr rfl
    | @lazy γ T' μ' h' => exact typed_TSub h' v hv
    | @object body bind R μs hfields hrest =>
      cases body with | mk fields ff rest =>
      simp only [Body.fields_mk, Body.at_mk, Body.rest_mk] at hfields hrest ⊢
      -- No case split on `v`: the object's `T` is `carriedCodec`'s, so it *hands over*
      -- the payload — a key set and a function on it, which is exactly `HObject`'s
      -- witness. The list representation had to take `v` apart to find one.
      obtain ⟨⟨keys, kvs⟩, hvp, hval, hall⟩ := hv
      refine ⟨keys, kvs, hvp, ?_, ?_⟩
      · -- every required binding's name is present, because its field is not `opt`
        intro k hreq
        have hty := hfields k
        have hno : ∀ c, fieldSem (ff k) ≠ FieldSem.opt c := by
          intro c hc
          obtain ⟨t', -, hshape⟩ := TypedField.term hty
          rcases hshape with heq | heq | ⟨v, heq⟩
          · rw [heq] at hc; exact nomatch hc
          · exact TypedField.not_optional hty hreq t' heq
          · rw [heq] at hc; exact nomatch hc
        exact valPresentB_spec hval (MapOf.at_of_mem (m := ⟨fields, _⟩) k) hno
      · -- and every present name holds what its binding, or the open part, says
        intro k
        have hentry := hall k
        by_cases hk : k.1 ∈ fields
        · -- declared: the entry holds its field's set, and the binding is at the same key
          rw [dif_pos hk]
          simp only [objEntryT,
            MapOf.at_of_mem (m := (⟨fields, fun k => fieldSem (ff k)⟩ :
              MapOf FieldSem)) ⟨k.1, hk⟩] at hentry
          obtain ⟨t', hty', hshape⟩ := TypedField.term (hfields ⟨k.1, hk⟩)
          rcases hshape with heq | heq | ⟨v₀, heq⟩ <;> rw [heq] at hentry <;>
            exact typed_TSub hty' _ hentry
        · -- undeclared: it falls to the open part
          rw [dif_neg hk]
          simp only [objEntryT, MapOf.at, dif_neg hk] at hentry
          obtain ⟨rc, hrc, hrcT⟩ := hentry
          cases hrest with
          | drop => exact nomatch hrc
          | refuse => exact nomatch hrc
          | @codec t' T'' μ'' hty' =>
            replace hrc : some (denote t') = some rc := hrc
            cases hrc
            exact ⟨T'', rfl, typed_TSub hty' _ hrcT⟩
    | @union opts Ts μs hlist _ =>
      simp only [denote, optionSems_eq, denoteμs_eq_map] at hv
      obtain ⟨o, ho, hT⟩ := hv
      simp only [List.mem_map] at ho
      obtain ⟨tx, htx, rfl⟩ := ho
      obtain ⟨T', hT', μ', hty⟩ := TypedListμ.mem hlist tx htx
      rw [optionSemOf_c] at hT
      exact ⟨T', hT', typed_TSub hty v hT⟩
    | @dunion d variants Ts hty hone =>
      -- the codec's held set is the variants' disjunction over the key set, and so is the
      -- judgement's, so this is the induction hypothesis at whichever key the value landed on
      obtain ⟨k, hTv⟩ := hv
      exact ⟨k, typed_TSub (hty k) v hTv⟩

termination_by t _ _ _ _ _ => Term.depth t
decreasing_by term_depth_wf

-- the shared `term_depth_wf` block has alternatives this theorem's goals do not use
set_option linter.unreachableTactic false in
/-- Every derivable term denotes a pair **on its carrier** — §3's `e : T ⇀ 𝔸`,
    `p : 𝔸 ⇀ T`. One walk of the derivation, dispatching to the `Carrier` lemmas, with
    `soundness_both` supplying the lawfulness the `held` and `custom` cases need. -/
theorem carrier_denote : ∀ {t T μ}, Typed t T μ → Obligations t → Carrier (denote t)
  | t, T, μ, h, hob => by
    cases h with
    | literal k ls => exact carrier_literalCodec k ls
    | string => exact carrier_stringCodec
    | number => exact carrier_numberCodec
    | decimal => exact carrier_decimalCodec
    | boolean => exact carrier_booleanCodec
    | null => exact carrier_nullCodec
    | binary => exact carrier_binaryCodec
    | set b => exact carrier_setCodec (carrier_setBase b)
    | @array t' T' μ' h' =>
      exact carrier_arrayCodec (carrier_denote h' hob.array)
    | @record t' T' μ' h' =>
      exact carrier_recordCodec (carrier_denote h' hob.record)
    | @tuple ts Ts tail Tt hlist hopt =>
      rw [denote_tuple, denoteList_eq, denoteOpt_eq]
      refine carrier_tupleCodec (forall_mem_map ?_) (forall_mem_map_option ?_)
      · intro t' ht'
        obtain ⟨T', μ', hty⟩ := TypedList.forall hlist t' ht'
        exact carrier_denote hty ((Obligations.tuple hob).1 t' ht')
      · intro t' ht'
        cases tail with
        | none => exact nomatch ht'
        | some tx =>
          replace ht' : some tx = some t' := ht'
          cases ht'
          cases hopt with
          | some hty => exact carrier_denote hty ((Obligations.tuple hob).2 t' rfl)
    | @held t' I' μ' f g h' =>
      exact carrier_through (carrier_denote h' hob.1)
        (soundness_both h' hob.1).1 hob.2.2
    | @refine t' T' μ' p h' =>
      exact carrier_restrict (carrier_denote h' hob.refine) p.eval
    | @legacy t' T' μ' r h' =>
      exact carrier_extendRead (carrier_denote h' hob.1) hob.2.1
    | @nullable t' T' μ' h' =>
      exact carrier_withNull (carrier_denote h' hob)
    | @lazy γ T' μ' h' =>
      have ih := carrier_denote h' hob.lazy
      exact ⟨fun he => ih.domE he, fun hp => ih.ranP hp⟩
    | custom ce cp =>
      refine ⟨?_, ?_⟩
      · intro v a he
        replace he : ce v = some a := he
        show (ce v).isSome = true
        rw [he]
        rfl
      · intro a v hp
        replace hp : cp a = some v := hp
        exact hob.canon hp
    | opaq lossy => exact carrier_opaqCodecω lossy
    | @object body bind R μs hfields hrest =>
      cases body with | mk fields ff rest =>
      simp only [Body.fields_mk, Body.at_mk, Body.rest_mk] at hfields hrest
      have hsems : ∀ k : {k // k ∈ fields},
          Carrier (fieldSem (ff k)).codec := by
        intro k
        have hobf := hob.1 k
        obtain ⟨t', hty', hshape⟩ := TypedField.term (hfields k)
        rcases hshape with heq | heq | ⟨v, heq⟩ <;> rw [heq] at hobf ⊢
        · exact carrier_denote hty' hobf
        · exact carrier_denote hty' hobf
        · exact carrier_denote hty' (Obligations.fallback hobf).1
      have hfb := fieldSems_fb hob.1
      have hrc : ∀ rc, rcOf (restSem rest) = some rc → Carrier rc := by
        intro rc hcr
        cases hrest with
        | drop => exact nomatch hcr
        | refuse => exact nomatch hcr
        | @codec t' T' μ' hty =>
          replace hcr : some (denote t') = some rc := hcr
          cases hcr
          exact carrier_denote hty hob.2
      exact carrier_objectCodec hsems hrc hfb
    | @union opts Ts μs hlist _ =>
      rw [denote_union_sems, optionSems_eq]
      refine carrier_altCodec (forall_mem_map fun t' ht' => ?_)
      obtain ⟨T', μ', hty⟩ := TypedListμ.forall hlist t' ht'
      exact (optionSemOf_c _ _) ▸ carrier_denote hty ((Obligations.union hob).1 t' ht')
    | @dunion d variants Ts hty hone =>
      rw [denote_dunion_tags]
      exact carrier_dunionTable fun k => carrier_denote (hty k) (Obligations.dunion hob k)

termination_by t _ _ _ _ => Term.depth t
decreasing_by term_depth_wf
/-- §3's `e : T ⇀ 𝔸`, at the judgement's own index: a derivable term writes only
    values of the held set it names. -/
theorem typed_e_mem {t T μ} (h : Typed t T μ) (hob : Obligations t)
    {v a} (he : (denote t).e v = some a) : T v :=
  typed_TSub h v ((carrier_denote h hob).domE he)

/-- §3's `p : 𝔸 ⇀ T`, at the judgement's own index: a derivable term reads only into
    the held set it names. -/
theorem typed_p_mem {t T μ} (h : Typed t T μ) (hob : Obligations t)
    {a v} (hp : (denote t).p a = some v) : T v :=
  typed_TSub h v ((carrier_denote h hob).ranP hp)

/-- §5 Theorem (soundness), core half: (R), (C), (W) for every derivable term — the
    `legacy` case included, which is exactly where this differs from `soundness`. -/
theorem soundness_core {t T μ} (h : Typed t T μ)
    (hob : Obligations t) : LawfulCore (denote t) :=
  (soundness_both h hob).1

/-- §5 Theorem (soundness), full: all four laws where the derivation is legacy-free —
    the doc's (MP) exemption, made a hypothesis. Each case dispatches to its
    combinator lemma; the grouping is the doc's proof, machine-checked. -/
theorem soundness {t T μ} (h : Typed t T μ)
    (hob : Obligations t) (hmp : MPOk t) : Lawful (denote t) :=
  (soundness_both h hob).2 hmp

end Calculus
