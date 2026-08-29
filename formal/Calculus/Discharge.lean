import Calculus.Soundness

/-!
# §5 — The decidable dischargers of (U)

The machinery of (K): `Kind`, `κ`, `ident` and `adm` as total structural recursions over
the term language, exactly as §5's tables state them, plus the theorem that puts them to
work — `uAtCan_of_separated`, discharging `(union)`'s residual (U) at the declaration.

Separation is asked of each side of the pair. On the writable side: disjoint `κ`
(no `⊤`), or disjoint `adm`. On the readable side: distinct named members, or disjoint
`admA`. Open object options are excluded, since an undeclared name disqualifies the
option even where its rest codec would hold it — so an open object never admits its own
canonical pairs.

§5's (D) is *not* among these, and `not_uAtCan_literal_held` is why: held sets are sets
of values, (U)'s readable side quantifies over attributes, and `held`'s adapter relabels
between them. Two options can hold disjoint sets and read one attribute. (D) stays a
well-formedness condition on the `T` index; the readable side is decided on stored
attributes.

The `ident` exemption is here in its repaired form. An earlier §5 stated (K) as
`κ(cᵢ) ∩ κ(cⱼ) = ∅ ∨ ident(cᵢ) ∨ ident(cⱼ)` and called it sufficient for (U); it is
not, on either disjunct, and the two counterexamples at the foot of this file are
machine-checked. What carries the exemption is `adm` — the set an `ident` term checks
against — disjoint on *both* sides, which is what §5's worked example,
`union(literal("A"), literal("B"))`, actually has and what `uAtCan_literal_literal`
now discharges. `uAtCan_of_separated` is the combined theorem; `uAtCan_of_disjoint`
is its kind/member half.
-/

namespace Calculus

/-! ## `κ` — the kinds a term accepts

    `Kind` itself is §1 vocabulary and lives in `Domain.lean`, on both sides of the
    pair (`Value.kind`, `Attr.kind`). What is §5's is `κ`: which of those kinds a
    *term* accepts. -/

mutual

/-- §5's `κ`: the kinds of value a term accepts. `none` is the table's `⊤`, and it
    absorbs — `nullable`'s `∪` and `union`'s `⋃` answer `⊤` whenever a subterm does. -/
def κ : Term → Option (List Kind)
  | .string | .decimal | .literalS _ => some [.string]
  | .number | .numeric _ | .literalN _ => some [.number]
  | .boolean => some [.boolean]
  | .null => some [.null]
  | .binary => some [.binary]
  | .set _ => some [.set]
  | .array _ | .tuple _ _ => some [.array]
  | .record _ | .object _ _ | .dunion _ _ => some [.map]
  | .refine t _ | .legacy t _ => κ t
  | .nullable t => (κ t).map (.null :: ·)
  | .union opts => κList opts
  | .held _ _ _ | .lazy _ | .custom _ _ | .opaq _ => none

/-- `⋃ κ(cᵢ)`, `⊤`-absorbing. -/
def κList : List Term → Option (List Kind)
  | [] => some []
  | t :: ts =>
    match κ t, κList ts with
    | some ks, some ks' => some (ks ++ ks')
    | _, _ => none

end

mutual

/-- §5's `ident`: the term decides its own membership — attempted admission is
    evidence. Holds of `literal` and `dunion`; propagates through the containers and
    the transparent wrappers; never otherwise (`nullable` deliberately: two nullable
    options both admit the null neither subterm decides). -/
def ident : Term → Bool
  | .literalS _ | .literalN _ => true
  | .dunion _ _ => true
  | .set t | .array t | .record t => ident t
  | .refine t _ | .legacy t _ => ident t
  | .tuple ts tail =>
    identList ts && (match tail with | some t => ident t | none => true)
  | .union opts => identList opts
  | _ => false

def identList : List Term → Bool
  | [] => true
  | t :: ts => ident t && identList ts

end

/-! ## `adm` — the sets an `ident` term checks against

    §5's third auxiliary. `ident` says a term decides its own membership; `adm` says
    *against what*. Only two terms carry a real set — a `literal`'s values and a
    `discriminatedUnion`'s tags — and `refine`/`legacy` pass one through. Everywhere
    else `adm` is `true`: **no information**, which is what makes two such options
    never separable this way.

    In particular `adm` does *not* propagate through the containers, though `ident`
    does. `adm(array(c))` would have to contain the empty array whatever `c` is, so
    propagating it would claim a separation that is false — see
    `not_uAtCan_array_literals` below. -/

/-- The tags a `(dunion)`'s options answer to, pooled. Spelled out rather than a
    `flatMap` so the membership lemma is one induction. -/
def allTags (d : Name) : List Term → List String
  | [] => []
  | t :: ts => tagsOf d t ++ allTags d ts

theorem mem_allTags {d : Name} {ts : List Term} {t tag} (ht : t ∈ ts)
    (htag : tag ∈ tagsOf d t) : tag ∈ allTags d ts := by
  induction ts with
  | nil => exact absurd ht (by simp)
  | cons t₀ ts ih =>
    rcases List.mem_cons.mp ht with rfl | ht'
    · exact List.mem_append.mpr (Or.inl htag)
    · exact List.mem_append.mpr (Or.inr (ih ht'))

/-- `adm`, value side. `noncomputable` only because `literalN` compares `Double`s, whose
    `DecidableEq` is axiomatized (§1) — the recursion itself is structural. -/
noncomputable def adm : Term → Value → Bool
  | .literalS ls => fun v => match v with | .str s => s ∈ ls | _ => false
  | .literalN ls => fun v => match v with | .num d => d ∈ ls | _ => false
  | .dunion d opts => fun v =>
    match v with
    | .map kvs =>
      match kvs.lookup d with
      | some (.str tag) => (allTags d opts).contains tag
      | _ => false
    | _ => false
  | .refine t _ => adm t
  | .legacy t _ => adm t
  | _ => fun _ => true

/-- `adm`, attribute side. `legacy` is **not** transparent here: `extendRead` widens `p`
    past the subterm's admissible set, which is exactly the direction `adm` claims to
    bound. `literalN` is `true` — the read side goes through `Double.ofDec`, which is
    axiomatized, so no syntactic set bounds it; numeric literals fall to (U) per input
    on the attribute side. -/
def admA : Term → Attr → Bool
  | .literalS ls => fun a => match a with | .s s => s ∈ ls | _ => false
  | .dunion d opts => fun a =>
    match a with
    | .m kvs =>
      match kvs.lookup d with
      | some (.s tag) => (allTags d opts).contains tag
      | _ => false
    | _ => false
  | .refine t _ => admA t
  | _ => fun _ => true

/-! ### Tag admission, on both sides

`(dunion)`'s admission and `adm`/`admA` at a `dunion` are the same shape — a lookup of the
discriminator, and a membership test on the tag it carries. Stating that shape once is
what lets the `dunion` cases below say the one thing they are about: the tag the
admitting option matched is one of the union's tags. -/

/-- A tag option admits exactly the items whose discriminator carries one of its tags. -/
theorem byTag_admitA {d : Name} {tags : List String} {c : Codec} {a : Attr} :
    (OptionSem.byTag d tags c).admitA a = true ↔
      ∃ kvs tag, a = .m kvs ∧ kvs.lookup d = some (.s tag) ∧ tags.contains tag = true := by
  cases a <;> simp only [OptionSem.byTag] <;> try simp
  case m kvs =>
    cases hlk : kvs.lookup d with
    | none => simp [hlk]
    | some x => cases x <;> simp [hlk]

/-- …and the values whose discriminator carries one, on the way in. -/
theorem byTag_admitV {d : Name} {tags : List String} {c : Codec} {v : Value} :
    (OptionSem.byTag d tags c).admitV v = true ↔
      ∃ kvs tag, v = .map kvs ∧ kvs.lookup d = some (.str tag) ∧ tags.contains tag = true := by
  cases v <;> simp only [OptionSem.byTag] <;> try simp
  case map kvs =>
    cases hlk : kvs.lookup d with
    | none => simp [hlk]
    | some x => cases x <;> simp [hlk]

/-- `adm` at a `dunion` is the same test, against the union's whole tag set. -/
theorem adm_dunion {d : Name} {opts : List Term} {v : Value} :
    adm (.dunion d opts) v = true ↔
      ∃ kvs tag, v = .map kvs ∧ kvs.lookup d = some (.str tag) ∧
        (allTags d opts).contains tag = true := by
  cases v <;> simp only [adm] <;> try simp
  case map kvs =>
    cases hlk : kvs.lookup d with
    | none => simp [hlk]
    | some x => cases x <;> simp [hlk]

/-- …and `admA` likewise. -/
theorem admA_dunion {d : Name} {opts : List Term} {a : Attr} :
    admA (.dunion d opts) a = true ↔
      ∃ kvs tag, a = .m kvs ∧ kvs.lookup d = some (.s tag) ∧
        (allTags d opts).contains tag = true := by
  cases a <;> simp only [admA] <;> try simp
  case m kvs =>
    cases hlk : kvs.lookup d with
    | none => simp [hlk]
    | some x => cases x <;> simp [hlk]

/-! ## κ is sound for the denotation -/

/-- Every option of a `⋃` is a sublist of it. -/
theorem κList_mem : ∀ {ts : List Term} {ks}, κList ts = some ks →
    ∀ t ∈ ts, ∃ ks', κ t = some ks' ∧ ∀ k ∈ ks', k ∈ ks
  | [], _, _, t, ht => absurd ht (by simp)
  | t₀ :: ts, ks, h, t, ht => by
      replace h : (match κ t₀, κList ts with
        | some ks₀, some ks' => some (ks₀ ++ ks') | _, _ => none) = some ks := h
      cases hk₀ : κ t₀ with
      | none => rw [hk₀] at h; exact nomatch h
      | some ks₀ =>
        cases hks : κList ts with
        | none => rw [hk₀, hks] at h; exact nomatch h
        | some ks' =>
          rw [hk₀, hks] at h
          replace h : some (ks₀ ++ ks') = some ks := h
          cases h
          rcases List.mem_cons.mp ht with rfl | ht'
          · exact ⟨ks₀, hk₀, fun k hk => List.mem_append.mpr (Or.inl hk)⟩
          · obtain ⟨ks₁, hκ₁, hsub⟩ := κList_mem hks t ht'
            exact ⟨ks₁, hκ₁, fun k hk => List.mem_append.mpr (Or.inr (hsub k hk))⟩

/-- Fourteen of `κ`'s rules name a **single kind**, and are settled by the same two
    moves: `κ` reduces to that singleton, and the codec's own `e` refuses every value of
    another kind. Written out that is five lines fourteen times; here it is once. -/
local macro "single_kind" hk:ident hv:ident he:ident : tactic =>
  `(tactic| (cases $hk:ident
             cases $hv:ident <;> first
               | exact List.mem_cons_self _ _
               | exact nomatch $he:ident))

/-- Encoding lands in `κ`: a term's writable values have the kinds its `κ` names.
    (Where `κ` answers `⊤` there is nothing to say — the table's point.)

    The rules that are not `single_kind` are exactly the ones where `κ` is *computed*
    from a subterm's: the two transparent wrappers, `nullable`'s `∪`, `union`'s `⋃`,
    and `dunion`, whose kind comes from the option that admitted rather than from its
    own syntax. Four more answer `⊤`, where the hypothesis is unsatisfiable. -/
theorem κ_sound : ∀ (fuel : Nat) (t : Term) {ks : List Kind} {v a},
    κ t = some ks → (denote fuel t).e v = some a → Value.kind v ∈ ks
  | 0, _, _, _, _, _, he => nomatch he
  | fuel+1, t, ks, v, a, hκ, he => by
    cases t with
    | string => single_kind hκ v he
    | decimal => single_kind hκ v he
    | literalS ls => single_kind hκ v he
    | number => single_kind hκ v he
    | numeric q => single_kind hκ v he
    | literalN ls => single_kind hκ v he
    | boolean => single_kind hκ v he
    | null => single_kind hκ v he
    | binary => single_kind hκ v he
    | set t' => single_kind hκ v he
    | array t' => single_kind hκ v he
    | tuple ts tail => single_kind hκ v he
    | record t' => single_kind hκ v he
    | object fields rest => single_kind hκ v he
    | dunion d opts =>
      -- a stamped option writes a `map`, so the kind is `map` however it was reached
      cases hκ
      obtain ⟨o, ho, hadm, -⟩ := altCodec_e_admits he
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ho
      cases v <;> first
        | exact List.mem_cons_self _ _
        | exact nomatch hadm
    | refine t' q => exact κ_sound fuel t' hκ (restrict_e.mp he).2
    | legacy t' r => exact κ_sound fuel t' hκ he
    | nullable t' =>
      -- `nullable`'s `∪`: `null` is the wrapper's own kind, everything else the
      -- subterm's, and `orNull` sends every non-`null` value straight to it
      replace hκ : (κ t').map (Kind.null :: ·) = some ks := hκ
      obtain ⟨ks', hκt, rfl⟩ := Option.map_eq_some'.mp hκ
      cases v
      case null => exact List.mem_cons_self _ _
      all_goals exact List.mem_cons_of_mem _ (κ_sound fuel t' hκt he)
    | union opts =>
      -- `union`'s `⋃`: the kind is the admitting option's, and `κList` contains it
      obtain ⟨o, ho, -, hoe⟩ := altCodec_e_admits he
      obtain ⟨tx, htx, rfl⟩ := List.mem_map.mp ho
      rw [optionSemOf_c] at hoe
      obtain ⟨ksx, hκx, hsub⟩ := κList_mem hκ tx htx
      exact hsub _ (κ_sound fuel tx hκx hoe)
    -- `κ` is `⊤` here: nothing is claimed, and the hypothesis is unsatisfiable
    | held t' f g => exact nomatch hκ
    | lazy γ => exact nomatch hκ
    | custom ce cp => exact nomatch hκ
    | opaq lossy => exact nomatch hκ
theorem adm_sound : ∀ (fuel : Nat) (t : Term) {v a},
    (denote fuel t).e v = some a → adm t v = true
  | 0, _, _, _, he => nomatch he
  | fuel+1, t, v, a, he => by
    cases t
    case literalS ls =>
      cases v <;> simp_all [denote, literalSCodec, adm]
    case literalN ls =>
      cases v <;> simp_all [denote, literalNCodec, adm]
    case dunion d opts =>
      -- the admitting option's tag check is exactly `adm`'s, at one option
      obtain ⟨o, ho, hadm, -⟩ := altCodec_e_admits he
      simp only [List.mem_map] at ho
      obtain ⟨-, ⟨tx, htx, rfl⟩, rfl⟩ := ho
      obtain ⟨kvs, tag, rfl, hlk, htag⟩ := byTag_admitV.mp hadm
      exact adm_dunion.mpr ⟨kvs, tag, rfl, hlk,
        contains_of_mem (mem_allTags htx (mem_of_contains htag))⟩
    case refine t' q => exact adm_sound fuel t' (restrict_e.mp he).2
    case legacy t' r => exact adm_sound fuel t' (extendRead_e.mp he)
    all_goals rfl

/-- Reading lands in `admA`. -/
theorem admA_sound : ∀ (fuel : Nat) (t : Term) {a v},
    (denote fuel t).p a = some v → admA t a = true
  | 0, _, _, _, hp => nomatch hp
  | fuel+1, t, a, v, hp => by
    cases t
    case literalS ls =>
      cases a <;> simp_all [denote, literalSCodec, admA]
    case dunion d opts =>
      obtain ⟨o, ho, hadm, -⟩ := altCodec_p_admits hp
      simp only [List.mem_map] at ho
      obtain ⟨-, ⟨tx, htx, rfl⟩, rfl⟩ := ho
      obtain ⟨kvs, tag, rfl, hlk, htag⟩ := byTag_admitA.mp hadm
      exact admA_dunion.mpr ⟨kvs, tag, rfl, hlk,
        contains_of_mem (mem_allTags htx (mem_of_contains htag))⟩
    case refine t' q => exact admA_sound fuel t' (restrict_p.mp hp).1
    all_goals rfl

/-! ## Admission is guarded -/

/-- Any option's value admission is `κ`-guarded: an admitted value has a kind the
    option's (non-`⊤`) `κ` names. -/
theorem admitV_kind (fuel : Nat) (t : Term) {ks : List Kind} {v}
    (hκ : κ t = some ks)
    (h : (optionSemOf (denote fuel t) (specOf t)).admitV v = true) :
    Value.kind v ∈ ks := by
  cases hs : specOf t with
  | none =>
    rw [hs] at h
    replace h : ((denote fuel t).e v).isSome = true := h
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h
    exact κ_sound fuel t hκ ha
  | some spec =>
    rw [hs] at h
    cases t
    case object fields rest =>
      replace hκ : some [Kind.map] = some ks := hκ
      cases hκ
      cases v <;> first
        | exact List.mem_cons_self _ _
        | exact nomatch h
    all_goals exact nomatch hs

/-- Any option's attribute admission is member-guarded: with a lawful pair and a
    named member, an admitted attribute carries that member — §5's read-side (W),
    doing (D)'s job through the member index. -/
theorem admitA_member (fuel : Nat) (t : Term) {μ a}
    (hμ : μSyn t = some μ) (hlaw : Lawful (denote fuel t))
    (h : (optionSemOf (denote fuel t) (specOf t)).admitA a = true) :
    a.member = μ := by
  cases hs : specOf t with
  | none =>
    rw [hs] at h
    replace h : ((denote fuel t).p a).isSome = true := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
    refine hlaw.reads ?_ hv
    rw [denote_μ]
    exact hμ
  | some spec =>
    rw [hs] at h
    cases t
    case object fields rest =>
      replace hμ : some Member.M = some μ := hμ
      cases hμ
      cases a <;> first
        | rfl
        | exact nomatch h
    all_goals exact nomatch hs

/-! ## Options admit their own canonical pairs -/

/-- Traversal success is entrywise success. -/
theorem traverse_input_isSome {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys}, traverse f xs = some ys → ∀ x ∈ xs, (f x).isSome
  | [], _, _, x, hx => absurd hx (by simp)
  | x₀ :: xs, ys, h, x, hx => by
      simp only [traverse] at h
      cases hfx : f x₀ with
      | none => rw [hfx] at h; exact nomatch h
      | some y₀ =>
        rw [hfx] at h
        cases hxs : traverse f xs with
        | none => rw [hxs] at h; exact nomatch h
        | some ys' =>
          rcases List.mem_cons.mp hx with rfl | hx'
          · rw [hfx]; rfl
          · exact traverse_input_isSome hxs x hx'

/-- Name admission from names alone: everything present is declared, everything
    required is present. -/
theorem keysOk_of_names {α : Type} {fields : List (Name × Field)} {l : List (Name × α)}
    (hsub : ∀ k ∈ l.map (·.1), k ∈ fields.map (·.1))
    (hreq : ∀ kf ∈ fields,
      (match kf.2 with | Field.optional _ => false | _ => true) = true →
      kf.1 ∈ l.map (·.1)) :
    keysOk (fields.map fun kf =>
      (kf.1, match kf.2 with | Field.optional _ => false | _ => true)) l = true := by
  simp only [keysOk, Bool.and_eq_true]
  constructor
  · refine List.all_eq_true.mpr fun kv hkv => ?_
    have hk := hsub kv.1 (List.mem_map.mpr ⟨kv, hkv, rfl⟩)
    obtain ⟨kf, hkf, hfst⟩ := List.mem_map.mp hk
    refine List.any_eq_true.mpr
      ⟨(kf.1, match kf.2 with | Field.optional _ => false | _ => true),
        List.mem_map.mpr ⟨kf, hkf, rfl⟩, ?_⟩
    show (kf.1 == kv.1) = true
    rw [hfst]
    exact beq_self_eq_true kv.1
  · refine List.all_eq_true.mpr fun kb hkb => ?_
    obtain ⟨kf, hkf, rfl⟩ := List.mem_map.mp hkb
    show (!(match kf.2 with | Field.optional _ => false | _ => true) ||
      (l.lookup kf.1).isSome) = true
    cases hb : (match kf.2 with | Field.optional _ => false | _ => true) with
    | false => rfl
    | true => exact lookup_isSome_of_mem_fst (hreq kf hkf hb)

/-- Object-encode under a closed rest policy stamps name admission on both sides:
    every written name is declared and every non-`opt` name is written — for the
    value and for the attribute it becomes. -/
theorem keysOk_of_encode {fields : List (Name × Field)} {den : Term → Codec}
    {kvs : List (Name × Value)} {ds : List (Name × Attr)}
    (hval : valPresentB (fields.map fun kf => (kf.1, fieldSemOf den kf.2))
      (kvs.map (·.1)) = true)
    (htr : traverse (encEntry
        (fun k => (fields.map fun kf => (kf.1, fieldSemOf den kf.2)).lookup k) none)
      kvs = some ds) :
    keysOk (fields.map fun kf =>
        (kf.1, match kf.2 with | Field.optional _ => false | _ => true)) kvs = true ∧
    keysOk (fields.map fun kf =>
        (kf.1, match kf.2 with | Field.optional _ => false | _ => true)) ds = true := by
  have hnames : ds.map (·.1) = kvs.map (·.1) :=
    traverse_fst (encEntry_fst (rc? := none)) htr
  have hsub : ∀ k ∈ kvs.map (·.1), k ∈ fields.map (·.1) := by
    intro k hk
    obtain ⟨kv, hkv, rfl⟩ := List.mem_map.mp hk
    have hsome := traverse_input_isSome htr kv hkv
    simp only [encEntry] at hsome
    cases hlk : (fields.map fun kf => (kf.1, fieldSemOf den kf.2)).lookup kv.1 with
    | none => rw [hlk] at hsome; exact nomatch hsome
    | some fs =>
      have hm := mem_of_lookup hlk
      obtain ⟨kf, hkf, heq⟩ := List.mem_map.mp hm
      exact List.mem_map.mpr ⟨kf, hkf, congrArg Prod.fst heq⟩
  have hreq : ∀ kf ∈ fields,
      (match kf.2 with | Field.optional _ => false | _ => true) = true →
      kf.1 ∈ kvs.map (·.1) := by
    intro kf hkf hb
    have hmem : (kf.1, fieldSemOf den kf.2) ∈
        fields.map fun kf => (kf.1, fieldSemOf den kf.2) :=
      List.mem_map.mpr ⟨kf, hkf, rfl⟩
    have hno : ∀ c, fieldSemOf den kf.2 ≠ FieldSem.opt c := by
      intro c hc
      cases hf2 : kf.2 with
      | optional t' => rw [hf2] at hb; exact nomatch hb
      | req t' => rw [hf2] at hc; exact nomatch hc
      | fallback t' v' => rw [hf2] at hc; exact nomatch hc
    have := valPresentB_spec hval hmem hno
    exact mem_of_contains this
  refine ⟨keysOk_of_names hsub hreq, keysOk_of_names ?_ ?_⟩
  · rw [hnames]; exact hsub
  · rw [hnames]; exact hreq

/-- A closed option admits its own canonical pairs, on both sides. An *open* object —
    a rest codec — is excluded, as §5 demands: an undeclared name disqualifies the
    option even where its rest codec would hold it. -/
theorem optionSem_self_admit (fuel : Nat) (t : Term)
    (hcl : ∀ fields tr, t ≠ .object fields (.codec tr))
    (hlaw : Lawful (denote fuel t)) {v a}
    (he : (denote fuel t).e v = some a) :
    (optionSemOf (denote fuel t) (specOf t)).admitV v = true ∧
    (optionSemOf (denote fuel t) (specOf t)).admitA a = true := by
  cases hs : specOf t with
  | none =>
    constructor
    · show ((denote fuel t).e v).isSome = true
      rw [he]; rfl
    · show ((denote fuel t).p a).isSome = true
      rw [hlaw.retract he]; rfl
  | some spec =>
    cases t
    case object fields rest =>
      replace hs : some (fields.map fun kf =>
        (kf.1, match kf.2 with | Field.optional _ => false | _ => true)) =
        some spec := hs
      cases hs
      cases fuel with
      | zero => exact nomatch he
      | succ f =>
        have hrc : rcOf (restSemOf (denote f) rest) = none := by
          cases rest with
          | drop => rfl
          | refuse => rfl
          | codec tr => exact absurd rfl (hcl fields tr)
        replace he : (objectCodecCore
            (fields.map fun kf => (kf.1, fieldSemOf (denote f) kf.2))
            (rcOf (restSemOf (denote f) rest))
            (keepB (restSemOf (denote f) rest)
              (fields.map fun kf => (kf.1, fieldSemOf (denote f) kf.2)))).e v =
          some a := he
        obtain ⟨kvs, ds, rfl, rfl, hval, htr⟩ := objectCodecCore_e_inv he
        rw [hrc] at htr
        replace htr : traverse (encEntry
            (fun k => (fields.map fun kf =>
              (kf.1, fieldSemOf (denote f) kf.2)).lookup k) none)
          kvs = some ds := htr
        exact keysOk_of_encode hval htr
    all_goals exact nomatch hs

/-- Any option's value admission is `adm`-guarded. -/
theorem admitV_adm (fuel : Nat) (t : Term) {v}
    (h : (optionSemOf (denote fuel t) (specOf t)).admitV v = true) : adm t v = true := by
  cases hs : specOf t with
  | none =>
    rw [hs] at h
    replace h : ((denote fuel t).e v).isSome = true := h
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h
    exact adm_sound fuel t ha
  | some spec =>
    cases t
    case object fields rest => rfl
    all_goals exact nomatch hs

/-- Any option's attribute admission is `admA`-guarded. -/
theorem admitA_admA (fuel : Nat) (t : Term) {a}
    (h : (optionSemOf (denote fuel t) (specOf t)).admitA a = true) : admA t a = true := by
  cases hs : specOf t with
  | none =>
    rw [hs] at h
    replace h : ((denote fuel t).p a).isSome = true := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
    exact admA_sound fuel t hv
  | some spec =>
    cases t
    case object fields rest => rfl
    all_goals exact nomatch hs

/-! ## The discharger -/

/-- `Pairwise`, upgraded with membership. -/
theorem pairwise_imp_mem {α : Type} {R S : α → α → Prop} :
    ∀ {l : List α}, (∀ x ∈ l, ∀ y ∈ l, R x y → S x y) → List.Pairwise R l →
      List.Pairwise S l
  | [], _, _ => .nil
  | a :: l, h, hp => by
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hp
      refine List.Pairwise.cons (fun y hy =>
          h a (List.mem_cons_self a l) y (List.mem_cons_of_mem a hy) (hhead y hy)) ?_
      exact pairwise_imp_mem
        (fun x hx y hy => h x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy))
        htail

/-- One admitting element under pairwise mutual exclusion filters to a singleton. -/
theorem filter_map_singleton {α β : Type} (f : α → β) (P : β → Bool) :
    ∀ (l : List α),
      List.Pairwise (fun x y => (P (f x) = true → P (f y) = false) ∧
        (P (f y) = true → P (f x) = false)) l →
      ∀ x ∈ l, P (f x) = true → (l.map f).filter P = [f x]
  | [], _, x, hx, _ => nomatch hx
  | y :: l, hp, x, hx, hPx => by
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hp
      rcases List.mem_cons.mp hx with rfl | hx'
      · have hnil : (l.map f).filter P = [] := by
          refine filter_nil_of fun b hb => ?_
          obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hb
          exact (hhead y' hy').1 hPx
        simp only [List.map, List.filter, hPx, hnil]
      · have hny : P (f y) = false := (hhead x hx').2 hPx
        simp only [List.map, List.filter, hny]
        exact filter_map_singleton f P l htail x hx' hPx

/-- §5 (K), repaired and decidable: two options are separated on the writable side by
    disjoint kinds, **or** by disjoint admissible sets. The second disjunct is the
    honest form of the doc's `ident` exemption — see the counterexamples below for why
    `ident` on one side, or even on both, is not it. -/
def SepV (x y : Term) : Prop :=
  (∃ kx ky, κ x = some kx ∧ κ y = some ky ∧ ∀ k ∈ kx, k ∉ ky) ∨
  (∀ v, adm x v = true → adm y v = false)

/-! ### Why `SepV` may drop §5's two `ident` conjuncts

    §5 states (K)'s second disjunct as `ident(cᵢ) ∧ ident(cⱼ) ∧ adm(cᵢ) ∩ adm(cⱼ) = ∅`;
    `SepV` keeps only the `adm` clause. Dropping a conjunct from a premise *weakens* the
    discharger, so `uAtCan_of_separated` is the stronger theorem either way — but it
    leaves `ident` asserting nothing, which is how a faithful transcription becomes an
    unlocatable claim. Here is the argument that the two conjuncts are redundant, which
    until now lived only in prose.

    It turns on `adm`'s default: every term that is not a `literal`, a
    `discriminatedUnion`, or a transparent wrapper over one answers `true` everywhere,
    and those are exactly the terms `ident` holds of at the leaves. So a term whose `adm`
    ever *refuses* is `ident` — and two options with disjoint `adm` must each refuse
    somewhere, provided each also admits somewhere. -/

/-- **`adm` is informative only where `ident` holds.** If `adm` refuses a single value,
    the term is `ident`. This is the pinning `ident` otherwise lacks: `κ`, `adm` and
    `admA` each have a soundness lemma tying them to the denotation, and `ident` has no
    denotational content to tie — what it has is this relation to `adm`, which is what
    §5 actually uses it for. -/
theorem ident_of_adm : ∀ {t : Term} {v : Value}, adm t v = false → ident t = true
  | .literalS _, _, _ => rfl
  | .literalN _, _, _ => rfl
  | .dunion _ _, _, _ => rfl
  | .refine t _, v, h => ident_of_adm (t := t) (v := v) h
  | .legacy t _, v, h => ident_of_adm (t := t) (v := v) h
  | .string, _, h | .number, _, h | .decimal, _, h | .boolean, _, h | .binary, _, h
  | .null, _, h | .numeric _, _, h | .set _, _, h | .array _, _, h | .tuple _ _, _, h
  | .record _, _, h | .held _ _ _, _, h | .nullable _, _, h | .lazy _, _, h
  | .custom _ _, _, h | .opaq _, _, h | .object _ _, _, h | .union _, _, h => nomatch h

/-- **§5's (K), recovered from `SepV`'s second disjunct.** Disjoint `adm` implies both
    `ident` conjuncts, so `SepV` is not weaker than the doc's condition where the doc's
    condition means anything — the two side conditions ask that each option admit *some*
    value, which is what stops an option with an empty admissible set from separating
    itself from everything.

    Both side conditions are needed, and the witness is not exotic: `dunion(d)` with no
    options is derivable (`Typed.dunion` quantifies its premises over the option list)
    and its `adm` is `false` everywhere, so it is trivially `adm`-disjoint from `string`,
    which is not `ident`. -/
theorem admDisj_ident {x y : Term} (hdisj : ∀ v, adm x v = true → adm y v = false)
    (hx : ∃ v, adm x v = true) (hy : ∃ v, adm y v = true) :
    ident x = true ∧ ident y = true := by
  obtain ⟨vx, hvx⟩ := hx
  obtain ⟨vy, hvy⟩ := hy
  refine ⟨ident_of_adm (v := vy) ?_, ident_of_adm (v := vx) (hdisj vx hvx)⟩
  by_contra hc
  exact absurd (hdisj vy (by simpa using hc)) (by simp [hvy])

/-! ### The gap that remains, exhibited

    `admDisj_ident`'s two side conditions are not bookkeeping. A term whose admissible
    set is *empty* is `adm`-disjoint from everything, so it separates itself from options
    §5's (K) would refuse — and one such term is derivable. -/

/-- A `discriminatedUnion` with no options refuses every value: `allTags` is empty. -/
theorem adm_dunion_nil (d : Name) (v : Value) : adm (.dunion d []) v = false := by
  cases v <;> simp only [adm, allTags]
  split <;> rfl

/-- And it is derivable — `(dunion)`'s premises are quantified over the option list. -/
theorem typed_dunion_nil (d : Name) : Typed (.dunion d []) (HUnion []) (some .M) :=
  .dunion .nil (by simp) (by simp)

/-- **`SepV` is strictly weaker than §5's (K)**, at a derivable pair. `string` is not
    `ident`, so (K) refuses this pair on both of its disjuncts; `SepV` accepts it,
    because `dunion(d)` admits nothing to collide with. Weaker is the safe direction —
    `uAtCan_of_separated` takes `SepV` as a premise, so it discharges strictly more —
    but it means `SepV` and (K) are not the same condition, and the difference is here
    rather than in prose. -/
theorem sepV_string_dunion_nil (d : Name) : SepV .string (.dunion d []) :=
  Or.inr fun v _ => adm_dunion_nil d v

theorem not_ident_string : ident .string = false := rfl

/-- §5 (D)'s stand-in, likewise widened: two options are separated on the readable side
    by distinct named members, **or** by disjoint admissible sets. The `adm` disjunct is
    what carries `union(literal("A"), literal("B"))`, whose options share `⇝ S`. -/
def SepA (x y : Term) : Prop :=
  (∃ μx μy, μSyn x = some μx ∧ μSyn y = some μy ∧ μx ≠ μy) ∨
  (∀ a, admA x a = true → admA y a = false)

/-- §5's dischargers, combined: pairwise separation on each side of the pair, and
    closed options admitting their own canonicals — so admission is unique at every
    canonical input, which is exactly the theorem's residue `UAtCan`. Every premise is
    decidable from the syntax except lawfulness, which soundness supplies. -/
theorem uAtCan_of_separated (fuel : Nat) {opts : List Term}
    (hlaw : ∀ t ∈ opts, Lawful (denote fuel t))
    (hcl : ∀ t ∈ opts, ∀ fields tr, t ≠ .object fields (.codec tr))
    (hV : List.Pairwise SepV opts)
    (hA : List.Pairwise SepA opts) :
    UAtCan fuel opts := by
  intro o ho t a he
  simp only [semsOf, List.mem_map] at ho
  obtain ⟨tx, htx, rfl⟩ := ho
  rw [optionSemOf_c] at he
  obtain ⟨hVx, hAx⟩ := optionSem_self_admit fuel tx (hcl tx htx) (hlaw tx htx) he
  constructor
  · show ((opts.map fun t' => optionSemOf (denote fuel t') (specOf t')).filter
      (·.admitA a)) = [optionSemOf (denote fuel tx) (specOf tx)]
    refine filter_map_singleton _ _ opts ?_ tx htx hAx
    refine pairwise_imp_mem ?_ hA
    intro x hx y hy hxy
    -- one exclusion argument, used in both directions
    have key : ∀ u v, SepA u v → u ∈ opts → v ∈ opts →
        (optionSemOf (denote fuel u) (specOf u)).admitA a = true →
        (optionSemOf (denote fuel v) (specOf v)).admitA a = false := by
      intro u v hs hu hv hau
      cases hav : (optionSemOf (denote fuel v) (specOf v)).admitA a with
      | false => rfl
      | true =>
        rcases hs with ⟨μu, μv, hμu, hμv, hne⟩ | hdisj
        · exact absurd ((admitA_member fuel u hμu (hlaw u hu) hau).symm.trans
            (admitA_member fuel v hμv (hlaw v hv) hav)) hne
        · have hav' := admitA_admA fuel v hav
          rw [hdisj a (admitA_admA fuel u hau)] at hav'
          exact nomatch hav'
    refine ⟨key x y hxy hx hy, fun hay => ?_⟩
    cases hax : (optionSemOf (denote fuel x) (specOf x)).admitA a with
    | false => rfl
    | true => rw [key x y hxy hx hy hax] at hay; exact nomatch hay
  · show ((opts.map fun t' => optionSemOf (denote fuel t') (specOf t')).filter
      (·.admitV t)) = [optionSemOf (denote fuel tx) (specOf tx)]
    refine filter_map_singleton _ _ opts ?_ tx htx hVx
    refine pairwise_imp_mem ?_ hV
    intro x hx y hy hxy
    have key : ∀ u v, SepV u v →
        (optionSemOf (denote fuel u) (specOf u)).admitV t = true →
        (optionSemOf (denote fuel v) (specOf v)).admitV t = false := by
      intro u v hs hvu
      cases hvv : (optionSemOf (denote fuel v) (specOf v)).admitV t with
      | false => rfl
      | true =>
        rcases hs with ⟨ku, kv, hku, hkv, hne⟩ | hdisj
        · exact absurd (admitV_kind fuel v hkv hvv)
            (hne _ (admitV_kind fuel u hku hvu))
        · have hvv' := admitV_adm fuel v hvv
          rw [hdisj t (admitV_adm fuel u hvu)] at hvv'
          exact nomatch hvv'
    refine ⟨key x y hxy, fun hvy => ?_⟩
    cases hvx : (optionSemOf (denote fuel x) (specOf x)).admitV t with
    | false => rfl
    | true => rw [key x y hxy hvx] at hvy; exact nomatch hvy

/-- The kind/member half on its own — the original disjointness discharger, now a
    corollary of `uAtCan_of_separated`. -/
theorem uAtCan_of_disjoint (fuel : Nat) {opts : List Term}
    (hlaw : ∀ t ∈ opts, Lawful (denote fuel t))
    (hcl : ∀ t ∈ opts, ∀ fields tr, t ≠ .object fields (.codec tr))
    (hκ : ∀ t ∈ opts, (κ t).isSome)
    (hμ : ∀ t ∈ opts, (μSyn t).isSome)
    (hκd : List.Pairwise (fun x y => ∀ kx ky, κ x = some kx → κ y = some ky →
      ∀ k ∈ kx, k ∉ ky) opts)
    (hμd : List.Pairwise (fun x y => μSyn x ≠ μSyn y) opts) :
    UAtCan fuel opts := by
  refine uAtCan_of_separated fuel hlaw hcl (pairwise_imp_mem ?_ hκd)
    (pairwise_imp_mem ?_ hμd)
  · intro x hx y hy hxy
    obtain ⟨kx, hkx⟩ := Option.isSome_iff_exists.mp (hκ x hx)
    obtain ⟨ky, hky⟩ := Option.isSome_iff_exists.mp (hκ y hy)
    exact Or.inl ⟨kx, ky, hkx, hky, hxy kx ky hkx hky⟩
  · intro x hx y hy hxy
    obtain ⟨μx, hμx⟩ := Option.isSome_iff_exists.mp (hμ x hx)
    obtain ⟨μy, hμy⟩ := Option.isSome_iff_exists.mp (hμ y hy)
    exact Or.inl ⟨μx, μy, hμx, hμy, fun h => hxy (by rw [hμx, hμy, h])⟩

/-! ## The premises are jointly inhabited

    `uAtCan_of_disjoint` takes six premises, and a theorem whose premises cannot all
    hold discharges nothing. `union(string, boolean)` satisfies every one of them —
    disjoint kinds, distinct members, closed, lawful — so the discharger really does
    decide unions. -/

/-- A premise of the form `∀ t ∈ [x, y], P t`, checked at the two options. -/
theorem forall_mem_pair {α : Type} {P : α → Prop} {x y : α} (hx : P x) (hy : P y) :
    ∀ z ∈ [x, y], P z := by
  intro z hz
  rcases List.mem_cons.mp hz with rfl | hz
  · exact hx
  · rcases List.mem_cons.mp hz with rfl | hz
    · exact hy
    · exact absurd hz (by simp)

/-- A pairwise premise over two options, checked at the single unordered pair. -/
theorem pairwise_pair {α : Type} {R : α → α → Prop} {x y : α} (h : R x y) :
    List.Pairwise R [x, y] := by
  refine List.Pairwise.cons ?_ (List.Pairwise.cons (by simp) List.Pairwise.nil)
  intro z hz
  rcases List.mem_cons.mp hz with rfl | hz
  · exact h
  · exact absurd hz (by simp)

/-- Satisfiability witness for `uAtCan_of_disjoint` at the new ground term:
    `union(string, null)` — the explicit spelling of a nullable string, and the one
    §3's `(null)` rule exists for. Kinds settle it at the declaration: `κ(null)` is
    `{null}`, disjoint from every other ground kind, and `NULL` is a member no other
    ground term names. -/
theorem uAtCan_string_null (fuel : Nat) :
    UAtCan fuel [Term.string, Term.null] := by
  refine uAtCan_of_disjoint fuel
    (forall_mem_pair (lawful_string fuel) (lawful_null fuel))
    (forall_mem_pair (fun _ _ h => nomatch h) (fun _ _ h => nomatch h))
    (forall_mem_pair rfl rfl) (forall_mem_pair rfl rfl)
    (pairwise_pair ?_) (pairwise_pair ?_)
  · intro kx ky hx hy k hk
    replace hx : some [Kind.string] = some kx := hx
    replace hy : some [Kind.null] = some ky := hy
    cases hx; cases hy
    simp only [List.mem_singleton] at hk
    subst hk
    simp
  · intro h
    replace h : some Member.S = some Member.NULL := h
    exact nomatch h

/-- Satisfiability witness for `uAtCan_of_disjoint`: `union(string, boolean)` is
    discharged at the declaration, at every fuel. -/
theorem uAtCan_string_boolean (fuel : Nat) :
    UAtCan fuel [Term.string, Term.boolean] := by
  refine uAtCan_of_disjoint fuel
    (forall_mem_pair (lawful_string fuel) (lawful_boolean fuel))
    (forall_mem_pair (fun _ _ h => nomatch h) (fun _ _ h => nomatch h))
    (forall_mem_pair rfl rfl) (forall_mem_pair rfl rfl)
    (pairwise_pair ?_) (pairwise_pair ?_)
  · intro kx ky hx hy k hk
    replace hx : some [Kind.string] = some kx := hx
    replace hy : some [Kind.boolean] = some ky := hy
    cases hx; cases hy
    simp only [List.mem_singleton] at hk
    subst hk
    simp
  · intro h
    replace h : some Member.S = some Member.BOOL := h
    exact nomatch h

/-- §5's worked example, discharged — and out of reach of `uAtCan_of_disjoint`. The two
    options share `κ = {string}` *and* share `⇝ S`, so neither kinds nor members
    separate them; the `adm` disjunct on both sides is what carries it. This is the
    pair §5 claims for `ident`, and `adm` is what makes the claim good. -/
theorem uAtCan_literal_literal (fuel : Nat) :
    UAtCan fuel [Term.literalS ["A"], Term.literalS ["B"]] := by
  refine uAtCan_of_separated fuel
    (forall_mem_pair (lawful_literalS _ fuel) (lawful_literalS _ fuel))
    (forall_mem_pair (fun _ _ h => nomatch h) (fun _ _ h => nomatch h))
    (pairwise_pair (Or.inr ?_)) (pairwise_pair (Or.inr ?_))
  · intro v hv
    cases v
    case str s =>
      replace hv : decide (s ∈ ["A"]) = true := hv
      show decide (s ∈ ["B"]) = false
      have : s = "A" := by simpa using of_decide_eq_true hv
      subst this
      simp
    all_goals exact nomatch hv
  · intro a ha
    cases a
    case s s =>
      replace ha : decide (s ∈ ["A"]) = true := ha
      show decide (s ∈ ["B"]) = false
      have : s = "A" := by simpa using of_decide_eq_true ha
      subst this
      simp
    all_goals exact nomatch ha

/-! ## Why `ident` is *not* an exemption from (K), as §5 states it

    §5 states **(K)** as `∀ i ≠ j. κ(cᵢ) ∩ κ(cⱼ) = ∅ ∨ ident(cᵢ) ∨ ident(cⱼ)`, and
    calls it a discharger — decidable and *sufficient* for (U). It is not sufficient,
    and the two counterexamples below are the reason the `ident` half of (K) is absent
    from `uAtCan_of_disjoint`. This is a correction of the doc, not a gap in the
    mechanization.

    The prose is right about what `ident` buys: attempted admission on a `literal` is
    evidence, where attempted admission on `string` is not. What the rule as written
    drops is that evidence only *resolves* a pair when it is available on **both**
    sides and the two admissible sets are **disjoint**. §5's own worked example,
    `union(literal("A"), literal("B"))`, has both; the rule it is offered in support of
    demands neither. -/

/-- A helper: two options of a two-element union that both admit one value refute (U).
    `hne` separates the options at some other value, so the singleton filter fails. -/
theorem not_uAtCan_pair {fuel : Nat} {t₁ t₂ : Term} {v w : Value} {a : Attr}
    (he : (denote fuel t₁).e v = some a)
    (h₂ : (optionSemOf (denote fuel t₂) (specOf t₂)).admitV v = true)
    (hne : (optionSemOf (denote fuel t₁) (specOf t₁)).admitV w ≠
      (optionSemOf (denote fuel t₂) (specOf t₂)).admitV w) :
    ¬ UAtCan fuel [t₁, t₂] := by
  intro h
  have ho : optionSemOf (denote fuel t₁) (specOf t₁) ∈ semsOf fuel [t₁, t₂] :=
    List.mem_cons_self _ _
  have hfilt := (h _ ho v a (by rw [optionSemOf_c]; exact he)).2
  -- the second option survives the filter too, so the filter cannot be `[o₁]`
  have hmem : optionSemOf (denote fuel t₂) (specOf t₂) ∈
      [optionSemOf (denote fuel t₁) (specOf t₁)] := by
    rw [← hfilt]
    exact List.mem_filter.mpr
      ⟨List.mem_cons_of_mem _ (List.mem_cons_self _ _), h₂⟩
  rcases List.mem_cons.mp hmem with heq | hnil
  · exact hne (congrArg (fun o => OptionSem.admitV o w) heq.symm)
  · exact absurd hnil (by simp)

/-- **One-sided `ident` does not discharge (K).** `union(literal("A"), string)` passes
    §5's (K) — `ident(literal("A"))` holds — and violates (U) at the value `"A"`, which
    both options admit. `literal`'s attempt *is* evidence; `string`'s is not, and one
    honest answer does not resolve a pair. -/
theorem not_uAtCan_literal_string :
    ¬ UAtCan 1 [Term.literalS ["A"], Term.string] := by
  have hA : (denote 1 (Term.literalS ["A"])).e (Value.str "A") = some (Attr.s "A") := by
    show (if "A" ∈ ["A"] then some (Attr.s "A") else none) = some (Attr.s "A")
    rw [if_pos (List.mem_cons_self _ _)]
  have hB : (denote 1 (Term.literalS ["A"])).e (Value.str "B") = none := by
    show (if "B" ∈ ["A"] then some (Attr.s "B") else none) = none
    rw [if_neg (by simp)]
  refine not_uAtCan_pair (v := .str "A") (a := Attr.s "A") (w := .str "B") hA rfl ?_
  · show ((denote 1 (Term.literalS ["A"])).e (Value.str "B")).isSome ≠
      ((denote 1 Term.string).e (Value.str "B")).isSome
    rw [hB]
    exact fun h => nomatch h

/-- **Two-sided `ident` does not discharge (K) either.** `ident` propagates through
    `array` (§5's table), so `union(array(literal("A")), array(literal("B")))` has it on
    both sides — and both options admit the empty array, which neither literal ever
    sees. Propagating `ident` through a container does not propagate disjointness of
    the admissible sets: every container admits its empty case. -/
theorem not_uAtCan_array_literals :
    ¬ UAtCan 2 [Term.array (.literalS ["A"]), Term.array (.literalS ["B"])] := by
  refine not_uAtCan_pair (v := .arr []) (a := Attr.l []) (w := .arr [.str "A"])
    rfl rfl ?_
  -- separated one fuel down, where the element codecs are live: `["A"]` is written by
  -- the first option and refused by the second
  show ((match (if "A" ∈ ["A"] then some (Attr.s "A") else none),
      some ([] : List Attr) with
      | some y, some ys => some (y :: ys) | _, _ => none).map Attr.l).isSome ≠
    ((match (if "A" ∈ ["B"] then some (Attr.s "A") else none),
      some ([] : List Attr) with
      | some y, some ys => some (y :: ys) | _, _ => none).map Attr.l).isSome
  rw [if_pos (List.mem_cons_self _ _), if_neg (by simp)]
  exact fun h => nomatch h

/-- Both counterexamples are `ident` on the side(s) §5's (K) appeals to — so they are
    admitted by the rule as stated, not excluded by a side condition it carries. -/
example : ident (.literalS ["A"]) = true := rfl
example : ident (.array (.literalS ["A"])) = true := rfl
example : ident (.array (.literalS ["B"])) = true := rfl

/-! ## Why (D) does not discharge the readable side either

    §5 lists **(D)** — incomparable held sets — as a discharger of (U)'s readable side,
    and says in prose that stating it as genuine *disjointness* "would be sound and
    would reject unions that work". The first half of that is false: held sets are sets
    of **values**, (U)'s readable side quantifies over **attributes**, and `held` is
    exactly the term that separates the two. Its adapter relabels, so two options can
    hold disjoint sets of values and still read one attribute — each to its own value.

    The witness below is `union(literal("A"), held(literal("A"), f, g))` with `f` and
    `g` swapping `"B"` for `"A"`. Its held sets are `{"A"}` and `{"B"}` — disjoint, so
    (D) passes in the strongest form §5 proposes — and both options read the attribute
    `S "A"`, the first to `"A"` and the second to `"B"`. What decides the readable side
    is a condition on stored attributes: distinct members, or disjoint `admA`. -/

/-- (D) in its held-set form, as the disjointness §5 proposes: no value is held by two
    options. Stated so the counterexample below can be about it.

    This is *not* the rule's premise: `(union)` carries `DIncomp` (`Typing.lean`), §5's
    incomparability. `DDisj` is the strictly stronger reading §5 considered and withdrew,
    and it is here only to be refuted — the witness below satisfies it and still fails
    (U). -/
def DDisj (Tx Ty : Held) : Prop := ∀ v, Tx v → ¬ Ty v

/-- The relabelling adapter: `"B"` on the outside is `"A"` on the inside. -/
def fRel : Value → Value := fun v => match v with | .str "B" => .str "A" | _ => .null

/-- Its inverse on the carriers. -/
def gRel : Value → Value := fun v => match v with | .str "A" => .str "B" | _ => .null

/-- `held(literal("A"), fRel, gRel)` — holds `{"B"}`, stores it as `S "A"`. -/
def tRel : Term := .held (.literalS ["A"]) fRel gRel

/-- The attribute-side twin of `not_uAtCan_pair`. -/
theorem not_uAtCan_pair_A {fuel : Nat} {t₁ t₂ : Term} {v w : Value} {a : Attr}
    (he : (denote fuel t₁).e v = some a)
    (h₂ : (optionSemOf (denote fuel t₂) (specOf t₂)).admitA a = true)
    (hne : (optionSemOf (denote fuel t₁) (specOf t₁)).admitV w ≠
      (optionSemOf (denote fuel t₂) (specOf t₂)).admitV w) :
    ¬ UAtCan fuel [t₁, t₂] := by
  intro h
  have ho : optionSemOf (denote fuel t₁) (specOf t₁) ∈ semsOf fuel [t₁, t₂] :=
    List.mem_cons_self _ _
  have hfilt := (h _ ho v a (by rw [optionSemOf_c]; exact he)).1
  have hmem : optionSemOf (denote fuel t₂) (specOf t₂) ∈
      [optionSemOf (denote fuel t₁) (specOf t₁)] := by
    rw [← hfilt]
    exact List.mem_filter.mpr
      ⟨List.mem_cons_of_mem _ (List.mem_cons_self _ _), h₂⟩
  rcases List.mem_cons.mp hmem with heq | hnil
  · exact hne (congrArg (fun o => OptionSem.admitV o w) heq.symm)
  · exact absurd hnil (by simp)

/-- Both options are derivable, and their held sets are disjoint — so this really is a
    union (D) admits, in the disjointness form §5 calls sound. -/
theorem typed_tRel :
    Typed tRel (fun v => ∃ s, s ∈ ["A"] ∧ fRel v = .str s) (some .S) := by
  refine Typed.held (I := fun w => ∃ s, s ∈ ["A"] ∧ w = .str s) ?_ (fun _ => Iff.rfl)
  exact Typed.literalS ["A"] (by simp) (by simp)

theorem dDisj_tRel :
    DDisj (fun v => ∃ s, s ∈ ["A"] ∧ v = .str s)
      (fun v => ∃ s, s ∈ ["A"] ∧ fRel v = .str s) := by
  rintro v ⟨s, hs, rfl⟩ ⟨s', hs', hf⟩
  -- `v = "A"`, so `fRel v = null`, which is no string
  have : s = "A" := by simpa using hs
  subst this
  exact nomatch hf

/-- **(D) does not discharge the readable side.** Disjoint held sets, and both options
    admit the attribute `S "A"` — the first reading it to `"A"`, the second to `"B"`. -/
theorem not_uAtCan_literal_held :
    ¬ UAtCan 2 [Term.literalS ["A"], tRel] := by
  have hA : (denote 2 (Term.literalS ["A"])).e (Value.str "A") = some (Attr.s "A") := by
    show (if "A" ∈ ["A"] then some (Attr.s "A") else none) = some (Attr.s "A")
    rw [if_pos (List.mem_cons_self _ _)]
  refine not_uAtCan_pair_A (v := .str "A") (a := Attr.s "A") (w := .str "A") hA ?_ ?_
  · show (((if "A" ∈ ["A"] then some (Value.str "A") else none).map gRel)).isSome = true
    rw [if_pos (List.mem_cons_self _ _)]
    rfl
  · show ((denote 2 (Term.literalS ["A"])).e (Value.str "A")).isSome ≠
      ((denote 1 (Term.literalS ["A"])).e (fRel (Value.str "A"))).isSome
    rw [hA]
    show true ≠ ((denote 1 (Term.literalS ["A"])).e Value.null).isSome
    exact fun h => nomatch h

end Calculus
