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
between them. Two options can hold disjoint sets and read one attribute. (D) is a
well-formedness condition on the `T` index and lives there — `DIncomp`, a premise of
`Typed.union` (Typing.lean); the readable side is decided on stored attributes. `DDisj`
below is the *stronger* reading §5 considered and withdrew, kept only to be refuted.

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
  -- §3 `(literal)`: the kind is the value's, which is also what fixes its base.
  | .literal v => some [v.kind]
  | .string | .decimal | .literalS _ => some [.string]
  | .number | .literalN _ => some [.number]
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
  -- `number` and `decimal` decide their own membership: each checks §1's gate on the way
  -- in and on the way out (§3 `(number)` "gates both halves"). The other four ground
  -- scalars accept their whole carrier and so decide nothing.
  | .number | .decimal => true
  -- `(literal)` checks its one value on both halves — the definition of deciding your
  -- own membership, and the reason the constructor is worth having over `refine`.
  | .literal _ => true
  | .set t | .array t | .record t => ident t
  -- `refine` *holds* it rather than propagating: `q` is checked on the way in and on the
  -- way out, which is what deciding your own membership means. §3 argues the same — a `p`
  -- returning the value it read without verifying `q` would break (C).
  | .refine _ _ => true
  | .legacy t _ => ident t
  | .tuple ts tail =>
    identList ts && (match tail with | some t => ident t | none => true)
  | .union opts => identList opts
  | _ => false

def identList : List Term → Bool
  | [] => true
  | t :: ts => ident t && identList ts

end

/-! ## `adm` — the sets an `ident` term checks against

    §5's third auxiliary, and the specification now states it as the two functions below
    rather than as one: its table is term-by-term and matches these definitions clause for
    clause, so a reviewer can read the two side by side. `ident` says a term decides its own
    membership; `adm` says *against what*. Only two terms carry a real set — a `literal`'s values and a
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

mutual

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
  -- `q` is a predicate on *values*, so it tightens this side and only this side.
  -- `refine`'s `e` is defined only where `q` holds, so `adm t ∩ q` is a sound bound and a
  -- strictly better one than the passthrough. `admA` cannot follow: `q` tests the value a
  -- read *produces*, and no syntactic set of attributes bounds that — `held` one-sided the
  -- other way.
  | .refine t q => fun v => adm t v && q v
  | .legacy t _ => adm t
  -- §1's two number gates, recorded for the same reason a literal's set is: each is a
  -- `refine` over an ungated base (`numberCodec_e_restrict`, `decimalCodec_e_restrict`),
  -- and a gate the term owns is exactly what `adm` is for.
  | .literal v => fun w =>
      match v, w with
      | .str s, .str s'   => decide (s' = s)
      | .num d, .num d'   => decide (d' = d)
      | .bool b, .bool b' => decide (b' = b)
      | .bin b, .bin b'   => decide (b' = b)
      | .null, .null      => true
      | _, _              => false
  | .number => inD
  | .decimal => isStored
  -- A union admits what some option admits — the same `⋃` `κ` already takes. Without it
  -- the union spelling of a literal set forgets both sets, where the n-ary literal keeps
  -- them, which would make `union(literal a, literal b)` strictly weaker than
  -- `literal(a, b)` for no reason the semantics gives.
  | .union opts => fun v => admList opts v
  | _ => fun _ => true

/-- `adm`'s union row, as the list recursion the kernel needs. -/
noncomputable def admList : List Term → Value → Bool
  | [], _ => false
  | t :: ts, v => adm t v || admList ts v

end

mutual

/-- `adm`, attribute side. The two wrappers that are `⊤` for `adm` part company here,
    and the reason is which half of the pair each one touches.

    `legacy` is **not** transparent: `extendRead` widens `p` past the subterm's
    admissible set, which is exactly the direction `admA` claims to bound
    (`not_admA_legacy`).

    `held` **is**, and this is the one case where `admA` sees further than `adm`.
    `through`'s `g` post-processes a read and is total, so `dom(p)` is the subterm's
    *exactly* (`through_p`) — the adapter changes which value comes out, never which
    attributes go in. Only `f` is opaque, and `f` gates the write, which is why `adm`
    stays `⊤` here. §5's table gave `held` a single `⊤` row on both sides; its opacity
    is one-sided, and `sepA_literal_heldLiteral` is a pair this separates.

    `literalN` is `true` — the read side goes through `Double.ofDec`, which is
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
  | .held t _ _ => admA t
  | .union opts => fun a => admAList opts a
  -- `decimal` is to `number` as `literal-S` is to `literal-N`: it holds numerals *as
  -- their text*, so its gate is a test on the stored attribute and both sides see it.
  -- `number`'s is not — the numeral goes through `Double.ofDec` — so it stays `⊤`.
  | .decimal => fun a => match a with | .n x => Numeral.Stored x | _ => false
  -- The payoff over `refine`: for every base but `number` the stored attribute *is* the
  -- value, so `ℓ` bounds the readable side too. At `number` it cannot — the numeral goes
  -- through `Double.ofDec` — which is §5's `literal-S`/`literal-N` split, one rule down.
  | .literal v => fun a =>
      match v, a with
      | .str s, .s s'   => decide (s' = s)
      | .bool b, .bool b' => decide (b' = b)
      | .bin b, .b b'   => decide (b' = b)
      | .null, .null    => true
      | .num _, _       => true
      | _, _            => false
  | _ => fun _ => true

/-- …and on the attribute side. -/
def admAList : List Term → Attr → Bool
  | [], _ => false
  | t :: ts, a => admA t a || admAList ts a

end

/-! ### Tag admission, on both sides

`(dunion)`'s admission and `adm`/`admA` at a `dunion` are the same shape — a lookup of the
discriminator, and a membership test on the tag it carries. Stating that shape once is
what lets the `dunion` cases below say the one thing they are about: the tag the
admitting option matched is one of the union's tags. -/

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
    | literal w =>
      -- `(literal)` is the one single-kind rule whose kind comes from *data*, so the
      -- macro cannot serve: the codec must be reduced at `w` before `v` is split.
      cases hκ
      cases w <;> cases v <;>
        simp_all [denote, literalCodec, Codec.restrict, stringCodec, rawNumberCodec,
                  booleanCodec, binaryCodec, nullCodec, Codec.empty, Value.kind]
    | literalS ls => single_kind hκ v he
    | number => single_kind hκ v he
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
      cases hw : (denote fuel t').ownsNull with
      | true =>
        -- the guard declined: the wrapper writes exactly what the subterm writes
        rw [show (denote (fuel+1) (.nullable t')).e = (denote fuel t').e from
          withNull_e_of_owns hw] at he
        exact List.mem_cons_of_mem _ (κ_sound fuel t' hκt he)
      | false =>
        rw [show denote (fuel+1) (.nullable t') = (denote fuel t').withNull from rfl,
          withNull_eq_orNull hw] at he
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
/-- An option's admission lifts to the list — the `⋃` of `adm`'s union row. -/
theorem admList_of_mem : ∀ {opts : List Term} {t : Term} {v : Value},
    t ∈ opts → adm t v = true → admList opts v = true
  | t' :: ts, t, v, hm, h => by
    rcases List.mem_cons.mp hm with rfl | hm'
    · simp [admList, h]
    · simp [admList, admList_of_mem hm' h]

/-- …and on the attribute side. -/
theorem admAList_of_mem : ∀ {opts : List Term} {t : Term} {a : Attr},
    t ∈ opts → admA t a = true → admAList opts a = true
  | t' :: ts, t, a, hm, h => by
    rcases List.mem_cons.mp hm with rfl | hm'
    · simp [admAList, h]
    · simp [admAList, admAList_of_mem hm' h]

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
    case refine t' q =>
      obtain ⟨hq, hc⟩ := restrict_e.mp he
      simp only [adm, adm_sound fuel t' hc, hq, Bool.and_self]
    case literal w =>
      cases w <;> cases v <;>
        simp_all [denote, literalCodec, Codec.restrict, stringCodec, rawNumberCodec,
                  booleanCodec, binaryCodec, nullCodec, Codec.empty, adm]
    case number => cases v <;> simp_all [denote, numberCodec, inD, adm]
    case decimal => cases v <;> simp_all [denote, decimalCodec, isStored, adm]
    case legacy t' r => exact adm_sound fuel t' (extendRead_e.mp he)
    case union opts =>
      obtain ⟨o, ho, -, hoe⟩ := altCodec_e_admits he
      simp only [List.mem_map] at ho
      obtain ⟨tx, htx, rfl⟩ := ho
      rw [optionSemOf_c] at hoe
      exact admList_of_mem htx (adm_sound fuel tx hoe)
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
    case literal w =>
      cases w <;> cases a <;>
        simp_all [denote, literalCodec, Codec.restrict, stringCodec, rawNumberCodec,
                  booleanCodec, binaryCodec, nullCodec, Codec.empty, admA]
    case decimal => cases a <;> simp_all [denote, decimalCodec, admA]
    case held t' f g =>
      obtain ⟨w, hw, -⟩ := through_p.mp hp
      exact admA_sound fuel t' hw
    case union opts =>
      obtain ⟨o, ho, -, hop⟩ := altCodec_p_admits hp
      simp only [List.mem_map] at ho
      obtain ⟨tx, htx, rfl⟩ := ho
      rw [optionSemOf_c] at hop
      exact admAList_of_mem htx (admA_sound fuel tx hop)
    all_goals rfl

/-! ### Why `admA` has no `legacy` case

    §5 lists `refine`, `optional`, `fallback` and `legacy` as passing `adm` through, on
    one `adm`. The value side can: `adm` above does have a `legacy` case. The attribute
    side cannot, and the reason is what `legacy` is for — `extendRead` widens `p` by `r`,
    which is exactly the direction `admA` bounds.

    `admA_sound` is what would break. The witness below reads an `N` attribute out of a
    `legacy` over a string literal, so a passthrough `admA` would claim the read is
    inside `literal("A")`'s admissible set when the whole point of the migration is that
    it is not. This is the specification defect with no other machine-checked witness;
    `docs/codec-formalization.md` §4 records it. -/

/-- A migration that reads a numeral into the literal's value — the shape `legacy` exists
    for, and the shape no syntactic set over the subterm can bound. -/
def rNumeral : Attr → Option Value
  | .n _ => some (.str "A")
  | _ => none

/-- The read really does land outside the subterm's `admA`. -/
theorem legacy_p_outside_admA (fuel : Nat) :
    (denote (fuel+2) (.legacy (.literalS ["A"]) rNumeral)).p (.n "1") = some (.str "A") ∧
      admA (.literalS ["A"]) (.n "1") = false := ⟨rfl, rfl⟩

/-- **§5's `adm` cannot pass through `legacy` on the read side.** Stated as the row's
    refutation rather than as an omission, so the divergence between the document's one
    `adm` and the model's two is a theorem rather than a comment. -/
theorem not_admA_legacy :
    ¬ ∀ (t : Term) (r : Attr → Option Value) (fuel : Nat) (a : Attr) (v : Value),
      (denote fuel (.legacy t r)).p a = some v → admA t a = true := by
  intro h
  have hbad := h (.literalS ["A"]) rNumeral 2 (.n "1") (.str "A")
    (legacy_p_outside_admA 0).1
  rw [(legacy_p_outside_admA 0).2] at hbad
  exact nomatch hbad

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

mutual

/-- **`adm` is informative only where `ident` holds.** If `adm` refuses a single value,
    the term is `ident`. This is the pinning `ident` otherwise lacks: `κ`, `adm` and
    `admA` each have a soundness lemma tying them to the denotation, and `ident` has no
    denotational content to tie — what it has is this relation to `adm`, which is what
    §5 actually uses it for. -/
theorem ident_of_adm : ∀ {t : Term} {v : Value}, adm t v = false → ident t = true
  | .literalS _, _, _ => rfl
  | .literalN _, _, _ => rfl
  | .dunion _ _, _, _ => rfl
  | .refine _ _, _, _ => rfl
  | .literal _, _, _ => rfl
  | .number, _, _ => rfl
  | .decimal, _, _ => rfl
  | .legacy t _, v, h => ident_of_adm (t := t) (v := v) h
  | .union opts, v, h => identList_of_admList (opts := opts) (v := v) h
  | .string, _, h | .boolean, _, h | .binary, _, h
  | .null, _, h | .set _, _, h | .array _, _, h | .tuple _ _, _, h
  | .record _, _, h | .held _ _ _, _, h | .nullable _, _, h | .lazy _, _, h
  | .custom _ _, _, h | .opaq _, _, h | .object _ _, _, h => nomatch h

/-- A union all of whose options refuse a value is one all of whose options decide their
    own membership — `ident_of_adm` lifted to the list, which `adm`'s union row makes
    necessary. -/
theorem identList_of_admList : ∀ {opts : List Term} {v : Value},
    admList opts v = false → identList opts = true
  | [], _, _ => rfl
  | t :: ts, v, h => by
    simp only [admList, Bool.or_eq_false_iff] at h
    simp [identList, ident_of_adm h.1, identList_of_admList h.2]

end

/-- **§5's (K), recovered from `SepV`'s second disjunct.** Disjoint `adm` implies both
    `ident` conjuncts — given that each option admits *something*.

    That side condition is not bookkeeping: `dunion(d)` with no options is derivable, admits
    nothing, and is therefore `adm`-disjoint from `string`, which is not `ident`. -/
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

/-- **What `q` in `adm` buys.** Two refinements of one base with disjoint predicates are
    separated on the writable side by `SepV`'s `adm` disjunct — which the passthrough
    could never satisfy, both sides having been `⊤`. The `κ` disjunct is no help here:
    both options are `{string}`. -/
theorem sepV_refine_disjoint {q q' : Value → Bool} (h : ∀ v, q v = true → q' v = false) :
    SepV (.refine .string q) (.refine .string q') :=
  Or.inr fun v hv => by
    simp only [adm, Bool.true_and] at hv ⊢
    exact h v hv

/-- **Disjoint refinements of one base separate on both sides.** `adm` can carry `q` and
    `admA` cannot — `q` tests the value a read *produces*, which no syntactic set of
    attributes bounds — so the readable side looks undischargeable from the tables alone.
    It is not. Two refinements of one base read an attribute to the **same** value, so at
    most one predicate accepts it, and the readable side separates for the same reason the
    writable side does.

    The condition is *relational* — it is about options sharing a base, not about any one
    option's admissible set — which is why it is a discharger of its own rather than a row
    in the `adm` table. `uniqueAdmission_of_disjoint` takes the two families as arbitrary
    predicates, so nothing here has to be syntactic: the attribute family is
    `∃ v, base.p a = some v ∧ q v`, and disjointness is the base reading `a` to one value. -/
theorem uAtCan_of_refine_disjoint (fuel : Nat) {base : Term} {qs : List (Value → Bool)}
    (hlaw : LawfulCore (denote fuel base))
    (hdisj : List.Pairwise (fun q q' => ∀ v, q v = true → q' v = false) qs) :
    UAtCan (fuel+1) (qs.map (fun q => Term.refine base q)) := by
  show UniqueAdmission (semsOf (fuel+1) (qs.map (fun q => Term.refine base q)))
  refine uniqueAdmission_of_disjoint
    (SVs := qs.map (fun q v => q v = true))
    (SAs := qs.map (fun q a => ∃ v, (denote fuel base).p a = some v ∧ q v = true))
    ?_ ?_ ?_ ?_ ?_
  · rw [semsOf, List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.mpr fun q _ v hv => ?_
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hv
    exact (restrict_e.mp hw).1
  · rw [semsOf, List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.mpr fun q _ a ha => ?_
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ha
    obtain ⟨hp, hq⟩ := restrict_p.mp hw
    exact ⟨w, hp, hq⟩
  · rw [List.pairwise_map]
    refine hdisj.imp fun h v hv hv' => ?_
    simp only at hv hv'
    rw [h v hv] at hv'; exact nomatch hv'
  · rw [List.pairwise_map]
    refine hdisj.imp fun h a hx hy => ?_
    obtain ⟨v, hv, hqv⟩ := hx
    obtain ⟨v', hv', hqv'⟩ := hy
    rw [hv] at hv'; cases hv'
    rw [h v hqv] at hqv'; exact nomatch hqv'
  · rw [semsOf, List.map_map]
    refine forall_mem_map fun q _ t a he => ?_
    simp only [Function.comp_apply] at he ⊢
    rw [optionSemOf_c] at he
    obtain ⟨hq, hb⟩ := restrict_e.mp he
    refine ⟨?_, ?_⟩
    · show ((denote (fuel+1) (.refine base q)).e t).isSome = true
      rw [show (denote (fuel+1) (.refine base q)).e t = some a from he]; rfl
    · show ((denote (fuel+1) (.refine base q)).p a).isSome = true
      rw [show (denote (fuel+1) (.refine base q)).p a = some t from
        restrict_p.mpr ⟨hlaw.retract hb, hq⟩]
      rfl

/-- **Literals over any base, in one theorem.** Drop the lawfulness side-condition by
    taking it from soundness, and what is left is the whole result: for *any derivable
    term* as base, a union of refinements with pairwise disjoint predicates admits uniquely
    on both sides.

    §3's `(literal-S)` and `(literal-N)` are two instantiations — `string` and the ungated
    double codec, at `∈ ℓ`. `boolean` and `binary` are two more, for which §3 writes no
    rule. And the base need not be ground at all: a union of disjoint refinements of one
    `object`, or of one `union`, discharges by the same theorem. There was never a
    per-member argument to make. -/
theorem uAtCan_of_refine_disjoint_of_typed (fuel : Nat) {base : Term} {T μ}
    {qs : List (Value → Bool)} (h : Typed base T μ) (hob : Obligations fuel base)
    (hdisj : List.Pairwise (fun q q' => ∀ v, q v = true → q' v = false) qs) :
    UAtCan (fuel+1) (qs.map (fun q => Term.refine base q)) :=
  uAtCan_of_refine_disjoint fuel (soundness_both fuel h hob).1 hdisj

/-! ### Literals over a primitive §3 gives no `literal` rule for

    §3 names two `literal` rules, at `S` and at `N`. Nothing makes those two special: a
    literal over any ground term is `refine(base, ∈ ℓ)`, which is derivable already, and
    since `adm` now carries `q` and refinements of one base separate on both sides, such a
    union discharges exactly as a string literal's does. The two rules are the two someone
    bothered to name, not the two that are possible. -/

/-- A boolean "literal", as the refinement it is. -/
def isTrueV : Value → Bool := fun v => match v with | .bool b => b | _ => false

/-- …and its complement. -/
def isFalseV : Value → Bool := fun v => match v with | .bool b => !b | _ => false

/-- It is derivable, with the member the base names — no rule of its own. -/
theorem typed_boolLiteral : ∃ T, Typed (.refine .boolean isTrueV) T (some .BOOL) :=
  ⟨_, Typed.refine Typed.boolean⟩

/-- A base that is not ground at all, to show the theorem does not care. Two disjoint
    refinements of one `array(string)` separate exactly as two literals over `string` do —
    "literal" was never the operative word, "one base, disjoint predicates" was. -/
theorem uAtCan_refine_container (fuel : Nat) {q q' : Value → Bool}
    (hd : List.Pairwise (fun a b => ∀ v, a v = true → b v = false) [q, q']) :
    UAtCan (fuel+2) [Term.refine (.array .string) q, Term.refine (.array .string) q'] :=
  uAtCan_of_refine_disjoint_of_typed (fuel+1) (Typed.array Typed.string)
    (by cases fuel <;> trivial) hd

/-- And a union of two discharges on **both** sides, by the same shared-base argument that
    settles numeric literals — a primitive §3 never wrote a `literal` rule for. -/
theorem uAtCan_boolLiterals (fuel : Nat) :
    UAtCan (fuel+2) [Term.refine .boolean isTrueV, Term.refine .boolean isFalseV] := by
  have h : ∀ v, isTrueV v = true → isFalseV v = false := by
    intro v hv; cases v <;> simp_all [isTrueV, isFalseV]
  exact uAtCan_of_refine_disjoint (fuel+1) (qs := [isTrueV, isFalseV])
    lawful_booleanCodec.core (by simpa using h)

/-! ### What the unified `literal` carries

    At arity one `literal(v)` and `refine(g, · = v)` denote the same pair, so it is fair to
    ask why the constructor exists. `adm` is the same either way. `admA` is not: `ℓ` is data
    the *term* owns, so it can be tested against the stored attribute, where `refine`'s `q`
    is a value predicate and cannot be pushed there. That is the whole of it, and it holds
    at every base but one. -/

/-- `admA` sees the value at a string base… -/
theorem admA_literal_str (s s' : String) :
    admA (.literal (.str s)) (.s s') = decide (s' = s) := rfl

/-- …and at a boolean base, which §3 never wrote a `literal` rule for at all. -/
theorem admA_literal_bool (b b' : Bool) :
    admA (.literal (.bool b)) (.bool b') = decide (b' = b) := rfl

/-- …and at `number` it cannot, the stored text not being the value — §1's asymmetry, now
    stated once for the unified rule instead of twice for two. -/
theorem admA_literal_num_blind (d : Double) (x : Numeral) :
    admA (.literal (.num d)) (.n x) = true := rfl

/-- The writable side sees it everywhere, `number` included. -/
theorem adm_literal_num (d d' : Double) :
    adm (.literal (.num d)) (.num d') = decide (d' = d) := rfl

/-- **Where the two literal rules part.** A string literal's stored text *is* its value, so
    `q` is visible on both sides and `admA` carries `ℓ` outright — §5's table separates such
    a union with no help. A numeric literal's is not, so `admA` is `⊤` and the shared base
    is what recovers the readable side. The two `rfl`s below are that difference, and it is
    the whole of why `(literal-N)` needed an argument `(literal-S)` did not. -/
theorem admA_literalS_sees (ls : List String) (s : String) :
    admA (.literalS ls) (.s s) = decide (s ∈ ls) := rfl

/-- …and the numeric side sees nothing. -/
theorem admA_literalN_blind (ls : List Double) (x : Numeral) :
    admA (.literalN ls) (.n x) = true := rfl

/-- **A union of numeric literals discharges on both sides.** §5's `admA` row sends a
    numeric literal to `⊤`, and the reason is real — distinct numerals read to the same
    double, so no syntactic set of attributes bounds one. Read from the *pair* rather than
    the table, though, the options are refinements of a single `rawNumberCodec` with
    disjoint predicates, and `uniqueAdmission_of_sharedBase` settles both sides.

    Which is the honest reading of what a numeric literal set *is*: options told apart by
    the value a read produces, never by the text the store holds. The table cannot see that
    because it answers about one term at a time; this answers about a family sharing a
    base. -/
theorem uAtCan_of_literalN_disjoint (fuel : Nat) {lss : List (List Double)}
    (hdisj : List.Pairwise (fun ls ls' => ∀ d ∈ ls, d ∉ ls') lss) :
    UAtCan (fuel+1) (lss.map Term.literalN) := by
  show UniqueAdmission (semsOf (fuel+1) (lss.map Term.literalN))
  have hs : semsOf (fuel+1) (lss.map Term.literalN)
      = (lss.map literalNCodec).map OptionSem.byAttempt := by
    simp [semsOf, List.map_map, specOf, optionSemOf, denote]
  rw [hs]
  refine uniqueAdmission_of_sharedBase (base := rawNumberCodec) (qs := lss.map inLN)
    lawfulCore_rawNumberCodec ?_ ?_
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun ls _ =>
      ⟨literalNCodec_e_restrict ls, literalNCodec_p_restrict ls⟩
  · rw [List.pairwise_map]
    refine hdisj.imp fun h v hv => ?_
    cases v
    case num d =>
      simp only [inLN, decide_eq_true_eq] at hv
      simp only [inLN, decide_eq_false_iff_not]
      exact h d hv
    all_goals exact Bool.noConfusion hv

/-- §5 (D)'s stand-in, likewise widened: two options are separated on the readable side
    by distinct named members, **or** by disjoint admissible sets. The `adm` disjunct is
    what carries `union(literal("A"), literal("B"))`, whose options share `⇝ S`. -/
def SepA (x y : Term) : Prop :=
  (∃ μx μy, μSyn x = some μx ∧ μSyn y = some μy ∧ μx ≠ μy) ∨
  (∀ a, admA x a = true → admA y a = false)

/-- **`held`'s one-sided opacity, discharging a pair §5's table could not.**
    `union(literal("A"), held(literal("B"), f, g))` separates on the readable side for
    *every* `f` and `g`: the adapter post-processes a read, so it cannot move which
    attributes the option accepts, and the two footprints are `{S "A"}` and `{S "B"}`.
    The member disjunct is no help — both options are `⇝ S` — so this is the new `admA`
    row doing the work alone. -/
theorem sepA_literal_heldLiteral (f g : Value → Value) :
    SepA (.literalS ["A"]) (.held (.literalS ["B"]) f g) :=
  Or.inr fun a ha => by cases a <;> simp_all [admA]

/-- And it is the *subterm* that decides, not the wrapper: with the same inner literal
    the two footprints coincide and `SepA` fails on both disjuncts. That is the pair of
    `not_uAtCan_literal_held`, still refused — §5's `held` counterexample survives the
    row that discharges its neighbour. -/
theorem not_sepA_literal_heldLiteral (f g : Value → Value) :
    ¬ SepA (.literalS ["A"]) (.held (.literalS ["A"]) f g) := by
  rintro (⟨μx, μy, hx, hy, hne⟩ | hdisj)
  · cases hx; cases hy; exact hne rfl
  · exact absurd (hdisj (.s "A") rfl) (by simp [admA])

/-! ### Separation, as one set per option per side

    `SepV` and `SepA` each offer a *choice* — a disjoint kind or a disjoint admissible
    set, a distinct member or a disjoint `admA` — and the choice is made per pair. That
    shape is an artifact of asking the question pairwise. Asked per *option*, the two
    sources of constraint simply **intersect**: an option admits a value only if `κ`
    allows its kind and `adm` allows the value. Disjointness of the intersections is
    implied by disjointness in either factor, so `SepV` and `SepA` are exactly what makes
    these families pairwise disjoint — and `uniqueAdmission_of_disjoint` finishes it,
    once, for both sides. -/

/-- What `κ` and `adm` between them allow an option to write. -/
def SVof (t : Term) : Value → Prop :=
  fun v => (∀ ks, κ t = some ks → Value.kind v ∈ ks) ∧ adm t v = true

/-- What `μ` and `admA` between them allow an option to read. -/
def SAof (t : Term) : Attr → Prop :=
  fun a => (∀ μ, μSyn t = some μ → a.member = μ) ∧ admA t a = true

/-- Admission lands in the value family — `κ` and `adm`'s soundness lemmas, together. -/
theorem admitV_SVof (fuel : Nat) (t : Term) {v}
    (h : (optionSemOf (denote fuel t) (specOf t)).admitV v = true) : SVof t v :=
  ⟨fun _ hκ => admitV_kind fuel t hκ h, admitV_adm fuel t h⟩

/-- …and in the attribute family. Lawfulness is what `μ`'s bridge needs. -/
theorem admitA_SAof (fuel : Nat) (t : Term) (hlaw : Lawful (denote fuel t)) {a}
    (h : (optionSemOf (denote fuel t) (specOf t)).admitA a = true) : SAof t a :=
  ⟨fun _ hμ => admitA_member fuel t hμ hlaw h, admitA_admA fuel t h⟩

/-- **§5's `SepV` is disjointness of the value families.** Either disjunct gives it,
    because a disjoint factor makes the intersection disjoint. -/
theorem SVof_disjoint {x y : Term} (h : SepV x y) : ∀ v, SVof x v → ¬ SVof y v := by
  rintro v ⟨hkx, hax⟩ ⟨hky, hay⟩
  rcases h with ⟨kx, ky, hkxe, hkye, hne⟩ | hdisj
  · exact hne _ (hkx kx hkxe) (hky ky hkye)
  · rw [hdisj v hax] at hay; exact nomatch hay

/-- …and `SepA` of the attribute families. -/
theorem SAof_disjoint {x y : Term} (h : SepA x y) : ∀ a, SAof x a → ¬ SAof y a := by
  rintro a ⟨hmx, hax⟩ ⟨hmy, hay⟩
  rcases h with ⟨μx, μy, hμx, hμy, hne⟩ | hdisj
  · exact hne ((hmx μx hμx).symm.trans (hmy μy hμy))
  · rw [hdisj a hax] at hay; exact nomatch hay

/-- §5's dischargers, combined: pairwise separation on each side of the pair, and closed
    options admitting their own canonicals — so admission is unique at every canonical
    input, which is exactly the theorem's residue `UAtCan`. Every premise is decidable
    from the syntax except lawfulness, which soundness supplies.

    The proof is now one appeal to `uniqueAdmission_of_disjoint`: the two families are
    `SVof`/`SAof`, their disjointness is what `SepV`/`SepA` say, and neither side needs an
    argument of its own. -/
theorem uAtCan_of_separated (fuel : Nat) {opts : List Term}
    (hlaw : ∀ t ∈ opts, Lawful (denote fuel t))
    (hcl : ∀ t ∈ opts, ∀ fields tr, t ≠ .object fields (.codec tr))
    (hV : List.Pairwise SepV opts)
    (hA : List.Pairwise SepA opts) :
    UAtCan fuel opts := by
  refine uniqueAdmission_of_disjoint
    (SVs := opts.map SVof) (SAs := opts.map SAof) ?_ ?_ ?_ ?_ ?_
  · rw [semsOf, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun t _ v hv => admitV_SVof fuel t hv
  · rw [semsOf, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun t ht a ha => admitA_SAof fuel t (hlaw t ht) ha
  · rw [List.pairwise_map]; exact hV.imp SVof_disjoint
  · rw [List.pairwise_map]; exact hA.imp SAof_disjoint
  · refine forall_mem_map fun t ht v a he => ?_
    rw [optionSemOf_c] at he
    exact optionSem_self_admit fuel t (hcl t ht) (hlaw t ht) he

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

/-! ## The other two rows of §5's table

    §5's discharger table has four rows, and until now a reviewer checking it changed
    vocabulary halfway across: two rows are about `UAtCan fuel opts` — a list of
    **terms** — and two are about `UniqueAdmission os`, a list of `OptionSem`. Worse,
    `(dunion)`'s row was never stated at all: it appeared only inside
    `lawful_dunionCodec`, where it is an argument rather than a claim.

    `(dunion)`'s row moves to term level here, so three of the four are one vocabulary.
    The fourth cannot follow, and the reason is worth stating rather than working
    around: `denote` gives `(opaque)` the **fuel-free** `opaqCodecω`, which budgets each
    input by its own depth and is not `altCodec` over any one list of options. Its (U)
    is therefore a statement about `opaqCodec` at a fuel, one level below the term
    language. That is a fact about `opaque`, not a gap in the table. -/

/-- The options of a `(dunion)`, exactly as `denote`'s dunion case builds them: tag
    admission on `d`, where `(union)`'s `semsOf` uses name admission. -/
noncomputable def semsOfD (fuel : Nat) (d : Name) (opts : List Term) : List OptionSem :=
  (opts.map fun t' => (tagsOf d t', denote fuel t')).map fun o => .byTag d o.1 o.2

/-- And it really is the denotation's option list — the `rfl` that keeps `semsOfD` from
    drifting away from `denote`. -/
theorem denote_dunion (fuel : Nat) (d : Name) (opts : List Term) :
    denote (fuel+1) (.dunion d opts) = altCodec (semsOfD fuel d opts) (some .M) := rfl

/-- §5 (U) for a `(dunion)`, in `UAtCan`'s vocabulary. -/
def UAtCanD (fuel : Nat) (d : Name) (opts : List Term) : Prop :=
  UniqueAdmission (semsOfD fuel d opts)

/-- **Row three: `(dunion)`'s (U) is a theorem, not a premise** — §5's "the one union
    whose (U) is discharged by the rule itself". The premises are exactly `Typed.dunion`'s
    two syntactic side conditions, so a derivable `discriminatedUnion` never carries an
    obligation — `Obligations.dunion` is the other half of that claim, and says the
    rule's obligation list has no (U) entry to begin with. Stated here because inside
    `lawful_dunionCodec` it is an argument to a lemma, and a reviewer checking §5's table
    has nothing to point at. -/
theorem uAtCan_dunion (fuel : Nat) {d : Name} {opts : List Term}
    (htags : ∀ t' ∈ opts, tagsOf d t' ≠ [])
    (hdisj : List.Pairwise (fun a b => ∀ tag ∈ tagsOf d a, tag ∉ tagsOf d b) opts) :
    UAtCanD fuel d opts :=
  uniqueAdmission_byTag (dunion_stamp fuel htags) (List.pairwise_map.mpr hdisj)

/-- **Row four: `(opaque)`'s (U), unconditionally.** `uniqueAdmission_opaque` asks for the
    recursive option's lawfulness; `lawful_opaqCodec` supplies it, so the row has no
    premises at all. It is stated about `opaqCodec` at a fuel rather than about the term
    `opaque` for the reason given above — `denoteω` of `opaque` is not a sum over one
    list. -/
theorem uAtCan_opaque (fuel : Nat) (lossy : Bool) :
    UniqueAdmission (opaqOptions lossy (opaqCodec fuel lossy)) :=
  uniqueAdmission_opaque fuel lossy (lawful_opaqCodec fuel lossy)

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

/-! ## Why one-sided `ident` was never an exemption from (K)

    An earlier §5 stated **(K)** as `∀ i ≠ j. κ(cᵢ) ∩ κ(cⱼ) = ∅ ∨ ident(cᵢ) ∨ ident(cⱼ)`
    and called it *sufficient* for (U). It is not, and the two counterexamples below are
    why the `ident` half is absent from `uAtCan_of_disjoint`. §5 now carries the repaired
    form — `ident` on both sides **and** disjoint `adm` — and cites these two as its
    reason, so what follows is the machine-checked half of a correction the doc has
    already made, not a live disagreement with it.

    The withdrawn rule was right about what `ident` buys: attempted admission on a
    `literal` is evidence, where attempted admission on `string` is not. What it dropped
    is that evidence only *resolves* a pair when it is available on **both** sides and
    the two admissible sets are **disjoint**. §5's own worked example,
    `union(literal("A"), literal("B"))`, has both; the rule offered in support of it
    demanded neither. -/

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

/-- **One-sided `ident` does not discharge (U).** `union(literal("A"), string)` passes
    the exemption §5 withdrew — `ident(literal("A"))` holds — and violates (U) at the
    value `"A"`, which both options admit. `literal`'s attempt *is* evidence; `string`'s is not, and one
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

/-- **Two-sided `ident` does not discharge (U) either.** `ident` propagates through
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

/-! ### …and the same union meets the residue the laws actually carry

    `not_uAtCan_array_literals` refutes `UAtCan` at `[]` — a canonical pair of *each*
    option, and one the union never writes, since both admit it and `altCodec` declines
    what it cannot resolve. `UAtAct` (§5, `Soundness.lean`) asks only where the union
    acts, and the same term meets it: every value the union does write is read back by
    the option that wrote it.

    So the two residues are not the same condition, and the gap is not a curiosity — it
    holds `union(array(literal "A"), array(literal "B"))`, which is a schema people write.
    What carries it is that a `literal`'s two halves test one set, so an element the
    neighbouring option declines to *write* is one it declines to *read*. That is exactly
    what `held` breaks (`not_uAtCan_literal_held`), which is why the argument is about
    literals and not about containers in general. -/

/-- §3 `(literal-S)`'s two halves test one set, so a `literal` declines to read the
    attribute it declines to write. -/
theorem literalS_p_none {ls ls' : List String} {t : Value} {a : Attr}
    (he : (literalSCodec ls).e t = some a) (hne : (literalSCodec ls').e t = none) :
    (literalSCodec ls').p a = none := by
  cases t <;> simp_all [literalSCodec]
  obtain ⟨-, rfl⟩ := he
  simp [hne]

/-- …the reading half of the same §3 `(literal-S)` fact. -/
theorem literalS_e_none {ls ls' : List String} {t : Value} {a : Attr}
    (hp : (literalSCodec ls).p a = some t) (hne : (literalSCodec ls').p a = none) :
    (literalSCodec ls').e t = none := by
  cases a <;> simp_all [literalSCodec]
  obtain ⟨-, rfl⟩ := hp
  simp [hne]

/-- §3 `(array)`'s traversal inherits it: an element the neighbour refuses makes the
    whole list unreadable, at the position the writing traversal already fixed. -/
theorem traverse_literalS_p_none {ls ls' : List String} {vs : List Value} {as : List Attr}
    (he : traverse (literalSCodec ls).e vs = some as)
    (hne : traverse (literalSCodec ls').e vs = none) :
    traverse (literalSCodec ls').p as = none := by
  cases hres : traverse (literalSCodec ls').p as with
  | none => rfl
  | some ws =>
    exfalso
    have hall : ∀ v ∈ vs, ((literalSCodec ls').e v).isSome := by
      intro v hv
      obtain ⟨a, ha, hea⟩ := (traverse_eq_some.mp he).mem_left hv
      obtain ⟨w, -, hpw⟩ := (traverse_eq_some.mp hres).mem_left ha
      cases hev : (literalSCodec ls').e v with
      | none => rw [literalS_p_none hea hev] at hpw; exact nomatch hpw
      | some _ => rfl
    have hs := traverse_isSome_of_all hall
    rw [hne] at hs
    exact nomatch hs

/-- …and dually, at §3 `(array)`. -/
theorem traverse_literalS_e_none {ls ls' : List String} {as : List Attr} {vs : List Value}
    (hp : traverse (literalSCodec ls).p as = some vs)
    (hne : traverse (literalSCodec ls').p as = none) :
    traverse (literalSCodec ls').e vs = none := by
  cases hres : traverse (literalSCodec ls').e vs with
  | none => rfl
  | some ws =>
    exfalso
    have hall : ∀ a ∈ as, ((literalSCodec ls').p a).isSome := by
      intro a ha
      obtain ⟨v, hv, hpv⟩ := (traverse_eq_some.mp hp).mem_left ha
      obtain ⟨w, -, hew⟩ := (traverse_eq_some.mp hres).mem_left hv
      cases hpa : (literalSCodec ls').p a with
      | none => rw [literalS_e_none hpv hpa] at hew; exact nomatch hew
      | some _ => rfl
    have hs := traverse_isSome_of_all hall
    rw [hne] at hs
    exact nomatch hs

/-- §3 `(array)` over §3 `(literal-S)`: it refuses on the attribute side whatever it
    refuses on the value side, at the attribute its neighbour wrote. -/
theorem arrayLiteral_p_none {ls ls' : List String} {t : Value} {a : Attr}
    (he : (arrayCodec (literalSCodec ls)).e t = some a)
    (hne : (arrayCodec (literalSCodec ls')).e t = none) :
    (arrayCodec (literalSCodec ls')).p a = none := by
  cases t with
  | arr vs =>
    simp only [arrayCodec, Option.map_eq_some'] at he
    obtain ⟨as, has, rfl⟩ := he
    simp only [arrayCodec] at hne ⊢
    cases h2 : traverse (literalSCodec ls').e vs with
    | some _ => rw [h2] at hne; exact nomatch hne
    | none => rw [traverse_literalS_p_none has h2]; rfl
  | _ => exact nomatch he

/-- …and dually, the same §3 pair. -/
theorem arrayLiteral_e_none {ls ls' : List String} {t : Value} {a : Attr}
    (hp : (arrayCodec (literalSCodec ls)).p a = some t)
    (hne : (arrayCodec (literalSCodec ls')).p a = none) :
    (arrayCodec (literalSCodec ls')).e t = none := by
  cases a with
  | l as =>
    simp only [arrayCodec, Option.map_eq_some'] at hp
    obtain ⟨vs, hvs, rfl⟩ := hp
    simp only [arrayCodec] at hne ⊢
    cases h2 : traverse (literalSCodec ls').p as with
    | some _ => rw [h2] at hne; exact nomatch hne
    | none => rw [traverse_literalS_e_none hvs h2]; rfl
  | _ => exact nomatch hp

/-- The two §5 options are distinct — needed only to read a singleton filter back. -/
theorem optionSem_arrayLiterals_ne :
    OptionSem.byAttempt (arrayCodec (literalSCodec ["A"])) ≠
      OptionSem.byAttempt (arrayCodec (literalSCodec ["B"])) := by
  intro h
  have := congrArg (fun o => o.admitV (.arr [.str "A"])) h
  simp [OptionSem.byAttempt, arrayCodec, traverse, literalSCodec] at this

/-- **§5's two residues, separated at a schema people write.**
    `union(array(literal "A"), array(literal "B"))` fails `UAtCan`
    (`not_uAtCan_array_literals`) and meets `UAtAct` — so the soundness theorem covers it
    once (U) is asked where the union acts rather than at every option's canonicals. The
    union declines the empty array, and every value it does write round-trips through the
    option that wrote it. -/
theorem uAtAct_array_literals :
    UAtAct 2 [Term.array (.literalS ["A"]), Term.array (.literalS ["B"])] := by
  show UniqueBothWays [OptionSem.byAttempt (arrayCodec (literalSCodec ["A"])),
    OptionSem.byAttempt (arrayCodec (literalSCodec ["B"]))]
  have lawA : LawfulCore (arrayCodec (literalSCodec ["A"])) :=
    lawfulCore_arrayCodec (lawful_literalSCodec _).core
  have lawB : LawfulCore (arrayCodec (literalSCodec ["B"])) :=
    lawfulCore_arrayCodec (lawful_literalSCodec _).core
  refine ⟨?_, ?_⟩
  · intro o ho t a hf he
    rcases List.mem_cons.mp ho with rfl | ho'
    · obtain ⟨-, hB⟩ := filter_pair_left_inv optionSem_arrayLiterals_ne hf
      rw [OptionSem.byAttempt_admitV] at hB
      have hBe : (arrayCodec (literalSCodec ["B"])).e t = none := by
        cases h : (arrayCodec (literalSCodec ["B"])).e t with
        | none => rfl
        | some _ => rw [h] at hB; exact nomatch hB
      refine filter_pair_left ?_ ?_
      · rw [OptionSem.byAttempt_admitA, lawA.retract he]; rfl
      · rw [OptionSem.byAttempt_admitA, arrayLiteral_p_none he hBe]; rfl
    · rcases List.mem_singleton.mp ho' with rfl
      obtain ⟨hA, -⟩ := filter_pair_right_inv optionSem_arrayLiterals_ne hf
      rw [OptionSem.byAttempt_admitV] at hA
      have hAe : (arrayCodec (literalSCodec ["A"])).e t = none := by
        cases h : (arrayCodec (literalSCodec ["A"])).e t with
        | none => rfl
        | some _ => rw [h] at hA; exact nomatch hA
      refine filter_pair_right ?_ ?_
      · rw [OptionSem.byAttempt_admitA, arrayLiteral_p_none he hAe]; rfl
      · rw [OptionSem.byAttempt_admitA, lawB.retract he]; rfl
  · intro o ho a t a' hf hp he
    rcases List.mem_cons.mp ho with rfl | ho'
    · obtain ⟨-, hB⟩ := filter_pair_left_inv optionSem_arrayLiterals_ne hf
      rw [OptionSem.byAttempt_admitA] at hB
      have hBp : (arrayCodec (literalSCodec ["B"])).p a = none := by
        cases h : (arrayCodec (literalSCodec ["B"])).p a with
        | none => rfl
        | some _ => rw [h] at hB; exact nomatch hB
      have h' : (arrayCodec (literalSCodec ["A"])).e t = some a' := he
      refine filter_pair_left ?_ ?_
      · rw [OptionSem.byAttempt_admitV, h']; rfl
      · rw [OptionSem.byAttempt_admitV, arrayLiteral_e_none hp hBp]; rfl
    · rcases List.mem_singleton.mp ho' with rfl
      obtain ⟨hA, -⟩ := filter_pair_right_inv optionSem_arrayLiterals_ne hf
      rw [OptionSem.byAttempt_admitA] at hA
      have hAp : (arrayCodec (literalSCodec ["A"])).p a = none := by
        cases h : (arrayCodec (literalSCodec ["A"])).p a with
        | none => rfl
        | some _ => rw [h] at hA; exact nomatch hA
      have h' : (arrayCodec (literalSCodec ["B"])).e t = some a' := he
      refine filter_pair_right ?_ ?_
      · rw [OptionSem.byAttempt_admitV, arrayLiteral_e_none hp hAp]; rfl
      · rw [OptionSem.byAttempt_admitV, h']; rfl

/-- Both counterexamples are `ident` on the side(s) the withdrawn exemption appealed to
    — so it admitted them outright, rather than excluding them by a side condition. The
    `adm`-disjointness §5 now demands is what excludes them. -/
example : ident (.literalS ["A"]) = true := rfl
example : ident (.array (.literalS ["A"])) = true := rfl
example : ident (.array (.literalS ["B"])) = true := rfl

/-! ## Why (D) does not discharge the readable side either

    An earlier §5 listed **(D)** — incomparable held sets — as a discharger of (U)'s
    readable side, and held that stating it as genuine *disjointness* would be sound
    though needlessly strict. Disjointness is not sound either: held sets are sets of
    **values**, (U)'s readable side quantifies over **attributes**, and `held` is exactly
    the term that separates the two. Its adapter relabels, so two options can hold
    disjoint sets of values and still read one attribute — each to its own value. §5 now
    says this, and (D) is a well-formedness condition on the `T` index rather than a
    discharger; the witness below is what settled it.

    That witness is `union(literal("A"), held(literal("A"), f, g))` with `f` and `g`
    swapping `"B"` for `"A"`. Its held sets are `{"A"}` and `{"B"}` — disjoint, so (D)
    passes in the strongest form ever proposed for it — and both options read the
    attribute `S "A"`, the first to `"A"` and the second to `"B"`. What decides the
    readable side is a condition on stored attributes: distinct members, or disjoint
    `admA`. -/

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
    union (D) admits, in the disjointness form §5 once proposed and withdrew. -/
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
