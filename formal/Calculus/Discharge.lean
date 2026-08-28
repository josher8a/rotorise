import Calculus.Soundness

/-!
# §5 — The decidable dischargers of (U)

The machinery of (K): `Kind`, `κ` and `ident` as total structural recursions over the
term language, exactly as §5's tables state them, plus the theorem that puts them to
work — `uAtCan_of_disjoint`, discharging `(union)`'s residual (U) at the declaration.

The discharger proved here is the disjointness route, on both sides of the pair:
pairwise-disjoint `κ` (no `⊤`) settles the value side, and pairwise-distinct named
members settle the attribute side — the member index standing in for §5 (D), whose
held-set form waits on the `T` index (README). Open object options are excluded, as
§5 demands: an undeclared name disqualifies the option even where its rest codec would
hold it, so an open object never admits its own canonical pairs.

`ident` is defined, per §5's table, but is deliberately *not* consumed as an exemption
from κ-disjointness. §5 states (K) as `κ(cᵢ) ∩ κ(cⱼ) = ∅ ∨ ident(cᵢ) ∨ ident(cⱼ)` and
calls it sufficient for (U); it is not, on either disjunct, and the two counterexamples
at the foot of this file are machine-checked. A repaired exemption needs `ident` on
*both* sides *and* disjoint admissible sets — which is what §5's own worked example,
`union(literal("A"), literal("B"))`, actually has.
-/

namespace Calculus

/-! ## Kinds -/

/-- §5's runtime shapes: the coarse partition of `Value` mirroring `μ` on the other
    side of the pair. -/
inductive Kind where
  | string | number | boolean | binary | set | array | map | null
deriving DecidableEq, Repr

def kindOf : Value → Kind
  | .str _ => .string
  | .num _ => .number
  | .bool _ => .boolean
  | .bin _ => .binary
  | .null => .null
  | .set _ => .set
  | .arr _ => .array
  | .map _ => .map

mutual

/-- §5's `κ`: the kinds of value a term accepts. `none` is the table's `⊤`, and it
    absorbs — `nullable`'s `∪` and `union`'s `⋃` answer `⊤` whenever a subterm does. -/
def κ : Term → Option (List Kind)
  | .string | .decimal | .literalS _ => some [.string]
  | .number | .numeric _ | .literalN _ => some [.number]
  | .boolean => some [.boolean]
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

/-- A sum's encode routes through an admitting option. -/
theorem altCodec_e_admits {os : List OptionSem} {μA : Option Member} {v a}
    (he : (altCodec os μA).e v = some a) :
    ∃ o ∈ os, o.admitV v = true ∧ o.c.e v = some a := by
  replace he : (match os.filter (·.admitV v) with
    | [o] => o.c.e v | _ => none) = some a := he
  cases hf : os.filter (·.admitV v) with
  | nil => rw [hf] at he; exact nomatch he
  | cons o tl =>
    cases tl with
    | cons _ _ => rw [hf] at he; exact nomatch he
    | nil =>
      rw [hf] at he
      have hom : o ∈ os.filter (·.admitV v) := by
        rw [hf]; exact List.mem_cons_self o []
      have hmem := List.mem_filter.mp hom
      exact ⟨o, hmem.1, hmem.2, he⟩

/-- Encoding lands in `κ`: a term's writable values have the kinds its `κ` names.
    (Where `κ` answers `⊤` there is nothing to say — the table's point.) -/
theorem κ_sound : ∀ (fuel : Nat) (t : Term) {ks : List Kind} {v a},
    κ t = some ks → (denote fuel t).e v = some a → kindOf v ∈ ks
  | 0, _, _, _, _, _, he => nomatch he
  | fuel+1, t, ks, v, a, hκ, he => by
    cases t with
    | string =>
      replace hκ : some [Kind.string] = some ks := hκ
      cases hκ
      cases v <;> first
        | exact List.mem_cons_self _ _
        | exact nomatch he
    | decimal =>
      replace hκ : some [Kind.string] = some ks := hκ
      cases hκ
      cases v <;> first
        | exact List.mem_cons_self _ _
        | exact nomatch he
    | literalS ls =>
      replace hκ : some [Kind.string] = some ks := hκ
      cases hκ
      cases v <;> first
        | exact List.mem_cons_self _ _
        | exact nomatch he
    | number =>
      replace hκ : some [Kind.number] = some ks := hκ
      cases hκ
      cases v <;> first
        | exact List.mem_cons_self _ _
        | exact nomatch he
    | numeric q =>
      replace hκ : some [Kind.number] = some ks := hκ
      cases hκ
      cases v <;> first
        | exact List.mem_cons_self _ _
        | exact nomatch he
    | literalN ls =>
      replace hκ : some [Kind.number] = some ks := hκ
      cases hκ
      cases v <;> first
        | exact List.mem_cons_self _ _
        | exact nomatch he
    | boolean =>
      replace hκ : some [Kind.boolean] = some ks := hκ
      cases hκ
      cases v <;> first
        | exact List.mem_cons_self _ _
        | exact nomatch he
    | binary =>
      replace hκ : some [Kind.binary] = some ks := hκ
      cases hκ
      cases v <;> first
        | exact List.mem_cons_self _ _
        | exact nomatch he
    | set t' =>
      replace hκ : some [Kind.set] = some ks := hκ
      cases hκ
      cases v <;> first
        | exact List.mem_cons_self _ _
        | exact nomatch he
    | array t' =>
      replace hκ : some [Kind.array] = some ks := hκ
      cases hκ
      cases v <;> first
        | exact List.mem_cons_self _ _
        | exact nomatch he
    | tuple ts tail =>
      replace hκ : some [Kind.array] = some ks := hκ
      cases hκ
      cases v <;> first
        | exact List.mem_cons_self _ _
        | exact nomatch he
    | record t' =>
      replace hκ : some [Kind.map] = some ks := hκ
      cases hκ
      cases v <;> first
        | exact List.mem_cons_self _ _
        | exact nomatch he
    | object fields rest =>
      replace hκ : some [Kind.map] = some ks := hκ
      cases hκ
      cases v <;> first
        | exact List.mem_cons_self _ _
        | exact nomatch he
    | dunion d opts =>
      replace hκ : some [Kind.map] = some ks := hκ
      cases hκ
      replace he : (dunionCodec d
        (opts.map fun t' => (tagsOf d t', denote fuel t'))).e v = some a := he
      obtain ⟨o, ho, hadm, -⟩ := altCodec_e_admits he
      simp only [List.mem_map] at ho
      obtain ⟨x, hx, rfl⟩ := ho
      cases v <;> first
        | exact List.mem_cons_self _ _
        | exact nomatch hadm
    | refine t' q =>
      replace hκ : κ t' = some ks := hκ
      replace he : (if q v then (denote fuel t').e v else none) = some a := he
      split at he
      · exact κ_sound fuel t' hκ he
      · exact nomatch he
    | legacy t' r =>
      replace hκ : κ t' = some ks := hκ
      replace he : (denote fuel t').e v = some a := he
      exact κ_sound fuel t' hκ he
    | nullable t' =>
      replace hκ : (κ t').map (Kind.null :: ·) = some ks := hκ
      cases hκt : κ t' with
      | none => rw [hκt] at hκ; exact nomatch hκ
      | some ks' =>
        rw [hκt] at hκ
        replace hκ : some (Kind.null :: ks') = some ks := hκ
        cases hκ
        cases v with
        | null => exact List.mem_cons_self _ _
        | str s => exact List.mem_cons_of_mem _ (κ_sound fuel t' hκt he)
        | num d => exact List.mem_cons_of_mem _ (κ_sound fuel t' hκt he)
        | bool b => exact List.mem_cons_of_mem _ (κ_sound fuel t' hκt he)
        | bin b => exact List.mem_cons_of_mem _ (κ_sound fuel t' hκt he)
        | set vs => exact List.mem_cons_of_mem _ (κ_sound fuel t' hκt he)
        | arr vs => exact List.mem_cons_of_mem _ (κ_sound fuel t' hκt he)
        | map kvs => exact List.mem_cons_of_mem _ (κ_sound fuel t' hκt he)
    | union opts =>
      replace hκ : κList opts = some ks := hκ
      replace he : (altCodec
        (opts.map fun t' => optionSemOf (denote fuel t') (specOf t'))
        (unanimous (opts.map fun t' => (denote fuel t').μ))).e v = some a := he
      obtain ⟨o, ho, -, hoe⟩ := altCodec_e_admits he
      simp only [List.mem_map] at ho
      obtain ⟨tx, htx, rfl⟩ := ho
      rw [optionSemOf_c] at hoe
      obtain ⟨ksx, hκx, hsub⟩ := κList_mem hκ tx htx
      exact hsub _ (κ_sound fuel tx hκx hoe)
    | held t' f g => exact nomatch hκ
    | lazy γ => exact nomatch hκ
    | custom ce cp => exact nomatch hκ
    | opaq lossy => exact nomatch hκ

/-! ## Admission is guarded -/

/-- Any option's value admission is `κ`-guarded: an admitted value has a kind the
    option's (non-`⊤`) `κ` names. -/
theorem admitV_kind (fuel : Nat) (t : Term) {ks : List Kind} {v}
    (hκ : κ t = some ks)
    (h : (optionSemOf (denote fuel t) (specOf t)).admitV v = true) :
    kindOf v ∈ ks := by
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

/-- §5's disjointness dischargers, combined: pairwise-disjoint `κ` (no `⊤`) settles
    the value side of (U), pairwise-distinct named members settle the attribute side,
    and closed options admit their own canonicals — so admission is unique at every
    canonical input, which is exactly the theorem's residue `UAtCan`. Every premise
    is decidable from the syntax except lawfulness, which soundness supplies. -/
theorem uAtCan_of_disjoint (fuel : Nat) {opts : List Term}
    (hlaw : ∀ t ∈ opts, Lawful (denote fuel t))
    (hcl : ∀ t ∈ opts, ∀ fields tr, t ≠ .object fields (.codec tr))
    (hκ : ∀ t ∈ opts, (κ t).isSome)
    (hμ : ∀ t ∈ opts, (μSyn t).isSome)
    (hκd : List.Pairwise (fun x y => ∀ kx ky, κ x = some kx → κ y = some ky →
      ∀ k ∈ kx, k ∉ ky) opts)
    (hμd : List.Pairwise (fun x y => μSyn x ≠ μSyn y) opts) :
    UAtCan fuel opts := by
  intro o ho t a he
  simp only [semsOf, List.mem_map] at ho
  obtain ⟨tx, htx, rfl⟩ := ho
  rw [optionSemOf_c] at he
  obtain ⟨hV, hA⟩ := optionSem_self_admit fuel tx (hcl tx htx) (hlaw tx htx) he
  constructor
  · show ((opts.map fun t' => optionSemOf (denote fuel t') (specOf t')).filter
      (·.admitA a)) = [optionSemOf (denote fuel tx) (specOf tx)]
    refine filter_map_singleton _ _ opts ?_ tx htx hA
    refine pairwise_imp_mem ?_ hμd
    intro x hx y hy hxy
    obtain ⟨μx, hμx⟩ := Option.isSome_iff_exists.mp (hμ x hx)
    obtain ⟨μy, hμy⟩ := Option.isSome_iff_exists.mp (hμ y hy)
    have hne : μx ≠ μy := fun h => hxy (by rw [hμx, hμy, h])
    constructor
    · intro hax
      cases hay : (optionSemOf (denote fuel y) (specOf y)).admitA a with
      | false => rfl
      | true =>
        have h1 := admitA_member fuel x hμx (hlaw x hx) hax
        have h2 := admitA_member fuel y hμy (hlaw y hy) hay
        exact (hne (h1.symm.trans h2)).elim
    · intro hay
      cases hax : (optionSemOf (denote fuel x) (specOf x)).admitA a with
      | false => rfl
      | true =>
        have h1 := admitA_member fuel x hμx (hlaw x hx) hax
        have h2 := admitA_member fuel y hμy (hlaw y hy) hay
        exact (hne (h1.symm.trans h2)).elim
  · show ((opts.map fun t' => optionSemOf (denote fuel t') (specOf t')).filter
      (·.admitV t)) = [optionSemOf (denote fuel tx) (specOf tx)]
    refine filter_map_singleton _ _ opts ?_ tx htx hV
    refine pairwise_imp_mem ?_ hκd
    intro x hx y hy hxy
    obtain ⟨kx, hkx⟩ := Option.isSome_iff_exists.mp (hκ x hx)
    obtain ⟨ky, hky⟩ := Option.isSome_iff_exists.mp (hκ y hy)
    constructor
    · intro hvx
      cases hvy : (optionSemOf (denote fuel y) (specOf y)).admitV t with
      | false => rfl
      | true =>
        have h1 := admitV_kind fuel x hkx hvx
        have h2 := admitV_kind fuel y hky hvy
        exact absurd h2 (hxy kx ky hkx hky _ h1)
    · intro hvy
      cases hvx : (optionSemOf (denote fuel x) (specOf x)).admitV t with
      | false => rfl
      | true =>
        have h1 := admitV_kind fuel x hkx hvx
        have h2 := admitV_kind fuel y hky hvy
        exact absurd h2 (hxy kx ky hkx hky _ h1)

/-! ## The premises are jointly inhabited

    `uAtCan_of_disjoint` takes six premises, and a theorem whose premises cannot all
    hold discharges nothing. `union(string, boolean)` satisfies every one of them —
    disjoint kinds, distinct members, closed, lawful — so the discharger really does
    decide unions. -/

/-- Satisfiability witness for `uAtCan_of_disjoint`: `union(string, boolean)` is
    discharged at the declaration, at every fuel. -/
theorem uAtCan_string_boolean (fuel : Nat) :
    UAtCan fuel [Term.string, Term.boolean] := by
  -- Each premise is checked at the two options and refuted past them.
  have two : ∀ {P : Term → Prop}, P .string → P .boolean →
      ∀ t ∈ [Term.string, Term.boolean], P t := by
    intro P hs hb t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact hs
    · rcases List.mem_cons.mp ht with rfl | ht
      · exact hb
      · exact absurd ht (by simp)
  -- and each pairwise premise at the single unordered pair.
  have pair : ∀ {R : Term → Term → Prop}, R .string .boolean →
      List.Pairwise R [Term.string, Term.boolean] := by
    intro R h
    refine List.Pairwise.cons ?_ (List.Pairwise.cons (by simp) List.Pairwise.nil)
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact h
    · exact absurd hy (by simp)
  refine uAtCan_of_disjoint fuel (two (lawful_string fuel) (lawful_boolean fuel))
    (two (fun _ _ h => nomatch h) (fun _ _ h => nomatch h))
    (two rfl rfl) (two rfl rfl) (pair ?_) (pair ?_)
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

end Calculus
