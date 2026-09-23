import Calculus.HeldSet
import Calculus.ExactV

/-!
# (D) is a property of the selector

§5's (D) asks that the union's selector be total on the union's held set: each held value
selects an option, and that option writes the value. `SelTotal` states that of a selector.
`altCodec` selects by count, and for the count, totality is pairwise disjointness
(`countSel_total`), which is `DIncomp`. A nested pair fails the count: `unionLiteralString`
holds `"A"` and writes nothing.

The least-admitter selector `findSel` is the find operation of union-find over the options. A laminar family
(each pair disjoint or nested) makes `findSel` total (`findSel_total`), and a strictly laminar
family makes the answer unique (`strictLaminar_least_unique`). The witness is the nested pair:
`findSel` writes `"A"` (`findCodec_writes_A`), and the count does not (`contrast`). A crossing pair
defeats both selectors (`not_selTotal_xOs`, `not_countTotal_xOs`). First match is total on each
family (`firstSel_total`), so totality alone does not force laminarity: order independence does.
`cells_count_eq_find` shows that a nested union normalizes to its cells, each option minus its
strict children, and that the count selector over the cells is `findSel`.

The union of the model still selects by count. `findCodec` is a theorem-level extension, and
`Term.union` does not use it.

Under the count's (D), the judgement's index is exact: `typed_T_adm` proves that a derivable
term holds exactly the values it admits. `survivors` carries (D) through the meet, because the
meet shrinks each option and disjointness survives a shrink.
-/

namespace Calculus

/-- Inclusion of the held sets of two options. -/
def HeldLe (a b : OptionSem) : Prop := ∀ v, a.c.T v → b.c.T v

def HeldLt (a b : OptionSem) : Prop := HeldLe a b ∧ ¬ HeldLe b a

/-- Each option admits by attempt, and its held set is its write domain. -/
def AttemptDom (os : List OptionSem) : Prop :=
  ∀ o ∈ os, (∀ v, o.admitV v = (o.c.e v).isSome) ∧ TIsDomE o.c

/-- **(D), stated on a selector.** The selector is total on the union's held set: each held
    value selects an option, and that option writes the value. -/
def SelTotal (sel : List OptionSem → Value → Option OptionSem) (os : List OptionSem) : Prop :=
  ∀ v, HUnion (os.map (·.c.T)) v → ∃ o, sel os v = some o ∧ o ∈ os ∧ (o.c.e v).isSome = true

/-- The count selector: exactly one admitting option. -/
def countSel (os : List OptionSem) (v : Value) : Option OptionSem :=
  match os.filter (·.admitV v) with
  | [o] => some o
  | _ => none

/-- `altCodec` writes through the count selector. -/
theorem altCodec_e_countSel (os : List OptionSem) (μ : Option Member) (v : Value) :
    (altCodec os μ).e v = (countSel os v).bind (·.c.e v) := by
  show select _ _ _ v = _
  unfold select countSel
  generalize os.filter (·.admitV v) = l
  rcases l with _ | ⟨o, _ | _⟩ <;> rfl

/-- Under `AttemptDom`, admission is membership in the held set. -/
theorem AttemptDom.admit_iff {os : List OptionSem} (h : AttemptDom os) {o : OptionSem}
    (ho : o ∈ os) (v : Value) : o.admitV v = true ↔ o.c.T v := by
  rw [(h o ho).1 v]; exact ((h o ho).2 v).symm

/-- A value in the union's held set is held by one option. -/
theorem held_mem {os : List OptionSem} {v : Value} (h : HUnion (os.map (·.c.T)) v) :
    ∃ o ∈ os, o.c.T v := by
  obtain ⟨T, hT, hv⟩ := h
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hT
  exact ⟨o, ho, hv⟩

/-- A pairwise-disjoint list whose members all hold `v` has at most the one member. -/
theorem singleton_of_disj {l : List OptionSem} {v : Value} {o : OptionSem}
    (hp : l.Pairwise fun a b => HDisj a.c.T b.c.T) (hall : ∀ x ∈ l, x.c.T v) (ho : o ∈ l) :
    l = [o] := by
  match l, hp with
  | [], _ => exact nomatch ho
  | [x], _ =>
    have : o = x := List.mem_singleton.mp ho
    rw [this]
  | x :: y :: t, hp =>
    exact absurd (hall y (by simp)) ((List.pairwise_cons.mp hp).1 y (by simp) v
      (hall x (by simp)))

/-- **The count selector is total on pairwise-disjoint options.** This is the codec form of
    `DIncomp`: pairwise disjointness of the held sets gives totality of `altCodec`'s selector. -/
theorem countSel_total {os : List OptionSem} (hA : AttemptDom os)
    (hD : os.Pairwise fun a b => HDisj a.c.T b.c.T) : SelTotal countSel os := by
  intro v hv
  obtain ⟨o, ho, hTv⟩ := held_mem hv
  have hadm : o.admitV v = true := (hA.admit_iff ho v).mpr hTv
  have hf : os.filter (·.admitV v) = [o] :=
    singleton_of_disj (hD.sublist List.filter_sublist)
      (fun x hx => by
        have hx' := List.mem_filter.mp hx
        exact (hA.admit_iff hx'.1 v).mp hx'.2)
      (List.mem_filter.mpr ⟨ho, hadm⟩)
  refine ⟨o, by simp only [countSel, hf], ho, ?_⟩
  rw [← (hA o ho).1 v]; exact hadm

/-- A laminar family: every pair disjoint or nested. -/
def Laminar (os : List OptionSem) : Prop :=
  os.Pairwise fun a b => HDisj a.c.T b.c.T ∨ HeldLe a b ∨ HeldLe b a

/-- Strictly laminar: every pair disjoint or strictly nested. Two equal non-empty options are
    as ambiguous to `findSel` as to the count. -/
def StrictLaminar (os : List OptionSem) : Prop :=
  os.Pairwise fun a b => HDisj a.c.T b.c.T ∨ HeldLt a b ∨ HeldLt b a

/-- A strictly laminar family is laminar. -/
theorem StrictLaminar.laminar {os : List OptionSem} (h : StrictLaminar os) : Laminar os :=
  h.imp fun r => r.imp_right (Or.imp (·.1) (·.1))

/-- `o` is a least admitting option at `v`. -/
def IsLeast (os : List OptionSem) (v : Value) (o : OptionSem) : Prop :=
  o ∈ os ∧ o.admitV v = true ∧ ∀ o' ∈ os, o'.admitV v = true → HeldLe o o'

/-- Inclusion is reflexive. -/
theorem HeldLe.refl (a : OptionSem) : HeldLe a a := fun _ h => h
/-- Inclusion is transitive. -/
theorem HeldLe.trans {a b c : OptionSem} (h : HeldLe a b) (h' : HeldLe b c) : HeldLe a c :=
  fun v hv => h' v (h v hv)

/-- Laminar: a least admitting option exists wherever one option admits. -/
theorem laminar_least_exists : ∀ {os : List OptionSem}, AttemptDom os → Laminar os →
    ∀ {v}, (∃ o ∈ os, o.admitV v = true) → ∃ m, IsLeast os v m
  | [], _, _, _, ⟨_, h, _⟩ => nomatch h
  | x :: t, hA, hL, v, hex => by
    have hA' : AttemptDom t := fun o ho => hA o (List.mem_cons_of_mem _ ho)
    have hL' := (List.pairwise_cons.mp hL)
    cases ht : t.any (·.admitV v)
    · -- nothing in `t` admits: the head is least
      obtain ⟨o, ho, hoa⟩ := hex
      have hnt : ∀ o' ∈ t, o'.admitV v = false := by
        intro o' ho'; simpa using List.any_eq_false.mp ht o' ho'
      have hxa : x.admitV v = true := by
        rcases List.mem_cons.mp ho with rfl | ho
        · exact hoa
        · rw [hnt o ho] at hoa; exact nomatch hoa
      refine ⟨x, List.mem_cons_self, hxa, fun o' ho' ha' => ?_⟩
      rcases List.mem_cons.mp ho' with rfl | ho'
      · exact HeldLe.refl _
      · rw [hnt o' ho'] at ha'; exact nomatch ha'
    · obtain ⟨o, ho, hoa⟩ := List.any_eq_true.mp ht
      obtain ⟨m, hm, hma, hmin⟩ := laminar_least_exists hA' hL'.2 ⟨o, ho, hoa⟩
      cases hxa : x.admitV v
      · refine ⟨m, List.mem_cons_of_mem _ hm, hma, fun o' ho' ha' => ?_⟩
        rcases List.mem_cons.mp ho' with rfl | ho'
        · rw [hxa] at ha'; exact nomatch ha'
        · exact hmin o' ho' ha'
      · have hxT := (hA.admit_iff List.mem_cons_self v).mp hxa
        have hmT := (hA'.admit_iff hm v).mp hma
        rcases hL'.1 m hm with hd | hs | hs
        · exact absurd hmT (hd v hxT)
        · refine ⟨x, List.mem_cons_self, hxa, fun o' ho' ha' => ?_⟩
          rcases List.mem_cons.mp ho' with rfl | ho'
          · exact HeldLe.refl _
          · exact hs.trans (hmin o' ho' ha')
        · refine ⟨m, List.mem_cons_of_mem _ hm, hma, fun o' ho' ha' => ?_⟩
          rcases List.mem_cons.mp ho' with rfl | ho'
          · exact hs
          · exact hmin o' ho' ha'

/-- Strictly laminar: the least admitting option is unique. -/
theorem strictLaminar_least_unique : ∀ {os : List OptionSem}, AttemptDom os →
    StrictLaminar os → ∀ {v a b}, IsLeast os v a → IsLeast os v b → a = b
  | [], _, _, _, _, _, ⟨h, _⟩, _ => nomatch h
  | x :: t, hA, hS, v, a, b, ⟨ha, haa, hamin⟩, ⟨hb, hba, hbmin⟩ => by
    have hS' := List.pairwise_cons.mp hS
    have hab := hamin b hb hba
    have hba' := hbmin a ha haa
    have haT := (hA.admit_iff ha v).mp haa
    have hbT := (hA.admit_iff hb v).mp hba
    have kill : ∀ y ∈ t, (HDisj x.c.T y.c.T ∨ HeldLt x y ∨ HeldLt y x) →
        HeldLe x y → HeldLe y x → x.c.T v → y.c.T v → False := by
      intro y _ r h1 h2 hx hy
      rcases r with hd | hs | hs
      · exact hd v hx hy
      · exact hs.2 h2
      · exact hs.2 h1
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact (kill b hb' (hS'.1 b hb') hab hba' haT hbT).elim
    · exact (kill a ha' (hS'.1 a ha') hba' hab hbT haT).elim
    · have hA' : AttemptDom t := fun o ho => hA o (List.mem_cons_of_mem _ ho)
      exact strictLaminar_least_unique hA' hS'.2
        ⟨ha', haa, fun o' ho' => hamin o' (List.mem_cons_of_mem _ ho')⟩
        ⟨hb', hba, fun o' ho' => hbmin o' (List.mem_cons_of_mem _ ho')⟩

/-- A decision of inclusion, correct on the family. -/
def LeOk (le : OptionSem → OptionSem → Bool) (os : List OptionSem) : Prop :=
  ∀ a ∈ os, ∀ b ∈ os, le a b = true ↔ HeldLe a b

/-- **The `findSel` selector**, the find operation of union-find over the options: the first option that
    admits `v` and lies below each option that admits `v`. -/
def findSel (le : OptionSem → OptionSem → Bool) (os : List OptionSem) (v : Value) :
    Option OptionSem :=
  os.find? fun o => o.admitV v && os.all fun o' => !o'.admitV v || le o o'

/-- A list on which `all` fails holds a witness. `List.all_eq_false` states the same fact, and
    that lemma reaches `Classical.choice`; this induction does not. -/
theorem exists_of_all_false {α : Type} {q : α → Bool} :
    ∀ {l : List α}, l.all q = false → ∃ x ∈ l, q x = false
  | [], h => nomatch h
  | a :: l, h => by
      cases hq : q a with
      | false => exact ⟨a, List.mem_cons_self, hq⟩
      | true =>
        rw [List.all_cons, hq, Bool.true_and] at h
        obtain ⟨x, hx, hqx⟩ := exists_of_all_false h
        exact ⟨x, List.mem_cons_of_mem a hx, hqx⟩

/-- …and a witness makes `all` fail. -/
theorem all_false_of_mem {α : Type} {q : α → Bool} {l : List α} {x : α} (hx : x ∈ l)
    (hq : q x = false) : l.all q = false := by
  cases h : l.all q with
  | false => rfl
  | true => rw [List.all_eq_true.mp h x hx] at hq; exact nomatch hq

/-- `findSel` returns a least admitting option. -/
theorem findSel_isLeast {le} {os : List OptionSem} (hle : LeOk le os) {v o}
    (h : findSel le os v = some o) : IsLeast os v o := by
  have ho : o ∈ os := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hp
  refine ⟨ho, hp.1, fun o' ho' ha' => ?_⟩
  rcases hp.2 o' ho' with hn | hl
  · rw [hn] at ha'; exact nomatch ha'
  · exact (hle o ho o' ho').mp hl

/-- Where a least admitting option exists, `findSel` returns an option. -/
theorem findSel_of_least {le} {os : List OptionSem} (hle : LeOk le os) {v m}
    (hm : IsLeast os v m) : ∃ o, findSel le os v = some o := by
  cases hf : findSel le os v with
  | some o => exact ⟨o, rfl⟩
  | none =>
    have := List.find?_eq_none.mp hf m hm.1
    simp only [hm.2.1, Bool.true_and] at this
    obtain ⟨o', ho', hn⟩ := exists_of_all_false (Bool.eq_false_iff.mpr this)
    have : o'.admitV v = true ∧ le m o' = false := by
      cases h1 : o'.admitV v <;> cases h2 : le m o' <;> simp_all
    rw [(hle m hm.1 o' ho').mpr (hm.2.2 o' ho' this.1)] at this
    exact nomatch this.2

/-- **A laminar family gives a total `findSel`.** -/
theorem findSel_total {le} {os : List OptionSem} (hA : AttemptDom os) (hL : Laminar os)
    (hle : LeOk le os) : SelTotal (findSel le) os := by
  intro v hv
  obtain ⟨o, ho, hTv⟩ := held_mem hv
  obtain ⟨m, hm⟩ := laminar_least_exists hA hL ⟨o, ho, (hA.admit_iff ho v).mpr hTv⟩
  obtain ⟨o', ho'⟩ := findSel_of_least hle hm
  have hl := findSel_isLeast hle ho'
  exact ⟨o', ho', hl.1, by rw [← (hA o' hl.1).1 v]; exact hl.2.1⟩

/-- Strictly laminar: `findSel` returns the one least option, whatever the order of the list. -/
theorem findSel_wellDefined {le} {os : List OptionSem} (hA : AttemptDom os)
    (hS : StrictLaminar os) (hle : LeOk le os) {v o m} (h : findSel le os v = some o)
    (hm : IsLeast os v m) : o = m :=
  strictLaminar_least_unique hA hS (findSel_isLeast hle h) hm

/-- The find-based codec: `T` is the union's, `e` writes through `findSel`. -/
def findCodec (le : OptionSem → OptionSem → Bool) (os : List OptionSem) (μ : Option Member) :
    Codec :=
  { altCodec os μ with e := fun v => (findSel le os v).bind (·.c.e v) }

/-- On a laminar family, the `findSel` codec writes exactly its held set. -/
theorem findCodec_TIsDomE {le} {os : List OptionSem} (hA : AttemptDom os) (hL : Laminar os)
    (hle : LeOk le os) (μ) : TIsDomE (findCodec le os μ) := by
  intro v
  constructor
  · intro hv
    obtain ⟨o, hs, _, he⟩ := findSel_total hA hL hle v
      (by obtain ⟨o, ho, h⟩ := hv; exact ⟨o.c.T, List.mem_map_of_mem ho, h⟩)
    simp only [findCodec, hs, Option.bind_some]; exact he
  · intro he
    simp only [findCodec] at he
    cases hs : findSel le os v with
    | none => rw [hs] at he; exact nomatch he
    | some o =>
      rw [hs] at he
      have ho := List.mem_of_find?_eq_some hs
      exact ⟨o, ho, ((hA o ho).2 v).mpr he⟩

/-! ## The witness: a nested pair -/

noncomputable def litA : OptionSem := .byAttempt (literalCodec .string "A")
def strO : OptionSem := .byAttempt stringCodec
noncomputable def wOs : List OptionSem := [litA, strO]

/-- Inclusion decided by the one probe that separates the pair. -/
def wLe (a b : OptionSem) : Bool := b.admitV (.str "B") || !a.admitV (.str "B")

/-- `string` writes exactly its held set. -/
theorem TIsDomE_string : TIsDomE stringCodec := by
  intro v; cases v <;> simp [stringCodec]

/-- `literal "A"` writes exactly its held set. -/
theorem TIsDomE_litA : TIsDomE (literalCodec .string "A") := by
  intro v; cases v <;> simp [literalCodec, baseCodec, Codec.restrict, inL, stringCodec, HLit]

/-- The witness options admit by attempt, on their held sets. -/
theorem wOs_attemptDom : AttemptDom wOs := by
  intro o ho
  simp only [wOs, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · exact ⟨fun _ => rfl, TIsDomE_litA⟩
  · exact ⟨fun _ => rfl, TIsDomE_string⟩

/-- `literal "A"` is inside `string`. -/
theorem heldLe_litA_str : HeldLe litA strO := by
  intro v h
  simp only [litA, OptionSem.byAttempt, literalCodec, HLit] at h
  exact ⟨"A", h⟩

/-- …and `string` is not inside `literal "A"`. -/
theorem not_heldLe_str_litA : ¬ HeldLe strO litA := by
  intro h
  have := h (.str "B") ⟨"B", rfl⟩
  simp [litA, OptionSem.byAttempt, literalCodec, HLit] at this

/-- The witness pair is strictly laminar. -/
theorem wOs_strictLaminar : StrictLaminar wOs := by
  refine List.Pairwise.cons (fun y hy => ?_) (List.Pairwise.cons (fun _ h => nomatch h) .nil)
  rw [List.mem_singleton.mp hy]
  exact Or.inr (Or.inl ⟨heldLe_litA_str, not_heldLe_str_litA⟩)

/-- The witness decision of inclusion is correct on the pair. -/
theorem wLe_ok : LeOk wLe wOs := by
  intro a ha b hb
  simp only [wOs, List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact ⟨fun _ => HeldLe.refl _, fun _ => rfl⟩
  · exact ⟨fun _ => heldLe_litA_str, fun _ => rfl⟩
  · refine ⟨fun h => ?_, fun h => absurd h not_heldLe_str_litA⟩
    simp [wLe, litA, strO, OptionSem.byAttempt, literalCodec, baseCodec, Codec.restrict, inL,
      stringCodec] at h
  · exact ⟨fun _ => HeldLe.refl _, fun _ => rfl⟩

/-- `findSel` selects `literal "A"` at `"A"`. -/
theorem findSel_A : findSel wLe wOs (.str "A") = some litA := by
  simp [findSel, wOs, wLe, litA, strO, OptionSem.byAttempt, literalCodec, baseCodec,
    Codec.restrict, inL, stringCodec]

/-- …and `string` at `"B"`. -/
theorem findSel_B : findSel wLe wOs (.str "B") = some strO := by
  simp [findSel, wOs, wLe, litA, strO, OptionSem.byAttempt, literalCodec, baseCodec,
    Codec.restrict, inL, stringCodec]

/-- The find-based codec writes `"A"`. -/
theorem findCodec_writes_A : (findCodec wLe wOs (some .S)).e (.str "A") = some (.s "A") := by
  simp only [findCodec, findSel_A, Option.bind_some]
  simp [litA, OptionSem.byAttempt, literalCodec, baseCodec, Codec.restrict, inL, stringCodec]

/-- The count codec over the same options is `unionLiteralString`, and writes nothing. -/
theorem count_is_unionLiteralString : altCodec wOs (some .S) = unionLiteralString := rfl

/-- The `findSel` codec over the witness writes exactly its held set. -/
theorem findCodec_TIsDomE_witness : TIsDomE (findCodec wLe wOs (some .S)) :=
  findCodec_TIsDomE wOs_attemptDom wOs_strictLaminar.laminar wLe_ok _

/-- **The contrast.** Over one nested pair, `findSel` writes exactly its held set, and the
    count does not. -/
theorem contrast : TIsDomE (findCodec wLe wOs (some .S)) ∧ ¬ TIsDomE (altCodec wOs (some .S)) :=
  ⟨findCodec_TIsDomE_witness, count_is_unionLiteralString ▸ not_TIsDomE_unionLiteralString⟩

/-! ## The false control: a crossing pair -/

def inAB : Value → Bool | .str s => s == "A" || s == "B" | _ => false
def inBC : Value → Bool | .str s => s == "B" || s == "C" | _ => false
def ab : OptionSem := .byAttempt (stringCodec.restrict inAB)
def bc : OptionSem := .byAttempt (stringCodec.restrict inBC)
def xOs : List OptionSem := [ab, bc]

/-- The crossing options admit by attempt, on their held sets. -/
theorem xOs_attemptDom : AttemptDom xOs := by
  intro o ho
  simp only [xOs, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl <;> refine ⟨fun _ => rfl, fun v => ?_⟩ <;>
    cases v <;> simp [ab, bc, OptionSem.byAttempt, Codec.restrict, stringCodec, inAB, inBC]

/-- The crossing pair is not laminar. -/
theorem not_laminar_xOs : ¬ Laminar xOs := by
  intro h
  rcases (List.pairwise_cons.mp h).1 bc (by simp) with hd | hs | hs
  · exact hd (.str "B") ⟨⟨"B", rfl⟩, rfl⟩ ⟨⟨"B", rfl⟩, rfl⟩
  · have := (hs (.str "A") ⟨⟨"A", rfl⟩, rfl⟩).2; simp [inBC] at this
  · have := (hs (.str "C") ⟨⟨"C", rfl⟩, rfl⟩).2; simp [inAB] at this

/-- At `"B"`, the crossing pair has no least admitting option. -/
theorem no_least_xOs_B : ¬ ∃ m, IsLeast xOs (.str "B") m := by
  rintro ⟨m, hm, _, hmin⟩
  simp only [xOs, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · have := (hmin bc (by simp [xOs]) rfl (.str "A") ⟨⟨"A", rfl⟩, rfl⟩).2; simp [inBC] at this
  · have := (hmin ab (by simp [xOs]) rfl (.str "C") ⟨⟨"C", rfl⟩, rfl⟩).2; simp [inAB] at this

/-- **The crossing control.** Under each correct inclusion decision, `findSel` is not total on
    the crossing pair. -/
theorem not_selTotal_xOs {le} (hle : LeOk le xOs) : ¬ SelTotal (findSel le) xOs := by
  intro h
  obtain ⟨o, hs, _, _⟩ := h (.str "B") ⟨ab.c.T, by simp [xOs], ⟨"B", rfl⟩, rfl⟩
  exact no_least_xOs_B ⟨o, findSel_isLeast hle hs⟩

/-- …and the count selector refuses it too: both admit `"B"`. -/
theorem not_countTotal_xOs : ¬ SelTotal countSel xOs := by
  intro h
  obtain ⟨o, hs, _, _⟩ := h (.str "B") ⟨ab.c.T, by simp [xOs], ⟨"B", rfl⟩, rfl⟩
  simp [countSel, xOs, ab, bc, OptionSem.byAttempt, Codec.restrict, stringCodec, inAB, inBC]
    at hs



/-! ## First match is total on each family

Totality alone does not force laminarity. The invariant that forces laminarity is totality
and independence from the order of the options: a least admitter exists. -/

def firstSel (os : List OptionSem) (v : Value) : Option OptionSem := os.find? (·.admitV v)

/-- First match is total on each family, crossing pairs included. -/
theorem firstSel_total {os : List OptionSem} (hA : AttemptDom os) : SelTotal firstSel os := by
  intro v hv
  obtain ⟨o, ho, hTv⟩ := held_mem hv
  cases hf : firstSel os v with
  | none =>
    have := List.find?_eq_none.mp hf o ho
    rw [(hA.admit_iff ho v).mpr hTv] at this; exact nomatch this
  | some o' =>
    have hf' : os.find? (·.admitV v) = some o' := hf
    have ho' := List.mem_of_find?_eq_some hf'
    refine ⟨o', rfl, ho', ?_⟩
    have hp := List.find?_some hf'; rw [← (hA o' ho').1 v]; exact hp

/-- …at the crossing pair. -/
theorem firstSel_total_xOs : SelTotal firstSel xOs := firstSel_total xOs_attemptDom

/-! ## Cells: each option minus its strict children -/

/-- `o'` is a strict child of `o`, by the decision. -/
def child (le : OptionSem → OptionSem → Bool) (o' o : OptionSem) : Bool := le o' o && !le o o'

def cellQ (le : OptionSem → OptionSem → Bool) (os : List OptionSem) (o : OptionSem)
    (v : Value) : Bool :=
  os.all fun o' => !o'.admitV v || !child le o' o

def cell (le : OptionSem → OptionSem → Bool) (os : List OptionSem) (o : OptionSem) :
    OptionSem :=
  .byAttempt (o.c.restrict (cellQ le os o))

/-- A restriction keeps `T = dom(e)`. -/
theorem TIsDomE_restrict {c : Codec} (h : TIsDomE c) (q : Value → Bool) :
    TIsDomE (c.restrict q) := by
  intro v
  simp only [Codec.restrict]
  cases hq : q v <;> simp [h v]

/-- The cells admit by attempt, on their held sets. -/
theorem cells_attemptDom {le} {os : List OptionSem} (hA : AttemptDom os) :
    AttemptDom (os.map (cell le os)) := by
  intro c hc
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hc
  exact ⟨fun _ => rfl, TIsDomE_restrict (hA o ho).2 _⟩

/-- A value outside an option's cell is held by a strict child of the option. -/
theorem cellQ_false {le} {os : List OptionSem} (hle : LeOk le os) {o v} (ho : o ∈ os)
    (h : cellQ le os o v = false) :
    ∃ o' ∈ os, o'.admitV v = true ∧ HeldLe o' o ∧ ¬ HeldLe o o' := by
  obtain ⟨o', ho', hn⟩ := exists_of_all_false h
  have hn' : o'.admitV v = true ∧ le o' o = true ∧ le o o' = false := by
    simp only [child] at hn
    cases h1 : o'.admitV v <;> simp_all
  refine ⟨o', ho', hn'.1, (hle o' ho' o ho).mp hn'.2.1, fun hs => ?_⟩
  rw [(hle o ho o' ho').mpr hs] at hn'; exact nomatch hn'.2.2

/-- Strictly laminar: the cells are pairwise disjoint. -/
theorem cells_disjoint {le} {os : List OptionSem} (hA : AttemptDom os)
    (hS : StrictLaminar os) (hle : LeOk le os) :
    (os.map (cell le os)).Pairwise fun a b => HDisj a.c.T b.c.T := by
  rw [List.pairwise_map]
  have key : ∀ a ∈ os, ∀ b ∈ os, (HDisj a.c.T b.c.T ∨ HeldLt a b ∨ HeldLt b a) →
      HDisj (cell le os a).c.T (cell le os b).c.T := by
    intro a ha b hb r v hav hbv
    simp only [cell, OptionSem.byAttempt, Codec.restrict] at hav hbv
    rcases r with hd | hs | hs
    · exact hd v hav.1 hbv.1
    · -- `a` is a strict child of `b` and holds `v`, so `b`'s cell drops `v`
      have : cellQ le os b v = false := by
        unfold cellQ
        refine all_false_of_mem ha ?_
        simp [child, (hA.admit_iff ha v).mpr hav.1, (hle a ha b hb).mpr hs.1,
          show le b a = false from by
            cases h : le b a
            · rfl
            · exact absurd ((hle b hb a ha).mp h) hs.2]
      rw [this] at hbv; exact nomatch hbv.2
    · have : cellQ le os a v = false := by
        unfold cellQ
        refine all_false_of_mem hb ?_
        simp [child, (hA.admit_iff hb v).mpr hbv.1, (hle b hb a ha).mpr hs.1,
          show le a b = false from by
            cases h : le a b
            · rfl
            · exact absurd ((hle a ha b hb).mp h) hs.2]
      rw [this] at hav; exact nomatch hav.2
  -- `Pairwise.imp` with membership, by hand
  have gen : ∀ l : List OptionSem, (∀ x ∈ l, x ∈ os) →
      l.Pairwise (fun a b => HDisj a.c.T b.c.T ∨ HeldLt a b ∨ HeldLt b a) →
      l.Pairwise (fun a b => HDisj (cell le os a).c.T (cell le os b).c.T) := by
    intro l
    induction l with
    | nil => intro _ _; exact .nil
    | cons x t ih =>
      intro hm hp
      have hp' := List.pairwise_cons.mp hp
      exact List.Pairwise.cons
        (fun y hy => key x (hm x List.mem_cons_self) y (hm y (List.mem_cons_of_mem _ hy))
          (hp'.1 y hy))
        (ih (fun y hy => hm y (List.mem_cons_of_mem _ hy)) hp'.2)
  exact gen os (fun _ h => h) hS

/-- The least option's cell holds `v`. -/
theorem cell_of_least {le} {os : List OptionSem} (hle : LeOk le os) {v o}
    (hm : IsLeast os v o) : cellQ le os o v = true := by
  cases h : cellQ le os o v with
  | true => rfl
  | false =>
    obtain ⟨o', ho', ha', _, hn⟩ := cellQ_false hle hm.1 h
    exact absurd (hm.2.2 o' ho' ha') hn

/-- **Nested unions normalize to cells.** On a strictly laminar family, the count selector
    over the cells writes what `findSel` writes over the options. So `findSel` needs no new
    core semantics: the cells are a union that the count selector already totals. -/
theorem cells_count_eq_find {le} {os : List OptionSem} (hA : AttemptDom os)
    (hS : StrictLaminar os) (hle : LeOk le os) (μ : Option Member) (v : Value) :
    (altCodec (os.map (cell le os)) μ).e v = (findCodec le os μ).e v := by
  rw [altCodec_e_countSel]
  simp only [findCodec]
  have hAc := cells_attemptDom (le := le) hA
  cases hf : findSel le os v with
  | some o =>
    have hm := findSel_isLeast hle hf
    have hq := cell_of_least hle hm
    have hTo := (hA.admit_iff hm.1 v).mp hm.2.1
    have hmem : cell le os o ∈ os.map (cell le os) := List.mem_map_of_mem hm.1
    have hcT : (cell le os o).c.T v := ⟨hTo, hq⟩
    have hfl : (os.map (cell le os)).filter (·.admitV v) = [cell le os o] :=
      singleton_of_disj ((cells_disjoint hA hS hle).sublist List.filter_sublist)
        (fun x hx => by
          have hx' := List.mem_filter.mp hx
          exact (hAc.admit_iff hx'.1 v).mp hx'.2)
        (List.mem_filter.mpr ⟨hmem, (hAc.admit_iff hmem v).mpr hcT⟩)
    simp only [countSel, hfl, Option.bind_some]
    simp [cell, OptionSem.byAttempt, Codec.restrict, hq]
  | none =>
    simp only [Option.bind_none]
    unfold countSel
    generalize hl : (os.map (cell le os)).filter (·.admitV v) = l
    rcases l with _ | ⟨c, _ | _⟩
    · rfl
    · have hc : c ∈ (os.map (cell le os)).filter (·.admitV v) := by rw [hl]; exact List.mem_singleton_self c
      have hc' := List.mem_filter.mp hc
      obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hc'.1
      have hcT := (hAc.admit_iff hc'.1 v).mp hc'.2
      obtain ⟨m, hm⟩ := laminar_least_exists hA hS.laminar ⟨o, ho, (hA.admit_iff ho v).mpr hcT.1⟩
      obtain ⟨o', ho'⟩ := findSel_of_least hle hm
      rw [hf] at ho'; exact nomatch ho'
    · rfl

/-! ## (B) under (D): the held set is the admission -/

/-- A term whose every held set is its admission. The induction hypothesis of `typed_T_adm`. -/
def AdmIff (t : Term) : Prop := ∀ T μ, Typed t T μ → ∀ v, T v ↔ Adm t v = true

/-- The rows of a term list are as many as the terms. -/
theorem AdmList_length (ts : List Term) : (AdmList ts).length = ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ihx => simp only [AdmList, List.length_cons, ihx]

/-- A spread holds a list exactly where the spread's row admits each element. -/
theorem htuple_nil_some_iff {t : Term} {T : Held} {μ} (hty : Typed t T μ) (ih : AdmIff t) :
    ∀ vs, HTuple [] (some T) vs ↔ alignP [] (some (Adm t)) vs = true
  | [] => by simp [HTuple, alignP]
  | x :: xs => by
      have := htuple_nil_some_iff hty ih xs
      simp only [HTuple, alignP, Bool.and_eq_true, List.forall_mem_cons] at this ⊢
      rw [ih _ _ hty x, this]

/-- `HTuple` is `alignP` at terms whose held sets are their admissions. -/
theorem htuple_iff {tail : Option Term} {Tt} (hopt : TypedOpt tail Tt)
    (iht : ∀ t' ∈ tail, AdmIff t') :
    ∀ {ts Ts}, TypedList ts Ts → (∀ t' ∈ ts, AdmIff t') →
      ∀ vs, HTuple Ts Tt vs ↔ alignP (AdmList ts) (AdmOptT tail) vs = true
  | _, _, .nil, _, vs => by
      cases hopt with
      | none => cases vs <;> simp [HTuple, alignP, AdmList, AdmOptT]
      | some hty => exact htuple_nil_some_iff hty (iht _ rfl) vs
  | _, _, .cons _ _, _, [] => by simp [HTuple, alignP, AdmList]
  | _, _, .cons hty hs, ih, v :: vs => by
      simp only [HTuple, AdmList, alignP, Bool.and_eq_true]
      rw [ih _ List.mem_cons_self _ _ hty v,
        htuple_iff hopt iht hs (fun t' h => ih t' (List.mem_cons_of_mem _ h)) vs]

/-- The suffix's held set is `zipP` at terms whose held sets are their admissions. -/
theorem zip_iff : ∀ {ts Ts}, TypedList ts Ts → (∀ t' ∈ ts, AdmIff t') →
    ∀ back, List.Forall₂ (fun (T : Held) v => T v) Ts back ↔ zipP (AdmList ts) back = true
  | _, _, .nil, _, [] => by simp [AdmList, zipP]
  | _, _, .nil, _, _ :: _ => by simp [AdmList, zipP]
  | _, _, .cons _ _, _, [] => by simp [AdmList, zipP]
  | _, _, .cons hty hs, ih, v :: vs => by
      simp only [List.forall₂_cons, AdmList, zipP, Bool.and_eq_true]
      rw [ih _ List.mem_cons_self _ _ hty v,
        zip_iff hs (fun t' h => ih t' (List.mem_cons_of_mem _ h)) vs]

/-- `HTupleL` is `alignPL` at terms whose held sets are their admissions. -/
theorem htupleL_iff {pre Tpre sp Tsp suf Tsuf} (hp : TypedList pre Tpre)
    (hs : TypedOpt sp Tsp) (hf : TypedList suf Tsuf)
    (ihp : ∀ t' ∈ pre, AdmIff t') (ihs : ∀ t' ∈ sp, AdmIff t') (ihf : ∀ t' ∈ suf, AdmIff t')
    (vs : List Value) :
    HTupleL Tpre Tsp Tsuf vs ↔ alignPL (AdmList pre) (AdmOptT sp) (AdmList suf) vs = true := by
  have hlen : (AdmList suf).length = Tsuf.length := by
    rw [AdmList_length, TypedList.length_eq hf]
  constructor
  · rintro ⟨front, back, rfl, hback, hfront⟩
    have hb : back.length = Tsuf.length := hback.length_eq.symm
    have hn : (front ++ back).length - (AdmList suf).length = front.length := by
      rw [hlen, List.length_append, hb]; omega
    simp only [alignPL, hn, List.take_left', List.drop_left', Bool.and_eq_true]
    exact ⟨(htuple_iff hs ihs hp ihp front).mp hfront, (zip_iff hf ihf back).mp hback⟩
  · intro h
    simp only [alignPL, Bool.and_eq_true] at h
    exact ⟨_, _, (List.take_append_drop _ vs).symm, (zip_iff hf ihf _).mpr h.2,
      (htuple_iff hs ihs hp ihp _).mpr h.1⟩

/-- A typed slot's mark is the slot's, and its held set is its admission. -/
theorem typedField_adm {s : ObjectSlot} {T b μ} (h : TypedField s T b μ)
    (ihr : ∀ t', s = .req t' → AdmIff t') (iho : ∀ t', s = .optional t' → AdmIff t') :
    b = s.isReq ∧ ∀ v, T v ↔ AdmField s v = true := by
  cases h with
  | req hty => exact ⟨rfl, fun v => ihr _ rfl _ _ hty v⟩
  | optional hty => exact ⟨rfl, fun v => iho _ rfl _ _ hty v⟩

/-- `HObject` is `AdmBody` at slots and an open block whose held sets are their admissions. -/
theorem hobject_iff {fields : Finset Name} {ff : {k // k ∈ fields} → ObjectSlot}
    {wild : Option Term} {bind : {k // k ∈ fields} → Bool × Held} {R : Option Held}
    {μs : {k // k ∈ fields} → Option Member}
    (hfields : ∀ k, TypedField (ff k) (bind k).2 (bind k).1 (μs k))
    (ihr : ∀ k t', ff k = .req t' → AdmIff t') (iho : ∀ k t', ff k = .optional t' → AdmIff t')
    (hrest : TypedWild wild R) (ihw : ∀ t', wild = some t' → AdmIff t') (v : Value) :
    HObject fields bind R v ↔ AdmBody (.mk fields ff wild) v = true := by
  have hF := fun k => typedField_adm (hfields k) (ihr k) (iho k)
  cases v with
  | map keys f =>
    simp only [AdmBody, Bool.and_eq_true, valPresentT_req, objAdmV, decide_eq_true_eq]
    have hpres : (∀ k : {k // k ∈ fields}, (bind k).1 = true → k.1 ∈ keys) ↔
        (∀ k : {k // k ∈ fields}, ObjectSlot.isReq (ff k) = true → k.1 ∈ keys) :=
      forall_congr' fun k => by rw [(hF k).1]
    have hent : ∀ k : {k // k ∈ keys},
        (if h : k.1 ∈ fields then (bind ⟨k.1, h⟩).2 (f k) else ∃ T, R = some T ∧ T (f k)) ↔
        (match entryP ⟨fields, fun k => AdmField (ff k)⟩ (AdmWild wild) k.1 with
          | some P => P (f k) | none => false) = true := by
      intro k
      rcases Decidable.em (k.1 ∈ fields) with hk | hk
      · rw [dif_pos hk]
        simp only [entryP, MapOf.at, dif_pos hk]
        exact (hF ⟨k.1, hk⟩).2 _
      · rw [dif_neg hk]
        simp only [entryP, MapOf.at, dif_neg hk]
        cases hrest with
        | none => exact ⟨fun ⟨_, h, _⟩ => (nomatch h), fun h => (nomatch h)⟩
        | @some t' T' μ' hty =>
          simp only [AdmWild, Option.some.injEq, exists_eq_left']
          exact ihw t' rfl _ _ hty _
    constructor
    · rintro ⟨keys', f', heq, hreq, hall⟩
      cases heq
      exact ⟨hpres.mp hreq, fun k => (hent k).mp (hall k)⟩
    · rintro ⟨hreq, hall⟩
      exact ⟨keys, f, rfl, hpres.mpr hreq, fun k => (hent k).mpr (hall k)⟩
  | _ => simp [HObject, AdmBody]

/-- A set base holds exactly what the base admits. -/
theorem setBase_held_adm (b : SetBase) (v : Value) : b.held v ↔ b.adm v = true := by
  cases b <;> cases v <;> simp [SetBase.held, SetBase.adm, inD]

/-- `HSet` is the set row of `Adm`. -/
theorem hset_iff (b : SetBase) (v : Value) : HSet b.held v ↔ Adm (.set b) v = true := by
  cases v with
  | strSet S => simp [HSet, Adm, setBase_held_adm]
  | numSet S => simp [HSet, Adm, setBase_held_adm]
  | binSet S => simp [HSet, Adm, setBase_held_adm]
  | _ => simp [HSet, Adm]

/-- An element of a list is no deeper than the list budget. -/
theorem depth_le_depthL {x : Value} : ∀ {vs : List Value}, x ∈ vs → Value.depth x ≤ Value.depthL vs
  | _ :: _, .head _ => by simp only [Value.depthL]; omega
  | _ :: _, .tail _ h => by have := depth_le_depthL h; simp only [Value.depthL]; omega

/-- `HOpaque` is `opaque`'s admission: each value is in `HOpaque`, and `opaque` writes each value. -/
theorem hopaque_adm (v : Value) : HOpaque v ↔ Adm .opaq v = true := by
  constructor
  · intro h
    induction h with
    | str s => show ((opaqCodec 1).e (.str s)).isSome = true; rw [opaqCodec_e_str 0]; simp [stringCodec]
    | bool b => show ((opaqCodec 1).e (.bool b)).isSome = true; rw [opaqCodec_e_bool 0]; simp [booleanCodec]
    | bin b => show ((opaqCodec 1).e (.bin b)).isSome = true; rw [opaqCodec_e_bin 0]; simp [binaryCodec]
    | null => show ((opaqCodec 1).e .null).isSome = true; rw [opaqCodec_e_null 0]; simp [nullCodec]
    | num d => show ((opaqCodec 1).e (.num d)).isSome = true; rw [opaqCodec_e_num 0]; simp [numberCodec]
    | strSet S _ _ =>
      show ((opaqCodec 2).e (.strSet S)).isSome = true
      rw [opaqCodec_e_strSet 1]
      show (encSet (opaqCodec 1) Value.str S).isSome = true
      rw [encSet_congr (d := SetBase.string.elem) (fun x _ => opaqCodec_e_str 0 x)]
      exact (Adm_exact (.set .string) (.strSet S)).mp (by simp [Adm, SetBase.adm])
    | numSet S _ _ =>
      show ((opaqCodec 2).e (.numSet S)).isSome = true
      rw [opaqCodec_e_numSet 1]
      show (encSet (opaqCodec 1) Value.num S).isSome = true
      rw [encSet_congr (d := SetBase.number.elem) (fun x _ => opaqCodec_e_num 0 x)]
      exact (Adm_exact (.set .number) (.numSet S)).mp (by simp [Adm, SetBase.adm, inD])
    | binSet S _ _ =>
      show ((opaqCodec 2).e (.binSet S)).isSome = true
      rw [opaqCodec_e_binSet 1]
      show (encSet (opaqCodec 1) Value.bin S).isSome = true
      rw [encSet_congr (d := SetBase.binary.elem) (fun x _ => opaqCodec_e_bin 0 x)]
      exact (Adm_exact (.set .binary) (.binSet S)).mp (by simp [Adm, SetBase.adm])
    | arr vs _ ih =>
      show ((opaqCodec (Value.depthL vs + 1)).e (.arr vs)).isSome = true
      rw [opaqCodec_e_arr]
      show ((traverse (opaqCodec (Value.depthL vs)).e vs).map Attr.l).isSome = true
      rw [Option.isSome_map, traverse_isSome_iff]
      intro x hx
      have := ih x hx
      change ((opaqCodec (Value.depth x)).e x).isSome = true at this
      rwa [opaq_e_agree x _ _ (Nat.le_refl _) (depth_le_depthL hx)] at this
    | map keys f _ ih =>
      obtain ⟨n, hn⟩ : ∃ n, Value.depth (.map keys f) = n + 1 := ⟨_, rfl⟩
      show ((opaqCodec (Value.depth (.map keys f))).e _).isSome = true
      rw [hn, opaqCodec_e_map]
      show ((funImage fun k => (opaqCodec n).e (f k)).map (Attr.m keys)).isSome = true
      rw [Option.isSome_map, funImage_isSome_iff]
      intro k
      have := ih k
      have hd := Value.depth_map_entry (f := f) k
      change ((opaqCodec (Value.depth (f k))).e (f k)).isSome = true at this
      rwa [opaq_e_agree (f k) (Value.depth (f k)) n (Nat.le_refl _) (by omega)] at this
  · intro h
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h
    exact (opaq_T_identity v).mp (carrier_opaqCodecω.domE ha)

/-- Under (D), a union option holds a value exactly where the option admits the value, and
    at most one option admits each value. -/
theorem union_count : ∀ {opts : List Term} {Ts μs}, TypedListμ opts Ts μs →
    (∀ t ∈ opts, AdmIff t) → DIncomp Ts → ∀ v,
      ((∃ T ∈ Ts, T v) ↔ ∃ x ∈ AdmSpecs opts, x.2 v = true) ∧
      ((AdmSpecs opts).filter (fun o => admitOptV o v)).length ≤ 1
  -- by hand: `simp` closes `∃ T ∈ [], T v` through the classical `Nonempty` instance of `Held`
  | _, _, _, .nil, _, _, v =>
      ⟨⟨fun ⟨_, h, _⟩ => absurd h List.not_mem_nil, fun ⟨_, h, _⟩ => absurd h (by simp [AdmSpecs])⟩,
        by simp [AdmSpecs]⟩
  | _, _, _, @TypedListμ.cons t ts _ _ _ _ hty hs, ih, hD, v => by
      have hD' := List.pairwise_cons.mp hD
      have ⟨hi, hl⟩ := union_count hs (fun t' h => ih t' (List.mem_cons_of_mem _ h)) hD'.2 v
      have hT := ih _ List.mem_cons_self _ _ hty v
      refine ⟨?_, ?_⟩
      · simp only [List.mem_cons, exists_eq_or_imp, AdmSpecs]
        rw [hT, hi]
      · simp only [AdmSpecs, List.filter_cons, admitOptV] at hl ⊢
        rcases Bool.eq_false_or_eq_true (Adm t v) with ha | ha
        · have hnil : (AdmSpecs ts).filter (fun o => o.2 v) = [] := by
            refine filter_nil_of fun x hx => Bool.eq_false_iff.mpr fun hxv => ?_
            obtain ⟨T', hT', hT'v⟩ := hi.mpr ⟨x, hx, hxv⟩
            exact hD'.1 T' hT' v (hT.mpr ha) hT'v
          rw [if_pos ha, hnil]; simp
        · rw [if_neg (by rw [ha]; exact Bool.false_ne_true)]; exact hl

/-- Under (D), the union's held set is the count row of `Adm`. -/
theorem hunion_iff {opts Ts μs} (h : TypedListμ opts Ts μs) (hD : DIncomp Ts)
    (ih : ∀ t ∈ opts, AdmIff t) (v : Value) :
    HUnion Ts v ↔ selOptV (AdmSpecs opts) v = true := by
  have ⟨hi, hl⟩ := union_count h ih hD v
  unfold selOptV HUnion
  constructor
  · intro hv
    obtain ⟨x, hx, hxv⟩ := hi.mp hv
    have hxf : x ∈ (AdmSpecs opts).filter (fun o => admitOptV o v) :=
      List.mem_filter.mpr ⟨hx, hxv⟩
    generalize (AdmSpecs opts).filter (fun o => admitOptV o v) = L at hxf hl
    rcases L with _ | ⟨y, _ | ⟨z, L⟩⟩
    · exact nomatch hxf
    · obtain rfl := List.mem_singleton.mp hxf; exact hxv
    · simp at hl
  · intro hs
    generalize hL : (AdmSpecs opts).filter (fun o => admitOptV o v) = L at hs
    rcases L with _ | ⟨y, _ | ⟨z, L⟩⟩
    · exact nomatch hs
    · have hy : y ∈ (AdmSpecs opts).filter (fun o => admitOptV o v) := by
        rw [hL]; exact List.mem_singleton_self y
      exact hi.mpr ⟨y, (List.mem_filter.mp hy).1, hs⟩
    · exact nomatch hs

-- the shared `term_depth_wf` block has alternatives this theorem's goals do not use
set_option linter.unreachableTactic false in
/-- **(B): the held set is the admission, at every rule.** A derivable term holds exactly the
    values it admits, so `T = dom(e)` by `Adm_exact`. The union row is the one that needs (D):
    the count selector writes each held value only because no value is held by two options.
    Under the incomparable reading of (D), `union(literal "A", string)` held `"A"` and wrote
    nothing. The rule now refuses that union, so the index is exact and not an upper bound. -/
theorem typed_T_adm : ∀ {t T μ}, Typed t T μ → ∀ v, T v ↔ Adm t v = true
  | t, T, μ, h, v => by
    cases h with
    | string => cases v <;> simp [Adm]
    | number => cases v <;> simp [Adm, inD]
    | boolean => cases v <;> simp [Adm]
    | binary => cases v <;> simp [Adm]
    | null => cases v <;> simp [Adm]
    | literal k x => cases k <;> cases v <;> simp [HLit, Adm, AdmLit, inL, GroundKind.toValue]
    | never => simp [HNever, Adm]
    | opaq => exact hopaque_adm v
    | set b => exact hset_iff b v
    | @list pre Tpre sp Tsp suf Tsuf hp hs hf =>
      cases v with
      | arr vs =>
        simp only [HList, Adm, Value.arr.injEq, exists_eq_left']
        exact htupleL_iff hp hs hf
          (fun t' _ _ _ hty w => typed_T_adm hty w)
          (fun t' _ _ _ hty w => typed_T_adm hty w)
          (fun t' _ _ _ hty w => typed_T_adm hty w) vs
      | _ => simp [HList, Adm]
    | @held t' I' μ' f g h' => exact typed_T_adm h' (f v)
    | @refine t' T' μ' q h' =>
      show (T' v ∧ q.eval v = true) ↔ (Adm t' v && q.eval v) = true
      rw [Bool.and_eq_true, typed_T_adm h' v]
    | @lazy t' T' μ' h' => exact typed_T_adm h' v
    | @object body bind R μs hfields hrest =>
      cases body with | mk fields ff wild =>
      simp only [Body.fields_mk, Body.at_mk, Body.wild_mk] at hfields hrest ⊢
      exact hobject_iff hfields
        (fun k t' _ _ _ hty w => typed_T_adm hty w)
        (fun k t' _ _ _ hty w => typed_T_adm hty w)
        hrest (fun t' _ _ _ hty w => typed_T_adm hty w) v
    | @union opts Ts μs h' hD =>
      exact hunion_iff h' hD (fun t' _ _ _ hty w => typed_T_adm hty w) v
termination_by t _ _ _ _ => Term.depth t
decreasing_by term_depth_wf


/-- A held set of the option judgements is some option's own. -/
theorem mem_typed_of_mem : ∀ {os : List Term} {Ts μs}, TypedListμ os Ts μs →
    ∀ T ∈ Ts, ∃ t ∈ os, ∃ μ, Typed t T μ
  | _, _, _, .nil, _, hT => nomatch hT
  | _, _, _, .cons hty hs, T, hT => by
    rcases List.mem_cons.mp hT with rfl | hT'
    · exact ⟨_, List.mem_cons_self, _, hty⟩
    · obtain ⟨t', ht', μ', hty'⟩ := mem_typed_of_mem hs T hT'
      exact ⟨t', List.mem_cons_of_mem _ ht', μ', hty'⟩

/-- Two terms that admit no common value. -/
def AdmDisj (a b : Term) : Prop := ∀ v, Adm a v = true → Adm b v = false

/-- The options of a derivable union are pairwise disjoint on admission. -/
theorem admDisj_of_typed : ∀ {os : List Term} {Ts μs}, TypedListμ os Ts μs → DIncomp Ts →
    os.Pairwise AdmDisj
  | _, _, _, .nil, _ => .nil
  | _, _, _, .cons hty hs, hD => by
    have hD' := List.pairwise_cons.mp hD
    refine .cons (fun t' ht' v hv => ?_) (admDisj_of_typed hs hD'.2)
    obtain ⟨T', hT', μ', hty'⟩ := TypedListμ.mem hs t' ht'
    cases h : Adm t' v with
    | false => rfl
    | true =>
      exact absurd ((typed_T_adm hty' v).mpr h)
        (hD'.1 T' hT' v ((typed_T_adm hty v).mpr hv))

/-- Options that are pairwise disjoint on admission satisfy (D). -/
theorem dincomp_of_admDisj : ∀ {ss : List Term} {Ts μs}, TypedListμ ss Ts μs →
    ss.Pairwise AdmDisj → DIncomp Ts
  | _, _, _, .nil, _ => .nil
  | _, _, _, .cons hty hs, hd => by
    have hd' := List.pairwise_cons.mp hd
    refine .cons (fun T' hT' v hv hv' => ?_) (dincomp_of_admDisj hs hd'.2)
    obtain ⟨t', ht', μ', hty'⟩ := mem_typed_of_mem hs T' hT'
    have := hd'.1 t' ht' v ((typed_T_adm hty v).mp hv)
    rw [(typed_T_adm hty' v).mp hv'] at this
    exact nomatch this

/-- A `Forall₂` relates every right element to some left one. -/
theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs → ∀ {b}, b ∈ bs → ∃ a ∈ as, R a b
  | _, _, .nil, _, hb => by simp at hb
  | _, _, .cons hr hrest, b, hb => by
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact ⟨_, List.mem_cons_self, hr⟩
      · obtain ⟨a, ha, hra⟩ := forall₂_mem_right hrest hb'
        exact ⟨a, List.mem_cons_of_mem _ ha, hra⟩

/-- Disjointness on admission survives a shrink of each option. -/
theorem admDisj_shrink : ∀ {os zs : List Term},
    List.Forall₂ (fun t w => ∀ v, Adm w v = true → Adm t v = true) os zs →
    os.Pairwise AdmDisj → zs.Pairwise AdmDisj
  | _, _, .nil, _ => .nil
  | _, _, .cons hr hs, hd => by
    have hd' := List.pairwise_cons.mp hd
    refine .cons (fun w' hw' v hv => ?_) (admDisj_shrink hs hd'.2)
    obtain ⟨t', ht', hr'⟩ := forall₂_mem_right hs hw'
    cases h : Adm w' v with
    | false => rfl
    | true =>
      have := hd'.1 t' ht' v (hr v hv)
      rw [hr' v h] at this
      exact nomatch this

/-- **The meet keeps (D).** The meet at a union shrinks each option: each survivor admits
    only what its option admits. The options are pairwise disjoint on admission, so the
    survivors are too, and each survivor is derivable. -/
theorem survivors {os zs ss : List Term} (hy : ∃ T μ, Typed (.union os) T μ)
    (hA : List.Forall₂ (fun t w => ∀ v, Adm w v = true → Adm t v = true) os zs)
    (hT : List.Forall₂ (fun t w => (∃ T μ, Typed t T μ) → ∃ T μ, Typed w T μ) os zs)
    (hs : ss.Sublist zs) : ss.Pairwise AdmDisj ∧ ∀ w ∈ ss, ∃ T μ, Typed w T μ := by
  obtain ⟨T, μ, hty⟩ := hy
  cases hty with
  | union hL hD =>
    refine ⟨(admDisj_shrink hA (admDisj_of_typed hL hD)).sublist hs, fun w hw => ?_⟩
    obtain ⟨t, ht, hr⟩ := forall₂_mem_right hT (hs.subset hw)
    obtain ⟨T', -, μ', hty'⟩ := TypedListμ.mem hL t ht
    exact hr ⟨T', μ', hty'⟩

/-- The left conjunct of an admission equation. -/
theorem adm_left_of_and {a b c : Bool} (h : a = (b && c)) (ha : a = true) : b = true := by
  rw [h, Bool.and_eq_true] at ha; exact ha.1

/-- The right conjunct of an admission equation. -/
theorem adm_right_of_and {a b c : Bool} (h : a = (b && c)) (ha : a = true) : c = true := by
  rw [h, Bool.and_eq_true] at ha; exact ha.2

end Calculus
