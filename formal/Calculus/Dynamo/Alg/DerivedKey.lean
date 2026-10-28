import Calculus.Dynamo.Alg.Codec

/-!
# The derived key as a codec

A derived key is the word of the segments that the components of the item print, joined by one
separator into one `S` attribute. This file states the key as a codec of the model, from the list
of segments to the string, and states the facts that the host builder relies on.

A segment is a string. The separator is one character. The join is injective on the segment
lists that have a segment and hold no separator, and the read splits at the separator. So the key
codec is lawful on those lists, and the laws of the model then cover the parse of a key. A segment
list that holds the separator breaks the write at two values that print one key, and no codec with
that write is lawful.

A partial key is the print of the first segments with a trailing separator. A prefix match on it
selects exactly the items that agree on those segments. The same match without the trailing
separator selects more.

The builder of the host prints each component as a word of segments: a name and a value, a tag
and a value, or a value alone. The model states the three shapes, the absent value, and the
boundary. The host appends the boundary where the print stops before the last component, which
`boundary` states. The count of components decides it, and the count of segments does not.

The multi-character separator, the print of a component that is not a string, and the encoding of
a string into the attribute are outside the model.
-/

namespace Calculus

namespace DerivedKey

/-! ## The word -/

/-- The key of a segment list: the segments, one separator between two neighbours. The empty list
    and the list of one empty segment print the same word, so the codec below holds the lists that
    have a segment. -/
def join (c : Char) : List (List Char) → List Char
  | [] => []
  | [s] => s
  | s :: t :: r => s ++ c :: join c (t :: r)

/-- The read of a key: the segments between the separators. The word with no separator is one
    segment, and the empty word is one empty segment. -/
def split (c : Char) : List Char → List (List Char)
  | [] => [[]]
  | x :: r =>
      if x = c then [] :: split c r
      else
        match split c r with
        | s :: ss => (x :: s) :: ss
        | [] => [[x]]

/-- No segment of the list holds the separator. -/
def NoSep (c : Char) (ss : List (List Char)) : Prop := ∀ s ∈ ss, c ∉ s

/-- The read of a key gives at least one segment. -/
theorem split_ne_nil (c : Char) : ∀ l : List Char, split c l ≠ []
  | [] => by simp [split]
  | x :: r => by
      have ih := split_ne_nil c r
      rcases Decidable.em (x = c) with h | h
      · simp [split, h]
      · cases hs : split c r with
        | nil => exact absurd hs ih
        | cons s ss => simp [split, h, hs]

/-- The word of a segment list that holds no separator, then the separator, then the rest, reads
    as that segment and the read of the rest. -/
theorem split_append (c : Char) :
    ∀ {s : List Char} (l : List Char), c ∉ s → split c (s ++ c :: l) = s :: split c l
  | [], l, _ => by simp [split]
  | x :: s, l, h => by
      have hx : x ≠ c := fun e => h (e ▸ List.mem_cons_self)
      have hs : c ∉ s := fun e => h (List.mem_cons_of_mem _ e)
      have ih := split_append c l hs
      simp [split, hx, ih]

/-- A word with no separator is one segment. -/
theorem split_of_notMem (c : Char) : ∀ {s : List Char}, c ∉ s → split c s = [s]
  | [], _ => by simp [split]
  | x :: s, h => by
      have hx : x ≠ c := fun e => h (e ▸ List.mem_cons_self)
      have hs : c ∉ s := fun e => h (List.mem_cons_of_mem _ e)
      simp [split, hx, split_of_notMem c hs]

/-- The read of a key holds no separator in a segment. -/
theorem split_noSep (c : Char) : ∀ l : List Char, NoSep c (split c l)
  | [] => by simp [split, NoSep]
  | x :: r => by
      have ih := split_noSep c r
      rcases Decidable.em (x = c) with h | h
      · intro s hs
        simp only [split, h, if_true, List.mem_cons] at hs
        rcases hs with rfl | hs
        · simp
        · exact ih s hs
      · cases hs : split c r with
        | nil => exact absurd hs (split_ne_nil c r)
        | cons s ss =>
            intro t ht
            simp only [split, h, if_false, hs, List.mem_cons] at ht
            rcases ht with rfl | ht
            · have := ih s (by simp [hs])
              simp [Ne.symm h, this]
            · exact ih t (by simp [hs, ht])

/-- **The join of the read is the word.** The read followed by the write gives back each key. -/
theorem join_split (c : Char) : ∀ l : List Char, join c (split c l) = l
  | [] => by simp [split, join]
  | x :: r => by
      have ih := join_split c r
      rcases Decidable.em (x = c) with h | h
      · cases hs : split c r with
        | nil => exact absurd hs (split_ne_nil c r)
        | cons s ss =>
            have : join c ([] :: s :: ss) = c :: join c (s :: ss) := by simp [join]
            simp only [split, h, if_true, hs] at ih ⊢
            rw [this, ih]
      · cases hs : split c r with
        | nil => exact absurd hs (split_ne_nil c r)
        | cons s ss =>
            simp only [split, h, if_false, hs] at ih ⊢
            cases ss with
            | nil => simp [join] at ih ⊢; rw [ih]
            | cons t ts => simp [join] at ih ⊢; rw [ih]

/-- **The read of the join is the segment list**, where the list has a segment and no segment holds
    the separator. -/
theorem split_join (c : Char) :
    ∀ ss : List (List Char), ss ≠ [] → NoSep c ss → split c (join c ss) = ss
  | [], h, _ => absurd rfl h
  | [s], _, hn => by simpa [join] using split_of_notMem c (hn s (by simp))
  | s :: t :: r, _, hn => by
      have hs : c ∉ s := hn s (by simp)
      have ht : NoSep c (t :: r) := fun u hu => hn u (List.mem_cons_of_mem _ hu)
      simp only [join]
      rw [split_append c _ hs, split_join c (t :: r) (by simp) ht]

/-- **The write is injective where no segment holds the separator.** Two segment lists with a
    segment each that print one word are one list. -/
theorem join_injective (c : Char) :
    ∀ {a b : List (List Char)}, a ≠ [] → b ≠ [] → NoSep c a → NoSep c b →
      join c a = join c b → a = b := by
  intro a b ha hb hna hnb h
  have := congrArg (split c) h
  rwa [split_join c a ha hna, split_join c b hb hnb] at this

/-! ## A collision where a segment holds the separator -/

/-- **A segment that holds the separator prints as two.** The lists `[a#b]` and `[a, b]` print one
    word at the separator `#`. -/
theorem join_collision :
    join '#' [['a', '#', 'b']] = join '#' [['a'], ['b']] := by decide

/-- **The empty list and the list of one empty segment print one word.** The two are different
    lists, so the codec holds the lists that have a segment. -/
theorem join_empty_collision (c : Char) : join c [] = join c [[]] := rfl

/-! ## The prefix law -/

/-- A prefix of a word with a separator, where neither side holds the separator before it, is the
    segment and a prefix of the rest. -/
theorem prefix_segment (c : Char) :
    ∀ {s t : List Char} {x y : List Char}, c ∉ s → c ∉ t →
      (s ++ c :: x) <+: (t ++ c :: y) → s = t ∧ x <+: y
  | [], t, x, y, _, ht, h => by
      cases t with
      | nil => exact ⟨rfl, by simpa using h⟩
      | cons b t =>
          obtain ⟨z, hz⟩ := h
          simp only [List.nil_append, List.cons_append, List.cons.injEq] at hz
          exact absurd (by simp [hz.1.symm]) ht
  | a :: s, t, x, y, hs, ht, h => by
      cases t with
      | nil =>
          obtain ⟨z, hz⟩ := h
          simp only [List.nil_append, List.cons_append, List.cons.injEq] at hz
          exact absurd (by simp [hz.1]) hs
      | cons b t =>
          obtain ⟨z, hz⟩ := h
          simp only [List.cons_append, List.cons.injEq] at hz
          obtain ⟨hab, hz⟩ := hz
          subst hab
          have hs' : c ∉ s := fun e => hs (List.mem_cons_of_mem _ e)
          have ht' : c ∉ t := fun e => ht (List.mem_cons_of_mem _ e)
          have h' : (s ++ c :: x) <+: (t ++ c :: y) := ⟨z, by simpa [List.append_assoc] using hz⟩
          obtain ⟨rfl, hxy⟩ := prefix_segment c hs' ht' h'
          exact ⟨rfl, hxy⟩

/-- A word with a separator after a segment is no prefix of a word with no separator. -/
theorem not_prefix_of_notMem (c : Char) {s x t : List Char} (ht : c ∉ t) :
    ¬ (s ++ c :: x) <+: t := by
  intro ⟨z, hz⟩
  exact ht (hz ▸ by simp)

/-- The join of two lists that each have a segment. -/
theorem join_append (c : Char) :
    ∀ {p r : List (List Char)}, p ≠ [] → r ≠ [] →
      join c (p ++ r) = join c p ++ c :: join c r
  | [], _, h, _ => absurd rfl h
  | [s], r, _, hr => by
      cases r with
      | nil => exact absurd rfl hr
      | cons t r => simp [join]
  | s :: u :: p, r, _, hr => by
      have h1 := join_append c (p := u :: p) (r := r) (by simp) hr
      show s ++ c :: join c (u :: (p ++ r)) = (s ++ c :: join c (u :: p)) ++ c :: join c r
      rw [show join c (u :: (p ++ r)) = join c (u :: p) ++ c :: join c r from h1]
      simp

/-- **A key that ends with a separator selects the items that agree on it.** The partial key is the
    word of the first segments and a trailing separator. A full key has a prefix match with it
    exactly where the segments of the item begin with those segments and have one more. -/
theorem prefix_iff (c : Char) :
    ∀ (p f : List (List Char)), p ≠ [] → NoSep c p → NoSep c f →
      ((join c p ++ [c]) <+: join c f ↔ ∃ r, r ≠ [] ∧ f = p ++ r)
  | [], _, h, _, _ => absurd rfl h
  | s :: p, f, _, hp, hf => by
      constructor
      · intro h
        cases f with
        | nil => simp [join] at h
        | cons t f =>
            have hs : c ∉ s := hp s (by simp)
            have ht : c ∉ t := hf t (by simp)
            cases p with
            | nil =>
                cases f with
                | nil =>
                    simp only [join] at h
                    exact absurd h (not_prefix_of_notMem c ht ∘ fun h' => by simpa using h')
                | cons u f =>
                    simp only [join] at h
                    obtain ⟨rfl, -⟩ := prefix_segment c hs ht (x := []) (y := join c (u :: f))
                      (by simpa using h)
                    exact ⟨u :: f, by simp, rfl⟩
            | cons q p =>
                cases f with
                | nil =>
                    simp only [join] at h
                    exact absurd h (not_prefix_of_notMem c ht ∘ fun h' => by
                      simpa using h')
                | cons u f =>
                    simp only [join] at h
                    obtain ⟨rfl, hrest⟩ := prefix_segment c hs ht
                      (x := join c (q :: p) ++ [c]) (y := join c (u :: f))
                      (by simpa using h)
                    have hp' : NoSep c (q :: p) := fun v hv => hp v (List.mem_cons_of_mem _ hv)
                    have hf' : NoSep c (u :: f) := fun v hv => hf v (List.mem_cons_of_mem _ hv)
                    obtain ⟨r, hr, hfe⟩ := (prefix_iff c (q :: p) (u :: f) (by simp) hp' hf').mp hrest
                    exact ⟨r, hr, by simp [hfe]⟩
      · rintro ⟨r, hr, rfl⟩
        rw [join_append c (by simp) hr]
        exact ⟨join c r, by simp⟩

/-- **A partial key with no trailing separator selects more.** `A#1` is a prefix of `A#10`, and the
    segments `A`, `1` are no prefix of the segments `A`, `10`. -/
theorem prefix_without_separator :
    (join '#' [['A'], ['1']]) <+: join '#' [['A'], ['1', '0']] ∧
      ¬ ∃ r, [['A'], ['1']] ++ r = [['A'], ['1', '0']] := by
  refine ⟨by decide, ?_⟩
  rintro ⟨r, hr⟩
  simp at hr

/-! ## The boundary of the host -/

/-- A component of the key spec, as the segments that it prints. -/
inductive Comp where
  /-- A plain component, or a transform that gives no object: the name and the value. -/
  | named (name value : String)
  /-- A transform that gives an object: the tag when it has one, and the value. -/
  | shaped (tag : Option String) (value : String)

/-- The segments of a component: two for a name and a value, two for a tag and a value, one for a
    value alone. -/
def Comp.segs : Comp → List String
  | .named n v => [n, v]
  | .shaped (some t) v => [t, v]
  | .shaped none v => [v]

/-- The components that print. A plain component is absent where its value is undefined, null or
    empty. A component with a transform is absent only where its value is undefined, because the
    transform reads a null or empty value. The caller of this function gives each part as `none`
    where it is absent.

    The components that print are all of them where the strict builder meets no absent value, and the
    ones before the first absent value where the builder allows a partial key. -/
def printed (allowPartial : Bool) : List (Option Comp) → Option (List Comp)
  | [] => some []
  | none :: _ => if allowPartial then some [] else none
  | some k :: r => (printed allowPartial r).map (k :: ·)

/-- **The strict builder prints each component or none.** -/
theorem printed_strict : ∀ ps : List (Option Comp), printed false ps = ps.mapM id
  | [] => rfl
  | none :: _ => rfl
  | some k :: r => by
      simp only [printed, printed_strict r, List.mapM_cons]
      generalize List.mapM id r = m
      cases m <;> rfl

/-- **The builder with a partial key stops at the first absent value.** -/
theorem printed_partial :
    ∀ ps : List (Option Comp),
      printed true ps = some ((ps.takeWhile Option.isSome).filterMap id)
  | [] => rfl
  | none :: _ => by simp [printed]
  | some k :: r => by simp [printed, printed_partial r]

/-- The boundary: a separator where the print stops before the last component. The host appends
    it by this rule. -/
def boundary (full : Nat) (cs : List Comp) : Bool := decide (cs.length < full)

/-- The key of the host: the segments of the printed components, and the empty segment of the
    boundary where the option is on and the print stops before the last component. -/
def build (allowPartial enforce : Bool) (parts : List (Option Comp)) : Option (List String) :=
  (printed allowPartial parts).map fun cs =>
    if enforce && boundary parts.length cs then cs.flatMap Comp.segs ++ [""]
    else cs.flatMap Comp.segs

/-- **The boundary is on exactly where the print stops before the last component.** The count of
    segments does not enter: a component with one segment counts as one component. -/
theorem boundary_iff (full : Nat) (cs : List Comp) :
    boundary full cs = true ↔ cs.length < full :=
  decide_eq_true_iff

/-- **A full key ends without the boundary.** Where the print holds each component of the spec,
    the key is the segments of the components, with the option on. -/
theorem build_full_ends_without_boundary {allowPartial : Bool} {parts : List (Option Comp)}
    {cs : List Comp} (h : printed allowPartial parts = some cs) (hfull : cs.length = parts.length) :
    build allowPartial true parts = some (cs.flatMap Comp.segs) := by
  have hb : boundary parts.length cs = false := by simp [boundary, hfull]
  simp [build, h, hb]

/-- **A partial key ends with the boundary.** Where the print stops before the last component, the
    key is the segments of the components and one empty segment, with the option on. -/
theorem build_partial_ends_with_boundary {allowPartial : Bool} {parts : List (Option Comp)}
    {cs : List Comp} (h : printed allowPartial parts = some cs) (hlt : cs.length < parts.length) :
    build allowPartial true parts = some (cs.flatMap Comp.segs ++ [""]) := by
  have hb : boundary parts.length cs = true := (boundary_iff _ _).mpr hlt
  simp [build, h, hb]

/-! ## The key as a codec -/

/-- **The view of a string as characters.** The string of the library reads its characters through
    a function that depends on `Classical.choice`. The key codec reads a string through this view
    instead, so each definition below stays free of that axiom, and the laws hold for each view
    that the two maps cancel. The view of the library is `String.toList` with `String.ofList`. Its
    two cancellation facts are core theorems that reach `Classical.choice`, so this module does
    not cite them. -/
structure StringView where
  /-- The characters of a string. -/
  chars : String → List Char
  /-- The string of a list of characters. -/
  str : List Char → String
  /-- The characters of the string of a list are the list. -/
  chars_str : ∀ l, chars (str l) = l
  /-- The string of the characters of a string is the string. -/
  str_chars : ∀ s, str (chars s) = s

variable (V : StringView)

/-- The word of a segment list, as a string. -/
def joinS (c : Char) (segs : List String) : String :=
  V.str (join c (segs.map V.chars))

/-- The read of a string: the segments between the separators. -/
def splitS (c : Char) (k : String) : List String :=
  (split c (V.chars k)).map V.str

/-- The segment list is usable as a key: it has a segment, and no segment holds the separator. -/
def Good (c : Char) (segs : List String) : Prop :=
  segs ≠ [] ∧ ∀ s ∈ segs, c ∉ V.chars s

instance (c : Char) (segs : List String) : Decidable (Good V c segs) := by
  unfold Good; infer_instance

/-- A segment list as an attribute: a list of strings. -/
def segsAttr (segs : List String) : Value := Attr.l (segs.map Attr.s)

/-- The strings of a list of attributes, or nothing where one is no string. -/
def strs : List Value → Option (List String)
  | [] => some []
  | Attr.s s :: r => (strs r).map (s :: ·)
  | _ :: _ => none

/-- The write of the key: a list of strings that is good prints one string. -/
def keyWrite (c : Char) : Value → Option Value
  | Attr.l vs =>
      match strs vs with
      | some segs => if Good V c segs then some (Attr.s (joinS V c segs)) else none
      | none => none
  | _ => none

/-- The read of the key: a string gives its segments. -/
def keyRead (c : Char) : Value → Option Value
  | Attr.s k => some (segsAttr (splitS V c k))
  | _ => none

/-- **The key codec.** The held set is the good segment lists, and the member is `S`. -/
def keyCodec (c : Char) : Codec :=
  Alg.Codec.ofEP (fun v => ∃ segs, Good V c segs ∧ v = segsAttr segs) (some Member.S)
    (keyWrite V c) (keyRead V c)

/-- The strings of the attributes of a segment list are the list. -/
theorem strs_map (segs : List String) : strs (segs.map Attr.s) = some segs := by
  induction segs with
  | nil => rfl
  | cons s r ih => simp [strs, ih]

/-- A list of attributes whose strings are a list is the attributes of that list. -/
theorem eq_segsAttr_of_strs : ∀ {vs : List Value} {segs : List String},
    strs vs = some segs → vs = segs.map Attr.s
  | [], segs, h => by simp [strs] at h; subst h; rfl
  | Attr.s s :: r, segs, h => by
      simp only [strs, Option.map_eq_some_iff] at h
      obtain ⟨rest, hr, rfl⟩ := h
      simp [eq_segsAttr_of_strs hr]
  | Attr.n _ :: _, _, h => by simp [strs] at h
  | Attr.b _ :: _, _, h => by simp [strs] at h
  | Attr.bool _ :: _, _, h => by simp [strs] at h
  | Attr.null :: _, _, h => by simp [strs] at h
  | Attr.ss _ :: _, _, h => by simp [strs] at h
  | Attr.ns _ :: _, _, h => by simp [strs] at h
  | Attr.bs _ :: _, _, h => by simp [strs] at h
  | Attr.l _ :: _, _, h => by simp [strs] at h
  | Attr.m _ _ :: _, _, h => by simp [strs] at h

/-- **The write of the read is the string.** Each string reads and writes back. -/
theorem joinS_splitS (c : Char) (k : String) : joinS V c (splitS V c k) = k := by
  simp [joinS, splitS, List.map_map, Function.comp_def, V.chars_str, join_split, V.str_chars]

/-- **The read of the write is the segment list**, where the list is good. -/
theorem splitS_joinS (c : Char) {segs : List String} (h : Good V c segs) :
    splitS V c (joinS V c segs) = segs := by
  have hne : segs.map V.chars ≠ [] := by simpa using h.1
  have hn : NoSep c (segs.map V.chars) := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
    exact h.2 t ht
  simp [splitS, joinS, V.chars_str, split_join c _ hne hn, List.map_map, Function.comp_def,
    V.str_chars]

/-- The read of a string is good: it has a segment, and no segment holds the separator. -/
theorem good_splitS (c : Char) (k : String) : Good V c (splitS V c k) := by
  refine ⟨?_, ?_⟩
  · simpa [splitS] using split_ne_nil c (V.chars k)
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
    simpa [V.chars_str] using split_noSep c (V.chars k) t ht

/-- **The key codec is lawful.** The write is the join of the good segment lists. The read is the
    split of each string. The two retract each other, because the join is injective on the good
    lists and every read gives a good list. -/
theorem keyCodec_lawful (c : Char) : Lawful (keyCodec V c) := by
  refine Alg.Lawful.ofRC ?_ ?_ ?_
  · intro t a he
    change keyWrite V c t = some a at he
    cases t with
    | l vs =>
        simp only [keyWrite] at he
        cases hs : strs vs with
        | none => simp [hs] at he
        | some segs =>
            simp only [hs] at he
            rcases Decidable.em (Good V c segs) with hg | hg
            · simp only [hg, if_true, Option.some.injEq] at he
              subst he
              simp [keyCodec, keyRead, splitS_joinS V c hg, segsAttr,
                eq_segsAttr_of_strs hs]
            · simp [hg] at he
    | _ => simp [keyWrite] at he
  · intro a t hp
    change keyRead V c a = some t at hp
    cases a with
    | s k =>
        simp only [keyRead, Option.some.injEq] at hp
        subst hp
        have hg := good_splitS V c k
        change keyWrite V c (segsAttr (splitS V c k)) = some (Attr.s k)
        simp [keyWrite, segsAttr, strs_map, hg, joinS_splitS]
    | _ => simp [keyRead] at hp
  · intro μ hμ t a he
    simp only [keyCodec, Alg.Codec.ofEP_μ, Option.some.injEq] at hμ
    subst hμ
    change keyWrite V c t = some a at he
    cases t <;> simp only [keyWrite] at he
    case l vs =>
      cases hs : strs vs with
      | none => simp [hs] at he
      | some segs =>
          simp only [hs] at he
          rcases Decidable.em (Good V c segs) with hg | hg
          · simp only [hg, if_true, Option.some.injEq] at he
            subst he; rfl
          · simp [hg] at he
    all_goals contradiction

/-! ## The write without the premise -/

/-- **A codec whose write prints two values as one key is not lawful.** The retraction makes the
    write injective on its held values. -/
theorem not_lawful_of_collision {c : Codec} {t t' a : Value} (he : c.e t = some a)
    (he' : c.e t' = some a) (hne : t ≠ t') : ¬ Lawful c :=
  fun h => hne (Alg.Lawful.e_injective h he he')

/-- The write with no check of the segments. -/
def rawWrite (c : Char) : Value → Option Value
  | Attr.l vs => (strs vs).map fun segs => Attr.s (joinS V c segs)
  | _ => none

/-- **A segment that holds the separator breaks the write.** The segment lists `[a#b]` and
    `[a, b]` are two values that print one key at the separator `#`, so no codec with this write
    is lawful, for each held set, member and read. -/
theorem rawWrite_not_lawful (T : Value → Prop) (μ : Option Member) (p : Value → Option Value) :
    ¬ Lawful (Alg.Codec.ofEP T μ (rawWrite V '#') p) := by
  have h1 : join '#' [V.chars (V.str ['a', '#', 'b'])] = join '#' [V.chars (V.str ['a']), V.chars (V.str ['b'])] := by
    simp only [V.chars_str]
    exact join_collision
  refine not_lawful_of_collision (t := segsAttr [V.str ['a', '#', 'b']])
    (t' := segsAttr [V.str ['a'], V.str ['b']])
    (a := Attr.s (joinS V '#' [V.str ['a', '#', 'b']])) ?_ ?_ ?_
  · simp only [Alg.Codec.ofEP_e, rawWrite, segsAttr, strs_map, Option.map_some]
  · simp only [Alg.Codec.ofEP_e, rawWrite, segsAttr, strs_map, Option.map_some]
    simp only [joinS, List.map_cons, List.map_nil]
    rw [h1]
  · simp [segsAttr]

/-- **The empty list and the list of one empty segment are two values that print one key.** A
    premise of the lawful codec is that the list has a segment. -/
theorem rawWrite_empty_collision (c : Char) :
    rawWrite V c (segsAttr []) = rawWrite V c (segsAttr [V.str []]) := by
  simp [rawWrite, segsAttr, strs, joinS, join, V.chars_str]

/-! ## The null arm -/

/-- **The null arm of a discriminated spec writes no attribute.** The model has `Codec.empty`: its
    held set is empty and its write is nowhere defined. -/
theorem nullArm_writes_nothing (v : Value) : (Codec.empty : Codec).e v = none := rfl

/-- The null arm is lawful, vacuously. -/
theorem nullArm_lawful : Lawful (Codec.empty : Codec) := Alg.Lawful.empty

end DerivedKey

end Calculus
