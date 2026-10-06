import Calculus.Dynamo.Analysis.Disjoint
import Calculus.Dynamo.Analysis.Orthogonality

variable {α : Calculus.Table}

/-!
# The slice of a certified union

A union carries options, and a clause selects among them. A clause names some of the names an
option declares, and admits a set of alternatives at each. The extraction keeps the options the
clause describes; the exclusion keeps the options it rejects. Both give a union over the same
options in the same order, and fewer of them.

**The clause carries an `Alts` at each name it speaks about, and not a set of text.** A union
option is told apart by the disjointness test, which separates two objects at a `boolean` or a
`binary` literal as well as at a `string` one, so a clause over text could not slice a union that
the certificate certifies. Non-emptiness is `Alts`'s own, so the record below declares no such
field.

**The union's obligation survives a slice on its own.** Pairwise compatibility is a property of
each pair of options, so any sub-selection keeps it, and the slice needs no certificate.

Not in `Merge.lean`, which says of itself that it is a syntactic operation on `Body` with a typing
corollary and sits with what it is about. These are syntactic operations on the option list, so
they sit here by the same rule.
-/

namespace Calculus

/-- A declared name's pin lies inside the clause's: the same adapter word, the same base, and
    alternatives that are a subset of the clause's.

    **Containment, not membership.** A name pinned to `a | b` admits values at both, so a clause
    at `a` alone does not describe it.

    Four rows, one per base whose carrier has more than one value. `null` has no row because its
    carrier has one inhabitant, so a clause there would keep every member rather than select
    among them. A name pinned at one base against a clause at another is no match, which is the
    `_` row. -/
def altsSub : Option Pin → Pin → Bool
  | some (w, ⟨.string, x⟩),  (w', ⟨.string, c⟩)  => decide (w = w') && decide (∀ a ∈ x.1.val, a ∈ c.1.val)
  | some (w, ⟨.number, x⟩),  (w', ⟨.number, c⟩)  => decide (w = w') && decide (∀ a ∈ x.1.val, a ∈ c.1.val)
  | some (w, ⟨.boolean, x⟩), (w', ⟨.boolean, c⟩) => decide (w = w') && decide (∀ a ∈ x.1.val, a ∈ c.1.val)
  | some (w, ⟨.binary, x⟩),  (w', ⟨.binary, c⟩)  => decide (w = w') && decide (∀ a ∈ x.1.val, a ∈ c.1.val)
  | _, _ => false

/-- **A clause at union level**: the names it speaks about, and the pin it admits at each.

    No index: a union declares no key set, so a name the clause asks for that no option declares
    is a clause that keeps nothing, which is `never` said in a place that can say it. -/
structure AltClause where
  keys : Finset Name
  pin : {k // k ∈ keys} → Pin

/-- One clause key, answered against one option's spec: the name is declared, the caller must
    write it, and its pin lies inside the clause's.

    Required presence is read because an optional literal name admits the map that omits the
    name, so the option holds values outside every fibre the clause describes, and
    the clause does not describe the option. A fill is required at the caller side, so a fill is
    kept. -/
def litSubAt (s : MapOf NameSpec) (c : AltClause) (k : {k // k ∈ c.keys}) : Bool :=
  match s.at k.1 with
  | some ns => ns.required && altsSub ns.pin (c.pin k)
  | none => false

/-- **Whether a clause describes an option**: the option is an object, and it answers at every key
    the clause names. A non-object option has no spec and is never kept. -/
def AltClause.admits (c : AltClause) (t : Term) : Bool :=
  match specOf t with
  | some s => decide (∀ k : {k // k ∈ c.keys}, litSubAt s c k = true)
  | none => false

/-- **A clause at a numeral keeps the option that pins that numeral**, and not an option that pins
    another one. -/
example : (AltClause.mk {"k"} fun _ => ([], ⟨.number, NEFinset.of (WFNumeral.of "1") ∅⟩)).admits
    (.object (.mk {"k"} (fun _ => .req (.literal .number (WFNumeral.of "1"))) none)) = true := by
  decide

example : (AltClause.mk {"k"} fun _ => ([], ⟨.number, NEFinset.of (WFNumeral.of "1") ∅⟩)).admits
    (.object (.mk {"k"} (fun _ => .req (.literal .number (WFNumeral.of "2"))) none)) = false := by
  decide

/-- **The extraction**: the options the clause describes, in their original order. -/
def AltClause.extract (c : AltClause) (opts : List Term) : List Term :=
  opts.filter c.admits

/-- **The exclusion**: the complement of the same predicate, so the two partition the options and
    no option is both kept and dropped. -/
def AltClause.exclude (c : AltClause) (opts : List Term) : List Term :=
  opts.filter (fun t => ! c.admits t)

/-- **Two clauses select the join of their extracts.**

    A clause pins one word per name, so selecting under two words is selecting with each clause
    in turn. Stated on membership and not as an append: `List.filter` fixes an order, and
    an append would carry an option both clauses admit twice. -/
theorem mem_extract_or (c c' : AltClause) (opts : List Term) (t : Term) :
    t ∈ opts.filter (fun u => c.admits u || c'.admits u) ↔
      t ∈ c.extract opts ∨ t ∈ c'.extract opts := by
  simp [AltClause.extract, List.mem_filter, and_or_left]

/-- The extraction keeps options and reorders none, which is what every corollary below reads. -/
theorem AltClause.extract_sublist (c : AltClause) (opts : List Term) :
    (c.extract opts).Sublist opts := List.filter_sublist

/-- ...and the same for the exclusion. -/
theorem AltClause.exclude_sublist (c : AltClause) (opts : List Term) :
    (c.exclude opts).Sublist opts := List.filter_sublist

/-! ### The typing corollaries -/

/-- **A sub-selection of typed options is typed**, at held sets and members that are the
    sub-selections of the originals.

    An existential, because the three lists the rule reads are positional: a selection speaks about
    the option, and the held set and the member at that position go or stay with it. The `Sublist`s
    are what the callers need, and they are what `HUnion` is read through.

    On the sub-selection and not on the filter. The filter form decides `p t` at each step and
    splits on the answer; this one recurses on `List.Sublist`, which already carries the decision
    in its constructor, and inverts the judgement in each case. -/
theorem TypedListμ.sublist {opts' opts : List Term} {Ts μs} (hsub : opts'.Sublist opts)
    (h : TypedListμ α opts Ts μs) :
    ∃ Ts' μs', TypedListμ α opts' Ts' μs' ∧ Ts'.Sublist Ts ∧ μs'.Sublist μs := by
  -- the recursion runs on `hsub`: `TypedListμ` is mutually inductive with `Typed`, and the
  -- `induction` tactic declines a mutually inductive type
  induction hsub generalizing Ts μs with
  | slnil => cases h; exact ⟨[], [], .nil, .slnil, .slnil⟩
  | cons _ _ ih =>
    cases h with
    | cons _ hs =>
      obtain ⟨Ts', μs', hts, hsT, hsμ⟩ := ih hs
      exact ⟨Ts', μs', hts, hsT.cons _, hsμ.cons _⟩
  | cons_cons _ _ ih =>
    cases h with
    | cons ht hs =>
      obtain ⟨Ts', μs', hts, hsT, hsμ⟩ := ih hs
      exact ⟨_ :: Ts', _ :: μs', .cons ht hts, hsT.cons_cons _, hsμ.cons_cons _⟩

/-- **The extraction of a derivable union is derivable.**

    Nothing new is proved about an option: each kept option carries the judgement it already
    has. The one lemma this needs is `TypedListμ.sublist` above. -/
theorem typed_union_extract {opts : List Term} {Ts μs} (c : AltClause)
    (h : TypedListμ α opts Ts μs) :
    ∃ Ts' μs', Ts'.Sublist Ts ∧ μs'.Sublist μs ∧
      Typed α (.union (c.extract opts)) (HUnion Ts') (unanimous μs') := by
  obtain ⟨Ts', μs', hts, hsT, hsμ⟩ := h.sublist (c.extract_sublist opts)
  exact ⟨Ts', μs', hsT, hsμ, .union hts⟩

/-- **The exclusion of a derivable union is derivable**, by the same argument at the complement. -/
theorem typed_union_exclude {opts : List Term} {Ts μs} (c : AltClause)
    (h : TypedListμ α opts Ts μs) :
    ∃ Ts' μs', Ts'.Sublist Ts ∧ μs'.Sublist μs ∧
      Typed α (.union (c.exclude opts)) (HUnion Ts') (unanimous μs') := by
  obtain ⟨Ts', μs', hts, hsT, hsμ⟩ := h.sublist (c.exclude_sublist opts)
  exact ⟨Ts', μs', hsT, hsμ, .union hts⟩

/-- The slice holds no value the original did not. A sub-selection of the held sets, so the
    disjunction narrows. -/
theorem hunion_sublist {Ts' Ts : List Held} (hs : Ts'.Sublist Ts) {v : Value}
    (hv : HUnion Ts' v) : HUnion Ts v :=
  hv.elim fun T hT => ⟨T, hs.subset hT.1, hT.2⟩

/-! ### The certificate, and the obligation -/

/-- **Separation survives the slice**, because it is `Pairwise`. -/
theorem separated_sublist {opts' opts : List Term} (hs : opts'.Sublist opts)
    (h : Separated α opts) : Separated α opts' :=
  List.Pairwise.sublist hs h

/-- **The union's obligation survives any sub-selection.** -/
theorem pairwiseCompat_sublist {opts' opts : List Term} (hs : opts'.Sublist opts)
    (h : PairwiseCompat α opts) : PairwiseCompat α opts' :=
  fun s hs' t ht' => h s (hs.subset hs') t (hs.subset ht')

/-- …so the extraction keeps it, with no certificate. -/
theorem pairwiseCompat_extract {opts : List Term} (c : AltClause) (h : PairwiseCompat α opts) :
    PairwiseCompat α (c.extract opts) :=
  pairwiseCompat_sublist (c.extract_sublist opts) h

/-- ...and the exclusion, at the complement of the same predicate. -/
theorem pairwiseCompat_exclude {opts : List Term} (c : AltClause) (h : PairwiseCompat α opts) :
    PairwiseCompat α (c.exclude opts) :=
  pairwiseCompat_sublist (c.exclude_sublist opts) h


/-! ## The slice partitions the union

The join half needs no certificate: `extract` and `exclude` filter by a predicate and its
negation. The disjointness half does, because two options may share a value. -/

/-- **A clause partitions a union's options, and the join is the union's admission.** Pure list
    algebra: `extract` and `exclude` filter by a predicate and its negation. -/
theorem AdmAny_extract_or_exclude (c : AltClause) (opts : List Term) (v : Value) :
    (AdmAny α (c.extract opts) v || AdmAny α (c.exclude opts) v) = AdmAny α opts v := by
  induction opts with
  | nil => rfl
  | cons t ts ih =>
    simp only [AltClause.extract, AltClause.exclude, List.filter_cons] at *
    cases hc : c.admits t <;> simp_all [AdmAny_cons] <;> cases Adm α t v <;> simp_all

/-- …and the two halves of a slice share no value, because the certificate bounds the options
    that admit one at a single option and the clause keeps them apart. -/
theorem AdmAny_extract_and_exclude {c : AltClause} {opts : List Term}
    (hok : certAll opts = true) (v : Value) :
    (AdmAny α (c.extract opts) v && AdmAny α (c.exclude opts) v) = false := by
  rcases hb : AdmAny α (c.extract opts) v with _ | _
  · simp
  rcases hb2 : AdmAny α (c.exclude opts) v with _ | _
  · simp
  exfalso
  obtain ⟨t1, ht1, ha1⟩ := AdmAny_iff.mp hb
  obtain ⟨t2, ht2, ha2⟩ := AdmAny_iff.mp hb2
  have hm1 : t1 ∈ opts := List.mem_of_mem_filter ht1
  have hm2 : t2 ∈ opts := List.mem_of_mem_filter ht2
  have hc1 : c.admits t1 = true := (List.mem_filter.mp ht1).2
  have hc2 : c.admits t2 = false := by
    have := (List.mem_filter.mp ht2).2; simpa using this
  have hne : t1 ≠ t2 := fun hh => by rw [hh, hc2] at hc1; exact Bool.noConfusion hc1
  have hlen : (opts.filter (fun t => Adm α t v)).length ≤ 1 := by
    have hone := (admitsAtMostOne_of_separated (α := α) (separated_of_certAll hok)).1 v
    rwa [filter_AdmList _ v,
      List.length_map] at hone
  have hf1 : t1 ∈ opts.filter (fun t => Adm α t v) :=
    List.mem_filter.mpr ⟨hm1, ha1⟩
  have hf2 : t2 ∈ opts.filter (fun t => Adm α t v) :=
    List.mem_filter.mpr ⟨hm2, ha2⟩
  match hL : opts.filter (fun t => Adm α t v), hlen with
  | [], _ => rw [hL] at hf1; exact absurd hf1 (by simp)
  | [x], _ =>
      rw [hL, List.mem_singleton] at hf1 hf2
      exact hne (hf1.trans hf2.symm)
  | _ :: _ :: _, hl => rw [hL] at hlen; simp at hlen

/-- **The two slices join to the union.** Stated on `Term.ofOptions`, because a slice of one
    option is that option and a slice of none is the bottom. -/
theorem Adm_extract_or_exclude (c : AltClause) (opts : List Term) (v : Value) :
    (Adm α (Term.ofOptions (c.extract opts)) v || Adm α (Term.ofOptions (c.exclude opts)) v)
      = Adm α (Term.ofOptions opts) v := by
  rw [Adm_ofOptions, Adm_ofOptions, Adm_ofOptions]
  exact AdmAny_extract_or_exclude c opts v

/-- …and no value falls in both slices of a certified union, so a certified union is the sum of
    any slice and its complement. -/
theorem Adm_extract_and_exclude {c : AltClause} {opts : List Term} (hok : certAll opts = true)
    (v : Value) :
    (Adm α (Term.ofOptions (c.extract opts)) v && Adm α (Term.ofOptions (c.exclude opts)) v)
      = false := by
  rw [Adm_ofOptions, Adm_ofOptions]
  exact AdmAny_extract_and_exclude hok v


/-! ## What the slice keeps

A kept option holds, at each clause key, only what the clause's pin describes. The stored side
reads the attribute. The caller side reads the value through the pin's word, and the word is the
clause's. -/

/-- Where each option of a list is a literal at one base, a value that an option's row holds is
    one of the literals. -/
theorem inLs_of_litsAt {R : Term → Value → Bool}
    (hlit : ∀ k x v, R (.literal k x) v = inL k x v) {k : GroundKind} :
    ∀ {ts : List Term} {s : Finset k.Carrier}, litsAt k ts = some s →
      ∀ {v}, anyP (ts.map R) v = true → ∃ x ∈ s, inL k x v = true
  | [], s, h, v, hv => by simp [anyP] at hv
  | t :: ts, s, h, v, hv => by
      cases t with
      | literal k' x =>
          simp only [litsAt] at h
          generalize instDecidableEqGroundKind k' k = d at h
          cases d with
          | isFalse => cases h
          | isTrue hk =>
            subst hk
            obtain ⟨s', hs, rfl⟩ := Option.map_eq_some_iff.mp h
            simp only [List.map_cons, anyP, Bool.or_eq_true] at hv
            refine hv.elim (fun hv => ⟨x, Finset.mem_insert_self _ _, (hlit _ _ _).symm.trans hv⟩)
              fun hv => ?_
            obtain ⟨y, hy, hyv⟩ := inLs_of_litsAt hlit hs hv
            exact ⟨y, Finset.mem_insert.mpr (Or.inr hy), hyv⟩
      | _ => cases h

/-- The alternatives that a term pins without an adapter hold each value that the term's row
    holds. -/
theorem inLs_of_altsOf {R : Term → Value → Bool}
    (hlit : ∀ k x v, R (.literal k x) v = inL k x v)
    (hun : ∀ ts v, R (.union ts) v = anyP (ts.map R) v) {t : Term} {al : Alts}
    (h : altsOf t = some al) {v : Value} (hv : R t v = true) : inLs al.1 al.2 v = true := by
  unfold altsOf at h
  split at h
  · cases h; rw [hlit] at hv
    exact inLs_eq_true.mpr ⟨_, NEFinset.mem_of _ _, hv⟩
  · rename_i k x ts
    obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [hun] at hv
    have hl : litsAt k (.literal k x :: ts) = some (insert x s) := by
      rw [litsAt, dif_pos rfl, hs]; rfl
    obtain ⟨y, hy, hyv⟩ := inLs_of_litsAt hlit hl hv
    exact inLs_eq_true.mpr ⟨y, hy, hyv⟩
  · cases h

/-- A pin read off `altsOf` under a word keeps the word, and holds each value the term's row
    holds. -/
theorem inLs_of_altsOf_map {R : Term → Value → Bool}
    (hlit : ∀ k x v, R (.literal k x) v = inL k x v)
    (hun : ∀ ts v, R (.union ts) v = anyP (ts.map R) v) {t : Term} {w₀ w : Word} {al : Alts}
    (h : (altsOf t).map (w₀, ·) = some (w, al)) {u : Value} (hv : R t u = true) :
    w = w₀ ∧ inLs al.1 al.2 u = true := by
  obtain ⟨al', ha, he⟩ := Option.map_eq_some_iff.mp h
  cases he
  exact ⟨rfl, inLs_of_altsOf hlit hun ha hv⟩

/-- **The alternatives of a pin hold each value the term's row holds**, read through the pin's
    word by `E`. -/
theorem inLs_of_pinOf {R : Term → Value → Bool} {E : Word → Value → Value}
    (hlit : ∀ k x v, R (.literal k x) v = inL k x v)
    (hun : ∀ ts v, R (.union ts) v = anyP (ts.map R) v) (hE : ∀ v, E [] v = v)
    (href : ∀ t p pA v, R (.refine t p pA) v = true → R t v = true)
    (hheld : ∀ t P k₀ ks v, R (.held false t P k₀ ks) v = true → R t (E (k₀ :: ks) v) = true) :
    ∀ {t : Term} {w : Word} {al : Alts}, pinOf t = some (w, al) →
      ∀ {v : Value}, R t v = true → inLs al.1 al.2 (E w v) = true
  | t, w, al, h, v, hv => by
      cases t with
      | refine t p pA => exact inLs_of_pinOf hlit hun hE href hheld (t := t) h (href _ _ _ _ hv)
      | held t P k₀ ks =>
        obtain ⟨rfl, hin⟩ := inLs_of_altsOf_map hlit hun h (hheld _ _ _ _ _ hv)
        exact hin
      | _ =>
        obtain ⟨rfl, hin⟩ := inLs_of_altsOf_map hlit hun h hv
        rw [hE]; exact hin

/-- A pin inside a clause's pin carries the clause's word, and its alternatives lie in the
    clause's. -/
theorem altsSub_inLs {p : Option Pin} {q : Pin} (h : altsSub p q = true) :
    ∃ w al, p = some (w, al) ∧ w = q.1 ∧
      ∀ v, inLs al.1 al.2 v = true → inLs q.2.1 q.2.2 v = true := by
  obtain _ | ⟨w, ⟨k, x⟩⟩ := p
  · simp [altsSub] at h
  obtain ⟨w', ⟨k', c⟩⟩ := q
  refine ⟨w, ⟨k, x⟩, rfl, ?_⟩
  cases k <;> cases k' <;>
    simp only [altsSub, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at h <;>
    exact ⟨h.1, fun v hv => by
      obtain ⟨y, hy, hyv⟩ := inLs_eq_true.mp hv
      exact inLs_eq_true.mpr ⟨y, h.2 y hy, hyv⟩⟩

/-- A clause that describes an option reads the option's object at each clause key: the name is
    declared, the caller must write it, and its pin lies inside the clause's. -/
theorem AltClause.admits_at {c : AltClause} {t : Term} (h : c.admits t = true)
    (k : {k // k ∈ c.keys}) :
    ∃ fields f wild, t = .object (.mk fields f wild) ∧ ∃ hf : k.1 ∈ fields,
      (f ⟨k.1, hf⟩).isReqAt .host = true ∧
        altsSub (altsOfField (f ⟨k.1, hf⟩)) (c.pin k) = true := by
  cases t with
  | object b =>
    obtain ⟨fields, f, wild⟩ := b
    refine ⟨fields, f, wild, rfl, ?_⟩
    have hk := of_decide_eq_true h k
    unfold litSubAt at hk
    split at hk
    · rename_i ns hs
      obtain ⟨hf, rfl⟩ := MapOf.at_eq_some.mp hs
      simp only [Bool.and_eq_true] at hk
      exact ⟨hf, hk⟩
    · cases hk
  | _ => cases h

/-- **The stored side of the slice.** A kept option reads, at a clause key, only an attribute in
    the clause's alternatives.

    The name can be absent from the attribute: a `fill` is required at the caller side, so the
    clause keeps the fill, and the fill reads a map that omits the name. -/
theorem AltClause.admits_AdmA {c : AltClause} {t : Term} (h : c.admits t = true)
    (k : {k // k ∈ c.keys}) {keys : Finset Name} {g : {n // n ∈ keys} → Attr}
    (ha : AdmA α t (.m keys g) = true) (hk : k.1 ∈ keys) :
    inLs (c.pin k).2.1 (c.pin k).2.2 (g ⟨k.1, hk⟩) = true := by
  obtain ⟨fields, f, wild, rfl, hf, -, hsub⟩ := c.admits_at h k
  obtain ⟨w, al, hp, -, hin⟩ := altsSub_inLs hsub
  rw [AdmA_object, AdmABody_mk] at ha
  simp only [Bool.and_eq_true] at ha
  have he := of_decide_eq_true ha.2 ⟨k.1, hk⟩
  simp only [entryP, MapOf.at_of_mem (m := ⟨fields, _⟩) ⟨k.1, hf⟩, Option.any_some] at he
  have hpin : ∀ {t : Term} {w : Word} {al : Alts}, pinOf t = some (w, al) →
      ∀ {v : Value}, AdmA α t v = true → inLs al.1 al.2 v = true := fun {_ _ _} h {_} hv =>
    inLs_of_pinOf (R := AdmA α) (E := fun _ v => v) (fun _ _ _ => rfl)
    (fun ts v => by rw [AdmA_union_row]; simp) (fun _ => rfl)
    (fun t p pA v hv => by rw [AdmA_refine] at hv; simp only [Bool.and_eq_true] at hv; exact hv.1)
    (fun t P k₀ ks v hv => by rw [AdmA_held] at hv; simp only [Bool.and_eq_true] at hv; exact hv.1)
    h hv
  refine hin _ ?_
  revert hp he
  cases f ⟨k.1, hf⟩ with
  | req u => exact fun hp he => hpin hp he
  | optional u => exact fun hp he => hpin hp he
  | fill u _ => exact fun hp he => hpin hp he

/-- **The caller side of the slice.** A kept option admits, at a clause key, only a value whose
    entry image under the clause's word is in the clause's alternatives.

    The empty word is the identity, so a literal pin admits only values in the clause's
    alternatives. A word that is not empty is the word of the pin, because `altsSub` compares the
    two words. -/
theorem AltClause.admits_Adm {c : AltClause} {t : Term} (h : c.admits t = true)
    (k : {k // k ∈ c.keys}) {keys : Finset Name} {g : {n // n ∈ keys} → Value}
    (hv : Adm α t (.map keys g) = true) :
    ∃ hk : k.1 ∈ keys,
      inLs (c.pin k).2.1 (c.pin k).2.2 ((α.word (c.pin k).1).1 (g ⟨k.1, hk⟩)) = true := by
  obtain ⟨fields, f, wild, rfl, hf, hreq, hsub⟩ := c.admits_at h k
  obtain ⟨w, al, hp, rfl, hin⟩ := altsSub_inLs hsub
  rw [Adm_object, AdmBody_mk] at hv
  simp only [Bool.and_eq_true] at hv
  have hk : k.1 ∈ keys := of_decide_eq_true hv.1 ⟨k.1, hf⟩ hreq
  refine ⟨hk, hin _ ?_⟩
  have he := of_decide_eq_true hv.2 ⟨k.1, hk⟩
  simp only [entryP, MapOf.at_of_mem (m := ⟨fields, _⟩) ⟨k.1, hf⟩, Option.any_some] at he
  have hpin : ∀ {t : Term} {w : Word} {al : Alts}, pinOf t = some (w, al) →
      ∀ {v : Value}, Adm α t v = true → inLs al.1 al.2 ((α.word w).1 v) = true :=
    fun {_ _ _} h {_} hv =>
    inLs_of_pinOf (R := Adm α) (E := fun w v => (α.word w).1 v) (fun _ _ _ => rfl)
      (fun ts v => by rw [Adm_union_row]; simp) (fun _ => rfl)
      (fun t p pA v hv => by rw [Adm_refine] at hv; simp only [Bool.and_eq_true] at hv; exact hv.1)
      (fun t P k₀ ks v hv => by rw [Adm_held] at hv; simp only [Bool.and_eq_true] at hv; exact hv.1)
      h hv
  revert hp he
  cases f ⟨k.1, hf⟩ with
  | req u => exact fun hp he => hpin hp he
  | optional u => exact fun hp he => hpin hp he
  | fill u _ => exact fun hp he => hpin hp he

end Calculus
