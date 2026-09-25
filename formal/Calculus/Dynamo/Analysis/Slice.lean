import Calculus.Dynamo.Analysis.Meet
import Calculus.Dynamo.Analysis.Orthogonality

/-!
# The slice of a certified union

A union carries options, and a clause selects among them. A clause names some of the names an
option declares, and admits a set of alternatives at each. The extraction keeps the options the
clause describes; the exclusion keeps the options it rejects. Both give a union over the same
options in the same order, and fewer of them.

**The clause carries an `Alts` at each name it speaks about, and not a set of text.** A union
option is told apart by the meet, which separates two objects at a `boolean` or a `binary`
literal as well as at a `string` one, so a clause over text could not slice a union that the
certificate certifies. Non-emptiness is `Alts`'s own, so the record below declares no such field.

**The union's obligation survives a slice on its own.** Pairwise compatibility is a property of
each pair of options, so any sub-selection keeps it, and the slice needs no certificate.

Not in `Merge.lean`, which says of itself that it is a syntactic operation on `Body` with a typing
corollary and sits with what it is about. These are syntactic operations on the option list, so
they sit here by the same rule.
-/

namespace Calculus

/-- A declared name's literal is the clause's value, at the same base.

    **A clause pins one value per name, because a literal carries one.** The subset test this
    replaces existed only while a literal held a set. Selecting several alternatives is
    selecting with one clause per alternative, which `mem_extract_or` below states.

    Three rows: `number` declines because
    the numeric carrier's equality came from an axiomatised host, and `null` because its carrier has one
    inhabitant, so a clause there would keep every member rather than select among them. A name
    pinned at one base against a clause at another is no match, which is the `_` row. -/
def altsSub : Option Alts → Alts → Bool
  | some ⟨.string, x⟩,  ⟨.string, c⟩  => decide (x = c)
  | some ⟨.boolean, x⟩, ⟨.boolean, c⟩ => decide (x = c)
  | some ⟨.binary, x⟩,  ⟨.binary, c⟩  => decide (x = c)
  | _, _ => false

/-- **A clause at union level**: the names it speaks about, and the alternatives it admits at each.

    No index: a union declares no key set, so a name the clause asks for that no option declares
    is a clause that keeps nothing, which is `never` said in a place that can say it. -/
structure AltClause where
  keys : Finset Name
  alts : {k // k ∈ keys} → Alts

/-- One clause key, answered against one option's spec: the name is declared, it is required,
    and its alternatives lie inside the clause's.

    Required presence is read because an optional literal name admits the map that omits the
    name, so the option holds values outside every fibre the clause describes, and
    the clause does not describe the option. -/
def litSubAt (s : MapOf NameSpec) (c : AltClause) (k : {k // k ∈ c.keys}) : Bool :=
  match s.at k.1 with
  | some ns => decide (ns.presence = (true, false)) && altsSub ns.alts (c.alts k)
  | none => false

/-- **Whether a clause describes an option**: the option is an object, and it answers at every key
    the clause names. A non-object option has no spec and is never kept. -/
def AltClause.admits (c : AltClause) (t : Term) : Bool :=
  match specOf t with
  | some s => decide (∀ k : {k // k ∈ c.keys}, litSubAt s c k = true)
  | none => false

/-- **The extraction**: the options the clause describes, in their original order. -/
def AltClause.extract (c : AltClause) (opts : List Term) : List Term :=
  opts.filter c.admits

/-- **The exclusion**: the complement of the same predicate, so the two partition the options and
    no option is both kept and dropped. -/
def AltClause.exclude (c : AltClause) (opts : List Term) : List Term :=
  opts.filter (fun t => ! c.admits t)

/-- **Several alternatives are several clauses, and the extracts join.**

    A clause pins one value per name, so selecting a set of alternatives is selecting with each
    clause in turn. Stated on membership and not as an append: `List.filter` fixes an order, and
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
    (h : TypedListμ opts Ts μs) :
    ∃ Ts' μs', TypedListμ opts' Ts' μs' ∧ Ts'.Sublist Ts ∧ μs'.Sublist μs := by
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

    Nothing is proved about an option that was not proved before: each kept option carries the
    judgement it already had. The one lemma this needs is `TypedListμ.sublist` above. -/
theorem typed_union_extract {opts : List Term} {Ts μs} (c : AltClause)
    (h : TypedListμ opts Ts μs) :
    ∃ Ts' μs', Ts'.Sublist Ts ∧ μs'.Sublist μs ∧
      Typed (.union (c.extract opts)) (HUnion Ts') (unanimous μs') := by
  obtain ⟨Ts', μs', hts, hsT, hsμ⟩ := h.sublist (c.extract_sublist opts)
  exact ⟨Ts', μs', hsT, hsμ, .union hts⟩

/-- **The exclusion of a derivable union is derivable**, by the same argument at the complement. -/
theorem typed_union_exclude {opts : List Term} {Ts μs} (c : AltClause)
    (h : TypedListμ opts Ts μs) :
    ∃ Ts' μs', Ts'.Sublist Ts ∧ μs'.Sublist μs ∧
      Typed (.union (c.exclude opts)) (HUnion Ts') (unanimous μs') := by
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
    (h : Separated opts) : Separated opts' :=
  List.Pairwise.sublist hs h

/-- **The union's obligation survives any sub-selection.** -/
theorem pairwiseCompat_sublist {opts' opts : List Term} (hs : opts'.Sublist opts)
    (h : PairwiseCompat opts) : PairwiseCompat opts' :=
  fun s hs' t ht' => h s (hs.subset hs') t (hs.subset ht')

/-- …so the extraction keeps it, with no certificate. -/
theorem pairwiseCompat_extract {opts : List Term} (c : AltClause) (h : PairwiseCompat opts) :
    PairwiseCompat (c.extract opts) :=
  pairwiseCompat_sublist (c.extract_sublist opts) h

/-- ...and the exclusion, at the complement of the same predicate. -/
theorem pairwiseCompat_exclude {opts : List Term} (c : AltClause) (h : PairwiseCompat opts) :
    PairwiseCompat (c.exclude opts) :=
  pairwiseCompat_sublist (c.exclude_sublist opts) h


/-! ## The slice partitions the union

The join half needs no certificate: `extract` and `exclude` filter by a predicate and its
negation. The disjointness half does, because two options may share a value. -/

/-- **A clause partitions a union's options, and the join is the union's admission.** Pure list
    algebra: `extract` and `exclude` filter by a predicate and its negation. -/
theorem AdmAny_extract_or_exclude (c : AltClause) (opts : List Term) (v : Value) :
    (AdmAny (c.extract opts) v || AdmAny (c.exclude opts) v) = AdmAny opts v := by
  induction opts with
  | nil => rfl
  | cons t ts ih =>
    simp only [AltClause.extract, AltClause.exclude, List.filter_cons] at *
    cases hc : c.admits t <;> simp_all [AdmAny_cons] <;> cases Adm t v <;> simp_all

/-- …and the two halves of a slice share no value, because the certificate bounds the options
    that admit one at a single option and the clause keeps them apart. -/
theorem AdmAny_extract_and_exclude {c : AltClause} {opts : List Term}
    (hok : unionOk opts = true) (v : Value) :
    (AdmAny (c.extract opts) v && AdmAny (c.exclude opts) v) = false := by
  rcases hb : AdmAny (c.extract opts) v with _ | _
  · simp
  rcases hb2 : AdmAny (c.exclude opts) v with _ | _
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
  have hlen : (opts.filter (fun t => Adm t v)).length ≤ 1 := by
    have hone := (admitsAtMostOne_of_separated (separated_of_unionOk hok)).1 v
    rwa [filter_AdmList (fun t _ => Adm_exact t) v,
      List.length_map] at hone
  have hf1 : t1 ∈ opts.filter (fun t => Adm t v) :=
    List.mem_filter.mpr ⟨hm1, ha1⟩
  have hf2 : t2 ∈ opts.filter (fun t => Adm t v) :=
    List.mem_filter.mpr ⟨hm2, ha2⟩
  match hL : opts.filter (fun t => Adm t v), hlen with
  | [], _ => rw [hL] at hf1; exact absurd hf1 (by simp)
  | [x], _ =>
      rw [hL, List.mem_singleton] at hf1 hf2
      exact hne (hf1.trans hf2.symm)
  | _ :: _ :: _, hl => rw [hL] at hlen; simp at hlen

/-- **The two slices join to the union.** Stated on `Term.ofOptions`, because a slice of one
    option is that option and a slice of none is the bottom. -/
theorem Adm_extract_or_exclude (c : AltClause) (opts : List Term) (v : Value) :
    (Adm (Term.ofOptions (c.extract opts)) v || Adm (Term.ofOptions (c.exclude opts)) v)
      = Adm (Term.ofOptions opts) v := by
  rw [Adm_ofOptions, Adm_ofOptions, Adm_ofOptions]
  exact AdmAny_extract_or_exclude c opts v

/-- …and no value falls in both slices of a certified union, so a certified union is the sum of
    any slice and its complement. -/
theorem Adm_extract_and_exclude {c : AltClause} {opts : List Term} (hok : unionOk opts = true)
    (v : Value) :
    (Adm (Term.ofOptions (c.extract opts)) v && Adm (Term.ofOptions (c.exclude opts)) v)
      = false := by
  rw [Adm_ofOptions, Adm_ofOptions]
  exact AdmAny_extract_and_exclude hok v



end Calculus
