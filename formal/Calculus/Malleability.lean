import Calculus.Combinators

/-!
# Non-malleability: the property we are asked to adopt, and the two places it dies

**Non-malleability is a property we deliberately fail, and `ker p` is why.** We do not have
`p a₁ = some v → p a₂ = some v → a₁ ≈ a₂` and should not: our `ker p` is deliberately not
equality. A proposal to replace the codec pair `(e, p)` with a relational format
`fmt : Value → Set Attr`, whose two decode clauses *entail* that property, is refuted here —
this file is the part of the refutation worth keeping, and it touches no existing declaration.

Three things are here, and the reason each is here rather than in `Codec.lean` is that none
of them is a new primitive.

* **`Fmt` is derived, not assumed.** It is the fibre of `p`, so it is `Codec.Ker`
  (`Calculus/Codec.lean:37`) seen from the other side: `Ker` is the relation "these two
  attributes are in one fibre", `Fmt` names the fibre. A relational presentation of a codec
  is therefore not a different model — it is the same model, addressed by fibre. Anything a
  `fmt` could express about reading, `p` already expresses.

* **And it is forced.** `fmt_forced` shows that the two relational decode directions together
  pin `fmt` on the nose. This is what makes the criticism's arithmetic wrong: one cannot
  *shrink* a fibre to buy the agreement clause, because shrinking loses the completeness
  direction and leaves `p` unconstrained outside `fmt` — which is a different, worse defect.
  So the fibre condition below is not a design choice a `fmt`-based development could decline.

* **`η` is renamed, not removed.** `survivesStore_iff` is §1's `η ⊆ ker p` with one word
  changed. The store premise does not go away under a relational format; it is restated
  against the same fibres.

## The named non-property

`NonMalleable` is the fibre condition — every two attributes in one fibre agree — and it is
**stated in order to be refuted**, which is why it is defined here and used by nothing. Two
facts about it, and they are the two reasons `docs/codec-calculus.md` gives for `ker p` not
being equality:

* **`η` normalising an `N` costs nothing** (`nonMalleable_numberCodec`). `number` reads only
  `.n` attributes and `Agree.n` is unconditional (`Calculus/Codec.lean:60`) — agreement never
  looks inside a numeral. So the store may rewrite `"1.500"` to `"1.5"` and the fibre
  condition still holds. Where `η` lives, non-malleability is *free*.

* **`drop` discarding names is fatal** (`not_nonMalleable_dropAll`). `objectCodec` under
  `.drop` with an empty field table reads *every* `M` attribute to the empty map, because
  `keepB .drop` (`Calculus/Combinators.lean`) filters away every undeclared name. Its
  whole `M` fragment is one fibre, and two attributes in it disagree at a shared key. That
  codec is `Lawful`, so this is not a pathology outside the theory: **a lawful shipped codec
  has no relational format at all.**

That is the sharpest form of the finding. The property is free exactly where §1's concession
lives and impossible exactly where §4's rest policy lives, so adopting it would not tighten a
weak spot — it would delete `object`/`drop`.

## Why this is strictly stronger than (MP)

`agree_not_transitive` is the reason the two are not the same demand. (MP) — `Lawful.agree` —
compares an accepted attribute against **the one attribute `e` wrote**; the fibre condition
compares **every pair** in the fibre. With `Agree` transitive those would coincide up to (R);
`Agree` is not transitive, and the shipped codec sits in the gap. `NonMalleable.agree` records
the one implication that does hold, so the direction of the strengthening is on the record too.
-/

namespace Calculus

/-! ## The fibre of `p`, and why it is not a choice -/

/-- **`Codec.Ker`, seen from the other side.** `Ker` says two attributes share a fibre;
    `Fmt c v` is that fibre. A relational format `fmt : Value → Set Attr` is not a rival
    presentation of a codec — it is this function, and `fmt_forced` says so. -/
def Fmt (c : Codec) (v : Value) : Set Attr := {a | c.p a = some v}

/-- Membership in a fibre is the reading equation. Stated once so nothing below has to
    unfold `Set`. -/
theorem mem_Fmt {c : Codec} {v : Value} {a : Attr} : a ∈ Fmt c v ↔ c.p a = some v :=
  Iff.rfl

/-- Two attributes share a fibre exactly when `Ker` relates them and the fibre is inhabited
    by a value — the sentence "`Fmt` and `Ker` are one definition" in the only form that can
    be checked. -/
theorem ker_of_mem_Fmt {c : Codec} {v : Value} {a a' : Attr}
    (h : a ∈ Fmt c v) (h' : a' ∈ Fmt c v) : c.Ker a a' := by
  show c.p a = c.p a'
  rw [mem_Fmt.mp h, mem_Fmt.mp h']

/-- **The forcing lemma: `fmt` is not a design choice.** Any relation satisfying both decode
    directions — sound (`a ∈ fmt v` reads back to `v`) and complete (everything reading to `v`
    is in `fmt v`) — *is* the fibre of `p`, on the nose.

    This is what closes §5.6 item 4's escape route. Faced with the agreement clause failing,
    the natural repair is to shrink `fmt v` until its members agree; this lemma says that
    repair is unavailable, because shrinking breaks completeness, and without completeness
    `p` is unconstrained outside `fmt` and can read attributes the format does not name. -/
theorem fmt_forced {c : Codec} {fmt : Value → Set Attr}
    (sound : ∀ v a, a ∈ fmt v → c.p a = some v)
    (complete : ∀ v a, c.p a = some v → a ∈ fmt v) :
    fmt = Fmt c := by
  funext v
  apply Set.ext
  intro a
  exact ⟨sound v a, complete v a⟩

/-! ## The store premise, restated against fibres

`SurvivesStore` (`Calculus/Codec.lean:231`) is §1's concession: the store is not the identity
on attributes, and all a codec needs is that it moves within a fibre. Under a relational
format that sentence is unchanged — which is the point. -/

/-- **`η ⊆ ker p`, in the format's vocabulary.** Read left to right: whatever `e` writes for
    `v`, the store's rewrite of it still lies in `v`'s fibre.

    (R) is needed in both directions and that is not an artefact: `SurvivesStore` compares
    `η a` against `a`, while the right-hand side compares `η a` against the *value* `a` came
    from, and only retraction identifies the two. So a relational presentation does not
    remove `η`; it renames the same quantified statement, and still owes (R) to state it. -/
theorem survivesStore_iff {c : Codec} (h : Lawful c) (η : Attr → Attr) :
    SurvivesStore c η ↔ ∀ v a, c.e v = some a → η a ∈ Fmt c v := by
  constructor
  · intro hη v a he
    show c.p (η a) = some v
    rw [hη a ⟨v, he⟩, h.retract he]
  · intro hη a ⟨v, he⟩
    show c.p (η a) = c.p a
    rw [hη v a he, h.retract he]

/-! ## The property, named in order to fail -/

/-- **Non-malleability**, in the verified-formats community's vocabulary: every two attributes
    a codec reads to one value agree. Their CBOR statement is the equality version; ours is
    weakened to `Agree`, and even weakened it fails.

    Nothing in this development uses it. It exists so that the answer to "why not adopt this?"
    is a theorem rather than a paragraph. -/
def NonMalleable (c : Codec) : Prop :=
  ∀ v a a', a ∈ Fmt c v → a' ∈ Fmt c v → Agree a a'

/-- The implication that does hold: with (R), non-malleability entails (MP). The converse is
    the interesting direction and it fails — see `agree_not_transitive` for why the two are
    not the same demand, and `not_nonMalleable_dropAll` for a codec on the wrong side of the
    gap. -/
theorem NonMalleable.agree {c : Codec} (h : NonMalleable c)
    (hr : ∀ {t a}, c.e t = some a → c.p a = some t) {a t a'}
    (hp : c.p a = some t) (he : c.e t = some a') : Agree a' a :=
  h t a' a (hr he) hp

/-- **`Agree` is not transitive**, which is the whole reason the fibre condition is strictly
    stronger than (MP). (MP) compares an accepted attribute against the single attribute `e`
    wrote; the fibre condition compares every pair, and with a non-transitive relation those
    are different demands rather than the same demand chained.

    The witness is `L` and the vacuity of zipping against `[]`: both outer pairs agree because
    there is no shared position, and the two ends do not. -/
theorem agree_not_transitive : ∃ x y z : Attr, Agree x y ∧ Agree y z ∧ ¬ Agree x z := by
  refine ⟨.l [.null], .l [], .l [.s "x"], ?_, ?_, ?_⟩
  · exact .l _ _ (by simp)
  · exact .l _ _ (by simp)
  · intro h
    cases h with
    | l _ _ hz => exact absurd (hz (.null, .s "x") (by simp)) (by rintro ⟨⟩)

/-! ### Where it is free: the numeral

§1's concession is that the store rewrites numerals, so `number`'s `ker p` is deliberately
coarse — `survivesStore_numberCodec` (`Calculus/Combinators.lean:2292`) is that coarseness put
to work. Non-malleability survives it untouched, because `Agree.n` is unconditional: agreement
never inspects a numeral's digits. So the property costs nothing at the one place §1 gives
something up, which is precisely why reading §5.6 item 4 on its own looks harmless. -/

/-- `number` reads nothing but an `N`. -/
theorem numberCodec_p_n_inv {a : Attr} {v : Value} (h : numberCodec.p a = some v) :
    ∃ x, a = .n x := by
  cases a with
  | n x => exact ⟨x, rfl⟩
  | _ => exact nomatch h

/-- Every attribute `number` reads is an `.n`, and `Agree.n` is unconditional — so the fibre
    condition holds however wildly the store rewrote the digits. -/
theorem nonMalleable_numberCodec : NonMalleable numberCodec := by
  intro v a a' ha ha'
  obtain ⟨x, rfl⟩ := numberCodec_p_n_inv (mem_Fmt.mp ha)
  obtain ⟨y, rfl⟩ := numberCodec_p_n_inv (mem_Fmt.mp ha')
  exact .n x y

/-! ### Where it breaks: `drop`

The other reason `ker p` is not equality, and it is not a concession to the store — it is what
`§4`'s rest policy *means*. `keepB .drop sems` keeps declared names only, so an object with an
empty field table discards everything it is given. Its `M` fragment is a single fibre. -/

/-- The empty binding, at any payload type: `∅` names no key, so the payload function is
    total by vacuity. -/
def noEntries {α : Type} : MapOf α := ⟨∅, fun k => (Finset.notMem_empty _ k.2).elim⟩

/-- **The object that declares nothing and drops everything.** Chosen because it makes the
    failure minimal: no field is involved, so nothing about any particular field's codec is
    doing the work — the rest policy alone is. -/
noncomputable def dropAll : Codec := objectCodec noEntries .drop

/-- It is `Lawful`, and this is the load-bearing half of the finding. `lawful_objectCodec`'s
    three hypotheses are all quantified over the declared names, so at the empty table they
    are vacuous — no proof obligation is being dodged. -/
theorem lawful_dropAll : Lawful dropAll :=
  lawful_objectCodec (fun k => (Finset.notMem_empty _ k.2).elim)
    (fun k => (Finset.notMem_empty _ k.2).elim) (fun _ h => nomatch h)

/-- No name survives the `drop` filter when nothing is declared. -/
theorem keepB_noEntries (k : Name) : keepB .drop (noEntries (α := FieldSem)) k = false := by
  simp [keepB, noEntries, MapOf.at]

/-- A binding whose key set is empty is *the* empty binding — the dependent rewrite the
    computation below needs, isolated so it happens once. `Finset` equality cannot be
    rewritten under the payload function without it. -/
theorem mapOf_of_keys_empty {α : Type} {s : Finset Name} (h : s = ∅)
    (g : {k // k ∈ s} → α) : (⟨s, g⟩ : MapOf α) = noEntries := by
  subst h
  have hg : g = fun k => (Finset.notMem_empty _ k.2).elim :=
    funext fun k => (Finset.notMem_empty _ k.2).elim
  rw [hg]
  rfl

/-- No name survives the filter, whatever the stored item carried. -/
theorem filter_keepB_noEntries (keys : Finset Name) :
    keys.filter (fun k => keepB .drop (noEntries (α := FieldSem)) k = true) = ∅ :=
  Finset.filter_false_of_mem fun k _ => by simp [keepB_noEntries k]

/-- …and there are no fallback names to reinstate either, so the read side reconstructs
    nothing at all. Proved by `rfl` rather than by `Finset.filter_empty`, which is classical
    in this toolchain — the axiom guard sees this file. -/
theorem fbNames_noEntries (keys : Finset Name) :
    fbNames keys (noEntries (α := FieldSem)) = ∅ := rfl

/-- The stored-side guard is vacuous: it quantifies over the declared names, and there are
    none. This is the same vacuity that makes `lawful_dropAll` free. -/
theorem reqPresentB_noEntries (keys : Finset Name) :
    reqPresentB (noEntries (α := FieldSem)) keys = true := by
  unfold reqPresentB
  exact decide_eq_true fun k => (Finset.notMem_empty _ k.2).elim

/-- **Every `M` attribute reads to the empty map.** The guard is vacuous, the filter is empty,
    and there are no fallback names to reinstate, so nothing whatever of the stored item
    reaches the value. This one equation is the fibre. -/
theorem dropAll_p (keys : Finset Name) (f : {k // k ∈ keys} → Attr) :
    dropAll.p (.m keys f) = some (mapV.into noEntries) := by
  show (objRead noEntries (rcOf .drop) (keepB .drop noEntries) ⟨keys, f⟩).map mapV.into
      = some (mapV.into noEntries)
  have hemp : ∀ k : {k // k ∈ keys.filter
      (fun k => keepB .drop (noEntries (α := FieldSem)) k = true)}, False :=
    fun k => by
      have hk := (Finset.mem_filter.mp k.2).2
      rw [keepB_noEntries] at hk
      exact Bool.noConfusion hk
  simp only [objRead, if_pos (reqPresentB_noEntries keys)]
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (funImage_isSome fun k => (hemp k).elim)
  rw [hd]
  refine congrArg (fun m => some (mapV.into m)) (mapOf_of_keys_empty ?_ _)
  rw [filter_keepB_noEntries, fbNames_noEntries]
  exact Finset.empty_union ∅

/-- **The headline: a `Lawful` shipped codec with no relational format at all.** Both
    attributes carry the key `"z"`, so `Agree.m`'s premise bites there, and they disagree.

    What this rules out is not a hypothetical: `objectCodec` under `.drop` is what `src/`
    ships for an open object. Adopting the fibre condition — as §5.6 item 4 proposes — would
    not constrain that codec, it would delete it. -/
theorem not_nonMalleable_dropAll : ¬ NonMalleable dropAll := by
  intro h
  have hz := h (mapV.into noEntries)
    (.m {"z"} (fun _ => .null)) (.m {"z"} (fun _ => .s "x"))
    (dropAll_p _ _) (dropAll_p _ _)
  cases hz with
  | m _ _ _ _ hk => cases hk "z" (by simp) (by simp)

end Calculus
