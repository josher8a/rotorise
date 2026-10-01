import Calculus.Dynamo.Lang.Denote
import Calculus.Lang.HeldFree

variable {α : Calculus.Table}

/-!
# Held-free terms are restrictions of `opaque`

A term with no `held` does not change the carrier. Each combinator either restricts its
subterm or composes subterms through the structure that `opaque` itself uses. So the write
graph and the read graph of a held-free term lie inside the graphs of `opaque`.
`confluence_W` and `confluence_R` state the two inclusions. `sub_denote` proves them from
`Alg.sub_denote`, one mutual induction over `Term`, `Body`, `ObjectSlot`, the list and the
option, for every universe. The instance `Ω_topLaws` gives the laws of `Ω` that the induction
reads.

`Sub c d` is the inclusion of graphs on both halves. The set cases go through `setAt_congr` and
`setAt_congr`.

The file sits below the meet because the meet's `set` row reads it: over a held-free element, a
set writes and reads exactly where each element does. `Confluence.lean` holds the payoffs.
-/

namespace Calculus
/-! ## Inclusion lemmas, one per combinator -/

/-- A restriction of a restriction of `Ω` is a restriction of `Ω`. -/
theorem sub_restrict {c : Codec} (h : Sub c Ω) (q : Value → Bool) : Sub (c.restrict q) Ω :=
  Alg.sub_trans (sub_restrict_self c q) h

/-- **Each ground base is a restriction of `Ω`**: a point codec at one prism sends a datum only
    to itself. -/
theorem sub_baseCodec (k : GroundKind) : Sub (baseCodec k) Ω := fun o x y h => by
  obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
  exact congrArg some (k.prism.into_out hz)

/-- A literal is a restriction of `Ω`, because a literal restricts its base. -/
theorem sub_literal (k : GroundKind) (x : k.Carrier) : Sub (literalCodec k x) Ω :=
  sub_restrict (sub_baseCodec k) (inL k x)

/-- `setAt` keeps an inclusion of graphs. -/
theorem setAt_sub {α : Type} {o : Alg.Orient} {c d : Codec} (h : Sub c d) {inj : α → Attr}
    {S : NEFinset α} {a : Attr} (he : setAt o c inj S = some a) : setAt o d inj S = some a := by
  rw [← setAt_congr (c := c) (fun x hx => by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (setAt_elem he x hx)
    rw [hy, h o _ _ hy])]
  exact he

/-- The image of a nonempty set under `some` is the set. -/
theorem neSetImage_id {α : Type} [DecidableEq α] (S : NEFinset α) :
    neSetImage (fun x => some x) S = some S := by
  refine neSetImage_eq_setImage.mpr (setImage_eq (fun _ _ => rfl)
    (fun _ _ _ _ _ h1 h2 => Option.some.inj (h1.trans h2.symm)) (fun y => ?_))
  simp

/-- `Ω` moves a string set to itself, at each orientation. -/
theorem setAt_Ω_s (o : Alg.Orient) (S : NEFinset String) : setAt o Ω Attr.s S = some (.ss S) := by
  unfold setAt
  rw [show (fun x => (Ω.f o (Attr.s x)).bind sC.out) = fun x => some x from funext fun x => rfl,
    neSetImage_id]

/-- …a number set. -/
theorem setAt_Ω_n (o : Alg.Orient) (S : NEFinset WFNumeral) : setAt o Ω Attr.n S = some (.ns S) := by
  obtain ⟨x₀, hx₀⟩ := S.2
  unfold setAt
  rw [neSetImage_none (setImage_none_of hx₀ rfl),
    show (fun x => (Ω.f o (Attr.n x)).bind nC.out) = fun x => some x from funext fun x => rfl,
    neSetImage_id]

/-- …and a binary set. -/
theorem setAt_Ω_b (o : Alg.Orient) (S : NEFinset Bytes) : setAt o Ω Attr.b S = some (.bs S) := by
  obtain ⟨x₀, hx₀⟩ := S.2
  unfold setAt
  rw [neSetImage_none (setImage_none_of hx₀ rfl), neSetImage_none (setImage_none_of hx₀ rfl),
    show (fun x => (Ω.f o (Attr.b x)).bind bC.out) = fun x => some x from funext fun x => rfl,
    neSetImage_id]; rfl

/-- A set over a restriction of `Ω` is a restriction of `Ω`. -/
theorem sub_setCodec {c : Codec} (h : Sub c Ω) : Sub (setCodec c) Ω := fun o x y hc => by
  rcases setCodec_f_eq.mp hc with ⟨S, rfl, hS⟩ | ⟨S, rfl, hS⟩ | ⟨S, rfl, hS⟩
  · exact (setAt_Ω_s o S).symm.trans (setAt_sub h hS)
  · exact (setAt_Ω_n o S).symm.trans (setAt_sub h hS)
  · exact (setAt_Ω_b o S).symm.trans (setAt_sub h hS)

/-- The selector returns the answer of one option, and nothing else. -/
theorem select_some {A B : Type} {os : List Codec} {run : Codec → A → Option B} {x : A} {y : B}
    (h : select os run x = some y) :
    ∃ o ∈ os, run o x = some y := by
  obtain ⟨o, ho, -, hr⟩ := select_admits h
  exact ⟨o, ho, hr⟩

/-! ## Held-free terms -/

-- A term is **held-free** when no `held` occurs in the term: `Alg.HF`, the test `hasHeld` at
-- `false`. The names are aliases, so a closed term is shown held-free by `rfl`.
export Alg (HF HFS HFL HFO)

/-- The laws of `Ω` that the held-free theory reads: each primitive is below `Ω`, `Ω` acts as the
    `arr` and `map` formers, and a set over a restriction of `Ω` is a restriction of `Ω`. The
    laws read no orientation, so one instance serves both. -/
instance Ω_topLaws (o : Alg.Orient) : Alg.TopLaws ⟨dynSig, o⟩ where
  ground
    | .base k => sub_baseCodec k
    | .literal k x => sub_literal k x
  set L hL c hc := by cases hL; exact sub_setCodec hc

/-- **Confluence**, closed: the denotation of a held-free term is a restriction of `Ω`. -/
theorem sub_denote (t : Term) (h : HF t) : Sub (denote α t) Ω :=
  Alg.sub_denote t h

/-- **(W)**: a held-free term writes only what `opaque` writes. -/
theorem confluence_W {t : Term} (h : HF t) {v a} (he : (denote α t).e v = some a) :
    (denote α .opaq).e v = some a := sub_denote t h .host _ _ he

/-- **(R)**: a held-free term reads only what `opaque` reads. -/
theorem confluence_R {t : Term} (h : HF t) {a v} (hp : (denote α t).p a = some v) :
    (denote α .opaq).p a = some v := sub_denote t h .dual _ _ hp



/-! ## `opaque` is the identity, and the held-free fragment is self-dual

With one carrier, `Ω` sends each datum to itself, at both orientations. A lawful codec below `Ω`
can then only send a datum to itself, so it is a partial identity: an idempotent of the inverse
monoid of the carrier. Its write and its read are one map, and a fact of such a codec needs no
orientation. The direction of a codec lives in its adapters (`held`) and in its one-sided
decorations, not in its domain. -/

/-- **`opaque` is the identity at every orientation**: the read inverts the write. -/
theorem Ω_f (o : Alg.Orient) (x : Attr) : Ω.f o x = some x := rfl

/-- **A codec below `opaque` sends a datum only to itself**, at each orientation. -/
theorem sub_fix {c : Codec} (h : Sub c Ω) {o : Alg.Orient} {x y : Attr}
    (hc : c.f o x = some y) : y = x :=
  Option.some.inj ((h o x y hc).symm.trans (Ω_f o x))

/-! ## A set over a restriction of `Ω`, element by element

A restriction of `Ω` sends each element to itself (`sub_fix`). So a set over one writes and reads
exactly where each element does: the element map is injective and lands in one wire family by
construction. The meet's `set` row reads
these. -/

/-- **Over a restriction of `Ω`, a set moves exactly where every element does**, at each
    orientation. -/
theorem setCodec_isSome_of_sub {c : Codec} (h : Sub c Ω) (o : Alg.Orient) (x : Attr) :
    ((setCodec c).f o x).isSome = true ↔
      (match x with
        | .ss S => ∀ s ∈ S.1, (c.f o (.s s)).isSome = true
        | .ns S => ∀ n ∈ S.1, (c.f o (.n n)).isSome = true
        | .bs S => ∀ b ∈ S.1, (c.f o (.b b)).isSome = true
        | _ => False) := by
  cases x
  case ss S =>
    refine ⟨fun he s hs => ?_, fun hall => ?_⟩
    · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp he; exact setAt_elem ha s hs
    · have hc : neSetImage (fun x => (c.f o (Attr.s x)).bind sC.out) S =
          neSetImage (fun x => some x) S := neSetImage_congr fun x hx => by
        obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hall x hx)
        rw [ha, sub_fix h ha]; rfl
      show (setAt o c Attr.s S).isSome = true
      unfold setAt; rw [hc, neSetImage_id]; rfl
  case ns S =>
    refine ⟨fun he s hs => ?_, fun hall => ?_⟩
    · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp he; exact setAt_elem ha s hs
    · obtain ⟨x₀, hx₀⟩ := S.2
      have hS : neSetImage (fun x => (c.f o (Attr.n x)).bind sC.out) S = none :=
        neSetImage_none (setImage_none_of hx₀ (by
          obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hall x₀ hx₀)
          rw [ha, sub_fix h ha]; rfl))
      have hN : neSetImage (fun x => (c.f o (Attr.n x)).bind nC.out) S =
          neSetImage (fun x => some x) S := neSetImage_congr fun x hx => by
        obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hall x hx)
        rw [ha, sub_fix h ha]; rfl
      show (setAt o c Attr.n S).isSome = true
      unfold setAt; rw [hS, hN, neSetImage_id]; rfl
  case bs S =>
    refine ⟨fun he s hs => ?_, fun hall => ?_⟩
    · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp he; exact setAt_elem ha s hs
    · obtain ⟨x₀, hx₀⟩ := S.2
      have hS : neSetImage (fun x => (c.f o (Attr.b x)).bind sC.out) S = none :=
        neSetImage_none (setImage_none_of hx₀ (by
          obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hall x₀ hx₀)
          rw [ha, sub_fix h ha]; rfl))
      have hN : neSetImage (fun x => (c.f o (Attr.b x)).bind nC.out) S = none :=
        neSetImage_none (setImage_none_of hx₀ (by
          obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hall x₀ hx₀)
          rw [ha, sub_fix h ha]; rfl))
      have hB : neSetImage (fun x => (c.f o (Attr.b x)).bind bC.out) S =
          neSetImage (fun x => some x) S := neSetImage_congr fun x hx => by
        obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hall x hx)
        rw [ha, sub_fix h ha]; rfl
      show (setAt o c Attr.b S).isSome = true
      unfold setAt; rw [hS, hN, hB, neSetImage_id]; rfl
  all_goals exact ⟨(fun h => nomatch h), (fun h => h.elim)⟩



end Calculus
