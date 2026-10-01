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
/-- `Ω` writes a string as `S`. -/
theorem Ωe_str (s : String) : Ω.e (.str s) = some (.s s) := rfl
/-- `Ω` writes a number as `N`. -/
theorem Ωe_num (x : WFNumeral) : Ω.e (.num x) = some (.n x) := rfl
/-- `Ω` writes a boolean as `BOOL`. -/
theorem Ωe_bool (b : Bool) : Ω.e (.bool b) = some (.bool b) := rfl
/-- `Ω` writes a byte string as `B`. -/
theorem Ωe_bin (b : Bytes) : Ω.e (.bin b) = some (.b b) := rfl
/-- `Ω` writes `null` as `NULL`. -/
theorem Ωe_null : Ω.e .null = some .null := rfl
/-- `Ω` reads `S` as a string. -/
theorem Ωp_s (s : String) : Ω.p (.s s) = some (.str s) := rfl
/-- `Ω` reads `N` as a number. -/
theorem Ωp_n (x : WFNumeral) : Ω.p (.n x) = some (.num x) := rfl
/-- `Ω` reads `BOOL` as a boolean. -/
theorem Ωp_bool (b : Bool) : Ω.p (.bool b) = some (.bool b) := rfl
/-- `Ω` reads `B` as a byte string. -/
theorem Ωp_b (b : Bytes) : Ω.p (.b b) = some (.bin b) := rfl
/-- `Ω` reads `NULL` as `null`. -/
theorem Ωp_null : Ω.p .null = some .null := rfl

/-! ## Inclusion lemmas, one per combinator -/

/-- A restriction of a restriction of `Ω` is a restriction of `Ω`. -/
theorem sub_restrict {c : Codec} (h : Sub c Ω) (q : Value → Bool) : Sub (c.restrict q) Ω :=
  Alg.sub_trans (sub_restrict_self c q) h

/-- **Each ground base is a restriction of `Ω`**: a point codec sends a datum only to itself. -/
theorem sub_baseCodec (k : GroundKind) : Sub (baseCodec k) Ω := fun o x y h => by
  obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
  have hx : x = (Calculus.Alg.Ctor.side k.prism k.prism o.c).into z := (Calculus.Alg.Ctor.side k.prism k.prism o.c).into_out hz
  rcases o with ⟨⟨_ | _, _ | _⟩, ho⟩
  · exact absurd rfl ho
  · simp only [Calculus.Alg.Ctor.side] at hx ⊢; subst hx; cases k <;> rfl
  · simp only [Calculus.Alg.Ctor.side] at hx ⊢; subst hx
    exact lawful_opaq.retract (by cases k <;> rfl)
  · exact absurd rfl ho

/-- A literal is a restriction of `Ω`, because a literal restricts its base. -/
theorem sub_literal (k : GroundKind) (x : k.Carrier) : Sub (literalCodec k x) Ω :=
  have h := sub_restrict (sub_baseCodec k) (inL k x)
  .ofEP (h .host) (h .dual)

/-- `setAt` keeps an inclusion of graphs. -/
theorem setAt_sub {α : Type} {o : Alg.Orient} {c d : Codec} (h : Sub c d) {inj : α → Attr}
    {S : NEFinset α} {a : Attr} (he : setAt o c inj S = some a) : setAt o d inj S = some a := by
  rw [← setAt_congr (c := c) (fun x hx => by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (setAt_elem he x hx)
    rw [hy, h o _ _ hy])]
  exact he

/-- A set over a restriction of `Ω` is a restriction of `Ω`. -/
theorem sub_setCodec {c : Codec} (h : Sub c Ω) : Sub (setCodec c) Ω := by
  refine .ofEP (fun v a he => ?_) (fun a v hp => ?_)
  · rcases setCodec_f_eq.mp he with ⟨S, rfl, hS⟩ | ⟨S, rfl, hS⟩ | ⟨S, rfl, hS⟩
    · rw [Ωe_strSet]; exact setAt_sub h hS
    · rw [Ωe_numSet]; exact setAt_sub h hS
    · rw [Ωe_binSet]; exact setAt_sub h hS
  · rcases setCodec_f_eq.mp hp with ⟨S, rfl, hS⟩ | ⟨S, rfl, hS⟩ | ⟨S, rfl, hS⟩
    · rw [Ωp_ss]; exact setAt_sub h hS
    · rw [Ωp_ns]; exact setAt_sub h hS
    · rw [Ωp_bs]; exact setAt_sub h hS

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
  list L hL := by cases hL; exact ⟨Ωe_arr, Ωp_l⟩
  map F hF := by cases hF; exact ⟨fun m => Ωe_map m.keys m.get, fun m => Ωp_m m.keys m.get⟩
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



/-- The image of a nonempty set under `some` is the set. -/
theorem neSetImage_id {α : Type} [DecidableEq α] (S : NEFinset α) :
    neSetImage (fun x => some x) S = some S := by
  refine neSetImage_eq_setImage.mpr (setImage_eq (fun _ _ => rfl)
    (fun _ _ _ _ _ h1 h2 => Option.some.inj (h1.trans h2.symm)) (fun y => ?_))
  simp

/-! ## `opaque` is the identity, and the held-free fragment is self-dual

With one carrier, `Ω` sends each datum to itself, at both orientations. A lawful codec below `Ω`
can then only send a datum to itself, so it is a partial identity: an idempotent of the inverse
monoid of the carrier. Its write and its read are one map, and a fact of such a codec needs no
orientation. The direction of a codec lives in its adapters (`held`) and in its one-sided
decorations, not in its domain. -/

mutual
/-- **`opaque` is the identity**, at the host. -/
theorem Ω_id : ∀ a : Attr, Ω.e a = some a
  | .s _ | .n _ | .b _ | .bool _ | .null => rfl
  | .ss S => by
      rw [Ωe_strSet]; unfold setAt
      rw [show (fun x => (Ω.e (Attr.s x)).bind sC.out) = fun x => some x from funext fun x => rfl,
        neSetImage_id]
  | .ns S => by
      obtain ⟨x₀, hx₀⟩ := S.2
      rw [Ωe_numSet]; unfold setAt
      rw [neSetImage_none (setImage_none_of hx₀ rfl),
        show (fun x => (Ω.e (Attr.n x)).bind nC.out) = fun x => some x from funext fun x => rfl,
        neSetImage_id]
  | .bs S => by
      obtain ⟨x₀, hx₀⟩ := S.2
      rw [Ωe_binSet]; unfold setAt
      rw [neSetImage_none (setImage_none_of hx₀ rfl), neSetImage_none (setImage_none_of hx₀ rfl),
        show (fun x => (Ω.e (Attr.b x)).bind bC.out) = fun x => some x from funext fun x => rfl,
        neSetImage_id]; rfl
  | .l as => by rw [Ωe_arr, ΩL_id as]; rfl
  | .m keys g => by
      rw [Ωe_map, Alg.funImage_eq (f := g) fun k => Ω_id (g k)]; rfl
/-- …and over a list. -/
theorem ΩL_id : ∀ as : List Attr, traverse Ω.e as = some as
  | [] => rfl
  | a :: as => by simp only [traverse]; rw [Ω_id a, ΩL_id as]
end

/-- **`opaque` is the identity at every orientation**: the read inverts the write. -/
theorem Ω_f : ∀ (o : Alg.Orient) (x : Attr), Ω.f o x = some x :=
  Alg.Orient.both (P := fun o => ∀ x, Ω.f o x = some x) Ω_id
    fun x => lawful_opaq.retract (Ω_id x)

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
