-- `Finset` and `Fintype`, for the key set of a map and for the elements of a set: a map writes
-- where every entry writes, and `Fintype` decides that quantifier. No other declaration of the
-- algebra needs the two.
import Mathlib.Data.Fintype.Basic
import Calculus.Alg.Codec

/-!
# The image of a map and of a set, over any key type

A map codec moves the values of a map and keeps its keys. `funImage` is that move on the
partial side: the image is defined when every entry is defined. The keys are a `Finset` of any
type, so the statement reads no fact of a store.

A set codec moves the elements of a set. `setImage` is that move: the image is defined when
every element is defined and no two elements collide. Its two laws read the pair of the element
codec, so they take the carrier as a parameter.
-/

namespace Calculus.Alg

/-- **The map analogue of `setImage`, and much simpler.** A set codec can collide two
    elements onto one; a map cannot, because the names are fixed and the codec only moves
    the values. So all this has to do is demand that every value succeeds. -/
noncomputable def funImage {κ β : Type} {keys : Finset κ}
    (g : {k // k ∈ keys} → Option β) : Option ({k // k ∈ keys} → β) :=
  if h : ∀ k, (g k).isSome = true then some (fun k => (g k).get (h k)) else none

theorem funImage_some {κ β : Type} {keys : Finset κ} {g : {k // k ∈ keys} → Option β}
    {f : {k // k ∈ keys} → β} (h : funImage g = some f) : ∀ k, g k = some (f k) := by
  unfold funImage at h
  split at h
  · next hall =>
      intro k
      have := Option.some.inj h
      subst this
      exact (Option.some_get (hall k)).symm
  · exact nomatch h

theorem funImage_isSome {κ β : Type} {keys : Finset κ} {g : {k // k ∈ keys} → Option β}
    (hall : ∀ k, (g k).isSome = true) : (funImage g).isSome = true := by
  unfold funImage; rw [dif_pos hall]; rfl

/-- …and exactly when, which is what the exactness rows need: `funImage` is defined at a
    key set precisely where every entry is. -/
theorem funImage_isSome_iff {κ β : Type} {keys : Finset κ}
    {g : {k // k ∈ keys} → Option β} :
    (funImage g).isSome = true ↔ ∀ k, (g k).isSome = true := by
  refine ⟨fun h k => ?_, funImage_isSome⟩
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp h
  rw [funImage_some hf k]; rfl

theorem funImage_eq {κ β : Type} {keys : Finset κ} {g : {k // k ∈ keys} → Option β}
    {f : {k // k ∈ keys} → β} (h : ∀ k, g k = some (f k)) : funImage g = some f := by
  unfold funImage
  rw [dif_pos (fun k => by rw [h k]; rfl)]
  congr 1
  funext k
  exact Option.some.inj ((Option.some_get _).trans (h k))

/-! ## The image of a set -/

section SetImage
variable {V M : Type} {member : V → M}

/-- **The set image.** Map a finite set through a partial function, refusing if an element
    fails *or if two elements collide*.

    Not `Finset.image`, for two reasons. It dedups, which is the wrong answer here — (R)
    needs the element map injective, and collapsing two elements makes `p (e v) = v`
    unsatisfiable — so a collision must be refused, not absorbed. And its API is classical:
    `Finset.mem_image` and `Multiset.mem_dedup` depend on `Classical.choice`, which §3's
    axiom base does not admit. A `Nodup`-guarded `Multiset.map` needs neither. -/
noncomputable def setImage {α β : Type} [DecidableEq β]
    (f : α → Option β) (S : Finset α) : Option (Finset β) :=
  if h : ∀ x ∈ S, (f x).isSome then
    if hn : (S.attach.val.map (fun x => (f x.1).get (h x.1 x.2))).Nodup then
      some ⟨_, hn⟩
    else none
  else none

/-- Every element of the source maps. -/
theorem setImage_some {α β : Type} [DecidableEq β] {f : α → Option β} {S : Finset α}
    {T : Finset β} (h : setImage f S = some T) : ∀ x ∈ S, (f x).isSome := by
  unfold setImage at h
  split at h
  · next hall => exact hall
  · exact nomatch h

/-- …and the image contains exactly the elements' images. -/
theorem mem_setImage {α β : Type} [DecidableEq β] {f : α → Option β} {S : Finset α}
    {T : Finset β} (h : setImage f S = some T) (y : β) :
    y ∈ T ↔ ∃ x ∈ S, f x = some y := by
  unfold setImage at h
  split at h
  · next hall =>
    split at h
    · next hn =>
      injection h with h
      subst h
      constructor
      · intro hy
        simp only [Finset.mem_mk, Multiset.mem_map] at hy
        obtain ⟨x, -, hxy⟩ := hy
        exact ⟨x.1, x.2, by rw [← hxy]; exact (Option.some_get (hall x.1 x.2)).symm⟩
      · rintro ⟨x, hx, hfx⟩
        simp only [Finset.mem_mk, Multiset.mem_map]
        refine ⟨⟨x, hx⟩, Multiset.mem_attach _ _, ?_⟩
        rw [Option.get_of_mem (hall x hx) hfx]
    · exact nomatch h
  · exact nomatch h

/-- A non-empty set has a non-empty image. -/
theorem setImage_nonempty {α β : Type} [DecidableEq β] {f : α → Option β} {S : Finset α}
    {T : Finset β} (h : setImage f S = some T) (hs : S.Nonempty) : T.Nonempty := by
  obtain ⟨x, hx⟩ := hs
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (setImage_some h x hx)
  exact ⟨y, (mem_setImage h y).mpr ⟨x, hx, hy⟩⟩

/-- **The constructor for `setImage`.** Given that every element maps, that the map is
    injective on the set, and a candidate image with the right membership, the image *is*
    that candidate. The injectivity hypothesis is what (R) supplies, and what `Finset.image`
    would have thrown away by dedupping. -/
theorem setImage_eq {α β : Type} [DecidableEq β] {f : α → Option β} {S : Finset α}
    {U : Finset β}
    (hall : ∀ x ∈ S, (f x).isSome)
    (hinj : ∀ x₁ ∈ S, ∀ x₂ ∈ S, ∀ y, f x₁ = some y → f x₂ = some y → x₁ = x₂)
    (hmem : ∀ y, y ∈ U ↔ ∃ x ∈ S, f x = some y) :
    setImage f S = some U := by
  unfold setImage
  rw [dif_pos hall]
  have hnd : (S.attach.val.map (fun x => (f x.1).get (hall x.1 x.2))).Nodup := by
    refine Multiset.Nodup.map_on ?_ S.attach.nodup
    intro x hx y hy hxy
    have hfx : f x.1 = some ((f x.1).get (hall x.1 x.2)) := (Option.some_get _).symm
    have hfy : f y.1 = some ((f y.1).get (hall y.1 y.2)) := (Option.some_get _).symm
    rw [hxy] at hfx
    exact Subtype.ext (hinj x.1 x.2 y.1 y.2 _ hfx hfy)
  rw [dif_pos hnd]
  congr 1
  apply Finset.ext
  intro y
  simp only [Finset.mem_mk, Multiset.mem_map, hmem y]
  constructor
  · rintro ⟨x, -, hxy⟩
    exact ⟨x.1, x.2, by rw [← hxy]; exact (Option.some_get (hall x.1 x.2)).symm⟩
  · rintro ⟨x, hx, hfx⟩
    exact ⟨⟨x, hx⟩, Multiset.mem_attach _ _, by rw [Option.get_of_mem (hall x hx) hfx]⟩

/-- **Inversion.** If the element map has a left inverse on its image, the set image
    inverts too. This is (R) lifted from elements to sets, and it is where the collision
    guard earns its place: without injectivity the image would be smaller than the source
    and could not invert. -/
theorem setImage_inv {α β : Type} [DecidableEq α] [DecidableEq β]
    {f : α → Option β} {g : β → Option α} {S : Finset α} {T : Finset β}
    (hfg : ∀ x y, f x = some y → g y = some x)
    (h : setImage f S = some T) : setImage g T = some S := by
  refine setImage_eq ?_ ?_ ?_
  · intro y hy
    obtain ⟨x, hx, hfx⟩ := (mem_setImage h y).mp hy
    rw [hfg x y hfx]; rfl
  · intro y₁ hy₁ y₂ hy₂ x hg₁ hg₂
    obtain ⟨x₁, hx₁, hf₁⟩ := (mem_setImage h y₁).mp hy₁
    obtain ⟨x₂, hx₂, hf₂⟩ := (mem_setImage h y₂).mp hy₂
    rw [hfg x₁ y₁ hf₁] at hg₁
    rw [hfg x₂ y₂ hf₂] at hg₂
    cases Option.some.inj hg₁
    cases Option.some.inj hg₂
    exact Option.some.inj (hf₁.symm.trans hf₂)
  · intro x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (setImage_some h x hx)
      exact ⟨y, (mem_setImage h y).mpr ⟨x, hx, hy⟩, hfg x y hy⟩
    · rintro ⟨y, hy, hgy⟩
      obtain ⟨x', hx', hf'⟩ := (mem_setImage h y).mp hy
      rw [hfg x' y hf'] at hgy
      cases Option.some.inj hgy
      exact hx'

/-- One failing element sinks the image. -/
theorem setImage_none_of {α β : Type} [DecidableEq β] {f : α → Option β} {S : Finset α}
    {x : α} (hx : x ∈ S) (hf : f x = none) : setImage f S = none := by
  unfold setImage
  rw [dif_neg]
  intro hall
  have := hall x hx
  rw [hf] at this
  exact absurd this (by simp)

/-- The image succeeds when every element maps and no two collide. -/
theorem setImage_isSome_of {α β : Type} [DecidableEq β] {f : α → Option β} {S : Finset α}
    (hall : ∀ x ∈ S, (f x).isSome)
    (hinj : ∀ x₁ ∈ S, ∀ x₂ ∈ S, ∀ y, f x₁ = some y → f x₂ = some y → x₁ = x₂) :
    (setImage f S).isSome = true := by
  unfold setImage
  rw [dif_pos hall]
  have hnd : (S.attach.val.map (fun x => (f x.1).get (hall x.1 x.2))).Nodup := by
    refine Multiset.Nodup.map_on ?_ S.attach.nodup
    intro x hx y hy hxy
    have hfx : f x.1 = some ((f x.1).get (hall x.1 x.2)) := (Option.some_get _).symm
    have hfy : f y.1 = some ((f y.1).get (hall y.1 y.2)) := (Option.some_get _).symm
    rw [hxy] at hfx
    exact Subtype.ext (hinj x.1 x.2 y.1 y.2 _ hfx hfy)
  rw [dif_pos hnd]
  rfl

/-- **The image only looks at the set.** Two element maps agreeing on `S` have the same
    image — needed because `Codec.restrict` changes `e` everywhere and the set only sees it
    at its own members. -/
theorem setImage_congr {α β : Type} [DecidableEq β] {f g : α → Option β} {S : Finset α}
    (h : ∀ x ∈ S, f x = g x) : setImage f S = setImage g S := by
  have hiff : (∀ x ∈ S, (f x).isSome) ↔ (∀ x ∈ S, (g x).isSome) :=
    ⟨fun hh x hx => (h x hx) ▸ hh x hx, fun hh x hx => (h x hx).symm ▸ hh x hx⟩
  unfold setImage
  split
  · next hf =>
    have hg := hiff.mp hf
    rw [dif_pos hg]
    have hmap : (S.attach.val.map (fun x => (f x.1).get (hf x.1 x.2)))
        = (S.attach.val.map (fun x => (g x.1).get (hg x.1 x.2))) := by
      refine Multiset.map_congr rfl (fun x _ => ?_)
      exact Option.some.inj (by rw [Option.some_get, Option.some_get, h x.1 x.2])
    simp only [hmap]
  · next hf =>
    rw [dif_neg (fun hg => hf (hiff.mpr hg))]

end SetImage

/-! ## The fields of an object

A field and a rest policy each carry a codec. The presence guards and the rest codec read the
shape of a field and never its codec, so each one takes the carrier as a parameter, and the
key type too. -/

/-- A field, denoted: presence marker plus the attribute pair. -/
inductive FieldSem (V M : Type) where
  | req (c : Codec V M)
  | opt (c : Codec V M)

/-- A rest policy, denoted. -/
inductive RestSem (V M : Type) where
  | refuse
  | codec (c : Codec V M)

section Fields
variable {V M : Type}

/-- The codec of a field. -/
def FieldSem.codec : FieldSem V M → Codec V M
  | .req c => c
  | .opt c => c

/-- What each guard asks of one binding, named so the guards themselves are a single
    quantifier over the key set rather than a `List.all` over a row. The write side and the
    read side ask the same: a `req` name is present. -/
def valPresentAt {κ : Type} [DecidableEq κ] (names : Finset κ) : κ → FieldSem V M → Bool
  | _, .opt _ => true
  | k, _ => decide (k ∈ names)

/-- The rest policy's codec, where it has one. -/
def rcOf : RestSem V M → Option (Codec V M)
  | .codec c => some c
  | _ => none

/-- Two fields of one shape whose codecs stand in `R`. -/
def FieldSem.Rel (R : Codec V M → Codec V M → Prop) : FieldSem V M → FieldSem V M → Prop
  | .req c₁, .req c₂ => R c₁ c₂
  | .opt c₁, .opt c₂ => R c₁ c₂
  | _, _ => False

/-- Two rest policies of one shape whose codecs stand in `R`. -/
def RestSem.Rel (R : Codec V M → Codec V M → Prop) : RestSem V M → RestSem V M → Prop
  | .refuse, .refuse => True
  | .codec c₁, .codec c₂ => R c₁ c₂
  | _, _ => False

variable {R : Codec V M → Codec V M → Prop}

/-- Related fields have related codecs. -/
theorem FieldSem.Rel.codec : ∀ {f₁ f₂ : FieldSem V M}, FieldSem.Rel R f₁ f₂ →
    R f₁.codec f₂.codec
  | .req _, .req _, h => h
  | .opt _, .opt _, h => h

/-- The presence guard reads the shape of a field, never its codec. -/
theorem FieldSem.Rel.valPresentAt {κ : Type} [DecidableEq κ] (names : Finset κ) (k : κ) :
    ∀ {f₁ f₂ : FieldSem V M}, FieldSem.Rel R f₁ f₂ →
      Alg.valPresentAt names k f₁ = Alg.valPresentAt names k f₂
  | .req _, .req _, _ => rfl
  | .opt _, .opt _, _ => rfl

/-- Related rest policies give related rest codecs. -/
theorem RestSem.Rel.rcOf : ∀ {r₁ r₂ : RestSem V M}, RestSem.Rel R r₁ r₂ →
    Option.Rel R (Alg.rcOf r₁) (Alg.rcOf r₂)
  | .refuse, .refuse, _ => .none
  | .codec _, .codec _, h => .some h

/-- A property of the rest policy's codec, from one per `rest = .codec c`. -/
theorem rcOf_forall {P : Codec V M → Prop} {rest : RestSem V M}
    (h : ∀ c, rest = .codec c → P c) : ∀ c ∈ rcOf rest, P c := by
  intro c hc
  cases rest with
  | codec c' =>
    replace hc : some c' = some c := hc
    cases hc
    exact h c rfl
  | refuse => exact nomatch hc

end Fields

end Calculus.Alg

namespace Calculus

/-! ## The keyed map

A key *set* with a function on it, which is what a stored map is, and what §4's field table is
one stratum up. A `List (String × α)` admits two orderings of one payload and a repeated key;
both are properties of this type instead.

The keys are strings. The store reads a name as a string, and so does the term language: §4's
field table is a `MapOf` of slots. Nothing about it is codec-shaped: a `Finset`, a function, and
a lookup.

**The structure keeps its name `Calculus.MapOf`, outside `Alg`.** Callers extend it
(`MapOf.restrict`, `MapOf.disjUnion`) and reach each extension by field notation. An abbreviation
over a generic structure sends field notation to the generic namespace, where no extension is. -/

/-- A map's payload: the key set, and the values on it. A dependent pair rather than a
    list of pairs, because that is what a stored map is. -/
structure MapOf (α : Type) where
  keys : Finset String
  get  : {k // k ∈ keys} → α

/-- Two map payloads are equal when their name sets are and their values agree on them.
    The dependent pair needs this said once; the list representation got it from
    `List.ext`. -/
theorem MapOf.ext {α : Type} {p q : MapOf α} (hk : p.1 = q.1)
    (hf : ∀ k (h₁ : k ∈ p.1) (h₂ : k ∈ q.1), p.2 ⟨k, h₁⟩ = q.2 ⟨k, h₂⟩) : p = q := by
  obtain ⟨kp, fp⟩ := p
  obtain ⟨kq, fq⟩ := q
  cases hk
  exact congrArg (MapOf.mk kp) (funext fun k => hf k.1 k.2 k.2)

/-- The value a `MapOf` gives a name, where it gives one — the lookup a key set with a
    function on it has. Generic because the *term*'s field table needs it too. -/
def MapOf.at {α : Type} (m : MapOf α) (k : String) : Option α :=
  if h : k ∈ m.keys then some (m.get ⟨k, h⟩) else none

/-- A declared name is one the table's key set carries, and conversely. -/
theorem MapOf.at_eq_some {α : Type} {m : MapOf α} {k : String} {x : α} :
    m.at k = some x ↔ ∃ h : k ∈ m.keys, m.get ⟨k, h⟩ = x := by
  simp only [MapOf.at]
  by_cases h : k ∈ m.1
  · rw [dif_pos h]
    exact ⟨fun he => ⟨h, Option.some.inj he⟩, fun ⟨_, he⟩ => by rw [← he]⟩
  · rw [dif_neg h]
    exact Iff.intro (fun he => nomatch he) (fun ⟨h', _⟩ => absurd h' h)

/-- Every key of the table is declared, at the value the table gives it. -/
theorem MapOf.at_of_mem {α : Type} {m : MapOf α} (k : {k // k ∈ m.1}) :
    m.at k.1 = some (m.2 k) := by
  simp only [MapOf.at, dif_pos k.2]

/-- A property of every value is a property of every declared name's value. -/
theorem MapOf.at_forall {α : Type} {m : MapOf α} {Q : α → Prop}
    (h : ∀ k, Q (m.2 k)) {k x} (hm : m.at k = some x) : Q x := by
  obtain ⟨hk, rfl⟩ := MapOf.at_eq_some.mp hm
  exact h ⟨k, hk⟩

end Calculus
