import Calculus.Alg.Positions
import Calculus.Alg.Maps

/-!
# The list and the object, over any carriers

A container reads a universe through two prisms onto a canonical carrier and one member: a list
prism pair onto `List`, and a keyed-map prism pair onto `MapOf`. Each container is
`carriedCodec` between its two prisms. So the laws of the payload pair are proved one time here,
and a universe supplies only its prisms and the member that its stored prism stamps.
-/

namespace Calculus.Alg

variable {V M : Type} {member : V → M}

/-! ## `list` (§3): one prefix, at most one spread, one suffix -/

section List
variable (pV : Ctor (List V) V) (pA : Ctor (List V) V) (μL : M)

/-- §3 `(list)`: the positional product over a prefix, a spread and a suffix, between two list
    prisms. -/
abbrev listCodec (pre : List (Codec V M)) (spread : Option (Codec V M))
    (suf : List (Codec V M)) : Codec V M :=
  carriedCodec pV pA μL
    (fun vs => ∃ ps, alignL pre spread suf vs = some ps ∧ ∀ p ∈ ps, p.1.T p.2)
    (fun vs => (alignL pre spread suf vs).bind (traverse fun cv => cv.1.e cv.2))
    (fun as => (alignL pre spread suf as).bind (traverse fun ca => ca.1.p ca.2))

variable {pV pA μL} {pre : List (Codec V M)} {sp : Option (Codec V M)}
  {suf : List (Codec V M)}

/-- A list is lawful: the alignment puts each position on its own codec. -/
theorem lawful_listCodec (hμ : ∀ y, member (pA.into y) = μL)
    (hpre : ∀ c ∈ pre, Lawful member c) (hsp : ∀ c ∈ sp, Lawful member c)
    (hsuf : ∀ c ∈ suf, Lawful member c) : Lawful member (listCodec pV pA μL pre sp suf) := by
  refine lawful_carried hμ
    (list_retract (fun c h => (hpre c h).core) (fun c h => (hsp c h).core)
      (fun c h => (hsuf c h).core)) ?_
  intro as vs hD
  obtain ⟨ps, hal, htr⟩ := Option.bind_eq_some_iff.mp hD
  obtain ⟨ds, hs, hlen, rfl⟩ := alignL_eq_some.mp hal
  have hn : vs.length = as.length := by
    rw [← traverse_length _ _ htr, List.length_zip, hlen, Nat.min_self]
  rw [alignL_of_slotsL hs hn]
  exact zip_canonS ds as vs (slotsL_all hpre hsp hsuf hs) hlen htr

/-- Writing and reading a `list` puts every position on its own carrier. -/
theorem carrier_listCodec (hpre : ∀ c ∈ pre, Carrier c) (hsp : ∀ c ∈ sp, Carrier c)
    (hsuf : ∀ c ∈ suf, Carrier c) : Carrier (listCodec pV pA μL pre sp suf) := by
  refine carrier_carried ?_ ?_
  · intro vs as hE
    obtain ⟨ps, hal, htr⟩ := Option.bind_eq_some_iff.mp hE
    obtain ⟨ds, hs, hlen, rfl⟩ := alignL_eq_some.mp hal
    exact ⟨_, hal, zip_domE ds vs as (slotsL_all hpre hsp hsuf hs) htr⟩
  · intro as vs hD
    obtain ⟨ps, hal, htr⟩ := Option.bind_eq_some_iff.mp hD
    obtain ⟨ds, hs, hlen, rfl⟩ := alignL_eq_some.mp hal
    have hn : vs.length = as.length := by
      rw [← traverse_length _ _ htr, List.length_zip, hlen, Nat.min_self]
    exact ⟨_, alignL_of_slotsL hs hn, zip_ranP ds as vs (slotsL_all hpre hsp hsuf hs) htr⟩

end List

/-! ## Objects (§4)

The field table is a map rather than a row, and the object is taken apart through it. Three
namings make §4 short. `entryCodec` is the codec one entry goes through: the field that its name
declares, or else the rest policy's. `objWrite` and `objRead` are the payload pair: the guard,
and the coming back. `objectCodecCore` is `carriedCodec` between the two keyed-map prisms, so
§2's prism halves are the ones already discharged. -/

section Object

/-- Every `req` name present on the value side. One `decide` over the key set. -/
def valPresentB (sems : MapOf (FieldSem V M)) (names : Finset String) : Bool :=
  decide (∀ k : {k // k ∈ sems.1}, valPresentAt names k.1 (sems.2 k) = true)

/-- The per-name half of §4's held set: a declared name holds its field's set, an
    undeclared one falls to the open part `R(ρ)`. -/
def objEntryT (sems : MapOf (FieldSem V M)) (rc? : Option (Codec V M)) :
    String × V → Prop := fun kv =>
  match sems.at kv.1 with
  | some fs => fs.codec.T kv.2
  | none => ∃ rc, rc? = some rc ∧ rc.T kv.2

/-- The codec one entry goes through: the field its name declares, or else the rest
    policy's. `none` is an undeclared name under `refuse`. -/
def entryCodec (sems : MapOf (FieldSem V M)) (rc? : Option (Codec V M)) (k : String) :
    Option (Codec V M) :=
  match sems.at k with
  | some fs => some fs.codec
  | none => rc?

variable {sems : MapOf (FieldSem V M)} {rc? : Option (Codec V M)} {kn : String → Bool}

/-- A property of every field and of the rest codec is a property of every entry's
    codec — which is how the object's per-entry laws are discharged, once each. -/
theorem entryCodec_of {Q : Codec V M → Prop} (hf : ∀ k, Q (sems.2 k).codec)
    (hrc : ∀ c ∈ rc?, Q c) {k c} (h : entryCodec sems rc? k = some c) : Q c := by
  simp only [entryCodec] at h
  cases hsp : sems.at k with
  | some fs => rw [hsp] at h; cases h; exact MapOf.at_forall (Q := fun fs => Q fs.codec) hf hsp
  | none => rw [hsp] at h; exact hrc c h

/-- §4's held set, per entry, in the same vocabulary. -/
theorem objEntryT_eq {kv} :
    objEntryT sems rc? kv ↔ ∃ c, entryCodec sems rc? kv.1 = some c ∧ c.T kv.2 := by
  simp only [objEntryT, entryCodec]
  cases sems.at kv.1 <;> simp

/-- **The object's payload pair at an orientation**: the presence guard, then each entry at the
    orientation. The write is the pair at the host, and the read is the pair at the dual. -/
noncomputable def objAt (sems : MapOf (FieldSem V M)) (rc? : Option (Codec V M)) (o : Orient) :
    MapOf (V) → Option (MapOf (V)) := fun p =>
  if valPresentB sems p.1 = true then
    (funImage (fun k => (entryCodec sems rc? k.1).bind (fun c => c.f o (p.2 k)))).map
      (fun g => ⟨p.1, g⟩)
  else none

/-- The payload pair, going out. -/
noncomputable abbrev objWrite (sems : MapOf (FieldSem V M)) (rc? : Option (Codec V M)) :
    MapOf V → Option (MapOf V) := objAt sems rc? Orient.host

/-- …and coming back. -/
noncomputable abbrev objRead (sems : MapOf (FieldSem V M)) (rc? : Option (Codec V M)) :
    MapOf V → Option (MapOf V) := objAt sems rc? Orient.dual

/-- What the payload pair sends at an orientation: the guard held, and the entrywise image. -/
theorem objAt_eq {o : Orient} {p : MapOf (V)} {q : MapOf (V)} :
    objAt sems rc? o p = some q ↔
      valPresentB sems p.1 = true ∧ ∃ g,
        funImage (fun k => (entryCodec sems rc? k.1).bind (fun c => c.f o (p.2 k))) = some g ∧
        q = ⟨p.1, g⟩ := by
  simp only [objAt]
  split
  · next hg => simp [hg, Option.map_eq_some_iff, eq_comm (a := q)]
  · next hg => simp [hg]

variable (mV : Ctor (MapOf V) V) (mA : Ctor (MapOf V) V) (μM : M)

/-- The object is `carriedCodec` between the two keyed-map prisms. -/
noncomputable abbrev objectCodecCore (sems : MapOf (FieldSem V M)) (rc? : Option (Codec V M)) :
    Codec V M :=
  carriedCodec mV mA μM
    (fun p => valPresentB sems p.1 = true ∧ ∀ k, objEntryT sems rc? (k.1, p.2 k))
    (objWrite sems rc?) (objRead sems rc?)

/-- §4's `object`: the core at the rest policy's codec. -/
noncomputable abbrev objectCodec (sems : MapOf (FieldSem V M)) (rest : RestSem V M) :
    Codec V M :=
  objectCodecCore mV mA μM sems (rcOf rest)

variable {mV mA μM}

/-! ### The guards and the filter -/

/-- A `req` name that the value-side guard passes is present. -/
theorem valPresentB_spec {names : Finset String}
    (h : valPresentB sems names = true) {k fs} (hm : sems.at k = some fs)
    (hno : ∀ c, fs ≠ FieldSem.opt c) : k ∈ names := by
  obtain ⟨hk, rfl⟩ := MapOf.at_eq_some.mp hm
  have hb := of_decide_eq_true h ⟨k, hk⟩
  cases hs : sems.2 ⟨k, hk⟩ with
  | opt c => rw [hs] at hno; exact absurd rfl (hno c)
  | req c => rw [hs] at hb; exact of_decide_eq_true hb

/-- The value-side guard passes where every `req` name is present. -/
theorem valPresentB_of {names : Finset String}
    (h : ∀ k fs, sems.at k = some fs → (∀ c, fs ≠ FieldSem.opt c) → k ∈ names) :
    valPresentB sems names = true := by
  refine decide_eq_true fun k => ?_
  cases hs : sems.2 k with
  | opt c => simp [valPresentAt]
  | req c =>
    simpa [valPresentAt, hs] using
      h k.1 (.req c) (by rw [MapOf.at_of_mem k, hs]) (fun _ h' => nomatch h')

/-- A `req` name that the presence guard passes is present. -/
theorem valPresentB_spec_req {names : Finset String}
    (h : valPresentB sems names = true) {k c} (hm : sems.at k = some (.req c)) :
    k ∈ names := by
  obtain ⟨hk, hs⟩ := MapOf.at_eq_some.mp hm
  have hb := of_decide_eq_true h ⟨k, hk⟩
  rw [hs] at hb
  exact of_decide_eq_true hb

/-- The presence guard passes where every `req` name is present. -/
theorem valPresentB_of_req {names : Finset String}
    (h : ∀ k c, sems.at k = some (.req c) → k ∈ names) :
    valPresentB sems names = true := by
  refine decide_eq_true fun k => ?_
  cases hs : sems.2 k with
  | req c => simpa [valPresentAt, hs] using h k.1 c (by rw [MapOf.at_of_mem k, hs])
  | opt c => simp [valPresentAt]

/-- The held set of an entry follows from the carrier of its codec, on the write step. -/
theorem entry_domE' (hs : ∀ k, Carrier (sems.2 k).codec) (hrc : ∀ c ∈ rc?, Carrier c)
    {k : String} {v : V} {a : V}
    (h : (entryCodec sems rc? k).bind (fun c => c.e v) = some a) :
    objEntryT sems rc? (k, v) := by
  cases hc : entryCodec sems rc? k with
  | none => rw [hc] at h; exact nomatch h
  | some c =>
    rw [hc] at h
    exact objEntryT_eq.mpr ⟨c, hc, (entryCodec_of hs hrc hc).domE h⟩

/-- …and on the read step. -/
theorem entry_ranP' (hs : ∀ k, Carrier (sems.2 k).codec) (hrc : ∀ c ∈ rc?, Carrier c)
    {k : String} {a : V} {v : V}
    (h : (entryCodec sems rc? k).bind (fun c => c.p a) = some v) :
    objEntryT sems rc? (k, v) := by
  cases hc : entryCodec sems rc? k with
  | none => rw [hc] at h; exact nomatch h
  | some c =>
    rw [hc] at h
    exact objEntryT_eq.mpr ⟨c, hc, (entryCodec_of hs hrc hc).ranP h⟩

/-- §4's held set follows from the entry carriers. The current-schema reader returns only stored
    entries, so the object row needs no extra reader premise. -/
theorem carrier_objectCodec {rest : RestSem V M}
    (hsems : ∀ k, Carrier (sems.2 k).codec)
    (hrc : ∀ rc, rcOf rest = some rc → Carrier rc) :
    Carrier (objectCodec mV mA μM sems rest) := by
  refine carrier_carried ?_ ?_
  · rintro p q h
    obtain ⟨hval, g, hg, rfl⟩ := objAt_eq.mp h
    exact ⟨hval, fun k => entry_domE' hsems hrc (funImage_some hg k)⟩
  · rintro q p h
    obtain ⟨hreq, d, hd, rfl⟩ := objAt_eq.mp h
    constructor
    · refine valPresentB_of fun k fs hm hno => ?_
      cases fs with
      | opt c => exact absurd rfl (hno c)
      | req c => exact valPresentB_spec_req hreq hm
    · intro k
      exact entry_ranP' hsems hrc (funImage_some hd k)

/-! ### §2's clauses for the object's payload pair -/

/-- **The inverse law of the payload pair**, at every orientation. The guard reads one key set
    on both sides, and each entry inverts its own map. -/
theorem object_inv {rest : RestSem V M} (hf : ∀ k, Lawful member (sems.2 k).codec)
    (hrc : ∀ c ∈ rcOf rest, Lawful member c) (o : Orient) :
    ∀ p q, objAt sems (rcOf rest) o p = some q → objAt sems (rcOf rest) o.op q = some p := by
  rintro p q h
  obtain ⟨hval, g, hg, rfl⟩ := objAt_eq.mp h
  refine objAt_eq.mpr ⟨hval, p.2, funImage_eq fun k => ?_, rfl⟩
  have hw := funImage_some hg k
  cases hc : entryCodec sems (rcOf rest) k.1 with
  | none => rw [hc] at hw; exact nomatch hw
  | some c =>
    simp only [hc, Option.bind_some] at hw ⊢
    exact (entryCodec_of hf hrc hc).inv hw

/-- The keyed product: the doc's current-schema `object`. -/
theorem lawful_objectCodec (hμ : ∀ y, member (mA.into y) = μM) {rest : RestSem V M}
    (hf : ∀ k, Lawful member (sems.2 k).codec)
    (hrest : ∀ c, rest = .codec c → Lawful member c) :
    Lawful member (objectCodec mV mA μM sems rest) := by
  exact lawful_carried hμ (object_inv hf (rcOf_forall hrest) .host)
    (object_inv hf (rcOf_forall hrest) .dual)

end Object

end Calculus.Alg
