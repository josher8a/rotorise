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

variable {V A M : Type} {member : A → M}

/-! ## `list` (§3): one prefix, at most one spread, one suffix -/

section List
variable (pV : Ctor (List V) V) (pA : Ctor (List A) A) (μL : M)

/-- §3 `(list)`: the positional product over a prefix, a spread and a suffix, between two list
    prisms. -/
abbrev listCodec (pre : List (Codec V A M)) (spread : Option (Codec V A M))
    (suf : List (Codec V A M)) : Codec V A M :=
  carriedCodec pV pA μL
    (fun vs => ∃ ps, alignL pre spread suf vs = some ps ∧ ∀ p ∈ ps, p.1.T p.2)
    (fun vs => (alignL pre spread suf vs).bind (traverse fun cv => cv.1.e cv.2))
    (fun as => (alignL pre spread suf as).bind (traverse fun ca => ca.1.p ca.2))

variable {pV pA μL} {pre : List (Codec V A M)} {sp : Option (Codec V A M)}
  {suf : List (Codec V A M)}

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
def valPresentB (sems : MapOf (FieldSem V A M)) (names : Finset String) : Bool :=
  decide (∀ k : {k // k ∈ sems.1}, valPresentAt names k.1 (sems.2 k) = true)

/-- Every `req` name present on the stored side. -/
def reqPresentB (sems : MapOf (FieldSem V A M)) (names : Finset String) : Bool :=
  decide (∀ k : {k // k ∈ sems.1}, valPresentAt names k.1 (sems.2 k) = true)

/-- The name filter: `drop` keeps declared names only; the others keep everything.
    A filter, never a traversal mode (§4). -/
def keepB (rest : RestSem V A M) (sems : MapOf (FieldSem V A M)) : String → Bool :=
  match rest with
  | .drop => fun k => (sems.at k).isSome
  | _ => fun _ => true

/-- The per-name half of §4's held set: a declared name holds its field's set, an
    undeclared one falls to the open part `R(ρ)`. -/
def objEntryT (sems : MapOf (FieldSem V A M)) (rc? : Option (Codec V A M)) :
    String × V → Prop := fun kv =>
  match sems.at kv.1 with
  | some fs => fs.codec.T kv.2
  | none => ∃ rc, rc? = some rc ∧ rc.T kv.2

/-- The codec one entry goes through: the field its name declares, or else the rest
    policy's. `none` is an undeclared name under `refuse`. -/
def entryCodec (sems : MapOf (FieldSem V A M)) (rc? : Option (Codec V A M)) (k : String) :
    Option (Codec V A M) :=
  match sems.at k with
  | some fs => some fs.codec
  | none => rc?

variable {sems : MapOf (FieldSem V A M)} {rc? : Option (Codec V A M)} {kn : String → Bool}

/-- A property of every field and of the rest codec is a property of every entry's
    codec — which is how the object's per-entry laws are discharged, once each. -/
theorem entryCodec_of {Q : Codec V A M → Prop} (hf : ∀ k, Q (sems.2 k).codec)
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

/-- The object's payload pair, going out: the value-side presence guard, then the
    name-dispatched steps. -/
noncomputable def objWrite (sems : MapOf (FieldSem V A M)) (rc? : Option (Codec V A M)) :
    MapOf V → Option (MapOf A) := fun p =>
  if valPresentB sems p.1 = true then
    (funImage (fun k => (entryCodec sems rc? k.1).bind (fun c => c.e (p.2 k)))).map
      (fun g => ⟨p.1, g⟩)
  else none

/-- …and coming back: the stored-side guard, the filter, and the entrywise steps. -/
noncomputable def objRead (sems : MapOf (FieldSem V A M)) (rc? : Option (Codec V A M))
    (kn : String → Bool) : MapOf A → Option (MapOf V) := fun p =>
  if reqPresentB sems p.1 = true then
    (funImage (fun k : {k // k ∈ p.1.filter (kn ·)} =>
        (entryCodec sems rc? k.1).bind
          (fun c => c.p (p.2 ⟨k.1, (Finset.mem_filter.mp k.2).1⟩)))).map
      (fun d => ⟨p.1.filter (kn ·), d⟩)
  else none

/-- What the payload pair writes: the guard held, and the entrywise image. -/
theorem objWrite_eq {p : MapOf V} {q : MapOf A} :
    objWrite sems rc? p = some q ↔
      valPresentB sems p.1 = true ∧ ∃ g,
        funImage (fun k => (entryCodec sems rc? k.1).bind (fun c => c.e (p.2 k))) = some g ∧
        q = ⟨p.1, g⟩ := by
  simp only [objWrite]
  split
  · next hg => simp [hg, Option.map_eq_some_iff, eq_comm (a := q)]
  · next hg => simp [hg]

/-- What the payload pair reads: the guard held, and the filtered entrywise image. -/
theorem objRead_eq {q : MapOf A} {p : MapOf V} :
    objRead sems rc? kn q = some p ↔
      reqPresentB sems q.1 = true ∧ ∃ d,
        funImage (fun k : {k // k ∈ q.1.filter (kn ·)} =>
            (entryCodec sems rc? k.1).bind
              (fun c => c.p (q.2 ⟨k.1, (Finset.mem_filter.mp k.2).1⟩))) = some d ∧
        p = ⟨q.1.filter (kn ·), d⟩ := by
  simp only [objRead]
  split
  · next hg => simp [hg, Option.map_eq_some_iff, eq_comm (a := p)]
  · next hg => simp [hg]

variable (mV : Ctor (MapOf V) V) (mA : Ctor (MapOf A) A) (μM : M)

/-- The object is `carriedCodec` between the two keyed-map prisms. -/
noncomputable abbrev objectCodecCore (sems : MapOf (FieldSem V A M)) (rc? : Option (Codec V A M))
    (kn : String → Bool) : Codec V A M :=
  carriedCodec mV mA μM
    (fun p => valPresentB sems p.1 = true ∧ ∀ k, objEntryT sems rc? (k.1, p.2 k))
    (objWrite sems rc?) (objRead sems rc? kn)

/-- §4's `object`: the core at the rest policy's codec and filter. -/
noncomputable abbrev objectCodec (sems : MapOf (FieldSem V A M)) (rest : RestSem V A M) :
    Codec V A M :=
  objectCodecCore mV mA μM sems (rcOf rest) (keepB rest sems)

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

/-- A `req` name that the stored-side guard passes is present. -/
theorem reqPresentB_spec {names : Finset String}
    (h : reqPresentB sems names = true) {k c} (hm : sems.at k = some (.req c)) :
    k ∈ names := by
  obtain ⟨hk, hs⟩ := MapOf.at_eq_some.mp hm
  have hb := of_decide_eq_true h ⟨k, hk⟩
  rw [hs] at hb
  exact of_decide_eq_true hb

/-- The stored-side guard passes where every `req` name is present. -/
theorem reqPresentB_of {names : Finset String}
    (h : ∀ k c, sems.at k = some (.req c) → k ∈ names) :
    reqPresentB sems names = true := by
  refine decide_eq_true fun k => ?_
  cases hs : sems.2 k with
  | req c => simpa [valPresentAt, hs] using h k.1 c (by rw [MapOf.at_of_mem k, hs])
  | opt c => simp [valPresentAt]

/-- The held set of an entry follows from the carrier of its codec, on the write step. -/
theorem entry_domE' (hs : ∀ k, Carrier (sems.2 k).codec) (hrc : ∀ c ∈ rc?, Carrier c)
    {k : String} {v : V} {a : A}
    (h : (entryCodec sems rc? k).bind (fun c => c.e v) = some a) :
    objEntryT sems rc? (k, v) := by
  cases hc : entryCodec sems rc? k with
  | none => rw [hc] at h; exact nomatch h
  | some c =>
    rw [hc] at h
    exact objEntryT_eq.mpr ⟨c, hc, (entryCodec_of hs hrc hc).domE h⟩

/-- …and on the read step. -/
theorem entry_ranP' (hs : ∀ k, Carrier (sems.2 k).codec) (hrc : ∀ c ∈ rc?, Carrier c)
    {k : String} {a : A} {v : V}
    (h : (entryCodec sems rc? k).bind (fun c => c.p a) = some v) :
    objEntryT sems rc? (k, v) := by
  cases hc : entryCodec sems rc? k with
  | none => rw [hc] at h; exact nomatch h
  | some c =>
    rw [hc] at h
    exact objEntryT_eq.mpr ⟨c, hc, (entryCodec_of hs hrc hc).ranP h⟩

/-- What object-encode produces, `keepB` keeps: under `drop` an encoded entry's name
    is declared, and the other policies keep everything. -/
theorem keepB_of_entryWrite {rest : RestSem V A M} :
    ∀ k v a, (entryCodec sems (rcOf rest) k).bind (fun c => c.e v) = some a →
      keepB rest sems k = true := by
  intro k v a h
  cases rest with
  | drop =>
    simp only [entryCodec] at h
    cases hsp : sems.at k with
    | none => rw [hsp] at h; simp only [rcOf, Option.bind_none] at h; exact nomatch h
    | some fs => simp [keepB, hsp]
  | refuse => rfl
  | codec rc => rfl

/-- Declared names pass every keep filter. -/
theorem keepB_of_declared {rest : RestSem V A M} :
    ∀ k, (sems.at k).isSome = true → keepB rest sems k = true := by
  intro k h
  cases rest with
  | drop => exact h
  | refuse => rfl
  | codec rc => rfl

/-- §4's held set follows from the entry carriers. The current-schema reader returns only stored
    entries, so the object row needs no extra reader premise. -/
theorem carrier_objectCodec {rest : RestSem V A M}
    (hsems : ∀ k, Carrier (sems.2 k).codec)
    (hrc : ∀ rc, rcOf rest = some rc → Carrier rc) :
    Carrier (objectCodec mV mA μM sems rest) := by
  refine carrier_carried ?_ ?_
  · rintro p q h
    obtain ⟨hval, g, hg, rfl⟩ := objWrite_eq.mp h
    exact ⟨hval, fun k => entry_domE' hsems hrc (funImage_some hg k)⟩
  · rintro q p h
    obtain ⟨hreq, d, hd, rfl⟩ := objRead_eq.mp h
    constructor
    · refine valPresentB_of fun k fs hm hno => ?_
      have hkn : keepB rest sems k = true := keepB_of_declared k (by rw [hm]; rfl)
      cases fs with
      | opt c => exact absurd rfl (hno c)
      | req c =>
        exact Finset.mem_filter.mpr ⟨reqPresentB_spec hreq hm, by simpa using hkn⟩
    · intro k
      exact entry_ranP' hsems hrc (funImage_some hd k)

/-! ### §2's clauses for the object's payload pair -/

/-- (R): a written row is complete, so reading it back is the entrywise round trip. -/
theorem object_retract {rest : RestSem V A M} (hf : ∀ k, LawfulCore member (sems.2 k).codec)
    (hrc : ∀ c ∈ rcOf rest, LawfulCore member c) :
    ∀ p q, objWrite sems (rcOf rest) p = some q →
      objRead sems (rcOf rest) (keepB rest sems) q = some p := by
  rintro p q h
  obtain ⟨hval, g, hg, rfl⟩ := objWrite_eq.mp h
  -- every name of a writable map is kept, so the `drop` filter is the identity
  have hfilter : p.1.filter (keepB rest sems ·) = p.1 :=
    Finset.filter_eq_self.mpr fun k hk => by
      simpa using keepB_of_entryWrite k (p.2 ⟨k, hk⟩) _ (funImage_some hg ⟨k, hk⟩)
  refine objRead_eq.mpr ⟨reqPresentB_of fun k c hm =>
    valPresentB_spec hval hm (fun _ h' => nomatch h'), ?_⟩
  refine ⟨fun k => p.2 ⟨k.1, (Finset.mem_filter.mp k.2).1⟩, funImage_eq fun k => ?_, ?_⟩
  · have hw := funImage_some hg ⟨k.1, (Finset.mem_filter.mp k.2).1⟩
    cases hc : entryCodec sems (rcOf rest) k.1 with
    | none => rw [hc] at hw; exact nomatch hw
    | some c =>
      simp only [hc, Option.bind_some] at hw ⊢
      exact (entryCodec_of hf hrc hc).retract hw
  · refine MapOf.ext ?_ ?_
    · exact hfilter.symm
    · intro k h₁ h₂
      rfl

/-- Canonical reads: a policy that keeps every name writes back the map that was read. -/
theorem object_canonS {rest : RestSem V A M} (hf : ∀ k, Lawful member (sems.2 k).codec)
    (hrc : ∀ c ∈ rcOf rest, Lawful member c) (hnd : rest ≠ .drop) :
    ∀ q p, objRead sems (rcOf rest) (keepB rest sems) q = some p →
      objWrite sems (rcOf rest) p = some q := by
  rintro q p h
  obtain ⟨hreq, d, hd, rfl⟩ := objRead_eq.mp h
  have hkeep : ∀ k, keepB rest sems k = true := by
    intro k; cases rest with
    | drop => exact absurd rfl hnd
    | refuse => rfl
    | codec _ => rfl
  have hfilter : q.1.filter (keepB rest sems ·) = q.1 :=
    Finset.filter_eq_self.mpr fun k _ => by simpa using hkeep k
  have hval : valPresentB sems (q.1.filter (keepB rest sems ·)) = true := by
    refine valPresentB_of fun k fs hm hno => ?_
    cases fs with
    | opt c => exact absurd rfl (hno c)
    | req c => exact Finset.mem_filter.mpr ⟨reqPresentB_spec hreq hm, by simpa using hkeep k⟩
  refine objWrite_eq.mpr ⟨hval, fun k => q.2 ⟨k.1, (Finset.mem_filter.mp k.2).1⟩,
    funImage_eq fun k => ?_, MapOf.ext hfilter.symm fun _ _ _ => rfl⟩
  have hp := funImage_some hd k
  cases hc : entryCodec sems (rcOf rest) k.1 with
  | none => rw [hc] at hp; exact nomatch hp
  | some c =>
    simp only [hc, Option.bind_some] at hp ⊢
    exact (entryCodec_of hf hrc hc).canon hp

/-- The keyed product: the doc's current-schema `object`. -/
theorem lawful_objectCodec (hμ : ∀ y, member (mA.into y) = μM) {rest : RestSem V A M}
    (hf : ∀ k, Lawful member (sems.2 k).codec)
    (hrest : ∀ c, rest = .codec c → Lawful member c) (hnd : rest ≠ .drop) :
    Lawful member (objectCodec mV mA μM sems rest) := by
  have hf' := fun k => (hf k).core
  have hrc' := fun c hc => ((rcOf_forall hrest) c hc).core
  exact lawful_carried hμ (object_retract hf' hrc') (object_canonS hf (rcOf_forall hrest) hnd)

end Object

end Calculus.Alg
