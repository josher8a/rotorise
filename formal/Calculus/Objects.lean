import Calculus.Products

/-!
# Objects (§4)

The field table is a map rather than a row, and the object is taken apart through it.
`objectCodec` is not argued on its own: `objectCodecCore_eq` cashes it as an equation.
-/

namespace Calculus

noncomputable section
/-! ## Objects (§4) -/

/-- A field, denoted: presence marker plus the attribute pair. -/
inductive FieldSem where
  | req (c : Codec)
  | opt (c : Codec)

def FieldSem.codec : FieldSem → Codec
  | .req c => c
  | .opt c => c

/-- A rest policy, denoted. -/
inductive RestSem where
  | drop | refuse
  | codec (c : Codec)

/-! ### The field table is a map, not a row

§4 declares a *set* of field names, each with one field — so the table is a `MapOf`,
exactly as `M`'s payload is, and for the same reason. A `List (Name × FieldSem)` admits
two orderings of one object and a repeated name, and the `Nodup` premise that used to
travel with every object law existed to make the first harmless and rule out the second.
Both are now properties of the type, and that premise is gone from all five of them.

The type and its lookup are in `Domain.lean`, because three strata need them and the lowest is
the term language. The lookup is deliberately shaped like `List.lookup`, so everything downstream
— `entryCodec`, `objEntryT`, `field value`, `keepB` and every proof that splits on them — reads
unchanged. -/

/-- What each guard asks of one binding, named so the guards themselves are a single
    quantifier over the key set rather than a `List.all` over a row. -/
def valPresentAt (names : Finset Name) : Name → FieldSem → Bool
  | _, .opt _ => true
  | k, _ => decide (k ∈ names)

def reqPresentAt (names : Finset Name) : Name → FieldSem → Bool
  | k, .req _ => decide (k ∈ names)
  | _, _ => true

def valPresentB (sems : MapOf FieldSem) (names : Finset Name) : Bool :=
  decide (∀ k : {k // k ∈ sems.1}, valPresentAt names k.1 (sems.2 k) = true)

/-- Every `req` name present on the stored side. -/
def reqPresentB (sems : MapOf FieldSem) (names : Finset Name) : Bool :=
  decide (∀ k : {k // k ∈ sems.1}, reqPresentAt names k.1 (sems.2 k) = true)

/-- The rest policy's codec, where it has one. -/
def rcOf : RestSem → Option Codec
  | .codec c => some c
  | _ => none

/-- The name filter: `drop` keeps declared names only; the others keep everything.
    A filter, never a traversal mode (§4). -/
def keepB (rest : RestSem) (sems : MapOf FieldSem) : Name → Bool :=
  match rest with
  | .drop => fun k => (sems.at k).isSome
  | _ => fun _ => true

/-! ### The object, taken apart

Three namings, and everything §4 asks becomes short. **`entryCodec`** is the codec one
entry goes through — the field its name declares, or else the rest policy's — which is
the only thing ~~encEntry~~/~~decEntry~~ do with a name, so every per-entry law is one appeal
to `entryCodec_of`. **`objWrite`/`objRead`** are the payload pair: the guard and the
coming back. **`objectCodecCore_eq`** then makes the object `carriedCodec` between `map`
and `M`, so §2's prism halves are the ones already discharged. -/

/-- The per-name half of §4's held set: a declared name holds its field's set, an
    undeclared one falls to the open part `R(ρ)`. -/
def objEntryT (sems : MapOf FieldSem) (rc? : Option Codec) :
    Name × Value → Prop := fun kv =>
  match sems.at kv.1 with
  | some fs => fs.codec.T kv.2
  | none => ∃ rc, rc? = some rc ∧ rc.T kv.2

/-- The codec one entry goes through: the field its name declares, or else the rest
    policy's. `none` is an undeclared name under `refuse`. -/
def entryCodec (sems : MapOf FieldSem) (rc? : Option Codec) (k : Name) :
    Option Codec :=
  match sems.at k with
  | some fs => some fs.codec
  | none => rc?

section Object
variable {sems : MapOf FieldSem} {rc? : Option Codec} {kn : Name → Bool}

/-- A property of every field and of the rest codec is a property of every entry's
    codec — which is how the object's per-entry laws are discharged, once each. -/
theorem entryCodec_of {Q : Codec → Prop} (hf : ∀ k, Q (sems.2 k).codec)
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
noncomputable def objWrite (sems : MapOf FieldSem) (rc? : Option Codec) :
    MapOf Value → Option (MapOf Attr) := fun p =>
  if valPresentB sems p.1 = true then
    (funImage (fun k => (entryCodec sems rc? k.1).bind (fun c => c.e (p.2 k)))).map
      (fun g => ⟨p.1, g⟩)
  else none

/-- …and coming back: the stored-side guard, the filter, and the entrywise steps. -/
noncomputable def objRead (sems : MapOf FieldSem) (rc? : Option Codec)
    (kn : Name → Bool) : MapOf Attr → Option (MapOf Value) := fun p =>
  if reqPresentB sems p.1 = true then
    (funImage (fun k : {k // k ∈ p.1.filter (kn ·)} =>
        (entryCodec sems rc? k.1).bind
          (fun c => c.p (p.2 ⟨k.1, (Finset.mem_filter.mp k.2).1⟩)))).map
      (fun d => ⟨p.1.filter (kn ·), d⟩)
  else none

theorem objWrite_eq {p : MapOf Value} {q : MapOf Attr} :
    objWrite sems rc? p = some q ↔
      valPresentB sems p.1 = true ∧ ∃ g,
        funImage (fun k => (entryCodec sems rc? k.1).bind (fun c => c.e (p.2 k))) = some g ∧
        q = ⟨p.1, g⟩ := by
  simp only [objWrite]
  split
  · next hg => simp [hg, Option.map_eq_some_iff, eq_comm (a := q)]
  · next hg => simp [hg]

theorem objRead_eq {q : MapOf Attr} {p : MapOf Value} :
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

/-- A filter that keeps every name transports an entrywise read to a record read. -/
theorem funImage_record_congr {S T : Finset Name} (hS : S = T)
    {g : {k // k ∈ S} → Option Value} {g' : {k // k ∈ T} → Option Value}
    (hg : ∀ (k : Name) (h : k ∈ S) (h' : k ∈ T), g ⟨k, h⟩ = g' ⟨k, h'⟩) :
    (funImage g).map (Value.map S) = (funImage g').map (Value.map T) := by
  subst hS
  have himg : g = g' := funext fun k => hg k.1 k.2 k.2
  subst himg
  rfl

/-- The object is `carriedCodec` between `map` and `M`, at that pair. -/
noncomputable def objectCodecCore (sems : MapOf FieldSem) (rc? : Option Codec)
    (kn : Name → Bool) : Codec :=
  carriedCodec mapV mA .M
    (fun p => valPresentB sems p.1 = true ∧ ∀ k, objEntryT sems rc? (k.1, p.2 k))
    (objWrite sems rc?) (objRead sems rc? kn)

noncomputable def objectCodec (sems : MapOf FieldSem) (rest : RestSem) : Codec :=
  objectCodecCore sems (rcOf rest) (keepB rest sems)

theorem objectCodecCore_eq :
    objectCodecCore sems rc? kn =
      carriedCodec mapV mA .M
        (fun p => valPresentB sems p.1 = true ∧ ∀ k, objEntryT sems rc? (k.1, p.2 k))
        (objWrite sems rc?) (objRead sems rc? kn) := rfl

/-- Inversion of an object-encode success: the value is a map, the guard held, and the
    written item is the entrywise traversal. -/
theorem objectCodecCore_e_inv {t a} (he : (objectCodecCore sems rc? kn).e t = some a) :
    ∃ keys f g, t = Value.map keys f ∧ a = Attr.m keys g ∧
      valPresentB sems keys = true ∧
      funImage (fun k => (entryCodec sems rc? k.1).bind (fun c => c.e (f k))) = some g := by
  obtain ⟨p, q, hv, hw, rfl⟩ := carried_e.mp (objectCodecCore_eq ▸ he)
  obtain ⟨hval, g, hg, rfl⟩ := objWrite_eq.mp hw
  exact ⟨p.1, p.2, g, mapV.into_out hv, rfl, hval, hg⟩

/-- **The empty body with an open block is the record.** `record` is not a term of its own: it
    is the object that declares no name and takes every key at one codec, and this is the
    equation that says so. Four components, and only the reading needs work: the keep filter is
    constantly true at an open block, so it drops no name. The output key set is therefore the
    map's own. `funImage_record_congr` carries the filter as a variable, which keeps the
    transport out of a dependent rewrite. -/
theorem objectCodec_empty_codec (c : Codec) :
    objectCodec ⟨∅, fun k => absurd k.2 (Finset.notMem_empty k.1)⟩ (.codec c) = recordCodec c := by
  -- A quantifier over the empty key set is vacuous, and simp discharges one through an
  -- emptiness instance that reaches `Classical.choice`. `hval` is the same fact as a direct
  -- term, so the guard rewrites without the instance and the route stays closed.
  have hval : ∀ keys : Finset Name,
      valPresentB ⟨∅, fun k => absurd k.2 (Finset.notMem_empty k.1)⟩ keys = true :=
    fun _ => decide_eq_true (fun k => absurd k.2 (Finset.notMem_empty k.1))
  apply Codec.ext
  · funext v
    cases v <;>
      simp [objectCodec, objectCodecCore, carriedCodec, recordCodec,
            objEntryT, rcOf, MapOf.at, mapV]
    constructor
    · rintro ⟨x, ⟨rfl, hf⟩, h⟩
      cases eq_of_heq hf
      exact h.2
    · rename_i keys f
      exact fun h => ⟨⟨keys, f⟩, ⟨rfl, HEq.rfl⟩, hval keys, h⟩
  · rfl
  · funext v
    cases v <;> try rfl
    rename_i keys f
    simp only [objectCodec, objectCodecCore, carriedCodec, recordCodec, Option.bind,
          objWrite, rcOf, entryCodec, MapOf.at, mapV, mA]
    rw [if_pos (hval keys), Option.map_map]
    refine congrArg (fun F => Option.map F _) (funext fun _ => rfl) |>.trans ?_
    exact congrArg (Option.map _) (congrArg funImage
      (funext fun k => by rw [dif_neg (Finset.notMem_empty k.1)]))
  · funext a
    cases a <;> try rfl
    rename_i keys f
    simp only [objectCodec, objectCodecCore, carriedCodec, mapV, mA, Option.bind,
               objRead, rcOf, recordCodec]
    -- simp over a vacuous `Finset ∅` goal reaches `Classical.choice` through three filter
    -- lemmas this development does not advertise. Each fact below is the direct term instead.
    rw [if_pos (show reqPresentB ⟨(∅ : Finset Name),
        fun k => absurd k.2 (Finset.notMem_empty k.1)⟩ keys = true from
      decide_eq_true (fun k => absurd k.2 (Finset.notMem_empty k.1)))]
    have hkeep : keys.filter
        (keepB (.codec c) ⟨(∅ : Finset Name), fun k => absurd k.2 (Finset.notMem_empty k.1)⟩ ·)
          = keys :=
      Finset.ext fun k =>
        ⟨fun hk => (Finset.mem_filter.mp hk).1, fun hk => Finset.mem_filter.mpr ⟨hk, rfl⟩⟩
    rw [Option.map_map]
    exact funImage_record_congr hkeep (fun k h h' => rfl)

end Object

end

end Calculus
