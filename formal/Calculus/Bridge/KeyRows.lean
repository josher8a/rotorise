import Calculus.Bridge.Verdicts
import Calculus.Dynamo.Alg.DerivedKey

/-!
# The rows of a derived key

The emitter runs the key builder of `src/` on a spec, an item and the options. A row holds what
the host read and what the host gave: the length of the spec, the options, the parts that the host
evaluated, the separator, the key or the refusal, and whether the segments are usable as a key.
The comparator states that `DerivedKey.build` gives the segments that the host joined, that the
join of the segments is the key, and that the read of the key gives the segments back exactly where
the row says so. A segment that holds the separator, or a list with no segment, is the case where
the read does not give the segments back.
-/

namespace Calculus

namespace DerivedKey

/-- What the host did with a row: it threw, it gave no key, or it gave a key. The builder gives no
    key where a discriminated spec has a `null` arm. -/
inductive HostKey where
  | refused
  | nothing
  | key (k : String)

/-- A row of the key builder: the name, the length of the spec, the options, the parts that the
    host evaluated, the separator, what the host gave, and whether the segment list has a segment
    and no segment holds the separator. -/
structure KeyRow where
  name : String
  full : Nat
  allowPartial : Bool
  enforce : Bool
  parts : List (Option Comp)
  sep : Char
  host : HostKey
  lawful : Bool

/-- The segments of a row, as characters. -/
def KeyRow.segs (r : KeyRow) : Option (List (List Char)) :=
  (build r.full r.allowPartial r.enforce r.parts).map (·.map String.toList)

/-- The segment list has a segment, and no segment holds the separator. -/
def lawfulSegs (c : Char) (segs : List (List Char)) : Bool :=
  !segs.isEmpty && segs.all fun s => !s.contains c

/-- The comparator of a row. The builder refuses where the host threw. The null arm writes nothing
    where the host gave no key. Where the host gave a key, the join of the segments is the key, the
    flag says whether the list is usable, and the read of the key gives the segments back exactly
    where the flag is `true`. -/
def keyRowOk (r : KeyRow) : Bool :=
  match r.host, r.segs with
  | .refused, none => true
  | .nothing, _ => ((Codec.empty : Codec).e (Attr.s "")).isNone
  | .key k, some segs =>
      join r.sep segs == k.toList && lawfulSegs r.sep segs == r.lawful &&
        (split r.sep k.toList == segs) == r.lawful
  | _, _ => false

/-- **A row that passes states what the host did.** Where the host threw, the model gives no
    segments. Where the host gave no key, the null arm writes nothing. Where the host gave a key,
    the model's segments join to the key, and the read gives them back where the flag is `true` and
    gives another list where the flag is `false`. -/
theorem keyRowOk_iff (r : KeyRow) : keyRowOk r = true ↔
    (r.host = .refused ∧ r.segs = none) ∨
    (r.host = .nothing ∧ ((Codec.empty : Codec).e (Attr.s "")) = none) ∨
      ∃ segs k, r.host = .key k ∧ r.segs = some segs ∧ join r.sep segs = k.toList ∧
        lawfulSegs r.sep segs = r.lawful ∧ (split r.sep k.toList = segs ↔ r.lawful = true) := by
  unfold keyRowOk
  cases hh : r.host with
  | refused => cases hs : r.segs <;> simp
  | nothing => simp [Option.isNone_iff_eq_none]
  | key k =>
      cases hs : r.segs with
      | none => simp
      | some segs =>
          cases hl : r.lawful <;> simp [beq_iff_eq, and_assoc]

/-- The names of the rows that fail. -/
def failingKeys (rows : List KeyRow) : List String :=
  (rows.filter fun r => !keyRowOk r).map KeyRow.name

/-- **A list with no failing row passes at each row.** -/
theorem keyRowOk_of_failing {rows : List KeyRow} (h : failingKeys rows = []) :
    ∀ r ∈ rows, keyRowOk r = true := fun r hr =>
  Bool.eq_false_imp_eq_true.mp fun hq => absurd
    ((congrArg (r.name ∈ ·) h).mp
      (List.mem_map_of_mem (List.mem_filter.mpr ⟨hr, by rw [hq]; rfl⟩)))
    List.not_mem_nil

end DerivedKey

end Calculus
