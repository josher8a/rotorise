import Calculus.Bridge.Verdicts
import Calculus.Dynamo.Alg.DerivedKey
import Calculus.Dynamo.Alg.KeyMatch

/-!
# The rows of a derived key

The emitter runs the key builder of `src/` on a spec, an item and the options. A row holds what
the host read and what the host gave: the key spec as a tree with the parts that the host evaluated
at each leaf, the attributes of the item that the tree reads, the options, the separator, the key
or the refusal, and whether the segments are usable as a key. The comparator selects the arm that
the item reaches (`KeyMatch.select`), and states that `DerivedKey.build` gives the segments that
the host joined, that the join of the segments is the key, and that the read of the key gives the
segments back exactly where the row says so. The host refuses a segment that holds the separator,
because the join of that list is also the join of another list (`DerivedKey.join_collision`). So a
row of a key holds no such segment, and a row of that refusal states that the model's segments hold
the separator. The empty segment list is the one list that the host joins and the read does not
give back. A tree can nest a match inside an arm. The host reads no nested arm yet, so no row of the
pool holds one.
-/

namespace Calculus

namespace DerivedKey

/-- What the host did with a row: it threw at an absent value, it threw at a segment that holds the
    separator, it gave no key, or it gave a key. The host gives no key at a `null` arm and at an attribute
    that the item lacks. -/
inductive HostKey where
  | refused
  | separator
  | nothing
  | key (k : String)

/-- A row of the key builder: the name, the key spec with the leaves that the host evaluated for the
    item, the attributes of the item that the spec reads, the options, the separator, what the host
    gave, and whether the segment list has a segment and no segment holds the separator. -/
structure KeyRow where
  name : String
  spec : KeySpec String
  item : List (String × String)
  allowPartial : Bool
  enforce : Bool
  sep : Char
  host : HostKey
  lawful : Bool

/-- The item of a row, as the selection reads it. -/
def KeyRow.itemOf (r : KeyRow) : Item String := fun n => r.item.lookup n

/-- What the model gives for a row: the key of the arm that the item selects. -/
def KeyRow.out (r : KeyRow) : Out := keyOf r.allowPartial r.enforce r.itemOf r.spec

/-- The segment list has a segment, and no segment holds the separator. -/
def lawfulSegs (c : Char) (segs : List (List Char)) : Bool :=
  !segs.isEmpty && segs.all fun s => !s.contains c

/-- Some segment holds the separator. -/
def holdsSep (c : Char) (segs : List (List Char)) : Bool :=
  segs.any fun s => s.contains c

/-- The comparator of a row. The model refuses where the host threw at an absent value, at an
    absent discriminator, or at a literal that names no arm. The segments hold the separator where
    the host threw at one. The null arm writes nothing where the host gave no key. Where the host
    gave a key from segments, no segment holds the separator, the join of the segments is the key,
    the flag says whether the list is usable, and the read of the key gives the segments back
    exactly where the flag is `true`. Where the host gave the printed attribute, the key is that
    value, and the flag is `false` because no join made the key. -/
def keyRowOk (r : KeyRow) : Bool :=
  match r.host, r.out with
  | .refused, .refused => true
  | .separator, .segs ss => holdsSep r.sep (charSegs ss)
  | .nothing, .nothing => ((Codec.empty : Codec).e (Attr.s "")).isNone
  | .key k, .segs ss =>
      !holdsSep r.sep (charSegs ss) && join r.sep (charSegs ss) == k.toList &&
        lawfulSegs r.sep (charSegs ss) == r.lawful &&
        (split r.sep k.toList == charSegs ss) == r.lawful
  | .key k, .raw v => v == k && !r.lawful
  | _, _ => false

/-- **A row that passes states what the host did.** Where the host threw, the model selects nothing
    or gives no segments. Where the host threw at the separator, the model's segments hold it. Where
    the host gave no key, the null arm writes nothing. Where the host gave a key, either no segment
    holds the separator, the model's segments join to the key, and the read gives them back where
    the flag is `true` and gives another list where the flag is `false`, or the key is the printed
    attribute and the flag is `false`. -/
theorem keyRowOk_iff (r : KeyRow) : keyRowOk r = true ↔
    (r.host = .refused ∧ r.out = .refused) ∨
    (r.host = .separator ∧ ∃ ss, r.out = .segs ss ∧ holdsSep r.sep (charSegs ss) = true) ∨
    (r.host = .nothing ∧ r.out = .nothing ∧ ((Codec.empty : Codec).e (Attr.s "")) = none) ∨
    (∃ k v, r.host = .key k ∧ r.out = .raw v ∧ v = k ∧ r.lawful = false) ∨
      ∃ ss k, r.host = .key k ∧ r.out = .segs ss ∧ holdsSep r.sep (charSegs ss) = false ∧
        join r.sep (charSegs ss) = k.toList ∧
        lawfulSegs r.sep (charSegs ss) = r.lawful ∧
          (split r.sep k.toList = charSegs ss ↔ r.lawful = true) := by
  unfold keyRowOk
  cases hh : r.host with
  | refused => cases ho : r.out <;> simp
  | separator => cases ho : r.out <;> simp
  | nothing => cases ho : r.out <;> simp [Option.isNone_iff_eq_none]
  | key k =>
      cases ho : r.out with
      | refused => simp
      | nothing => simp
      | raw v => cases hl : r.lawful <;> simp [beq_iff_eq]
      | segs ss => cases hl : r.lawful <;> simp [beq_iff_eq, and_assoc]

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
