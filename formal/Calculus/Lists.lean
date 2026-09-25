import Calculus.AlgLists
import Calculus.Domain

/-!
# The list plumbing at the DynamoDB carriers

The traversal and the `filter` facts take no carrier, so they are generic. The aliases below
give them their names in this namespace. The keyed clause of the traversal reads `Name`, so it
stays here.

§5's keyed refinement, *"entries are dispatched and compared by name, first occurrence
first"*, is gone. It was a statement about `M` as a `List (Name × Attr)`: a clause needed because
a keyed list has an order and can repeat a key. `M` is now a name set with a function on it, so
there is no first occurrence to prefer. `traverse_fst` survives because `L` really is a list.
-/

namespace Calculus

export Alg (traverse traverse_nil traverse_cons traverse_eq_some traverse_length
  traverse_append_isSome traverse_roundTrip traverse_isSome_of_all traverse_isSome traverse_mem₂
  traverse_mem traverse_mem_input filter_nil_of filter_eq_singleton_of_disjoint
  filter_eq_singleton_of_labels forall_mem_map_option)

section Traverse
variable {α β : Type}

/-- §5, Lemma (traversal), keyed clause: names survive. A traversal that preserves each
    entry's name preserves the list of names. -/
theorem traverse_fst {f : Name × α → Option (Name × β)}
    (hf : ∀ kv kb, f kv = some kb → kb.1 = kv.1) {kvs : List (Name × α)} {ds}
    (h : traverse f kvs = some ds) : ds.map (·.1) = kvs.map (·.1) := by
  induction kvs generalizing ds with
  | nil => cases traverse_eq_some.mp h; rfl
  | cons kv kvs ih =>
      simp only [traverse_cons, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨kb, hkb, ds', hds', rfl⟩ := h
      simp [hf kv kb hkb, ih hds']

end Traverse

end Calculus
