import Calculus.Alg.Combinators

/-!
# The item with derived keys

A derived key lives only in the stored universe. Encode writes the key of the item. Decode never
reads a key, and a row may lack the key. The key adds no information to the item, so decode
deletes the key.

The key part of a row has its own carrier `κ`. A `Split` is a lens from the row onto its key part:
`keep` reads the key part, `join` puts a key part into a row, and `drop` is the complement, the row
without its key part. The key part is absent where the row holds no `κ` at the key names, so `keep`
gives an option. No law reads a name, so the generic layer states the lens, and a universe gives an
instance.

`graph` writes the item with its codec and writes the key part of the item. It reads a row only
where the key part of the row equals the key part of the item that the codec reads from the part
outside the keys. The graph is a prism, so `Lawful` holds in both orientations. `derive` extends
the read of the graph with the read that deletes the key part. A row with a stale key and a row with
no key read as the item. The read is one combinator, `Codec.extendRead`, and needs no new law.
-/

namespace Calculus.Alg

variable {V M : Type}

/-- **A split of the row at the key names, as a lens onto the key part `κ`.** `rows` holds the values
    that the split cuts. `keep a` is the key part of the row `a`, and `none` where the row holds no
    key part. `join x y` is the row `x` with the key part `y`. `drop a` is the complement: the row
    without its key part. `keep_join` is PutGet, `join_keep` is GetPut, and `drop_join` states that
    `join` leaves the complement alone. -/
structure Split (V κ : Type) where
  /-- The values that the split cuts: the rows. -/
  rows : V → Prop
  /-- The row without its key part. -/
  drop : V → V
  /-- The key part of a row, or none where the row holds no key part. -/
  keep : V → Option κ
  /-- The row with the key part. -/
  join : V → κ → V
  /-- PutGet: the key part of a joined row is the part that the join put. -/
  keep_join : ∀ {x}, rows x → ∀ y, keep (join x y) = some y
  /-- A joined row has the complement of the first row. -/
  drop_join : ∀ {x}, rows x → ∀ y, drop (join x y) = drop x
  /-- GetPut: a row is its complement joined to its key part. -/
  join_keep : ∀ {a y}, keep a = some y → join (drop a) y = a

variable {κ : Type} (s : Split V κ) [DecidableEq κ]



/-- **The graph of an item with derived keys.** The write is the write of `c` with the key part `k t`
    joined to the row. The read takes the outside part of the row, reads the item with `c`, and
    accepts only where the key part of the row is the key part of that item. The graph names no
    member. -/
def Split.graph (c : Codec V M) (k : V → κ) : Codec V M :=
  Codec.ofEP c.T none
    (fun t => (c.e t).map fun r => s.join r (k t))
    (fun a => (c.p (s.drop a)).filter fun t => decide (s.keep a = some (k t)))

variable (c : Codec V M) (k : V → κ)

/-- The graph writes the row of `c` joined to the key part of the item. -/
theorem Split.graph_e {t a : V} :
    (s.graph c k).e t = some a ↔ ∃ r, c.e t = some r ∧ a = s.join r (k t) := by
  simp [Split.graph, Option.map_eq_some_iff, eq_comm (a := a)]

/-- The graph reads an item where `c` reads the outside part of the row and the key part agrees. -/
theorem Split.graph_p {a t : V} :
    (s.graph c k).p a = some t ↔ c.p (s.drop a) = some t ∧ s.keep a = some (k t) := by
  simp [Split.graph, Option.filter_eq_some_iff]

variable {member : V → M} {c k}

/-- **The graph is lawful in both orientations.** The premises on `c` are the law of `c` and that the
    write of `c` is a row with no key part. The premise on `k` is none. -/
theorem Split.graph_lawful (hc : Lawful member c)
    (hw : ∀ {t r}, c.e t = some r → s.rows r ∧ s.drop r = r) :
    Lawful member (s.graph c k) := by
  refine Lawful.ofRC ?_ ?_ ?_
  · intro t a he
    obtain ⟨r, hr, rfl⟩ := (s.graph_e c k).mp he
    obtain ⟨hrow, hd⟩ := hw hr
    refine (s.graph_p c k).mpr ⟨?_, s.keep_join hrow _⟩
    rw [s.drop_join hrow, hd]
    exact hc.retract hr
  · intro a t hp
    obtain ⟨hr, hk⟩ := (s.graph_p c k).mp hp
    exact (s.graph_e c k).mpr ⟨s.drop a, hc.canon hr, (s.join_keep hk).symm⟩
  · intro μ hμ
    exact nomatch hμ

/-- **The derived item.** The graph, with the read that deletes the key part as the second reader.
    The write is the write of the graph. -/
def Split.derive (c : Codec V M) (k : V → κ) : Codec V M :=
  (s.graph c k).extendRead fun a => c.p (s.drop a)

/-- The derived item writes as the graph writes. -/
theorem Split.derive_e {t a : V} : (s.derive c k).e t = some a ↔ (s.graph c k).e t = some a :=
  extendRead_e

/-- **The derived item meets the core laws.** The statement is `LawfulCore.extendRead` on the core of
    the lawful graph. -/
theorem Split.derive_core (hc : Lawful member c)
    (hw : ∀ {t r}, c.e t = some r → s.rows r ∧ s.drop r = r) :
    LawfulCore member (s.derive c k) :=
  (s.graph_lawful hc hw).core.extendRead

/-- **The two readers agree.** Where the graph reads an item, the read that deletes the key part
    reads the same item. -/
theorem Split.derive_coherent :
    ReadsCoherently (s.graph c k) fun a => c.p (s.drop a) := by
  intro a v hr _ v' hp
  exact Option.some.inj (hr.symm.trans ((s.graph_p c k).mp hp).1)

/-- **The read of the derived item is the order-free union of the strict read and the read that
    deletes the key part.** -/
theorem Split.derive_p_union {a v : V} :
    (s.derive c k).p a = some v ↔
      (s.graph c k).p a = some v ∨ (c.p (s.drop a) = some v ∧ ((s.graph c k).e v).isSome) :=
  extendRead_p_union.mp (s.derive_coherent) a v

/-- **A row with no key part reads through the read that deletes the key part alone.** The graph
    refuses the row, so the derived item reads the outside part. -/
theorem Split.derive_p_no_keypart {a v : V} (h : s.keep a = none) :
    (s.derive c k).p a = some v ↔ c.p (s.drop a) = some v ∧ ((s.graph c k).e v).isSome := by
  rw [s.derive_p_union]
  constructor
  · rintro (hg | hr)
    · obtain ⟨-, hk⟩ := (s.graph_p c k).mp hg
      rw [h] at hk
      exact nomatch hk
    · exact hr
  · exact .inr

/-- A row whose outside part reads as a writable item reads as that item, with any key part. -/
theorem Split.derive_p_of_drop {a t : V} (hp : c.p (s.drop a) = some t) (hw : (c.e t).isSome) :
    (s.derive c k).p a = some t := by
  obtain ⟨r, he⟩ := Option.isSome_iff_exists.mp hw
  refine (s.derive_p_union).mpr (.inr ⟨hp, ?_⟩)
  exact Option.isSome_iff_exists.mpr ⟨_, (s.graph_e c k).mpr ⟨r, he, rfl⟩⟩

/-- **A row of `t` with a stale key reads as `t`.** The row joins the row of `t` to any key part `y`,
    and `y` need not be the key part of `t`. -/
theorem Split.derive_p_stale (hc : Lawful member c)
    (hw : ∀ {t r}, c.e t = some r → s.rows r ∧ s.drop r = r)
    {t r : V} (he : c.e t = some r) (y : κ) : (s.derive c k).p (s.join r y) = some t := by
  obtain ⟨hrow, hd⟩ := hw he
  refine s.derive_p_of_drop ?_ (by rw [he]; rfl)
  rw [s.drop_join hrow, hd]
  exact hc.retract he

/-- **A row of `t` with no key reads as `t`.** The row is the row of `t` and holds no key part. -/
theorem Split.derive_p_absent (hc : Lawful member c)
    (hw : ∀ {t r}, c.e t = some r → s.rows r ∧ s.drop r = r)
    {t r : V} (he : c.e t = some r) : (s.derive c k).p r = some t := by
  refine s.derive_p_of_drop ?_ (by rw [he]; rfl)
  rw [(hw he).2]
  exact hc.retract he

end Calculus.Alg
