import Calculus.Alg.Lists

/-!
# The positional products, over any carriers

`tuple` and `list` pair each position of a row with its own codec before the traversal. The
codec row that a shape assigns to a row of `n` positions (`slots`, `slotsL`) depends on the
position alone, never on what stands there. The pairing (`align`, `alignL`) is then a `zip` with
that row, and §2's clauses run position by position over it. Each fact reads only the pair, so
each one takes the carrier `V` and the members `M` as parameters.
-/

namespace Calculus.Alg

variable {V M : Type} {member : V → M}

/-- Pair each position with its codec: the fixed head positionally, the tail
    uniformly; length mismatches refuse. `tuple` is then `align` + `traverse`. -/
def align {α : Type} : List (Codec V M) → Option (Codec V M)
    → List α → Option (List (Codec V M × α))
  | [], _, [] => some []
  | [], tail, x :: xs =>
    match tail with
    | some c => (align [] tail xs).map ((c, x) :: ·)
    | none => none
  | _ :: _, _, [] => none
  | c :: cs, tail, x :: xs => (align cs tail xs).map ((c, x) :: ·)

/-! #### The codec row a shape assigns -/

/-- The codec row for a row of `n` positions: the fixed head, then the tail codec as
    often as needed. `none` is the length mismatch `align` refuses on. -/
def slots : List (Codec V M) → Option (Codec V M) → Nat → Option (List (Codec V M))
  | [], _, 0 => some []
  | [], none, _ + 1 => none
  | [], some c, n + 1 => (slots [] (some c) n).map (c :: ·)
  | _ :: _, _, 0 => none
  | c :: cs, tail, n + 1 => (slots cs tail n).map (c :: ·)

theorem align_eq_zip {α : Type} : ∀ (cs : List (Codec V M)) (tail : Option (Codec V M))
    (xs : List α),
    align cs tail xs = (slots cs tail xs.length).map (·.zip xs)
  | [], tail, [] => by cases tail <;> rfl
  | [], none, _ :: _ => rfl
  | [], some c, x :: xs => by
      show (align [] (some c) xs).map ((c, x) :: ·) = _
      rw [align_eq_zip [] (some c) xs]
      cases hs : slots [] (some c) xs.length <;> simp [slots, hs, List.zip]
  | _ :: _, tail, [] => by cases tail <;> rfl
  | c :: cs, tail, x :: xs => by
      show (align cs tail xs).map ((c, x) :: ·) = _
      rw [align_eq_zip cs tail xs]
      cases hs : slots cs tail xs.length <;> simp [slots, hs, List.zip]

theorem slots_length : ∀ (cs : List (Codec V M)) (tail : Option (Codec V M)) (n : Nat) (ds),
    slots cs tail n = some ds → ds.length = n
  | [], tail, 0, _, h => by cases tail <;> (simp [slots] at h; simp [← h])
  | [], some c, n + 1, ds, h => by
      obtain ⟨ds', h', rfl⟩ := Option.map_eq_some_iff.mp h
      simp [slots_length [] (some c) n ds' h']
  | c :: cs, tail, n + 1, ds, h => by
      obtain ⟨ds', h', rfl⟩ := Option.map_eq_some_iff.mp h
      simp [slots_length cs tail n ds' h']

/-- Every codec in the row is one the shape declared. -/
theorem slots_mem : ∀ (cs : List (Codec V M)) (tail : Option (Codec V M)) (n : Nat) (ds),
    slots cs tail n = some ds → ∀ c ∈ ds, c ∈ cs ∨ tail = some c
  | [], tail, 0, _, h, _, hm => by
      cases tail <;> (simp [slots] at h; subst h; exact nomatch hm)
  | [], some c, n + 1, ds, h, d, hm => by
      obtain ⟨ds', h', rfl⟩ := Option.map_eq_some_iff.mp h
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact .inr rfl
      · exact slots_mem [] (some c) n ds' h' d hm'
  | c :: cs, tail, n + 1, ds, h, d, hm => by
      obtain ⟨ds', h', rfl⟩ := Option.map_eq_some_iff.mp h
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact .inl (List.mem_cons_self)
      · exact (slots_mem cs tail n ds' h' d hm').imp (List.mem_cons_of_mem _) id

/-- A property of the shape's codecs is a property of every codec in every row. -/
theorem slots_all {Q : Codec V M → Prop} {cs : List (Codec V M)} {tail : Option (Codec V M)}
    (hcs : ∀ c ∈ cs, Q c) (htl : ∀ c ∈ tail, Q c) {n ds}
    (hs : slots cs tail n = some ds) : ∀ c ∈ ds, Q c := fun c hc =>
  (slots_mem cs tail n ds hs c hc).elim (hcs c) (htl c)

/-- **The pivot for `align`.** An alignment is the codec row zipped with the row: which
    codec a position gets depends on the position alone, never on what stands there. -/
theorem align_eq_some {α : Type} {cs : List (Codec V M)} {tail : Option (Codec V M)}
    {xs : List α} {ps} :
    align cs tail xs = some ps ↔
      ∃ ds, slots cs tail xs.length = some ds ∧ ds.length = xs.length ∧ ps = ds.zip xs := by
  rw [align_eq_zip]
  constructor
  · intro h
    obtain ⟨ds, h', rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨ds, h', slots_length _ _ _ _ h', rfl⟩
  · rintro ⟨ds, h', _, rfl⟩
    rw [h']; rfl

/-- …so any row of the same length aligns against the same codecs. -/
theorem align_of_slots {α : Type} {cs : List (Codec V M)} {tail : Option (Codec V M)} {n ds}
    (h : slots cs tail n = some ds) {xs : List α} (hn : xs.length = n) :
    align cs tail xs = some (ds.zip xs) := by
  rw [align_eq_zip, hn, h]; rfl

/-! #### §2's clauses, position by position over the codec row -/

theorem zip_roundTrip : ∀ (ds : List (Codec V M)) (vs : List V) (as : List V),
    (∀ c ∈ ds, LawfulCore member c) → ds.length = vs.length →
    traverse (fun cv : Codec V M × V => cv.1.e cv.2) (ds.zip vs) = some as →
    traverse (fun ca : Codec V M × V => ca.1.p ca.2) (ds.zip as) = some vs
  | [], vs, as, _, hlen, h => by simp_all [List.eq_nil_of_length_eq_zero hlen.symm]
  | _ :: _, [], as, _, hlen, h => by simp_all
  | d :: ds, v :: vs, as, hd, hlen, h => by
      rw [List.zip_cons_cons, traverse_cons] at h
      obtain ⟨a, ha, has⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨as', has', rfl⟩ := Option.map_eq_some_iff.mp has
      rw [List.zip_cons_cons, traverse_cons, (hd d (by simp)).retract ha,
        zip_roundTrip ds vs as' (fun c hc => hd c (by simp [hc])) (by simpa using hlen) has']
      rfl

theorem zip_canon : ∀ (ds : List (Codec V M)) (as : List V) (vs : List V),
    (∀ c ∈ ds, LawfulCore member c) →
    traverse (fun ca : Codec V M × V => ca.1.p ca.2) (ds.zip as) = some vs →
    (traverse (fun cv : Codec V M × V => cv.1.e cv.2) (ds.zip vs)).isSome
  | [], as, vs, _, h => by simp_all
  | _ :: _, [], vs, _, h => by simp_all
  | d :: ds, a :: as, vs, hd, h => by
      rw [List.zip_cons_cons, traverse_cons] at h
      obtain ⟨v, hv, hvs⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨vs', hvs', rfl⟩ := Option.map_eq_some_iff.mp hvs
      obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp ((hd d (by simp)).canon hv)
      obtain ⟨as', has'⟩ := Option.isSome_iff_exists.mp
        (zip_canon ds as vs' (fun c hc => hd c (by simp [hc])) hvs')
      simp [List.zip_cons_cons, traverse_cons, ha', has']

/-- Reading a row and writing it back gives the row: canonical reads, position by position. -/
theorem zip_canonS : ∀ (ds : List (Codec V M)) (as : List V) (vs : List V),
    (∀ c ∈ ds, Lawful member c) → ds.length = as.length →
    traverse (fun ca : Codec V M × V => ca.1.p ca.2) (ds.zip as) = some vs →
    traverse (fun cv : Codec V M × V => cv.1.e cv.2) (ds.zip vs) = some as
  | [], as, vs, _, hlen, h => by simp_all [List.eq_nil_of_length_eq_zero hlen.symm]
  | _ :: _, [], vs, _, hlen, h => by simp_all
  | d :: ds, a :: as, vs, hd, hlen, h => by
      rw [List.zip_cons_cons, traverse_cons] at h
      obtain ⟨v, hv, hvs⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨vs', hvs', rfl⟩ := Option.map_eq_some_iff.mp hvs
      rw [List.zip_cons_cons, traverse_cons, (hd d (by simp)).canon hv,
        zip_canonS ds as vs' (fun c hc => hd c (by simp [hc])) (by simpa using hlen) hvs']
      rfl

/-- Writing a row puts every position on its own carrier… -/
theorem zip_domE : ∀ (ds : List (Codec V M)) (vs : List V) (as : List V),
    (∀ c ∈ ds, Carrier c) →
    traverse (fun cv : Codec V M × V => cv.1.e cv.2) (ds.zip vs) = some as →
    ∀ q ∈ ds.zip vs, q.1.T q.2
  | [], vs, as, _, h => by simp_all
  | _ :: _, [], as, _, h => by simp_all
  | d :: ds, v :: vs, as, hd, h => by
      rw [List.zip_cons_cons, traverse_cons] at h
      obtain ⟨a, ha, has⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨as', has', rfl⟩ := Option.map_eq_some_iff.mp has
      intro q hq
      rcases List.mem_cons.mp (by simpa using hq) with rfl | hq'
      · exact (hd d (by simp)).domE ha
      · exact zip_domE ds vs as' (fun c hc => hd c (by simp [hc])) has' q hq'

/-- …and so does reading one. -/
theorem zip_ranP : ∀ (ds : List (Codec V M)) (as : List V) (vs : List V),
    (∀ c ∈ ds, Carrier c) →
    traverse (fun ca : Codec V M × V => ca.1.p ca.2) (ds.zip as) = some vs →
    ∀ q ∈ ds.zip vs, q.1.T q.2
  | [], as, vs, _, h => by simp_all
  | _ :: _, [], vs, _, h => by simp_all
  | d :: ds, a :: as, vs, hd, h => by
      rw [List.zip_cons_cons, traverse_cons] at h
      obtain ⟨v, hv, hvs⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨vs', hvs', rfl⟩ := Option.map_eq_some_iff.mp hvs
      intro q hq
      rcases List.mem_cons.mp (by simpa using hq) with rfl | hq'
      · exact (hd d (by simp)).ranP hv
      · exact zip_ranP ds as vs' (fun c hc => hd c (by simp [hc])) hvs' q hq'

section Tuple
variable {cs : List (Codec V M)} {tail : Option (Codec V M)}

/-- (R) for the payload pair: realign the written row against the same codecs, then
    read back position by position. -/
theorem tuple_retract (hd : ∀ c ∈ cs, LawfulCore member c) (htl : ∀ c ∈ tail, LawfulCore member c) :
    ∀ vs as, (align cs tail vs).bind (traverse fun cv => cv.1.e cv.2) = some as →
      (align cs tail as).bind (traverse fun ca => ca.1.p ca.2) = some vs := by
  intro vs as hE
  obtain ⟨ps, hal, htr⟩ := Option.bind_eq_some_iff.mp hE
  obtain ⟨ds, hs, hlen, rfl⟩ := align_eq_some.mp hal
  have hn : as.length = vs.length := by
    rw [← traverse_length _ _ htr, List.length_zip, hlen, Nat.min_self]
  exact Option.bind_eq_some_iff.mpr ⟨_, align_of_slots hs hn,
    zip_roundTrip ds vs as (slots_all hd htl hs) hlen htr⟩

end Tuple

/-- The codec row a `list` shape assigns to `n` positions: the prefix positionally, the
    spread as often as the middle needs, then the suffix. `none` is the length the shape
    refuses, which is every `n` below `|suf|`, and every `n` that `slots` then refuses. -/
def slotsL (pre : List (Codec V M)) (spread : Option (Codec V M)) (suf : List (Codec V M))
    (n : Nat) :
    Option (List (Codec V M)) :=
  if n < suf.length then none
  else (slots pre spread (n - suf.length)).map (· ++ suf)

/-- `align` for a `list`: the row zipped with the positions, exactly as `align_eq_zip`
    shows `align` itself to be. -/
def alignL {α : Type} (pre : List (Codec V M)) (spread : Option (Codec V M))
    (suf : List (Codec V M))
    (xs : List α) : Option (List (Codec V M × α)) :=
  (slotsL pre spread suf xs.length).map (·.zip xs)

/-- A row the shape accepts has exactly the length asked of it. -/
theorem slotsL_length (pre : List (Codec V M)) (sp : Option (Codec V M))
    (suf : List (Codec V M)) (n : Nat)
    (ds) (h : slotsL pre sp suf n = some ds) : ds.length = n := by
  unfold slotsL at h
  split at h
  · exact absurd h (by simp)
  · next hlt =>
    obtain ⟨ds', h', rfl⟩ := Option.map_eq_some_iff.mp h
    rw [List.length_append, slots_length pre sp (n - suf.length) ds' h']
    omega

/-- Every codec in the row is one the shape declared: a prefix position, the spread, or a
    suffix position. -/
theorem slotsL_mem (pre : List (Codec V M)) (sp : Option (Codec V M))
    (suf : List (Codec V M)) (n : Nat)
    (ds) (h : slotsL pre sp suf n = some ds) :
    ∀ c ∈ ds, c ∈ pre ∨ sp = some c ∨ c ∈ suf := by
  unfold slotsL at h
  split at h
  · exact absurd h (by simp)
  · next hlt =>
    obtain ⟨ds', h', rfl⟩ := Option.map_eq_some_iff.mp h
    intro c hc
    rcases List.mem_append.mp hc with hc' | hc'
    · exact (slots_mem pre sp (n - suf.length) ds' h' c hc').imp id Or.inl
    · exact Or.inr (Or.inr hc')

/-- A property of the shape's three parts is a property of every codec in every row. -/
theorem slotsL_all {Q : Codec V M → Prop} {pre : List (Codec V M)} {sp : Option (Codec V M)}
    {suf : List (Codec V M)} (hpre : ∀ c ∈ pre, Q c) (hsp : ∀ c ∈ sp, Q c)
    (hsuf : ∀ c ∈ suf, Q c) {n ds} (hs : slotsL pre sp suf n = some ds) :
    ∀ c ∈ ds, Q c := fun c hc =>
  (slotsL_mem pre sp suf n ds hs c hc).elim (hpre c)
    (fun h => h.elim (fun he => hsp c he) (hsuf c))

/-- **The pivot for `alignL`**, and it says what `align_eq_some` says: which codec a
    position gets depends on the position alone, never on what stands there. -/
theorem alignL_eq_some {α : Type} {pre : List (Codec V M)} {sp : Option (Codec V M)}
    {suf : List (Codec V M)}
    {xs : List α} {ps} :
    alignL pre sp suf xs = some ps ↔
      ∃ ds, slotsL pre sp suf xs.length = some ds ∧ ds.length = xs.length ∧ ps = ds.zip xs := by
  unfold alignL
  constructor
  · intro h
    obtain ⟨ds, h', rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨ds, h', slotsL_length _ _ _ _ _ h', rfl⟩
  · rintro ⟨ds, h', _, rfl⟩
    rw [h']; rfl

/-- …so any row of the same length aligns against the same codecs. -/
theorem alignL_of_slotsL {α : Type} {pre : List (Codec V M)} {sp : Option (Codec V M)}
    {suf : List (Codec V M)} {n ds} (h : slotsL pre sp suf n = some ds) {xs : List α}
    (hn : xs.length = n) : alignL pre sp suf xs = some (ds.zip xs) := by
  unfold alignL; rw [hn, h]; rfl

/-- No suffix is `tuple`'s row, on the nose. -/
theorem slotsL_nil_suf (pre : List (Codec V M)) (sp : Option (Codec V M)) (n : Nat) :
    slotsL pre sp [] n = slots pre sp n := by
  unfold slotsL
  simp

/-- …and therefore `tuple`'s alignment. -/
theorem alignL_nil_suf {α : Type} (pre : List (Codec V M)) (sp : Option (Codec V M))
    (xs : List α) :
    alignL pre sp [] xs = align pre sp xs := by
  unfold alignL
  rw [slotsL_nil_suf, align_eq_zip]

/-- A row the shape accepts splits at the suffix: `tuple`'s row for the positions before
    it, then the suffix itself. -/
theorem slotsL_split (pre : List (Codec V M)) (sp : Option (Codec V M))
    (suf : List (Codec V M)) (n : Nat)
    (ds) (h : slotsL pre sp suf n = some ds) :
    ∃ dsF, slots pre sp (n - suf.length) = some dsF ∧ ds = dsF ++ suf
        ∧ dsF.length = n - suf.length ∧ suf.length ≤ n := by
  unfold slotsL at h
  split at h
  · exact absurd h (by simp)
  · next hlt =>
    obtain ⟨dsF, h', rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨dsF, h', rfl, slots_length _ _ _ _ h', by omega⟩

/-- **The split for `alignL`.** An alignment of a `list` is an alignment of its prefix and
    spread against the left part, and the suffix zipped with the right part. This is what
    lets every `align` fact serve the `list` unchanged. -/
theorem alignL_split {α : Type} (pre : List (Codec V M)) (sp : Option (Codec V M))
    (suf : List (Codec V M))
    (xs : List α) (ps) (h : alignL pre sp suf xs = some ps) :
    ∃ front back psF, xs = front ++ back ∧ back.length = suf.length
      ∧ align pre sp front = some psF ∧ ps = psF ++ suf.zip back := by
  obtain ⟨ds, hs, hlen, rfl⟩ := alignL_eq_some.mp h
  obtain ⟨dsF, hsF, rfl, hlenF, hle⟩ := slotsL_split pre sp suf xs.length ds hs
  refine ⟨xs.take (xs.length - suf.length), xs.drop (xs.length - suf.length),
    dsF.zip (xs.take (xs.length - suf.length)),
    (List.take_append_drop _ _).symm, by simp; omega,
    align_of_slots hsF (by simp), ?_⟩
  conv_lhs => rw [← List.take_append_drop (xs.length - suf.length) xs]
  rw [List.zip_append (by simp; omega)]



/-- …and the split built rather than read: a row long enough for the suffix aligns. -/
theorem alignL_of_split {α : Type} {pre : List (Codec V M)} {sp : Option (Codec V M)}
    {suf : List (Codec V M)}
    {front back : List α} {psF} (hb : back.length = suf.length)
    (h : align pre sp front = some psF) :
    alignL pre sp suf (front ++ back) = some (psF ++ suf.zip back) := by
  obtain ⟨ds, hs, hlen, rfl⟩ := align_eq_some.mp h
  unfold alignL slotsL
  rw [if_neg (by simp [hb]), show (front ++ back).length - suf.length = front.length by
    simp [hb], hs]
  simp only [Option.map_some]
  rw [List.zip_append (by omega)]

/-- A row shorter than the suffix aligns against nothing. -/
theorem alignL_short {α : Type} (pre : List (Codec V M)) (sp : Option (Codec V M))
    (suf : List (Codec V M))
    (xs : List α) (h : xs.length < suf.length) : alignL pre sp suf xs = none := by
  unfold alignL slotsL; rw [if_pos h]; rfl

/-- **`alignL` as one equation.** A row long enough for the suffix aligns exactly when its
    left part aligns against the prefix and spread, and the answer is that alignment with
    the suffix zipped onto the right part. Every fact about `alignL` follows from this and
    the corresponding fact about `align`. -/
theorem alignL_eq_split {α : Type} (pre : List (Codec V M)) (sp : Option (Codec V M))
    (suf : List (Codec V M))
    (xs : List α) (h : suf.length ≤ xs.length) :
    alignL pre sp suf xs
      = (align pre sp (xs.take (xs.length - suf.length))).map
          (· ++ suf.zip (xs.drop (xs.length - suf.length))) := by
  cases hal : align pre sp (xs.take (xs.length - suf.length)) with
  | none =>
    simp only [Option.map_none]
    cases hL : alignL pre sp suf xs with
    | none => rfl
    | some ps =>
      obtain ⟨front, back, psF, rfl, hblen, halF, rfl⟩ := alignL_split _ _ _ _ _ hL
      have hlen : (front ++ back).length - suf.length = front.length := by simp [hblen]
      rw [hlen, List.take_left] at hal
      rw [hal] at halF
      exact nomatch halF
  | some psF =>
    have hb : (xs.drop (xs.length - suf.length)).length = suf.length := by simp; omega
    have := alignL_of_split (pre := pre) (sp := sp) (suf := suf) hb hal
    rw [List.take_append_drop] at this
    rw [this]
    rfl

section ListShape
variable {pre : List (Codec V M)} {sp : Option (Codec V M)} {suf : List (Codec V M)}

/-- (R) for the payload pair: realign the written row against the same codecs, then read
    back position by position. -/
theorem list_retract (hpre : ∀ c ∈ pre, LawfulCore member c) (hsp : ∀ c ∈ sp, LawfulCore member c)
    (hsuf : ∀ c ∈ suf, LawfulCore member c) :
    ∀ vs as, (alignL pre sp suf vs).bind (traverse fun cv => cv.1.e cv.2) = some as →
      (alignL pre sp suf as).bind (traverse fun ca => ca.1.p ca.2) = some vs := by
  intro vs as hE
  obtain ⟨ps, hal, htr⟩ := Option.bind_eq_some_iff.mp hE
  obtain ⟨ds, hs, hlen, rfl⟩ := alignL_eq_some.mp hal
  have hn : as.length = vs.length := by
    rw [← traverse_length _ _ htr, List.length_zip, hlen, Nat.min_self]
  exact Option.bind_eq_some_iff.mpr ⟨_, alignL_of_slotsL hs hn,
    zip_roundTrip ds vs as (slotsL_all hpre hsp hsuf hs) hlen htr⟩

end ListShape

/-- A spread alone assigns the same codec to every position. -/
theorem slots_spread (c : Codec V M) : ∀ n : Nat, slots [] (some c) n = some (List.replicate n c)
  | 0 => rfl
  | n + 1 => by rw [slots, slots_spread c n]; rfl

/-- Traversing a row of one repeated codec is traversing that codec. -/
theorem traverse_replicate_zip {α β : Type} (c : Codec V M) (g : Codec V M → α → Option β) :
    ∀ xs : List α,
      traverse (fun q : Codec V M × α => g q.1 q.2) ((List.replicate xs.length c).zip xs)
        = traverse (g c) xs
  | [] => rfl
  | x :: xs => by
      simp only [List.length_cons, List.replicate_succ, List.zip_cons_cons, traverse_cons]
      rw [traverse_replicate_zip c g xs]

/-- A spread alone aligns every position against the one codec. -/
theorem alignL_spread {α : Type} (c : Codec V M) (xs : List α) :
    alignL [] (some c) [] xs = some ((List.replicate xs.length c).zip xs) := by
  unfold alignL
  rw [slotsL_nil_suf, slots_spread]
  rfl

/-- A position of such an alignment is the codec paired with a member of the row. -/
theorem mem_replicate_zip {α : Type} (c : Codec V M) (xs : List α) (d : Codec V M) (x : α) :
    (d, x) ∈ (List.replicate xs.length c).zip xs ↔ d = c ∧ x ∈ xs := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := List.of_mem_zip h
    exact ⟨List.eq_of_mem_replicate h1, h2⟩
  · rintro ⟨rfl, h2⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp h2
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp [hi], by simp [List.getElem_zip]⟩

/-! ## Related shapes -/

/-- `Option.map` keeps a relation that the two functions keep. -/
theorem optionRel_map {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {f : α → γ} {g : β → δ} (hfg : ∀ x y, R x y → S (f x) (g y)) :
    ∀ {a : Option α} {b : Option β}, Option.Rel R a b → Option.Rel S (a.map f) (b.map g)
  | _, _, .none => .none
  | _, _, .some h => .some (hfg _ _ h)

/-- `Option.bind` sends related inputs to one answer when the two functions agree on them. -/
theorem optionRel_bind {α β γ : Type} {R : α → β → Prop} {f : α → Option γ} {g : β → Option γ}
    (hfg : ∀ x y, R x y → f x = g y) :
    ∀ {a : Option α} {b : Option β}, Option.Rel R a b → a.bind f = b.bind g
  | _, _, .none => rfl
  | _, _, .some h => hfg _ _ h

/-- Related options are defined together. -/
theorem optionRel_isSome {α β : Type} {R : α → β → Prop} :
    ∀ {a : Option α} {b : Option β}, Option.Rel R a b → a.isSome = b.isSome
  | _, _, .none => rfl
  | _, _, .some _ => rfl

/-- A slot row of one shape pairs related codecs position by position. -/
theorem slots_rel {R : Codec V M → Codec V M → Prop} :
    ∀ (n : Nat) {cs₁ cs₂ : List (Codec V M)} {t₁ t₂ : Option (Codec V M)},
      List.Forall₂ R cs₁ cs₂ → Option.Rel R t₁ t₂ →
      Option.Rel (List.Forall₂ R) (slots cs₁ t₁ n) (slots cs₂ t₂ n)
  | 0, _, _, _, _, .nil, _ => .some .nil
  | 0, _, _, _, _, .cons _ _, _ => .none
  | _ + 1, _, _, _, _, .nil, .none => .none
  | n + 1, _, _, _, _, .nil, .some hc =>
      optionRel_map (fun _ _ h => .cons hc h) (slots_rel n .nil (.some hc))
  | n + 1, _, _, _, _, .cons hc hcs, ht =>
      optionRel_map (fun _ _ h => .cons hc h) (slots_rel n hcs ht)

/-- A `list` shape assigns related rows to related parts, position by position. -/
theorem slotsL_rel {R : Codec V M → Codec V M → Prop} {pre₁ pre₂ suf₁ suf₂ : List (Codec V M)}
    {sp₁ sp₂ : Option (Codec V M)} (hpre : List.Forall₂ R pre₁ pre₂) (hsp : Option.Rel R sp₁ sp₂)
    (hsuf : List.Forall₂ R suf₁ suf₂) (n : Nat) :
    Option.Rel (List.Forall₂ R) (slotsL pre₁ sp₁ suf₁ n) (slotsL pre₂ sp₂ suf₂ n) := by
  unfold slotsL
  rw [hsuf.length_eq]
  split
  · exact .none
  · exact optionRel_map (fun _ _ h => List.rel_append h hsuf) (slots_rel _ hpre hsp)

end Calculus.Alg
