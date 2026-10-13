import Calculus.Dynamo.Analysis.Slice
import Calculus.Lang.Path

/-!
# The precondition of a clause, as data for the store

A clause narrows a union (`Alg.narrow`), and the narrowing law holds for an item whose attribute at
the union the stored view of the clause admits (`Alg.narrow_law`). The store tests a condition on
the update, so the port states that admission as data: a conjunction of conditions, each a test at
a path into the item. Each test is one that DynamoDB evaluates: `in` (the attribute is one of a
finite list of literals at one base), `type` (the attribute has one member), and `exists` (the
attribute exists).

`preconditionOf` states the precondition of a clause exactly, or refuses. The precondition reads the
stored view of the clause (`Alg.view .dual`), as `Alg.narrow` does. A stored view gives an exact
precondition where it is a literal, a union of literals at one base, a base, `opaque`, or an open
object whose slots are each required at a stored view that gives an exact precondition. Every other
stored view refuses, so the port states no precondition that `preconditionOf_exact` does not cover.
A clause with no key refuses below the root, because the empty conjunction admits an attribute that
is no map. `preconditionOf_exact` states that the precondition holds on an item exactly where the
stored view of the clause admits the attribute at the path. `narrow_law_precondition` is the
narrowing law with the precondition in place of the admission.

**The precondition is exact for the stored view, and not for the raw clause.** A `held` admits where
its stored side admits and where the read of the adapter satisfies the outer term. The store tests
the stored side alone, so the precondition of `number(1)` is `in [N 1]`, which is the admission of
the stored view. A refinement over an adapter has the truth as its stored predicate, so its
precondition is the precondition of its inner term. The narrowing law reads the stored view of the
clause, so the precondition discharges the law.
-/

namespace Calculus

open Alg (Seg)

/-! ## The order of the names

A precondition lists the condition of each name of an object, so the names of a `Finset` need one
list. A `Finset` holds its names up to a permutation, and a sort by `compare` gives one list for
each permutation. The sort is an insertion sort, with its laws proved here: the sort laws of the
library reach `Classical.choice` through constants that the gateway baseline does not list. -/

/-- The insertion of a name into a sorted list. -/
def insertName (a : String) : List String → List String
  | [] => [a]
  | b :: bs => if compare a b = .gt then b :: insertName a bs else a :: b :: bs

/-- The insertion sort of a list of names. -/
def sortNames : List String → List String
  | [] => []
  | a :: as => insertName a (sortNames as)

/-- An insertion is a permutation of the cons. -/
theorem perm_insertName (a : String) : ∀ l : List String, (insertName a l).Perm (a :: l)
  | [] => .refl _
  | b :: bs => by
      unfold insertName
      split
      · exact ((perm_insertName a bs).cons b).trans (.swap a b bs)
      · exact .refl _

/-- A sort is a permutation. -/
theorem perm_sortNames : ∀ l : List String, (sortNames l).Perm l
  | [] => .refl _
  | a :: as => (perm_insertName a _).trans ((perm_sortNames as).cons a)

/-- An insertion keeps a list sorted. -/
theorem pairwise_insertName (a : String) : ∀ l : List String,
    l.Pairwise (fun x y => compare x y ≠ .gt) →
      (insertName a l).Pairwise (fun x y => compare x y ≠ .gt)
  | [] => fun _ => List.pairwise_singleton _ _
  | b :: bs => fun h => by
      rw [List.pairwise_cons] at h
      unfold insertName
      split
      · next hab =>
        refine List.pairwise_cons.mpr ⟨fun c hc => ?_, pairwise_insertName a bs h.2⟩
        rcases List.mem_cons.mp ((perm_insertName a bs).mem_iff.mp hc) with rfl | hc
        · rw [Std.OrientedCmp.gt_iff_lt] at hab
          rw [hab]; exact fun h => nomatch h
        · exact h.1 c hc
      · next hab =>
        refine List.pairwise_cons.mpr ⟨fun c hc => ?_, List.pairwise_cons.mpr h⟩
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hab
        · exact Std.TransCmp.le_trans hab (h.1 c hc)

/-- A sort is sorted. -/
theorem pairwise_sortNames : ∀ l : List String,
    (sortNames l).Pairwise (fun x y => compare x y ≠ .gt)
  | [] => List.Pairwise.nil
  | a :: as => pairwise_insertName a _ (pairwise_sortNames as)

/-- Two sorts of two permutations are one list. -/
theorem sortNames_perm {l l' : List String} (h : l.Perm l') : sortNames l = sortNames l' :=
  List.Perm.eq_of_pairwise (fun a b _ _ hab hba => by
      cases hc : compare a b with
      | lt => exact absurd (Std.OrientedCmp.gt_iff_lt.mpr hc) hba
      | eq => exact Std.LawfulEqCmp.eq_of_compare hc
      | gt => exact absurd hc hab)
    (pairwise_sortNames l) (pairwise_sortNames l')
    ((perm_sortNames l).trans (h.trans (perm_sortNames l').symm))

/-- **The names of a `Finset`, in the order of `compare`.** -/
def sortedKeys (s : Finset String) : List String :=
  Quot.liftOn s.val sortNames fun _ _ h => sortNames_perm h

/-- The list holds the names of the `Finset`. -/
theorem mem_sortedKeys {s : Finset String} {k : String} : k ∈ sortedKeys s ↔ k ∈ s := by
  obtain ⟨⟨l⟩, _⟩ := s
  exact (perm_sortNames l).mem_iff

/-! ## The precondition of a term

The precondition of a term is the precondition of its stored view (`Alg.view .dual`). Each function
below reads the raw term and takes the row that the stored view takes, so the stored view is never
built: a `held` gives the precondition of its stored side, an alternate reader gives the
precondition of `opaque`, and a refinement that the stored view keeps as the truth gives the
precondition of its inner term. -/

/-- The literal that the stored view of a term is, where it is one. -/
def storedLit : Term → Option ((k : GroundKind) × k.Carrier)
  | .literal k x => some ⟨k, x⟩
  | .held s t P _ _ => bif s then storedLit P else storedLit t
  | _ => none

/-- The literals of the stored views of a list of terms, each at the base `k`, or a refusal. -/
def storedLits (k : GroundKind) : List Term → Option (List k.Carrier)
  | [] => some []
  | t :: ts =>
      match storedLit t with
      | some ⟨k', x⟩ => if h : k' = k then (storedLits k ts).map (h ▸ x :: ·) else none
      | none => none

/-- Whether the stored view of a term is `opaque`. -/
def storedOpaq : Term → Bool
  | .opaq => true
  | .legacy _ _ => true
  | .held s t P _ _ => bif s then storedOpaq P else storedOpaq t
  | _ => false

mutual
/-- **The precondition of a term at a path**, or a refusal (`none`). The stored view decides the
    row. A literal and a union of literals at one base give `in`, a base gives `type`, `opaque`
    gives `exists`, and an open object whose slots are each required gives `type M` and the
    precondition of each name. Every other stored view refuses. -/
def termPrecondition : Term → List Seg → Option (List Cond)
  | .base k, π => some [⟨π, .type k.member⟩]
  | .literal k x, π => some [⟨π, .in k x []⟩]
  | .union (t :: ts), π =>
      match storedLit t with
      | some ⟨k, x⟩ => (storedLits k ts).map fun xs => [⟨π, .in k x xs⟩]
      | none => none
  | .opaq, π => some [⟨π, .exists⟩]
  | .legacy _ _, π => some [⟨π, .exists⟩]
  | .held s t P _ _, π => bif s then termPrecondition P π else termPrecondition t π
  | .refine t _ _, π => if Alg.hasHeld t || !t.closed then termPrecondition t π else none
  | .object b, π => (keysPrecondition b π).map (⟨π, .type .M⟩ :: ·)
  | _, _ => none
/-- The preconditions of the names of an open body, each at the path of its name. -/
def keysPrecondition : Body → List Seg → Option (List Cond)
  | .mk fields fld (some w), π =>
      if storedOpaq w then
        ((sortedKeys fields).attach.mapM fun k =>
          slotPrecondition (fld ⟨k.1, mem_sortedKeys.mp k.2⟩) (π ++ [.name k.1])).map List.flatten
      else none
  | _, _ => none
/-- The precondition of a required slot. Any other slot refuses: the stored view of a filled slot is
    optional. -/
def slotPrecondition : ObjectSlot → List Seg → Option (List Cond)
  | .req t, π => termPrecondition t π
  | _, _ => none
end

/-- **The precondition of a clause at the path of the union.** A clause is an open object, and its
    precondition is the precondition of each name. A clause with no name refuses below the root: the
    clause admits each map there, and the empty conjunction admits each attribute. At the root the
    item is a map, so the empty conjunction is the precondition. -/
def preconditionOf : Term → List Seg → Option (List Cond)
  | .object (.mk fields fld w), π =>
      match sortedKeys fields, π with
      | [], _ :: _ => none
      | _, _ => keysPrecondition (.mk fields fld w) π
  | _, _ => none

/-- The stored view of a `held` is the stored view of its stored side. -/
theorem view_held (s : Bool) (t P : Term) k₀ k :
    Alg.view .dual (Term.held s t P k₀ k) = bif s then Alg.view .dual P else Alg.view .dual t := by
  cases s <;> rfl

/-- `storedLit` names the literal that the stored view is. -/
theorem view_storedLit : ∀ {t : Term} {k : GroundKind} {x : k.Carrier},
    storedLit t = some ⟨k, x⟩ → Alg.view .dual t = Term.literal k x
  | .literal k' x', k, x, h => by
      simp only [storedLit, Option.some.injEq] at h; cases h; rfl
  | .held s t P _ _, k, x, h => by
      rw [view_held]; cases s
      · exact view_storedLit (t := t) h
      · exact view_storedLit (t := P) h
  | .base _, _, _, h | .never, _, _, h | .opaq, _, _, h | .var _, _, _, h | .mu _, _, _, h
  | .set _, _, _, h | .union _, _, _, h | .object _, _, _, h | .list _ _ _, _, _, h
  | .refine _ _ _, _, _, h | .legacy _ _, _, _, h => nomatch h

/-- `storedOpaq` holds where the stored view is `opaque`. -/
theorem view_storedOpaq : ∀ {t : Term}, storedOpaq t = true → Alg.view .dual t = Term.opaq
  | .opaq, _ => rfl
  | .legacy _ _, _ => rfl
  | .held s t P _ _, h => by
      rw [view_held]; cases s
      · exact view_storedOpaq (t := t) h
      · exact view_storedOpaq (t := P) h
  | .prim _, h | .never, h | .var _, h | .mu _, h
  | .set _, h | .union _, h | .object _, h | .list _ _ _, h
  | .refine _ _ _, h => nomatch h


/-! ## The exactness law -/

variable (α : Table)

/-- A refinement whose predicate is the truth reads what its inner term reads. -/
theorem AdmA_refine_truth (u : Term) (pA : Alg.Syn.PredA dynSyn) (a : Attr) :
    AdmA α (Term.refine u (Alg.Mean.truth (B := dynSig) false) pA) a = AdmA α u a := by
  rw [AdmA_refine]
  show (AdmA α u a && refineReads α u _ a) = _
  rw [refineReads_eq, (Bool.eq_iff_iff.mpr (AdmA_exact u a) : AdmA α u a = _)]
  cases (denote α u).p a with
  | none => rfl
  | some v => exact Alg.Mean.eval_truth (B := dynSig) false v


/-- The stored view of an object is the object of the stored views of its slots and of its open
    block. -/
theorem view_object (fields : Finset String) (fld : {k // k ∈ fields} → ObjectSlot) (w : Term) :
    Alg.view .dual (Term.object (.mk fields fld (some w))) =
      Term.object (.mk fields (fun k => Alg.viewS .dual (fld k)) (some (Alg.view .dual w))) := rfl

/-- **The stored view of an open object admits a map** whose required names are each present and
    admitted by the stored view of the slot. -/
theorem objectAdm {fields : Finset String} {fld : {k // k ∈ fields} → ObjectSlot} {w : Term}
    (hw : storedOpaq w = true) (hreq : ∀ k, ∃ t, fld k = .req t) (A : Attr) :
    AdmA α (Alg.view .dual (Term.object (.mk fields fld (some w)))) A = true ↔
      ∃ keys g, A = .m keys g ∧ ∀ k t, fld k = .req t →
        ∃ h : k.1 ∈ keys, AdmA α (Alg.view .dual t) (g ⟨k.1, h⟩) = true := by
  rw [view_object, view_storedOpaq hw, AdmA_object, AdmABody_mk]
  cases A with
  | m keys g =>
      simp only [AdmAWild_some, AdmA_opaq, Bool.and_eq_true, Alg.valPresentT, objAdmV,
        decide_eq_true_eq]
      constructor
      · rintro ⟨hp, ha⟩
        refine ⟨keys, g, rfl, fun k t hk => ⟨hp k (by rw [hk]; rfl), ?_⟩⟩
        have := of_decide_eq_true ha ⟨k.1, hp k (by rw [hk]; rfl)⟩
        simp only [entryP, MapOf.at, dif_pos k.2, Option.any_some, hk] at this
        exact this
      · rintro ⟨keys', g', he, h⟩
        cases he
        refine ⟨fun k _ => ?_, decide_eq_true fun k => ?_⟩
        · obtain ⟨t, ht⟩ := hreq k
          exact (h k t ht).1
        · simp only [entryP, MapOf.at]
          rcases Decidable.em (k.1 ∈ fields) with hk | hk
          · obtain ⟨t, ht⟩ := hreq ⟨k.1, hk⟩
            obtain ⟨_, h'⟩ := h ⟨k.1, hk⟩ t ht
            rw [dif_pos hk]
            simp only [Option.any_some, ht]
            exact h'
          · rw [dif_neg hk]; rfl
  | _ => simp

/-- **The admission at a path**: the attribute at the path exists, and the stored view of the term
    admits the attribute. -/
def admAt (t : Term) (π : List Seg) (R : Attr) : Bool :=
  match readPath π R with
  | some A => AdmA α (Alg.view .dual t) A
  | none => false

/-- The admission at a name: the attribute at the path is a map that holds the name, and the stored
    view admits the entry. -/
theorem admAt_name (t : Term) (π : List Seg) (n : String) (R : Attr) :
    admAt α t (π ++ [.name n]) R = true ↔ ∃ keys g, readPath π R = some (.m keys g) ∧
      ∃ h : n ∈ keys, AdmA α (Alg.view .dual t) (g ⟨n, h⟩) = true := by
  unfold admAt
  rw [readPath_append]
  cases readPath π R with
  | none => simp
  | some A =>
      cases A with
      | m keys g =>
          simp only [Option.bind_some, getSeg_name, MapOf.at, Option.some.injEq,
            Attr.m.injEq]
          constructor
          · intro h
            rcases Decidable.em (n ∈ keys) with hn | hn
            · rw [dif_pos hn] at h; exact ⟨keys, g, ⟨rfl, HEq.rfl⟩, hn, h⟩
            · rw [dif_neg hn] at h; exact nomatch h
          · rintro ⟨_, _, ⟨rfl, h⟩, hn, ha⟩
            cases h
            rw [dif_pos hn]; exact ha
      | _ => simp [getSeg_name]

/-- `storedLits` names the literals that the stored views of the options are. -/
theorem viewL_storedLits {k : GroundKind} : ∀ {ts : List Term} {xs : List k.Carrier},
    storedLits k ts = some xs → Alg.viewL .dual ts = xs.map (Term.literal k)
  | [], xs, h => by simp only [storedLits, Option.some.injEq] at h; subst h; rfl
  | t :: ts, xs, h => by
      unfold storedLits at h
      split at h
      · next k' x hl =>
        split at h
        · next he =>
          subst he
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨ys, hys, rfl⟩ := h
          show Alg.view .dual t :: Alg.viewL .dual ts = _
          rw [view_storedLit hl, viewL_storedLits hys]; rfl
        · exact nomatch h
      · exact nomatch h

/-- A union of literals at one base reads one of the literals. -/
theorem anyP_lits (k : GroundKind) (a : Attr) : ∀ xs : List k.Carrier,
    anyP (AdmAList α (xs.map (Term.literal k))) a = xs.any fun y => inL k y a
  | [] => rfl
  | x :: xs => by
      show (AdmA α (Term.literal k x) a || anyP (AdmAList α (xs.map (Term.literal k))) a) = _
      rw [anyP_lits k a xs, AdmA_literal]; rfl

mutual
/-- **The precondition of a term is exact**: on each item, the precondition holds where the stored
    view of the term admits the attribute at the path. -/
theorem termPrecondition_exact : ∀ (t : Term) (π : List Seg) (gs : List Cond),
    termPrecondition t π = some gs →
    ∀ R, gs.all (·.eval R) = admAt α t π R
  | .base k, π, gs, h, R => by
      simp only [termPrecondition, Option.some.injEq] at h; subst h
      unfold admAt Cond.eval
      cases hR : readPath π R <;> simp [hR, Test.eval, AdmA_base, inBase, Alg.view]
      rfl
  | .literal k x, π, gs, h, R => by
      simp only [termPrecondition, Option.some.injEq] at h; subst h
      unfold admAt Cond.eval
      cases hR : readPath π R <;> simp [hR, Test.eval, Alg.view]
  | .union (t :: ts), π, gs, h, R => by
      unfold termPrecondition at h
      split at h
      · next k x hl =>
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨xs, hxs, rfl⟩ := h
        unfold admAt Cond.eval
        have hv : Alg.view .dual (Term.union (t :: ts)) =
            Term.union ((x :: xs).map (Term.literal k)) := by
          show Alg.Term.union (Alg.view .dual t :: Alg.viewL .dual ts) = _
          rw [view_storedLit hl, viewL_storedLits hxs]; rfl
        cases hR : readPath π R with
        | none => simp [hR]
        | some A =>
            simp only [List.all_cons, List.all_nil, Bool.and_true, hv, AdmA_union_row, hR]
            rw [anyP_lits]; rfl
      · exact nomatch h
  | .opaq, π, gs, h, R => by
      simp only [termPrecondition, Option.some.injEq] at h; subst h
      unfold admAt Cond.eval
      cases hR : readPath π R <;> simp [hR, Test.eval, Alg.view]
      rfl
  | .legacy _ _, π, gs, h, R => by
      simp only [termPrecondition, Option.some.injEq] at h; subst h
      unfold admAt Cond.eval
      cases hR : readPath π R <;> simp [hR, Test.eval, Alg.view]
      rfl
  | .held s t P _ _, π, gs, h, R => by
      unfold admAt; rw [view_held]
      cases s
      · rw [termPrecondition_exact t π gs h R]; rfl
      · rw [termPrecondition_exact P π gs h R]; rfl
  | .refine t p pA, π, gs, h, R => by
      simp only [termPrecondition] at h
      split at h
      · next hc =>
        rw [termPrecondition_exact t π gs h R]
        unfold admAt
        have hv : Alg.view .dual (Term.refine t p pA) =
            Term.refine (Alg.view .dual t) (Alg.Mean.truth (B := dynSig) false) pA := by
          simp only [Alg.view, hc]; rfl
        cases readPath π R with
        | none => rfl
        | some A => show AdmA α _ A = AdmA α _ A; rw [hv, AdmA_refine_truth]
      · exact nomatch h
  | .object b, π, gs, h, R => by
      simp only [termPrecondition, Option.map_eq_some_iff] at h
      obtain ⟨gs', hb, rfl⟩ := h
      obtain ⟨fields, fld, w⟩ := b
      obtain ⟨w', rfl, hw, hreq, hall⟩ := keysPrecondition_exact (.mk fields fld w) π gs' hb rfl
      refine Bool.eq_iff_iff.mpr ?_
      rw [List.all_cons, Bool.and_eq_true, hall R]
      unfold admAt Cond.eval
      cases hR : readPath π R with
      | none => simp
      | some A =>
          rw [objectAdm α hw hreq]
          simp only [Test.eval, decide_eq_true_eq]
          constructor
          · rintro ⟨hm, hk⟩
            cases A with
            | m keys g =>
                refine ⟨keys, g, rfl, fun k t ht => ?_⟩
                obtain ⟨_, _, he, hn, ha⟩ := (admAt_name α t π k.1 R).mp (hk k t ht)
                rw [hR] at he; cases he; exact ⟨hn, ha⟩
            | _ => exact nomatch hm
          · rintro ⟨keys, g, rfl, hk⟩
            exact ⟨rfl, fun k t ht => (admAt_name α t π k.1 R).mpr ⟨keys, g, hR, hk k t ht⟩⟩
  | .never, _, _, h, _ | .var _, _, _, h, _ | .mu _, _, _, h, _ | .set _, _, _, h, _
  | .list _ _ _, _, _, h, _ | .union [], _, _, h, _ => nomatch h

/-- The preconditions of the names of an open body hold where the stored view of each required slot
    admits the entry at the name. -/
theorem keysPrecondition_exact : ∀ (b : Body) (π : List Seg) (gs : List Cond),
    keysPrecondition b π = some gs → ∀ {fields fld w}, b = .mk fields fld w →
      ∃ w', w = some w' ∧ storedOpaq w' = true ∧ (∀ k, ∃ t, fld k = .req t) ∧
        ∀ R, (gs.all (·.eval R) = true ↔
          ∀ k t, fld k = .req t → admAt α t (π ++ [.name k.1]) R = true)
  | .mk fields fld (some w), π, gs, h, _, _, _, hb => by
      cases hb
      simp only [keysPrecondition] at h
      split at h
      · next hw =>
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨gss, hm, rfl⟩ := h
        have hslot : ∀ k : {k // k ∈ fields}, ∃ t ys, fld k = .req t ∧
            slotPrecondition (fld k) (π ++ [.name k.1]) = some ys ∧
            ∀ R, ys.all (·.eval R) = admAt α t (π ++ [.name k.1]) R := fun k => by
          obtain ⟨ys, hy⟩ := isSome_of_mapM hm ⟨k.1, mem_sortedKeys.mpr k.2⟩ (List.mem_attach _ _)
          obtain ⟨t, ht, he⟩ := slotPrecondition_exact (fld k) _ ys hy
          exact ⟨t, ys, ht, hy, he⟩
        refine ⟨w, rfl, hw, fun k => ?_, fun R => ?_⟩
        · obtain ⟨t, _, ht, _⟩ := hslot k; exact ⟨t, ht⟩
        rw [all_flatten_mapM hm]
        constructor
        · intro hall k t ht
          obtain ⟨t', ys, ht', hy, he⟩ := hslot k
          rw [ht] at ht'; cases ht'
          rw [← he R]
          exact hall ⟨k.1, mem_sortedKeys.mpr k.2⟩ (List.mem_attach _ _) ys hy
        · intro hall k _ ys hy
          obtain ⟨t, ys', ht, hy', he⟩ := hslot ⟨k.1, mem_sortedKeys.mp k.2⟩
          rw [hy] at hy'; cases hy'
          rw [he R]
          exact hall _ t ht
      · exact nomatch h
  | .mk _ _ none, _, _, h, _, _, _, _ => nomatch h

/-- The precondition of a slot is the precondition of the term of a required slot. -/
theorem slotPrecondition_exact : ∀ (s : ObjectSlot) (π : List Seg) (gs : List Cond),
    slotPrecondition s π = some gs → ∃ t, s = .req t ∧ ∀ R, gs.all (·.eval R) = admAt α t π R
  | .req t, π, gs, h => ⟨t, rfl, termPrecondition_exact t π gs h⟩
  | .optional _, _, _, h | .fill _ _, _, _, h => nomatch h
end

/-- **The precondition of a clause is exact on an item**: the precondition holds where the stored
    view of the clause admits the attribute at the path. An item is a map. -/
theorem preconditionOf_exact {φ : Term} {π : List Seg} {gs : List Cond}
    (h : preconditionOf φ π = some gs)
    (R : Attr) (hitem : ∃ keys g, R = .m keys g) : gs.all (·.eval R) = admAt α φ π R := by
  cases φ
  case object b =>
    obtain ⟨fields, fld, w⟩ := b
    have hroot :
        (π = [] ∨ ∃ k, k ∈ fields) ∧ keysPrecondition (.mk fields fld w) π = some gs := by
      cases hs : sortedKeys fields with
      | nil =>
          cases π with
          | nil => exact ⟨.inl rfl, by simpa [preconditionOf, hs] using h⟩
          | cons s π => simp [preconditionOf, hs] at h
      | cons k ks =>
          exact ⟨.inr ⟨k, mem_sortedKeys.mp (by rw [hs]; exact List.mem_cons_self)⟩,
            by simpa [preconditionOf, hs] using h⟩
    obtain ⟨hπ, hkg⟩ := hroot
    obtain ⟨w', rfl, hw, hreq, hall⟩ := keysPrecondition_exact α _ π gs hkg rfl
    refine Bool.eq_iff_iff.mpr ?_
    rw [hall R]
    unfold admAt
    have hmap : (∀ k t, fld k = .req t → admAt α t (π ++ [.name k.1]) R = true) →
        ∃ keys g, readPath π R = some (.m keys g) := fun hk => by
      rcases hπ with rfl | ⟨k, hk'⟩
      · obtain ⟨keys, g, rfl⟩ := hitem; exact ⟨keys, g, rfl⟩
      · obtain ⟨t, ht⟩ := hreq ⟨k, hk'⟩
        obtain ⟨keys, g, hR, -⟩ := (admAt_name α t π k R).mp (hk _ t ht)
        exact ⟨keys, g, hR⟩
    constructor
    · intro hk
      obtain ⟨keys, g, hR⟩ := hmap hk
      rw [hR, objectAdm α hw hreq]
      refine ⟨keys, g, rfl, fun k t ht => ?_⟩
      obtain ⟨_, _, he, hn, ha⟩ := (admAt_name α t π k.1 R).mp (hk k t ht)
      rw [hR] at he; cases he; exact ⟨hn, ha⟩
    · intro hA
      cases hR : readPath π R with
      | none => rw [hR] at hA; exact nomatch hA
      | some A =>
          rw [hR, objectAdm α hw hreq] at hA
          obtain ⟨keys, g, rfl, hk⟩ := hA
          exact fun k t ht => (admAt_name α t π k.1 R).mpr ⟨keys, g, hR, hk k t ht⟩
  all_goals simp [preconditionOf] at h

/-! ## The narrowing law with the precondition -/

/-- **The narrowing law, with the precondition in place of the admission.** Take an item whose
    attribute at the path of the union is `A`, and on which the precondition of the clause holds. No
    option that narrowing drops reads `A`. A write at a path whose frontier the narrowed union gives
    keeps `A` readable by the union. The store tests the precondition on the update, and the
    precondition is the admission of the stored view of the clause (`preconditionOf_exact`). -/
theorem narrow_law_precondition {φ : Term} {os : List Term} {T : Attr → Prop} {μ : Option Member}
    (hty : Alg.Typed α dynTableA (.union (Alg.narrow .dual φ os)) T μ)
    (hob : Alg.Obligations α dynTableA (.union (Alg.narrow .dual φ os)))
    (hg : (Alg.Term.union (Alg.narrow .dual φ os)).guarded = true)
    (π : List Seg) (res : List (Alg.Frame dynSyn))
    (hat : (Alg.Term.union (Alg.narrow .dual φ os)).at π = some res)
    (w : Codec) (hw : ∀ g ∈ res, ∀ x a, w.e x = some a → ((Alg.Frame.sem α dynTableA g).p a).isSome)
    {pre : List Seg} {gs : List Cond} (hgs : preconditionOf φ pre = some gs)
    {R A A' x a : Attr} (hitem : ∃ keys g, R = .m keys g) (hR : readPath pre R = some A)
    (hG : gs.all (·.eval R) = true) (hA : ((denote α (.union os)).p A).isSome)
    (hx : w.e x = some a) (hput : Alg.putPath (S := dynSyn) π a A = some A') :
    (∀ o ∈ os, o ∉ Alg.narrow .dual φ os → (denote α o).p A = none) ∧
      ((denote α (.union os)).p A').isSome := by
  have hφ : admAt α φ pre R = true := by rw [← preconditionOf_exact α hgs R hitem]; exact hG
  unfold admAt at hφ
  rw [hR] at hφ
  exact Alg.narrow_law rfl hty hob hg π res hat w hw hφ hA hx hput


/-! ## Vectors

Each vector reduces in the kernel. A precondition is shown as its conditions, each a path of names
and a test. A key of a clause reads at the path of the union and then the name. -/

/-- The names of a path. A position shows as `#`. -/
private def names (π : List Seg) : List String := π.map fun | .name k => k | .pos _ => "#"

/-- `in` at a path, over string literals. -/
private def inS (π : List String) (ys : List String) (c : Cond) : Bool :=
  names c.path == π && match c.test with
    | .in .string x xs => x :: xs == ys
    | _ => false

/-- `in` at a path, over numeric literals. -/
private def inN (π : List String) (ys : List WFNumeral) (c : Cond) : Bool :=
  names c.path == π && match c.test with
    | .in .number x xs => decide (x :: xs = ys)
    | _ => false

/-- `type` at a path. -/
private def typeAt (π : List String) (m : Member) (c : Cond) : Bool :=
  names c.path == π && match c.test with
    | .type m' => decide (m' = m)
    | _ => false

/-- `exists` at a path. -/
private def existsAt (π : List String) (c : Cond) : Bool :=
  names c.path == π && match c.test with
    | .exists => true
    | _ => false

/-- Each condition of a precondition against one check each, in order. -/
private def shows (r : Option (List Cond)) (cs : List (Cond → Bool)) : Bool :=
  match r with
  | some gs => gs.length == cs.length && (gs.zip cs).all fun p => p.2 p.1
  | none => false

private abbrev litS (s : String) : Term := .literal .string s
private abbrev n1 : Term := .literal .number (WFNumeral.of "1")
private abbrev n2 : Term := .literal .number (WFNumeral.of "2")
/-- `number(1)`: a caller adapter over the literal `N 1`. -/
private abbrev num (l : Term) : Term := Term.held false l Term.number (.caller 0, false) []
/-- `decimal('1')`: the library text adapter over the literal `N 1`. -/
private abbrev dec (l : Term) (s : String) : Term :=
  Term.held false l (Term.literal .string s) (.decimalText, false) []
/-- A clause of one key. -/
private abbrev cl1 (t : Term) : Term := Alg.clauseTerm {"k"} fun _ => t
private abbrev m : List Seg := [.name "m"]

-- a string tag
example : shows (preconditionOf (cl1 (litS "A")) m) [inS ["m", "k"] ["A"]] = true := by decide
-- a string tag of two literals
example : shows (preconditionOf (cl1 (.union [litS "A", litS "B"])) m) [inS ["m", "k"] ["A", "B"]] =
    true := by decide
-- a numeric tag: `number(1)` stores `N 1`
example : shows (preconditionOf (cl1 (num n1)) m) [inN ["m", "k"] [WFNumeral.of "1"]] = true := by
  decide
-- a decimal tag: `decimal('1')` stores `N 1`
example : shows (preconditionOf (cl1 (dec n1 "1")) m) [inN ["m", "k"] [WFNumeral.of "1"]] = true := by
  decide
-- a union of numeric tags reads through each adapter to one base
example : shows (preconditionOf (cl1 (.union [num n1, num n2])) m)
    [inN ["m", "k"] [WFNumeral.of "1", WFNumeral.of "2"]] = true := by decide
-- a presence clause: `opaque` gives `exists`
example : shows (preconditionOf (cl1 .opaq) m) [existsAt ["m", "k"]] = true := by decide
-- a base clause: `number` gives `type N`
example : shows (preconditionOf (cl1 .number) m) [typeAt ["m", "k"] .N] = true := by decide
-- two keys: a conjunction, in the order of the names
example : shows (preconditionOf (Alg.clauseTerm {"t", "k"} fun x => if x.1 = "k" then litS "A" else
    Term.number) m) [inS ["m", "k"] ["A"], typeAt ["m", "t"] .N] = true := by decide
-- an open object under a key: `type M` and the precondition of its name
example : shows (preconditionOf (cl1 (Alg.clauseTerm {"z"} fun _ => litS "Z")) [])
    [typeAt ["k"] .M, inS ["k", "z"] ["Z"]] = true := by decide
-- a refinement over an adapter: the stored view keeps the truth, so the inner term decides
example : shows (preconditionOf (cl1 (.refine (num n1) (.closure fun _ => true) ())) m)
    [inN ["m", "k"] [WFNumeral.of "1"]] = true := by decide
-- the empty clause: the empty conjunction at the root, and a refusal below the root
example : shows (preconditionOf (Alg.clauseTerm ∅ fun k => nomatch k.2) []) [] = true := by decide
example : (preconditionOf (Alg.clauseTerm ∅ fun k => nomatch k.2) m).isNone = true := by decide

-- a closed object refuses
example : (preconditionOf (cl1 (.object (.mk {"z"} (fun _ => .req .string) none))) m).isNone = true := by
  decide
-- a list with a spread refuses
example : (preconditionOf (cl1 (.list [] (some .string) [])) m).isNone = true := by decide
-- a refinement that the stored view keeps refuses
example : (preconditionOf (cl1 (.refine .string (.closure fun _ => true) ())) m).isNone = true := by
  decide
-- an optional slot under a key refuses
example : (preconditionOf (cl1 (.object (.mk {"z"} (fun _ => .optional .string) (some .opaq))))
    m).isNone = true := by decide
-- a union of two bases refuses
example : (preconditionOf (cl1 (.union [litS "A", n1])) m).isNone = true := by decide

end Calculus
