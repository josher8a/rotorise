import Calculus.Dynamo.Domain

/-!
# Equality of attributes

`Attr` has no derived equality, because the deriving handler does not read the function field of
`m`. Two maps are equal where the key sets are equal and the two functions agree at each key,
which is a finite check. The finite sets compare through membership in each direction, because
`Finset.decidableEq` is a route to `Classical.choice` that no other definition of the development
holds.
-/

namespace Calculus


/-- **Two finite sets are equal where each holds the members of the other.** The comparison
    reaches no route to `Classical.choice` that `Finset.decidableEq` adds. -/
def decFinset {α : Type} [DecidableEq α] (s t : Finset α) : Decidable (s = t) :=
  decidable_of_iff ((∀ x ∈ s, x ∈ t) ∧ ∀ x ∈ t, x ∈ s)
    ⟨fun h => Finset.ext fun x => ⟨h.1 x, h.2 x⟩, fun h => h ▸ ⟨fun _ h => h, fun _ h => h⟩⟩

mutual
/-- **Equality of attributes is decidable.** The map member compares its key sets, then each
    value at a key. -/
def Attr.decEq : (a b : Attr) → Decidable (a = b)
  | .s x, .s y => if h : x = y then isTrue (by rw [h]) else isFalse (fun e => h (Attr.s.inj e))
  | .n x, .n y => if h : x = y then isTrue (by rw [h]) else isFalse (fun e => h (Attr.n.inj e))
  | .b x, .b y => if h : x = y then isTrue (by rw [h]) else isFalse (fun e => h (Attr.b.inj e))
  | .bool x, .bool y =>
    if h : x = y then isTrue (by rw [h]) else isFalse (fun e => h (Attr.bool.inj e))
  | .null, .null => isTrue rfl
  | .ss x, .ss y =>
    match decFinset x.1 y.1 with
    | isTrue h => isTrue (by rw [Subtype.ext h])
    | isFalse h => isFalse (fun e => h (congrArg Subtype.val (Attr.ss.inj e)))
  | .ns x, .ns y =>
    match decFinset x.1 y.1 with
    | isTrue h => isTrue (by rw [Subtype.ext h])
    | isFalse h => isFalse (fun e => h (congrArg Subtype.val (Attr.ns.inj e)))
  | .bs x, .bs y =>
    match decFinset x.1 y.1 with
    | isTrue h => isTrue (by rw [Subtype.ext h])
    | isFalse h => isFalse (fun e => h (congrArg Subtype.val (Attr.bs.inj e)))
  | .l xs, .l ys =>
    match Attr.decEqL xs ys with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (fun e => h (Attr.l.inj e))
  | .m ks f, .m ks' g =>
    match decFinset ks ks' with
    | isFalse h => isFalse (fun e => h (by cases e; rfl))
    | isTrue h => by
      subst h
      exact match @Fintype.decidableForallFintype _ (fun k => f k = g k)
          (fun k => Attr.decEq (f k) (g k)) _ with
        | isTrue h => isTrue (by congr; funext k; exact h k)
        | isFalse h => isFalse (fun e => h (fun k => by cases e; rfl))
  | .s _, .n _ | .s _, .b _ | .s _, .bool _ | .s _, .null
  | .s _, .ss _ | .s _, .ns _ | .s _, .bs _ | .s _, .l _
  | .s _, .m _ _ | .n _, .s _ | .n _, .b _ | .n _, .bool _
  | .n _, .null | .n _, .ss _ | .n _, .ns _ | .n _, .bs _
  | .n _, .l _ | .n _, .m _ _ | .b _, .s _ | .b _, .n _
  | .b _, .bool _ | .b _, .null | .b _, .ss _ | .b _, .ns _
  | .b _, .bs _ | .b _, .l _ | .b _, .m _ _ | .bool _, .s _
  | .bool _, .n _ | .bool _, .b _ | .bool _, .null | .bool _, .ss _
  | .bool _, .ns _ | .bool _, .bs _ | .bool _, .l _ | .bool _, .m _ _
  | .null, .s _ | .null, .n _ | .null, .b _ | .null, .bool _
  | .null, .ss _ | .null, .ns _ | .null, .bs _ | .null, .l _
  | .null, .m _ _ | .ss _, .s _ | .ss _, .n _ | .ss _, .b _
  | .ss _, .bool _ | .ss _, .null | .ss _, .ns _ | .ss _, .bs _
  | .ss _, .l _ | .ss _, .m _ _ | .ns _, .s _ | .ns _, .n _
  | .ns _, .b _ | .ns _, .bool _ | .ns _, .null | .ns _, .ss _
  | .ns _, .bs _ | .ns _, .l _ | .ns _, .m _ _ | .bs _, .s _
  | .bs _, .n _ | .bs _, .b _ | .bs _, .bool _ | .bs _, .null
  | .bs _, .ss _ | .bs _, .ns _ | .bs _, .l _ | .bs _, .m _ _
  | .l _, .s _ | .l _, .n _ | .l _, .b _ | .l _, .bool _
  | .l _, .null | .l _, .ss _ | .l _, .ns _ | .l _, .bs _
  | .l _, .m _ _ | .m _ _, .s _ | .m _ _, .n _ | .m _ _, .b _
  | .m _ _, .bool _ | .m _ _, .null | .m _ _, .ss _ | .m _ _, .ns _
  | .m _ _, .bs _ | .m _ _, .l _ => isFalse (fun e => by cases e)
/-- The list mirror that `Attr.decEq` needs at `l`. -/
def Attr.decEqL : (xs ys : List Attr) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | x :: xs, y :: ys =>
    match Attr.decEq x y, Attr.decEqL xs ys with
    | isTrue h, isTrue h' => isTrue (by rw [h, h'])
    | isFalse h, _ => isFalse (fun e => h (List.cons.inj e).1)
    | _, isFalse h => isFalse (fun e => h (List.cons.inj e).2)
  | [], _ :: _ => isFalse (fun e => by cases e)
  | _ :: _, [] => isFalse (fun e => by cases e)
end

instance : DecidableEq Attr := Attr.decEq

end Calculus
