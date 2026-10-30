/-!
# The JSON carrier

A JSON value, and a decidable equality on it. The deriving handler does not read the pair list of
an object, so three functions compare the nested lists by hand.
-/

namespace Calculus.JSON

/-- A JSON value. A number is an integer. -/
inductive Json where
  | null
  | bool (b : Bool)
  | num (n : Int)
  | str (s : String)
  | arr (xs : List Json)
  | obj (kvs : List (String × Json))

mutual
/-- **Equality of JSON values is decidable.** The deriving handler does not read the pair list of
    an object, so the three functions compare the nested lists by hand. -/
def Json.decEq : (a b : Json) → Decidable (a = b)
  | .null, .null => isTrue rfl
  | .bool x, .bool y => if h : x = y then isTrue (by rw [h]) else isFalse (fun e => h (Json.bool.inj e))
  | .num x, .num y => if h : x = y then isTrue (by rw [h]) else isFalse (fun e => h (Json.num.inj e))
  | .str x, .str y => if h : x = y then isTrue (by rw [h]) else isFalse (fun e => h (Json.str.inj e))
  | .arr xs, .arr ys =>
    match Json.decEqL xs ys with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (fun e => h (Json.arr.inj e))
  | .obj xs, .obj ys =>
    match Json.decEqO xs ys with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (fun e => h (Json.obj.inj e))
  | .null, .bool _ | .null, .num _ | .null, .str _ | .null, .arr _
  | .null, .obj _ | .bool _, .null | .bool _, .num _ | .bool _, .str _
  | .bool _, .arr _ | .bool _, .obj _ | .num _, .null | .num _, .bool _
  | .num _, .str _ | .num _, .arr _ | .num _, .obj _ | .str _, .null
  | .str _, .bool _ | .str _, .num _ | .str _, .arr _ | .str _, .obj _
  | .arr _, .null | .arr _, .bool _ | .arr _, .num _ | .arr _, .str _
  | .arr _, .obj _ | .obj _, .null | .obj _, .bool _ | .obj _, .num _
  | .obj _, .str _ | .obj _, .arr _ => isFalse (fun e => by cases e)
/-- The list mirror at `arr`. -/
def Json.decEqL : (xs ys : List Json) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | x :: xs, y :: ys =>
    match Json.decEq x y, Json.decEqL xs ys with
    | isTrue h, isTrue h' => isTrue (by rw [h, h'])
    | isFalse h, _ => isFalse (fun e => h (List.cons.inj e).1)
    | _, isFalse h => isFalse (fun e => h (List.cons.inj e).2)
  | [], _ :: _ => isFalse (fun e => by cases e)
  | _ :: _, [] => isFalse (fun e => by cases e)
/-- The list mirror at `obj`: a pair holds a name and a value. -/
def Json.decEqO : (xs ys : List (String × Json)) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | (k, x) :: xs, (l, y) :: ys =>
    if hk : k = l then
      match Json.decEq x y, Json.decEqO xs ys with
      | isTrue h, isTrue h' => isTrue (by rw [hk, h, h'])
      | isFalse h, _ => isFalse (fun e => h (by have := (List.cons.inj e).1; simp_all))
      | _, isFalse h => isFalse (fun e => h (List.cons.inj e).2)
    else isFalse (fun e => hk (by have := (List.cons.inj e).1; simp_all))
  | [], _ :: _ => isFalse (fun e => by cases e)
  | _ :: _, [] => isFalse (fun e => by cases e)
end

instance : DecidableEq Json := Json.decEq

end Calculus.JSON
