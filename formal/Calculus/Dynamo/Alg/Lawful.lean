import Calculus.Dynamo.Alg.Carriers

/-!
# Lawfulness — proved

The combinators whose laws this development discharges, argued once per construction
rather than once per term.
-/

namespace Calculus

noncomputable section
/-! ## Lawfulness — proved -/

/-! ### The point ground codecs, argued once

`string`, `boolean`, `binary` and `null` are `pointCodec` at four different pairs of
prisms. Below, each of the four is that one lemma transported across the definitional
equality by `Lawful.congr`, which is what lets the definitions stay in the unfolded form
the rest of the development `simp`s with. -/

theorem lawful_stringCodec : Lawful stringCodec :=
  Lawful.congr (d := pointCodec strV sC .S)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl) rfl
    (lawful_pointCodec (fun _ => rfl))

theorem lawful_booleanCodec : Lawful booleanCodec :=
  Lawful.congr (d := pointCodec boolV boolA .BOOL)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl) rfl
    (lawful_pointCodec (fun _ => rfl))

theorem lawful_binaryCodec : Lawful binaryCodec :=
  Lawful.congr (d := pointCodec binV bC .B)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl) rfl
    (lawful_pointCodec (fun _ => rfl))

theorem lawful_nullCodec : Lawful nullCodec :=
  Lawful.congr (d := pointCodec nullV nullA .NULL)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl) rfl
    (lawful_pointCodec (fun _ => rfl))

/-- **The `(number)` case, with no axiom.** `e` and `p` are mutually inverse constructor
    wrappers over one carrier, so retract, canon and writes are `rfl` at the only inhabited
    row. No shortest-text round trip is needed, because there is no host spelling to
    round-trip through. -/
theorem lawful_numberCodec : Lawful numberCodec := by
  refine .ofRC ?_ ?_ ?_
  · intro t a he
    cases t with
    | n x => cases he; rfl
    | _ => exact nomatch he
  · intro a t hp
    cases a with
    | n x => cases hp; rfl
    | _ => exact nomatch hp
  · intro μ hμ t a he
    cases t with
    | n x => cases he; cases hμ; rfl
    | _ => exact nomatch he

/-- …and every base is lawful. -/
theorem lawful_baseCodec : ∀ k : GroundKind, Lawful (baseCodec k)
  | .string  => lawful_stringCodec
  | .number  => lawful_numberCodec
  | .boolean => lawful_booleanCodec
  | .binary  => lawful_binaryCodec
  | .null    => lawful_nullCodec

/-! ### The literal codec is lawful because its base is

`literal` adds a prism and nothing else, so retract, canon and writes come from
`Lawful.restrict`. That is one statement, because there is one codec. -/

/-- §3 `(literal)` is lawful, full stop.

    **No `ℓ ⊆ D` hypothesis, and the proof never needed one.** `Lawful` relates `e` and `p` to
    each other and never mentions `T`, so a restriction of a lawful pair is lawful whether or
    not the restriction is inhabited. That is why §3's `ℓ ⊆ D` belongs to the carrier and not
    here. -/
theorem lawful_literalCodec (k : GroundKind) (x : k.Carrier) :
    Lawful (literalCodec k x) :=
  Lawful.congr (d := (baseCodec k).restrict (inL k x)) rfl rfl rfl
    (Alg.Lawful.restrict (lawful_baseCodec k) (inL k x))

end

end Calculus
