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

/-- **Every base is lawful**: a point codec whose prism stamps the member of its kind. -/
theorem lawful_baseCodec (k : GroundKind) : Lawful (baseCodec k) :=
  lawful_pointCodec (by cases k <;> exact fun _ => rfl)

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
