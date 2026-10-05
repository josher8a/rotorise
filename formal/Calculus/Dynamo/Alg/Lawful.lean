import Calculus.Dynamo.Alg.Carriers

/-!
# Lawfulness — proved

The combinators whose laws this development discharges, argued once per construction
rather than once per term.
-/

namespace Calculus

section
/-! ## Lawfulness — proved -/

/-! ### The ground codecs, argued once

Each base is the identity on the fiber of its kind, so `lawful_fiberCodec` proves every
base. A literal is its base restricted, so `Lawful.restrict` proves every literal. -/

/-- **Every base is lawful**: the identity on the fiber of its kind. -/
theorem lawful_baseCodec (k : GroundKind) : Lawful (baseCodec k) := Alg.lawful_fiberCodec

/-! ### The literal codec is lawful because its base is

`literal` adds a prism and nothing else, so retract, canon and writes come from
`Lawful.restrict`. That is one statement, because there is one codec. -/

/-- The rule `(literal)` is lawful, full stop.

    **No `ℓ ⊆ D` hypothesis, and the proof never needed one.** `Lawful` relates `e` and `p` to
    each other and never mentions `T`, so a restriction of a lawful pair is lawful whether or
    not the restriction is inhabited. That is why the premise `ℓ ⊆ D` belongs to the carrier and not
    here. -/
theorem lawful_literalCodec (k : GroundKind) (x : k.Carrier) :
    Lawful (literalCodec k x) :=
  have h := Alg.Lawful.restrict (lawful_baseCodec k) (inL k x)
  ⟨h.inv, h.writes⟩

end

end Calculus
