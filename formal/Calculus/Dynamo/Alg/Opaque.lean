import Calculus.Dynamo.Alg.Frontier
import Calculus.Dynamo.Alg.Recursion

/-!
# `opaque` is the identity

The rule `(opaque)` states the recursive union of everything self-identifying: the five bases, and
`set`, `array` and `record` over `opaque`. With one carrier, each datum identifies itself, so that
union sends each datum to itself at each orientation. `opaque` is therefore the identity codec of
the carrier, by definition. That union is a theorem about the term `union [...]`
(`Adm_opaqUnfold`, `AdmA_opaqUnfold`), not the definition of `opaque`.
-/

namespace Calculus

/-- `opaque`'s codec: the identity codec of the carrier. -/
abbrev Ω : Codec := Alg.idCodec

/-- `opaque` is lawful. -/
theorem lawful_opaq : Lawful Ω := Alg.lawful_idCodec

/-- `opaque` holds every datum. -/
theorem carrier_opaq : Carrier Ω := Alg.carrier_idCodec

end Calculus
