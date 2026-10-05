import Calculus.Dynamo.Domain
import Calculus.Alg.Relations
import Calculus.Alg.Maps

/-!
# What a codec is, and its laws

The pair is data; the laws are a `Prop`-valued structure over it: a lawful codec is a canonical
partial bijection. The record and its laws take the carriers as parameters. This file instantiates
them at `Value`, `Attr` and `Member`. The side conditions and the combinators take the carriers as
parameters too, and the aliases below give them their names in this namespace.
-/

/-- The unfolds of a ground base: the point codec, the prism of each kind, and the five prisms.
    A proof that computes a base or a literal at a concrete datum reads this set. -/
register_simp_attr prism_rows

/-- The two readings of a codec: the write `e` is the map at the host, and the read `p` is the map
    at the dual. A proof that unfolds a reading to its map reads this set. -/
register_simp_attr orient_rows

namespace Calculus

/-- The codec record `c = (T, μ, f)`, at the DynamoDB carriers. -/
abbrev Codec := Alg.Codec Value Member

/-- The codec laws at the DynamoDB carriers: (W) reads the member of an attribute. -/
abbrev Lawful := Alg.Lawful (V := Value) Attr.member

/-- The core codec laws at the DynamoDB carriers. -/
abbrev LawfulCore := Alg.LawfulCore (V := Value) Attr.member

/- An `export` alias whose first explicit parameter is the generic record captures field
   notation, and Lean then refuses the argument of the abbreviation. So only the names that no
   caller reaches by field notation get an alias. Field notation reaches the others through the
   abbreviation. -/
export Alg (Can IsoCancels ReadsCoherently Carrier SurvivesStore Ctor partialId
  through_e through_p refine2_f
  length_le_one_of_pairwise_false AdmitsAtMostOne select altCodec select_admits altCodec_f
  carrier_restrict
  carrier_altCodec funImage funImage_some funImage_isSome funImage_isSome_iff
  funImage_eq Sub sub_restrict_self optBot selectF ConfluentAt
  Compat
  Canon lawful_altCodec compat_of_exclusive compat_of_common_bound'
  equiv_restrict_meet equiv_restrict_full altCodec_nest
  altCodec_assoc_heldSet)

namespace Codec
export Alg.Codec (ext empty Equiv)
end Codec

namespace Lawful
export Alg.Lawful (empty)
end Lawful

namespace Carrier
export Alg.Carrier (empty congr)
end Carrier

end Calculus
