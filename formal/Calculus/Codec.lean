import Calculus.Domain
import Calculus.AlgCombinators
import Calculus.AlgMaps

/-!
# §2 — What a codec is, and its laws

The pair is data; the laws are a `Prop`-valued structure over it: a lawful codec is a canonical
partial bijection. The record and its laws take the carriers as parameters. This file instantiates
them at `Value`, `Attr` and `Member`. The side conditions and the combinators take the carriers as
parameters too, and the aliases below give them their names in this namespace.
-/

namespace Calculus

/-- §2: `c = (T, μ, e, p)`, at the DynamoDB carriers. -/
abbrev Codec := Alg.Codec Value Attr Member

/-- §2 Laws at the DynamoDB carriers: (W) reads the member of an attribute. -/
abbrev Lawful := Alg.Lawful (V := Value) Attr.member

/-- §2 core laws at the DynamoDB carriers. -/
abbrev LawfulCore := Alg.LawfulCore (V := Value) Attr.member

/- An `export` alias whose first explicit parameter is the generic record captures field
   notation, and Lean then refuses the argument of the abbreviation. So only the names that no
   caller reaches by field notation get an alias. Field notation reaches the others through the
   abbreviation. -/
export Alg (Can IsoCancels ReadsCoherently Carrier can_iff_image SurvivesStore
  Ctor pointCodec partialId through_e_adapt through_p_adapt restrict_e_adapt restrict_p_adapt
  restrict_e_isSome through_e through_p restrict_p_isSome restrict_e restrict_p extendRead_e
  extendRead_p length_le_one_of_pairwise_false AdmitsAtMostOne select altCodec select_eq_some
  select_admits altCodec_e altCodec_p altCodec_e_admits altCodec_p_admits carrier_pointCodec
  carrier_through carrier_restrict carrier_extendRead carrier_altCodec lawful_pointCodec
  funImage funImage_some funImage_isSome funImage_isSome_iff funImage_eq)

namespace Codec
export Alg.Codec (ext ext_iff empty Ker.refl Ker.symm Ker.trans)
end Codec

namespace Lawful
export Alg.Lawful (empty congr)
end Lawful

namespace Carrier
export Alg.Carrier (empty congr)
end Carrier

end Calculus
