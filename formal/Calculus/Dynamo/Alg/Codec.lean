import Calculus.Dynamo.Domain
import Calculus.Alg.Relations
import Calculus.Alg.Maps

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
export Alg (Can IsoCancels ReadsCoherently Carrier SurvivesStore Ctor pointCodec partialId
  through_e_adapt restrict_e_adapt restrict_e_isSome through_e through_p restrict_e restrict_p
  length_le_one_of_pairwise_false AdmitsAtMostOne select altCodec select_admits altCodec_e
  altCodec_p altCodec_e_admits altCodec_p_admits carrier_pointCodec carrier_restrict
  carrier_altCodec lawful_pointCodec funImage funImage_some funImage_isSome funImage_isSome_iff
  funImage_eq Sub sub_restrict_self optBot selectF ConfluentAt selectF_mono_list
  selectF_continuous_list Compat find?_attempt_V find?_attempt_A acts_of_find?_V acts_of_find?_A
  Canon lawful_altCodec compat_of_exclusive compat_of_common_bound compat_of_common_bound'
  altCodec_perm equiv_restrict_meet equiv_restrict_full altCodec_nest_e altCodec_nest_p
  altCodec_assoc_heldSet)

namespace Codec
export Alg.Codec (ext empty Ker.refl Ker.symm Ker.trans Approx.refl Equiv Equiv.refl Equiv.symm)
end Codec

namespace ConfluentAt
export Alg.ConfluentAt (tail)
end ConfluentAt

namespace Compat
export Alg.Compat (cross)
end Compat

namespace Lawful
export Alg.Lawful (empty congr)
end Lawful

namespace Carrier
export Alg.Carrier (empty congr)
end Carrier

end Calculus
