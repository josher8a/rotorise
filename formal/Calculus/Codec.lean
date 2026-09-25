import Calculus.Domain
import Calculus.AlgRelations
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
  funImage funImage_some funImage_isSome funImage_isSome_iff funImage_eq
  Sub sub_restrict_self optBot approx_extendRead approx_restrict selectF ConfluentAt selectF_admit
  selectF_skip selectF_mono IsSupAt selectF_continuous selectF_mem selectF_of_mem
  selectF_mono_list selectF_continuous_list Compat find?_attempt_V find?_attempt_A acts_of_find?_V
  acts_of_find?_A Canon altCodec_e_of_mem altCodec_p_of_mem lawfulCore_altCodec lawful_altCodec
  compat_of_exclusive compat_of_agree compat_of_common_bound compat_of_common_bound'
  option_eq_of_some_iff altCodec_perm equiv_altCodec_perm equiv_altCodec_swap equiv_through_id
  equiv_through_comp equiv_restrict_meet equiv_restrict_full extendRead_self_p
  equiv_extendRead_self extendRead_eq_on_can equiv_altCodec_single through_μ restrict_μ
  extendRead_μ select_nil_eq select_cons altCodec_nest_e altCodec_nest_p altCodec_assoc_heldSet)

namespace Codec
export Alg.Codec (ext ext_iff empty Ker.refl Ker.symm Ker.trans Approx Approx.refl
  Approx.empty_le Equiv Equiv.refl Equiv.symm)
end Codec

namespace ConfluentAt
export Alg.ConfluentAt (tail)
end ConfluentAt

namespace Compat
export Alg.Compat (p_agree e_agree cross)
end Compat

namespace Lawful
export Alg.Lawful (empty congr)
end Lawful

namespace Carrier
export Alg.Carrier (empty congr)
end Carrier

end Calculus
