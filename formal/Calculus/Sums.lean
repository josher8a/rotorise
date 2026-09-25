import Calculus.Objects
import Calculus.AlgTerm

/-!
# Sums (§5), and unknown values

`altCodec` over the options' codecs: the first option that acts answers. `opaqStep` is one layer of
`opaque`: `altCodec` over everything self-identifying, and its number option is `numberCodec`,
which holds a numeral exactly.
-/

namespace Calculus

noncomputable section
export Alg (unanimous)

/-! ## Unknown values (§3 `(opaque)`) -/

/-- §3 `(opaque)`'s eight self-identifying options; `rec` is where the recursion goes.

    Named because three statements cite it — `opaqStep`, `opaq_onKinds`,
    `compat_opaque` — and a list spelled three times can drift twice. The number
    option is `numberCodec`, which holds a numeral exactly. -/
def opaqOptions (rec : Codec) : List Codec :=
  [stringCodec, booleanCodec, binaryCodec, nullCodec, numberCodec,
   setCodec rec, arrayCodec rec, recordCodec rec]

/-- `opaque`'s body: one layer of everything self-identifying, with `c` for the layer below.
    `opaque` is not special: it is the recursive codec of this body, closed under the
    containers — "the values whose type is recoverable", as a fixpoint of the algebra. Its
    compatibility is kind-disjointness (`compat_opaque`). -/
def opaqStep (c : Codec) : Codec := altCodec (opaqOptions c) none

end

end Calculus
