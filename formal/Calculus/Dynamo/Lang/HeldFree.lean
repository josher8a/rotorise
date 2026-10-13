import Calculus.Dynamo.Lang.Denote
import Calculus.Lang.HeldFree
import Calculus.Dynamo.Lang.Universe

variable {α : Calculus.Table}

/-!
# Held-free terms are restrictions of `opaque`

A term with no `held` does not change the carrier. Each combinator either restricts its
subterm or composes subterms through the structure that `opaque` itself uses. So the write
graph and the read graph of a held-free term lie inside the graphs of `opaque`.
`confluence_W` and `confluence_R` state the two inclusions. `sub_denote` proves them from
`Alg.sub_denote`, one mutual induction over `Term`, `Body`, `ObjectSlot`, the list and the
option, for every universe. The instance `Ω_topLaws` gives the laws of `Ω` that the induction
reads.

`Sub c d` is the inclusion of graphs on both halves. The set cases go through `setAt_congr` and
`setAt_congr`.

The set law of `Ω_topLaws` is `setCodec_mono`: over a held-free element, a set writes and reads
exactly where each element does. `Confluence.lean` holds the payoffs.
-/

namespace Calculus

/-! ## Held-free terms -/

-- A term is **held-free** when no `held` occurs in the term: `Alg.HF`, the test `hasHeld` at
-- `false`. The names are aliases, so a closed term is shown held-free by `rfl`.
export Alg (HF HFS HFL HFO)

/-- **Confluence**, closed: the denotation of a held-free term is a restriction of `Ω`. -/
theorem sub_denote (t : Term) (h : HF t) : Sub (denote α t) Ω :=
  Alg.sub_denote t h

/-- **(W)**: a held-free term writes only what `opaque` writes. -/
theorem confluence_W {t : Term} (h : HF t) {v a} (he : (denote α t).e v = some a) :
    (denote α .opaq).e v = some a := sub_denote t h .host _ _ he

/-- **(R)**: a held-free term reads only what `opaque` reads. -/
theorem confluence_R {t : Term} (h : HF t) {a v} (hp : (denote α t).p a = some v) :
    (denote α .opaq).p a = some v := sub_denote t h .dual _ _ hp

end Calculus
