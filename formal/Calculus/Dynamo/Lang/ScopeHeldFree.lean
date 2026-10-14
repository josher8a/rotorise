import Calculus.Dynamo.Lang.ScopeSound
import Calculus.Dynamo.Lang.Universe
import Calculus.Lang.ScopeHeldFree

/-!
# Held-free closed codecs are restrictions of `opaque`

A closed codec of DynamoDB is held-free when each term of each scope holds no `held`, no `legacy`
and no `fill` slot (`Closed.HF`). Its meaning is a restriction of the identity
(`Closed.sub_meaning`), from `Alg.Scoped.Closed.sub` and the laws `Ω_topLaws`. `opaque` as a
closed codec of one entry denotes the identity (`Closed.opaq_f`), so the meaning writes only what
`opaque` writes (`Closed.confluence_W`), and reads only what `opaque` reads
(`Closed.confluence_R`).
-/

namespace Calculus

/-- **A closed codec is held-free** when each term of its scope is held-free. The test is the
    definition, so a closed codec of a literal scope is shown held-free by `rfl`. -/
abbrev Closed.HF (t : Closed) : Prop := Alg.Scoped.Closed.HF t.scope

/-- **`opaque` is the identity** as a closed codec of one entry, at each orientation. -/
theorem Closed.opaq_f (α : Table) (o : Alg.Orient) (v : Value) :
    ((Closed.one .opaq).meaning α).f o v = some v :=
  Closed.one_fix α .opaq o v

/-- **Confluence**: the meaning of a held-free closed codec is a restriction of the identity. -/
theorem Closed.sub_meaning {α : Table} {t : Closed} (h : t.HF) : Alg.Sub (t.meaning α) Alg.idCodec :=
  Alg.Scoped.Closed.sub _ t.scope h t.root

/-- **(W)**: a held-free closed codec writes only what `opaque` writes. -/
theorem Closed.confluence_W {α : Table} {t : Closed} (h : t.HF) {v a}
    (he : (t.meaning α).e v = some a) : ((Closed.one .opaq).meaning α).e v = some a :=
  (Closed.opaq_f α .host v).trans (Closed.sub_meaning h .host _ _ he)

/-- **(R)**: a held-free closed codec reads only what `opaque` reads. -/
theorem Closed.confluence_R {α : Table} {t : Closed} (h : t.HF) {a v}
    (hp : (t.meaning α).p a = some v) : ((Closed.one .opaq).meaning α).p a = some v :=
  (Closed.opaq_f α .dual a).trans (Closed.sub_meaning h .dual _ _ hp)

end Calculus
