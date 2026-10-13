import Calculus.Lang.DisjointA
import Calculus.Lang.View
import Calculus.Dynamo.Lang.HeldSet
import Calculus.Dynamo.Lang.HeldFree
import Calculus.Dynamo.Analysis.Merge
import Calculus.Dynamo.Analysis.Orthogonality
import Calculus.Dynamo.Analysis.Laminar

variable {α : Calculus.Table}

/-!
# Disjointness at DynamoDB, and the union certificate

`Alg.Term.disjoint` decides that two terms share no value, and `Alg.disjoint_orthogonal` proves
the decision sound over any signature. DynamoDB supplies the leaves (`dynLeaf`): two primitives
are apart where no value is both (`Ground.apart`), and two data predicates are apart where no
value satisfies both (`Pred.apart`). DynamoDB supplies the laws of the leaves and of the set
former (`dynLeafAdm`, `dynFormerAdm` and their read-side twins), and the shape classes
(`dynShapes`).

**The certificate reads the views, not the terms.** A term denotes a partial isomorphism.
The caller view states its domain, and the stored view states its range. A `held` carries an adapter word,
and the test reads no table, so the test reads a raw `held` as disjoint from the bottom alone. The views replace each `held`
by a term that bounds its domain or its range, so the certificate asks the test of the two pairs
of views (`viewsDisjoint`). Two terms whose domains are disjoint and whose ranges are disjoint are
orthogonal: no value has two writers, and no attribute has two readers.

**The two halves part at a `held`.** A `held` writes where its caller-side term writes and reads
where its inner term reads, so an adapter and a native of the adapter's stored kind are disjoint
on the write half and not on the read half. The certificate asks both halves.
-/

namespace Calculus

open Alg (Orient Term.isNever ObjectSlot.isReqAt Body.fields_mk Body.wild_mk Body.at_mk Body.block view)

export Alg (Term.ofOptions hasHeld pair0)


/-! ## The union certificate

The certificate is defined here, after the leaves, because the test of the views reads them. -/

/-- **Whether the two pairs of views are disjoint**: the certificate for one pair of options. A
    term denotes a partial isomorphism. The caller view states its domain and the stored view
    states its range. Where the domains are disjoint and the ranges are disjoint, the product of
    the two domain idempotents is zero and the product of the two range idempotents is zero: the
    two options are orthogonal elements of an inverse semigroup (Lawson, *Primer on inverse
    semigroups I*, Lemma 2.16). So no value has two writers and no attribute has two readers
    (`viewsDisjoint_adm`, `viewsDisjoint_admA`).

    **The views state the domain and the range of a `held`**, which the test does not read on a
    raw term. On a term with no `held`, the caller view is the term, and the stored view keeps
    each predicate over a closed held-free inner term.

    **A `refine` at a `closure` has an admission that is a function.** The test reads it through
    its inner term. So `refine string (closure q)` beside `list [] (some number) []` is
    certified, because `string` beside the list is disjoint. -/
def viewsDisjoint (x y : Term) : Bool :=
  Alg.Term.disjoint pair0 (view .host x) (view .host y) &&
    Alg.Term.disjoint pair0 (view .dual x) (view .dual y)

/-- **The certificate a union must carry for its admission to be the join of its options'**: the
    certificate over a list of options, pair by pair. One condition. Each pair of options is
    certified, so no value and no attribute has two admitters, and nothing is refused for being
    admitted twice.

    An open object needs no second condition. The structural lemmas carry the open block
    themselves, so a union holding an open block certifies on separation alone. -/
def certAll : List Term → Bool
  | [] => true
  | t :: ts => ts.all (fun u => viewsDisjoint t u) && certAll ts

/-- The certificate, in the pairwise form. -/
theorem pairwise_of_certAll : ∀ {ts : List Term}, certAll ts = true →
    List.Pairwise (fun x y => viewsDisjoint x y = true) ts
  | [], _ => .nil
  | _ :: _, h => by
      simp only [certAll, Bool.and_eq_true, List.all_eq_true] at h
      exact .cons (fun u hu => h.1 u hu) (pairwise_of_certAll h.2)

/-! ## What the rows answer

Worked pairs, one per class, checked by the kernel rather than described. -/

/-- Two value kinds share no value. -/
example : Alg.Term.disjoint pair0 Term.string Term.number = true := by rfl

/-- A literal shares its value with its own base… -/
example : Alg.Term.disjoint pair0 (Term.literal .string "a") Term.string = false := by rfl

/-- …and shares nothing with another value of the same base. -/
example : Alg.Term.disjoint pair0 (Term.literal .string "a") (Term.literal .string "b") = true := by
  rfl

/-- A literal at a base that shares nothing with the partner is disjoint from it. -/
example : Alg.Term.disjoint pair0 (Term.literal .string "1") Term.boolean = true := by rfl

/-- **The null point needs no row of its own.** A null point is the null term joined by a union,
    so the union row reads each option. The top holds the null point, and a `null` shares it. -/
example : Alg.Term.disjoint pair0 (Term.union [.string, .null]) Term.opaq = false := by rfl

example : Alg.Term.disjoint pair0 (Term.union [.string, .null]) Term.null = false := by rfl

/-- **Two open objects are not disjoint where each holds the other's names.** The left body
    requires `x`, and the right body holds `x` in its open block. The two examples below are a
    value both admit. -/
example : Alg.Term.disjoint pair0
    (Term.object (.mk {"x"} (fun _ => .req .string) (some .string)))
    (Term.object (.mk {"y"} (fun _ => .optional .string) (some .string))) = false := by rfl

/-- The left body admits `{x := "1"}` through its declared slot… -/
example : Adm α (.object (.mk {"x"} (fun _ => .req .string) (some .string)))
    (.map {"x"} (fun _ => .str "1")) = true := by
  simp [Adm_rows, valPresentT, objAdmV, entryP, MapOf.at, inBase]

/-- …and the right body admits it through its open block, at a name it does not declare. -/
example : Adm α (.object (.mk {"y"} (fun _ => .optional .string) (some .string)))
    (.map {"x"} (fun _ => .str "1")) = true := by
  simp [Adm_rows, valPresentT, ObjectSlot.isReqAt, objAdmV, entryP, MapOf.at]
  apply decide_eq_true
  intro k
  rw [if_neg (by have hk := k.2; simp only [Finset.mem_singleton] at hk; simp [hk])]
  rfl

/-! ### The presence table

A slot pair is disjoint only where one slot requires the name: two optional slots both admit a
map without the name. -/

/-- A required slot beside an optional slot of a disjoint term is disjoint. -/
example : Alg.ObjectSlot.disjoint pair0 (ObjectSlot.req .string) (ObjectSlot.optional .boolean)
    = true := by rfl

/-- Two optional slots are never disjoint. -/
example : Alg.ObjectSlot.disjoint pair0 (ObjectSlot.optional .string)
    (ObjectSlot.optional .boolean) = false := by rfl

/-- **Two closed objects with no shared name and no required name are not disjoint**: both
    admit the empty map. -/
example : Alg.Term.disjoint pair0
    (Term.object (.mk {"x"} (fun _ => .optional .string) none))
    (Term.object (.mk {"y"} (fun _ => .optional .string) none)) = false := by rfl

/-- **Two objects that declare one name with one mark and no literal are certified**: the
    required slots hold `string` and `boolean`, which are disjoint. -/
example : certAll [.object (.mk {"a"} (fun _ => .req .string) none),
    .object (.mk {"a"} (fun _ => .req .boolean) none)] = true := by decide

/-! ### A required position and an element

A position that must hold a value keeps two shapes apart where the two position terms are
disjoint. An element of an `array` does not, because every array holds the empty list. -/

/-- A tuple's declared position is such a position… -/
example : Alg.Term.disjoint pair0 (Term.tuple [.string] none) (Term.tuple [.boolean] none)
    = true := by rfl

/-- …an `array`'s element is not. -/
example : Alg.Term.disjoint pair0 (Term.array .string) (Term.array .boolean) = false := by rfl

/-- A refinement is disjoint from what its inner term is disjoint from. -/
example : Alg.Term.disjoint pair0
    (Term.refine .string (.members .string ⟨{"1"}, Finset.singleton_nonempty _⟩) ()) Term.null
      = true := by rfl

/-- **A refinement is apart from a refined union in both orders.** The right union refines
    `literal "a" ∪ number` to `literal "b"`, and the test reads the predicate of the right
    refinement on each option below it. -/
theorem disjoint_refinedUnion_bothOrders :
    Alg.Term.disjoint pair0 (.refine Term.string (.members .string (NEFinset.of "b" ∅)) () : Term)
        (.union [.refine (.union [.refine Term.string (.members .string (NEFinset.of "a" ∅)) (),
          Term.number]) (.members .string (NEFinset.of "b" ∅)) (), Term.number]) = true ∧
      Alg.Term.disjoint pair0
        (.union [.refine (.union [.refine Term.string (.members .string (NEFinset.of "a" ∅)) (),
          Term.number]) (.members .string (NEFinset.of "b" ∅)) (), Term.number] : Term)
        (.refine Term.string (.members .string (NEFinset.of "b" ∅)) ()) = true := by
  decide

/-- **Two recursive terms are apart in both orders where a refinement covers one.** A list of
    booleans and a refined list of strings share no value, and the test reads the recursive
    term below the refinement on the right as it reads the term on the left. -/
theorem disjoint_refinedRecursion_bothOrders :
    Alg.Term.disjoint pair0
        (.mu (.union [Term.boolean, .object (.mk {"k"} (fun _ => .req (.var 0)) none)]) : Term)
        (.refine (.mu (.union [Term.string, .object (.mk {"k"} (fun _ => .req (.var 0)) none)]))
          (.closure fun _ => true) ()) = true ∧
      Alg.Term.disjoint pair0
        (.refine (.mu (.union [Term.string, .object (.mk {"k"} (fun _ => .req (.var 0)) none)]))
          (.closure fun _ => true) () : Term)
        (.mu (.union [Term.boolean, .object (.mk {"k"} (fun _ => .req (.var 0)) none)])) = true := by
  decide

/-- **The certificate of a union does not read the order of the options.** A recursive term
    beside a `held` over a refined recursive term is certified in both orders. -/
theorem viewsDisjoint_heldRecursion_bothOrders :
    viewsDisjoint (.mu (.union [Term.boolean, .object (.mk {"k"} (fun _ => .req (.var 0)) none)]))
        (.held false Term.string (.refine (.mu (.union [Term.string,
          .object (.mk {"k"} (fun _ => .req (.var 0)) none)])) (.closure fun _ => true) ())
          (.caller 0, false) []) = true ∧
      viewsDisjoint (.held false Term.string (.refine (.mu (.union [Term.string,
          .object (.mk {"k"} (fun _ => .req (.var 0)) none)])) (.closure fun _ => true) ())
          (.caller 0, false) [])
        (.mu (.union [Term.boolean, .object (.mk {"k"} (fun _ => .req (.var 0)) none)])) = true := by
  decide

example : certAll [.object (.mk {"x"} (fun _ => .optional .string) none)] = true := by
  simp [certAll]

example : certAll [.object (.mk {"x"} (fun _ => .req .string) none)]
    = true := by
  simp [certAll]

/-- …and a singleton union of an **open** object is certified: a union of one option has no
    pair to certify. -/
example : certAll [.object (.mk {"a"} (fun _ => .req .string) (some .string))]
    = true := by
  simp [certAll]

/-! ### Arrays told apart by a literal position

The owner's witness. Each list below starts with a literal, and the empty list is an option of
its own. Each pair is disjoint. -/

/-- The three options: a nonempty list of `"A"`, a nonempty list of `"B"`, and the empty list. -/
def literalListOptions : List Term :=
  [.list [.literal .string "A"] (some (.literal .string "A")) [],
   .list [.literal .string "B"] (some (.literal .string "B")) [],
   .list [] none []]

/-- **The test certifies the union**: each pair is disjoint. -/
theorem certAll_literalListOptions : certAll literalListOptions = true := by decide

/-- **The crossing control is not certified.** `array (literal "A")` and `array (literal "B")`
    both hold `[]`. -/
theorem not_certAll_literalArrays :
    certAll [.array (.literal .string "A"), .array (.literal .string "B")] = false := by decide

/-! ### Two restricted sets, apart at their elements

The test certifies two string sets whose members are disjoint, because the elements are
disjoint and no set is empty. -/

/-- **Two string sets with disjoint members are disjoint.** -/
theorem disjoint_disjointStringSets :
    Alg.Term.disjoint pair0 (.set (.refine .string (.members .string (NEFinset.of "a" {"b"})) ()) : Term)
      (.set (.refine .string (.members .string (NEFinset.of "c" ∅)) ()) : Term) = true := by
  decide

/-- **Two string sets that share a member are not disjoint.** -/
theorem not_disjoint_stringSets_shared :
    Alg.Term.disjoint pair0 (.set (.refine .string (.members .string (NEFinset.of "a" {"b"})) ()) : Term)
      (.set (.refine .string (.members .string (NEFinset.of "b" {"c"})) ()) : Term) = false := by
  decide

/-! ### The views certify a `held` whose caller side is precise

A string set held as a list of strings, beside a list of numbers. Both terms write a list, and
the test does not read a raw `held`, so the test of the two terms does not certify the pair. The
caller-side views are disjoint when the caller side requires one element or more, and the
stored-side views differ in kind. -/

/-- The test of the two terms does not certify the pair. -/
theorem disjoint_heldNE_base :
    Alg.Term.disjoint pair0 (.held false (.set .string) (.list [.string] (some .string) []) (.caller 0, false) [] : Term)
        (.list [] (some .number) [] : Term) = false := by
  decide

/-- **A caller side that requires one element or more is certified** beside a list of numbers. -/
theorem viewsDisjoint_heldNE :
    viewsDisjoint (.held false (.set .string) (.list [.string] (some .string) []) (.caller 0, false) [])
      (.list [] (some .number) []) = true := by
  decide

/-- **A caller side that admits the empty list is refused**, because the list of numbers admits
    the empty list too. -/
theorem viewsDisjoint_heldAny :
    viewsDisjoint (.held false (.set .string) (.list [] (some .string) []) (.caller 0, false) [])
      (.list [] (some .number) []) = false := by
  decide

/-- **A `held` below a recursion is certified where the views part.** The caller view of the
    recursive term is `mu (union [literal "1", list [] (some (var 0)) []])`, and the stored view
    is `mu (union [number, list [] (some (var 0)) []])`. Each is disjoint from
    `literal "A" ∪ literal "B"`. -/
theorem viewsDisjoint_heldBelowMu :
    viewsDisjoint (.union [.literal .string "A", .literal .string "B"])
      (.mu (.union [.held false .number (.literal .string "1") (.caller 0, false) [], .list [] (some (.var 0)) []]))
      = true := by
  decide

/-- …and the pair is refused where the caller views share a value: the text `"1"`. -/
theorem viewsDisjoint_heldBelowMu_meets :
    viewsDisjoint (.literal .string "1")
      (.mu (.union [.held false .number (.literal .string "1") (.caller 0, false) [], .list [] (some (.var 0)) []]))
      = false := by
  decide

/-- **The test does not read a raw `held`.** A `held` carries an adapter word, and the test reads
    no table, so the test keeps the `held` apart from the bottom alone. The views read it. -/
example : Alg.Term.disjoint pair0 (Term.held false .string .opaq (.caller 0, false) [])
    Term.number = false := by rfl

/-! ## The levers -/

/-! ## DynamoDB is an instance of the laws, on the write side

`Alg.disjoint_sound` proves the write side once, over any signature. DynamoDB supplies the law of
its set former (`dynFormerAdm`) and the laws of its leaves (`dynLeafAdm`). A primitive law is a
fact about `inBase` and `inL`, and the set law is a fact about `setCodec`. The disjointness of
two formers is a theorem of the shape classes (`dynShapes`). -/

/-- **`ofOptions` admits what its options admit**, and no certificate is spent. -/
theorem Adm_ofOptions (ts : List Term) (v : Value) :
    Adm α (Term.ofOptions ts) v = AdmAny α ts v := by
  match ts with
  | [] => rfl
  | [t] => simp only [Term.ofOptions, AdmAny_cons, AdmAny_nil, Bool.or_false]
  | _ :: _ :: _ => rfl

/-- **Two sets whose elements share no value share no set.** -/
theorem Adm_set_and_false {a y : Term} (h : ∀ u, (Adm α a u && Adm α y u) = false) (v : Value) :
    (Adm α (.set a) v && Adm α (.set y) v) = false :=
  Bool.eq_false_iff.mpr fun hv => by
    rw [Bool.and_eq_true] at hv
    refine setCodec_apart (o := .host) (fun w h1 h2 => ?_) v
      ((Adm_exact (.set a) v).mp hv.1) ((Adm_exact (.set y) v).mp hv.2)
    have := h w
    rw [(Adm_exact a w).mpr h1, (Adm_exact y w).mpr h2] at this
    exact Bool.noConfusion this

/-- **Two primitives apart share no value.** -/
theorem Adm_prim_apart : ∀ g g' : Ground, Ground.apart g g' = true →
    ∀ v, (Adm α (.prim g) v && Adm α (.prim g') v) = false :=
  admV_prim_apart

/-- The set former of DynamoDB: the set law of `setCodec`. -/
instance dynFormerAdm : Alg.FormerAdm dynSyn where
  set_never {_ β} _ _ h v := by
    obtain rfl : β = dynTableA := funext fun g => nomatch g
    exact Adm_set_and_false h v

/-- The leaves of DynamoDB keep apart the primitives that they say are apart, on the write side. -/
instance dynLeafAdm : Alg.LeafAdm dynSyn where
  prims_apart {_ β} g g' hp v := by
    obtain rfl : β = dynTableA := funext fun g => nomatch g
    exact Adm_prim_apart g g' hp v

/-! ## DynamoDB is an instance of the laws, on the read side

`Alg.disjoint_soundA` proves the read side once, over any signature. DynamoDB supplies the read
law of its set former (`dynFormerAdmA`) and of its primitives (`dynLeafAdmA`). Each primitive is
self-dual, so the read law of the primitives is their write law. -/

/-- **Two sets whose elements read no common attribute read no common set.** -/
theorem AdmA_set_and_false {a y : Term} (h : ∀ u, (AdmA α a u && AdmA α y u) = false) (att : Attr) :
    (AdmA α (.set a) att && AdmA α (.set y) att) = false :=
  Bool.eq_false_iff.mpr fun hv => by
    rw [Bool.and_eq_true] at hv
    refine setCodec_apart (o := .dual) (fun w h1 h2 => ?_) att
      ((AdmA_exact (.set a) att).mp hv.1) ((AdmA_exact (.set y) att).mp hv.2)
    have := h w
    rw [(AdmA_exact a w).mpr h1, (AdmA_exact y w).mpr h2] at this
    exact Bool.noConfusion this

/-- **Two primitives apart read nothing together.** Each primitive is self-dual, so its read-side
    row is its write-side row (`PrimAdm.dual`). -/
theorem admA_prim_apart : ∀ g g' : Ground, Ground.apart g g' = true →
    ∀ a, (AdmA α (.prim g) a && AdmA α (.prim g') a) = false :=
  Adm_prim_apart (α := α)

/-- The set former of DynamoDB, on the read side. -/
instance dynFormerAdmA : Alg.FormerAdmA dynSyn where
  set_never {β _} _ _ h c := by
    obtain rfl : β = dynTableA := funext fun g => nomatch g
    exact AdmA_set_and_false h c

/-- The primitives of DynamoDB keep apart the primitives that they say are apart, on the read
    side. -/
instance dynLeafAdmA : Alg.LeafAdmA dynSyn where
  prims_apart {β _} g g' hp c := by
    obtain rfl : β = dynTableA := funext fun g => nomatch g
    exact admA_prim_apart g g' hp c


/-! ## The orthogonal row -/

/-- **Orthogonal terms admit no common value.** A value that both terms admit is admitted by
    both caller views, and the views are disjoint. -/
theorem viewsDisjoint_adm {x y : Term} (h : viewsDisjoint x y = true) (v : Value) :
    (Adm α x v && Adm α y v) = false := by
  simp only [viewsDisjoint, Bool.and_eq_true] at h
  exact Alg.views_apart (S := dynSyn) α dynTableA h.1 [] [] v

/-- **Orthogonal terms read no common attribute.** An attribute that both terms read is read
    by both stored views, and the views are disjoint. -/
theorem viewsDisjoint_admA {x y : Term} (h : viewsDisjoint x y = true) (a : Attr) :
    (AdmA α x a && AdmA α y a) = false := by
  simp only [viewsDisjoint, Bool.and_eq_true] at h
  have : Alg.Shapes ⟨dynSig, Orient.dual⟩ := Alg.Shapes.op (S := dynSyn)
  exact Alg.views_apart (S := dynSyn.op) dynTableA α h.2 [] [] a

/-- **The pair certificate is sound**: orthogonality separates the pair. -/
theorem separates_of_viewsDisjoint {x y : Term} (h : viewsDisjoint x y = true) : Separates α x y := by
  refine ⟨fun v hx hy => ?_, fun a hx hy => ?_⟩
  · have := viewsDisjoint_adm (α := α) h v
    rw [hx, hy] at this; exact nomatch this
  · have := viewsDisjoint_admA (α := α) h a
    rw [hx, hy] at this; exact nomatch this

/-- **The certificate refuses a pair that only the model's caller carrier separates.** Each option
    is a set of adapters, and each caller side admits a boolean. The host builds `Set([true])` as
    a caller value of each option, and the two options write that value to `SS` and to `NS`. So
    the host refuses the union. The model's `Value` has no set of booleans, so in the model the
    two options write disjoint slots. The caller sides share `boolean`, so the caller views are
    not disjoint, and the certificate agrees with the host. -/
example :
    viewsDisjoint (.set (.refine (.held false .string (.union [.string, .boolean]) (.caller 0, false) [])
        (.closure fun _ => true) ()))
      (.set (.held false .number (.union [.number, .boolean]) (.caller 1, false) [])) = false := by
  decide

/-- **The certificate refuses a separated pair at a data predicate over a variable.** The pair is
    separated: `mu (refine (union [string, array (var 0)]) {a})` admits the string `"a"` and no
    other string, and `refine string {b}` admits the string `"b"` alone. The test compares two
    data predicates only over closed held-free inner terms, and this inner term holds a variable.
    So `viewsDisjoint` answers `false`. The host builds no data predicate over a variable, so no
    observable distinguishes this test from a finer test. A finer test becomes necessary only
    when the host builds such a term. -/
example :
    viewsDisjoint (.mu (.refine (.union [.string, .array (.var 0)]) (.members .string (NEFinset.of "a" ∅)) ()))
        (.refine .string (.members .string (NEFinset.of "b" ∅)) ()) = false := by
  decide

/-- **A certified union is separated**, which is the premise of `pairwiseCompat_of_separated`
    and of `admitsAtMostOne_of_separated`. -/
theorem separated_of_certAll {os : List Term} (h : certAll os = true) : Separated α os :=
  (pairwise_of_certAll h).imp separates_of_viewsDisjoint


end Calculus
