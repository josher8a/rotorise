import Calculus.Dynamo.Lang.ScopeSound

/-!
# Orthogonality of closed codecs: separation

A union of closed codecs owes pairwise compatibility of its meanings (`Closed.PairwiseCompat`).
Two separated options are compatible (`Closed.pairwiseCompat_of_separated`), and pairwise
separation bounds the options that admit one input at one (`Closed.admitsAtMostOne_of_separated`).

`Closed.Separates` reads the write domain and the read row of each meaning. The meaning holds the
two domains, so the separation needs no second description of a term.
-/

namespace Calculus

variable {α : Table}

/-- Two members that both meet `P`, in a list where no related pair both meets `P`, are one. -/
theorem eq_of_pairwise_excl {α : Type} {P : α → Prop} {R : α → α → Prop}
    (hR : ∀ x y, R x y → P x → P y → False) :
    ∀ {l : List α}, l.Pairwise R → ∀ x ∈ l, ∀ y ∈ l, P x → P y → x = y
  | [], _, _, hx, _, _, _, _ => nomatch hx
  | h :: tl, hp, x, hx, y, hy, px, py => by
    have hp' := List.pairwise_cons.mp hp
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact (hR _ _ (hp'.1 y hy') px py).elim
    · exact (hR _ _ (hp'.1 x hx') py px).elim
    · exact eq_of_pairwise_excl hR hp'.2 x hx' y hy' px py

/-- Each codec is compatible with itself. -/
theorem compat_self (c : Codec) : Compat c c := fun _ _ hp _ => hp

variable (α) in
/-- **The obligation of a union of closed codecs**: each meaning is compatible with each other
    meaning. -/
def Closed.PairwiseCompat (opts : List Closed) : Prop :=
  ∀ s ∈ opts, ∀ t ∈ opts, Compat (s.meaning α) (t.meaning α)

variable (α) in
/-- **What the discharger consumes**: no value is in the write domain of both meanings, and no
    attribute is in the read row of both. -/
def Closed.Separates (x y : Closed) : Prop :=
  (∀ v, ((x.meaning α).e v).isSome = true → ¬ ((y.meaning α).e v).isSome = true) ∧
    (∀ a, x.AdmA α a = true → ¬ y.AdmA α a = true)

variable (α) in
/-- **The whole premise the discharger takes**: every pair of options separated. -/
def Closed.Separated (opts : List Closed) : Prop := List.Pairwise (Closed.Separates α) opts

/-- **Pairwise separation bounds the admitters at one**, over the meanings of closed codecs. -/
theorem Closed.admitsAtMostOne_of_separated {opts : List Closed} (h : Closed.Separated α opts) :
    AdmitsAtMostOne (opts.map (Closed.meaning α)) := by
  constructor
  · intro v
    rw [List.filter_map, List.length_map]
    refine length_le_one_of_pairwise_false (List.Pairwise.imp_of_mem ?_
      (List.Pairwise.filter _ (h.imp fun hs => hs.1 v)))
    intro x y hx hy hxy
    exact hxy (List.mem_filter.mp hx).2 (List.mem_filter.mp hy).2
  · intro a
    rw [List.filter_map, List.length_map]
    refine length_le_one_of_pairwise_false (List.Pairwise.imp_of_mem ?_
      (List.Pairwise.filter _ (h.imp fun hs => hs.2 a)))
    intro x y hx hy hxy
    exact hxy (List.mem_filter.mp hx).2 (List.mem_filter.mp hy).2

/-- **Pairwise separation gives the obligation of a union** of lawful closed codecs. -/
theorem Closed.pairwiseCompat_of_separated {opts : List Closed}
    (hlaw : ∀ t ∈ opts, Lawful (t.meaning α)) (h : Closed.Separated α opts) :
    Closed.PairwiseCompat α opts := by
  intro s hs t ht a v hp hact
  have hsA : s.AdmA α a = true := by rw [Closed.AdmA_eq_isSome, hp]; rfl
  have hsV : ((s.meaning α).e v).isSome = true := (hlaw s hs).defined hp
  have hst : t = s := by
    rcases hact with hq | he
    · exact eq_of_pairwise_excl (P := fun u => u.AdmA α a = true)
        (fun x y hxy px py => hxy.2 a px py) h t ht s hs hq hsA
    · exact eq_of_pairwise_excl (P := fun u => ((u.meaning α).e v).isSome = true)
        (fun x y hxy px py => hxy.1 v px py) h t ht s hs he hsV
  subst hst; exact hp

/-- **The empty closed codec moves nothing**, at either orientation. -/
theorem Closed.never_f (o : Alg.Orient) (v : Value) :
    ((Closed.one .never).meaning α).f o v = none :=
  Closed.one_fix α .never o v

/-- **An empty option is compatible with every option**: the empty closed codec reads nothing. -/
theorem Closed.compat_never_left (c : Codec) : Compat ((Closed.one .never).meaning α) c :=
  fun a _ hp _ => nomatch (Closed.never_f .dual a).symm.trans hp

/-- …and on the other side: the empty closed codec reads and writes nothing. -/
theorem Closed.compat_never_right (c : Codec) : Compat c ((Closed.one .never).meaning α) :=
  fun a t _ hact => (hact.elim
    (fun h => Bool.false_ne_true ((congrArg Option.isSome (Closed.never_f .dual a)).symm.trans h))
    (fun h => Bool.false_ne_true ((congrArg Option.isSome (Closed.never_f .host t)).symm.trans h))).elim

/-- **A union with an empty option meets its obligation**, whatever the other option is. -/
theorem Closed.pairwiseCompat_never_right (x : Closed) :
    Closed.PairwiseCompat α [x, Closed.one .never] := by
  intro s hs t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ht
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    first | exact compat_self _ | exact Closed.compat_never_left _ | exact Closed.compat_never_right _

/-- …and with the empty option first. -/
theorem Closed.pairwiseCompat_never_left (x : Closed) :
    Closed.PairwiseCompat α [Closed.one .never, x] := by
  intro s hs t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ht
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    first | exact compat_self _ | exact Closed.compat_never_left _ | exact Closed.compat_never_right _

end Calculus
