import Calculus.Dynamo.Alg.DerivedKey

/-!
# The condition on a sort key

A query selects the items of one partition by a condition on the sort key. The attributes of the
query give some parts of the sort key, and the condition is the key that those parts print. A
condition with every part is an equality on the whole key. A condition with the leading parts is a
prefix match: the key of those parts and the boundary. A prefix is exact only where no part prints
after a part that does not, because the prefix stops at the first absent part and so drops each
later part (`gap_selects_both`). A query with a gap would then select items that disagree on a part
that the query names, so the condition refuses it.

This file states the condition as a function of the length of the spec and the parts, as `build`
does for the key. The condition is a layer above the key: the key builder gives a partial key and
drops a later part in silence (`printed_partial`), and the condition refuses the query where that
drop would widen the selection.
-/

namespace Calculus

namespace DerivedKey

/-! ## The gap -/

/-- The parts before the first absent part. -/
def leading (ps : List (Option Comp)) : List Comp := (ps.takeWhile Option.isSome).filterMap id

/-- **No part prints after an absent part.** The list ends with absent parts, or has none. -/
def gapFree : List (Option Comp) → Bool
  | [] => true
  | none :: r => r.all Option.isNone
  | some _ :: r => gapFree r

/-- **A list has no gap exactly where the parts after the leading parts are all absent.** -/
theorem gapFree_iff_dropWhile : ∀ ps : List (Option Comp),
    gapFree ps = true ↔ (ps.dropWhile Option.isSome).all Option.isNone = true
  | [] => by simp [gapFree]
  | none :: r => by simp [gapFree, List.dropWhile]
  | some _ :: r => by simp [gapFree, List.dropWhile, gapFree_iff_dropWhile r]

/-- **A print that stops at an absent part is the leading parts.** The strict and the partial
    builders agree on a list with no absent part. -/
theorem leading_printed (ps : List (Option Comp)) : printed true ps = some (leading ps) :=
  printed_partial ps

/-! ## The condition -/

/-- What the condition of a sort key is: no condition where no part is given, a refusal, the whole
    key, or the prefix of the leading parts with the boundary. -/
inductive Cond where
  | nothing
  | refused
  | equals (ss : List String)
  | prefix (ss : List String)
  deriving DecidableEq

/-- **The condition.** No part given gives no condition. A part that prints after an absent part is
    a refusal. Otherwise the leading parts give the whole key where they are every component of
    the spec, and the prefix with the boundary where they are not. `full` is the length of the
    spec. -/
def condition (full : Nat) (parts : List (Option Comp)) : Cond :=
  if parts.all Option.isNone then .nothing
  else if gapFree parts then
    if boundary full (leading parts) then .prefix ((leading parts).flatMap Comp.segs ++ [""])
    else .equals ((leading parts).flatMap Comp.segs)
  else .refused

/-- **A query that gives no part has no condition.** -/
theorem condition_nothing {full : Nat} {parts : List (Option Comp)}
    (h : parts.all Option.isNone = true) : condition full parts = .nothing := by
  simp [condition, h]

/-- **A query with a gap is a refusal.** A part is given, and a part prints after an absent part. -/
theorem condition_gap {full : Nat} {parts : List (Option Comp)}
    (hp : parts.all Option.isNone = false) (hg : gapFree parts = false) :
    condition full parts = .refused := by
  simp [condition, hp, hg]

/-- **A query with no gap has the key of its leading parts.** The condition is the key that
    `build` gives for the parts, as the whole key or as the prefix. -/
theorem condition_of_gapFree {full : Nat} {parts : List (Option Comp)}
    (hp : parts.all Option.isNone = false) (hg : gapFree parts = true) :
    ∃ ss, build full true true parts = some ss ∧
      (condition full parts = .prefix ss ∨ condition full parts = .equals ss) := by
  refine ⟨(leading parts).flatMap Comp.segs ++ (if boundary full (leading parts) then [""] else []),
    ?_, ?_⟩
  · simp only [build, leading_printed, Option.map_some]
    split <;> simp_all
  · by_cases hb : boundary full (leading parts) = true
    · left; simp [condition, hp, hg, hb]
    · right
      have hb' : boundary full (leading parts) = false := by simpa using hb
      simp [condition, hp, hg, hb']

/-- **A gap leaves the later part free.** The prefix of the leading segments `p` has a prefix match
    with the segments of each item that begins with `p`, whatever follows. So two items that
    differ after `p`, one that holds the later part that the query names and one that does not,
    both match the prefix, and the prefix does not select by the later part. -/
theorem gap_selects_both (c : Char) {p r r' : List (List Char)} (hp : p ≠ []) (hpn : NoSep c p)
    (hr : r ≠ []) (hr' : r' ≠ []) (hrn : NoSep c r) (hrn' : NoSep c r') :
    ((join c p ++ [c]) <+: join c (p ++ r) ∧ (join c p ++ [c]) <+: join c (p ++ r')) := by
  have hn : ∀ x : List (List Char), x ≠ [] → NoSep c x → NoSep c (p ++ x) := by
    intro x _ hx s hs
    rcases List.mem_append.mp hs with h | h
    · exact hpn s h
    · exact hx s h
  exact ⟨(prefix_iff c p (p ++ r) hp hpn (hn r hr hrn)).mpr ⟨r, hr, rfl⟩,
    (prefix_iff c p (p ++ r') hp hpn (hn r' hr' hrn')).mpr ⟨r', hr', rfl⟩⟩

end DerivedKey

end Calculus
