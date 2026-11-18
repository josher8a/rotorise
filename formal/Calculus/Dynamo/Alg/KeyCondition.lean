import Calculus.Dynamo.Alg.DerivedKey

/-!
# The condition on a sort key

A query selects the items of one partition by a condition on the sort key. The attributes of the
query give some parts of the sort key, and the condition is the key that those parts print. A
condition with every part is an equality on the whole key. A condition with the leading parts is a
prefix match: the key of those parts and the boundary. A prefix is exact only where no part prints
after a part that does not, because the prefix stops at the first absent part and so drops each
later part (`gap_selects_both`). A query with a gap would then select items that disagree on a part
that the query names, so `build` refuses it (`build_gap_refused`), and the condition reads `build`.
A query that gives no part is the position of no component, closed (`condition_no_part`).

This file states the condition as a function of the length of the spec and the parts, as `build`
does for the key. The condition reads `build`: the key builder gives a partial key, and refuses the
query where a later part would be dropped and the selection would widen.
-/

namespace Calculus

namespace DerivedKey

/-! ## The condition -/

/-- What the condition of a sort key is: no condition, a refusal, the whole key, or the prefix of
    the leading parts with the boundary. -/
inductive Cond where
  | nothing
  | refused
  | equals (ss : List String)
  | prefix (ss : List String)
  deriving DecidableEq

/-- **The condition.** The key is the key that `build` gives for the parts: the whole key where the
    print holds every component of the spec, and the prefix with the next tag and the boundary
    where it does not. A query that gives no part is the position of no component, closed: the
    prefix of the first tag and the boundary. Where the first component states no tag, `build`
    gives no key, and a query that gives no part has no condition. A part that prints after an
    absent part is a refusal of `build` (`build_gap_refused`), so the condition has no gap test of
    its own. A whole key whose text is empty is a refusal, as `build` states it. `full` is the
    length of the spec, and `tags` are the tags of its components. -/
def condition (full : Nat) (tags : List (Option String)) (parts : List (Option Comp)) : Cond :=
  match printed true parts, build full true true tags parts with
  | some cs, some ss => if boundary full cs then .prefix ss else .equals ss
  | _, _ => if parts.all Option.isNone then .nothing else .refused

/-- **A query that gives no part, and a first component with no tag, has no condition.** Nothing
    prints, so `build` gives no key. -/
theorem condition_nothing {full : Nat} {tags : List (Option String)} {parts : List (Option Comp)}
    (hp : parts.all Option.isNone = true) (hb : build full true true tags parts = none) :
    condition full tags parts = .nothing := by
  unfold condition
  cases printed true parts <;> simp [hb, hp]

/-- **A query that gives no part has the prefix of the first tag.** The position is no component,
    closed: the tag of the first component and the boundary. -/
theorem condition_no_part {full : Nat} {tags : List (Option String)} {parts : List (Option Comp)}
    {t : String} (hg : gapFree parts = true) (hc : printed true parts = some [])
    (hlt : 0 < full) (ht : nextTag tags 0 = some t) :
    condition full tags parts = .prefix [t, ""] := by
  have hb := build_closed_ends_with_tag (allowPartial := true) (cs := []) (by simp [hg]) hc
    (by simpa using hlt) (by simpa using ht)
  simp [condition, hc, hb, boundary, hlt]

/-- **A query with a gap is a refusal.** A part is given, and a part prints after an absent part. -/
theorem condition_gap {full : Nat} {tags : List (Option String)} {parts : List (Option Comp)}
    (hp : parts.all Option.isNone = false) (hg : gapFree parts = false) :
    condition full tags parts = .refused := by
  unfold condition
  cases printed true parts <;> simp [hp, build_gap_refused hg]

/-- **A query has the key that `build` gives.** The condition is that key, as the whole key where
    the print holds every component and as the prefix where it does not. -/
theorem condition_of_build {full : Nat} {tags : List (Option String)} {parts : List (Option Comp)}
    {cs : List Comp} {ss : List String} (hc : printed true parts = some cs)
    (hb : build full true true tags parts = some ss) :
    condition full tags parts = if boundary full cs then .prefix ss else .equals ss := by
  simp [condition, hc, hb]

/-- **A query that gives a part, and whose build is a refusal, is a refusal.** -/
theorem condition_refused_of_build {full : Nat} {tags : List (Option String)}
    {parts : List (Option Comp)} (hp : parts.all Option.isNone = false)
    (hb : build full true true tags parts = none) : condition full tags parts = .refused := by
  unfold condition
  cases printed true parts <;> simp [hb, hp]

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
