import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorCompleteness
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDAffineRestrictionIteration

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Residual geometry for reverse-LCP buckets

Meel--de Colnet derivation paths are written from the accepting sink back to
the current root.  Their common prefix is therefore a common accepting suffix
in the forward orientation of `FiniteUnambiguousFBDD.Walk`.

This file records the graph-theoretic completeness bridge needed by that
orientation.  If one start-to-accept walk is complete and is split at a
vertex, then syntactic read-once forces its suffix to query exactly
`postVars` at that vertex.  The result survives every affine padded prefix of
the mandatory canonical selector.

The bare `Walk` type does not retain edge identities.  In particular, when a
query has equal false and true successors, two inputs can induce the same
bare walk while taking differently labelled edges.  The input-labelled query
trace below supplies the value-agreement consequence needed by a residual
rectangle, but it is not yet a full edge-labelled canonical derivation trace:
an exact reverse-LCP partition must additionally retain silent-choice edge
indices.
-/

noncomputable section

namespace FiniteUnambiguousFBDD

namespace Walk

/-- A complete start-to-accept walk has, after any cut, exactly the variables
in `postVars` on its accepting suffix.  Completeness is required only for the
displayed concatenated walk.  Alternative suffixes are controlled by
syntactic read-once and the definition of `postVars`. -/
theorem queryVars_eq_postVars_of_append_queryVars_eq_univ
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    {vertex : B.Vertex}
    (prefixWalk : B.Walk B.start vertex)
    (suffixWalk : B.Walk vertex B.accept)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hcomplete : (prefixWalk.append suffixWalk).queryVars = Finset.univ) :
    suffixWalk.queryVars = B.postVars vertex := by
  apply Finset.Subset.antisymm
  · exact suffixWalk.queryVars_subset_postVars
  · intro queryIndex hpost
    by_contra hsuffix
    have hfull :
        queryIndex ∈ (prefixWalk.append suffixWalk).queryVars := by
      rw [hcomplete]
      exact Finset.mem_univ queryIndex
    have hprefixOrSuffix :
        queryIndex ∈ prefixWalk.queryVars ∨
          queryIndex ∈ suffixWalk.queryVars := by
      simpa only [queryVars_append, Finset.mem_union] using hfull
    have hprefix : queryIndex ∈ prefixWalk.queryVars :=
      hprefixOrSuffix.resolve_right hsuffix
    have hpre : queryIndex ∈ B.preVars vertex :=
      prefixWalk.queryVars_subset_preVars hprefix
    exact (Finset.disjoint_left.mp
      (B.preVars_disjoint_postVars hreadOnce vertex)) hpre hpost

end Walk

/-- A query event together with the input bit selecting its query edge.
The vertex field prevents two occurrences of the same queried coordinate from
being confused when this trace is later embedded in a labelled path. -/
structure InputLabelledQueryEvent {n : Nat}
    (B : FiniteUnambiguousFBDD n) where
  vertex : B.Vertex
  queryIndex : Fin n
  value : Bool

namespace Walk

/-- The query events of a walk labelled by the bits of a particular input.
This distinguishes the two query edges even when they have the same target.
Silent choice edges are deliberately not represented here. -/
def inputLabelledQueryTrace {n : Nat} {B : FiniteUnambiguousFBDD n}
    {source target : B.Vertex} (walk : B.Walk source target)
    (input : Fin n -> Bool) : List (InputLabelledQueryEvent B) :=
  walk.queryEvents.map fun event => {
    vertex := event.1
    queryIndex := event.2
    value := input event.2
  }

/-- Equality of input-labelled query traces for one bare walk forces the two
inputs to agree on every variable queried by that walk. -/
theorem eq_on_queryVars_of_inputLabelledQueryTrace_eq
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {source target : B.Vertex} (walk : B.Walk source target)
    (left right : Fin n -> Bool)
    (htrace : walk.inputLabelledQueryTrace left =
      walk.inputLabelledQueryTrace right) :
    ∀ queryIndex, queryIndex ∈ walk.queryVars ->
      left queryIndex = right queryIndex := by
  intro queryIndex hquery
  have hqueryTrace : queryIndex ∈ walk.queryEvents.map Prod.snd := by
    simpa [queryVars, queryTrace] using hquery
  rcases List.mem_map.mp hqueryTrace with
    ⟨event, hevent, heventIndex⟩
  have hleft :
      ({
        vertex := event.1
        queryIndex := event.2
        value := left event.2
      } : InputLabelledQueryEvent B) ∈
        walk.inputLabelledQueryTrace left := by
    apply List.mem_map.mpr
    exact ⟨event, hevent, rfl⟩
  rw [htrace] at hleft
  rcases List.mem_map.mp hleft with ⟨other, _hother, heq⟩
  have hindex : other.2 = event.2 :=
    congrArg InputLabelledQueryEvent.queryIndex heq
  have hvalue : right other.2 = left event.2 :=
    congrArg InputLabelledQueryEvent.value heq
  simpa [heventIndex, hindex] using hvalue.symm

/-- The two independent ingredients of the Meel--de Colnet splice premise:
complete read-once geometry upgrades a fixed suffix to all `postVars`, and an
input-labelled common suffix upgrades trace equality to value agreement.

This theorem does not claim that a common bare `Walk` supplies `htrace`.
That implication is false at a query whose two successors coincide. -/
theorem eq_on_postVars_of_inputLabelledQueryTrace_eq
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    {vertex : B.Vertex}
    (prefixWalk : B.Walk B.start vertex)
    (suffixWalk : B.Walk vertex B.accept)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hcomplete : (prefixWalk.append suffixWalk).queryVars = Finset.univ)
    (left right : Fin n -> Bool)
    (htrace : suffixWalk.inputLabelledQueryTrace left =
      suffixWalk.inputLabelledQueryTrace right) :
    ∀ queryIndex, queryIndex ∈ B.postVars vertex ->
      left queryIndex = right queryIndex := by
  have hsuffix : suffixWalk.queryVars = B.postVars vertex :=
    FiniteUnambiguousFBDD.Walk.queryVars_eq_postVars_of_append_queryVars_eq_univ
      B prefixWalk suffixWalk hreadOnce hcomplete
  intro queryIndex hpost
  apply suffixWalk.eq_on_queryVars_of_inputLabelledQueryTrace_eq
    left right htrace queryIndex
  rw [hsuffix]
  exact hpost

end Walk

/-- A formal full-walk premise transfers to one affine padded restriction.
Unlike the existing accepting-path theorem, this statement needs no input or
compatibility witness. -/
theorem affinePaddedRestrictBy_walk_queryVars_eq_univ
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (base mask : Fin n -> Bool)
    (hreadsAll : ∀ walk : B.Walk B.start B.accept,
      walk.queryVars = Finset.univ)
    (walk : (B.affinePaddedRestrictBy base mask).Walk
      (B.affinePaddedRestrictBy base mask).start
      (B.affinePaddedRestrictBy base mask).accept) :
    walk.queryVars = Finset.univ := by
  rw [← AffinePaddedRestrictionWalk.toOriginal_queryVars
    (B := B) (base := base) (mask := mask) walk]
  exact hreadsAll
    (AffinePaddedRestrictionWalk.toOriginal
      (B := B) (base := base) (mask := mask) walk)

/-- A formal full-walk premise survives an arbitrary list of affine padded
restriction rounds. -/
theorem affinePaddedRestrictByRounds_walk_queryVars_eq_univ
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (rounds : List (AffineRestrictionRound n))
    (hreadsAll : ∀ walk : B.Walk B.start B.accept,
      walk.queryVars = Finset.univ) :
    ∀ walk : (B.affinePaddedRestrictByRounds rounds).Walk
        (B.affinePaddedRestrictByRounds rounds).start
        (B.affinePaddedRestrictByRounds rounds).accept,
      walk.queryVars = Finset.univ := by
  induction rounds generalizing B with
  | nil => exact hreadsAll
  | cons round rounds ih =>
      exact ih (B := B.affinePaddedRestrictBy round.base round.mask)
        (B.affinePaddedRestrictBy_walk_queryVars_eq_univ
          round.base round.mask hreadsAll)

end FiniteUnambiguousFBDD

namespace FiniteLayeredQueryProgramFamily

/-- Formal-walk strengthening of
`selectorAcceptingPath_queryVars_eq_univ_of_fixedMandatoryOrder`.
Compatibility is unnecessary because the exact selector trace decoder already
quantifies over every root-to-accept walk. -/
theorem selectorWalk_queryVars_eq_univ_of_fixedMandatoryOrder
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (order : (index : family.Index) -> Fin (family.layers index) -> Fin n)
    (hfixed : ∀ index,
      (family.program index).HasFixedQueryOrder
        (fun layer => some (order index layer)))
    (hlayers : ∀ index, family.layers index = n)
    (hnodup : ∀ index, (List.ofFn (order index)).Nodup)
    (walk : (family.selectorFBDD).Walk
      (family.selectorFBDD).start (family.selectorFBDD).accept) :
    walk.queryVars = Finset.univ := by
  obtain ⟨index, htrace⟩ :=
    selectorRootWalk_to_accept_exists_queryTrace_eq_of_fixedMandatoryOrder
      family order hfixed walk
  unfold FiniteUnambiguousFBDD.Walk.queryVars
  rw [htrace]
  apply Finset.eq_univ_of_card
  rw [List.toFinset_card_of_nodup (hnodup index)]
  simp [hlayers index]

end FiniteLayeredQueryProgramFamily

/-- Every formal root-to-accept walk of the mandatory canonical selector
queries every input coordinate. -/
theorem mandatoryCanonicalUFBDD_walk_queryVars_eq_univ
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat)
    (walk : (mandatoryCanonicalUFBDD machine n T b).Walk
      (mandatoryCanonicalUFBDD machine n T b).start
      (mandatoryCanonicalUFBDD machine n T b).accept) :
    walk.queryVars = Finset.univ := by
  let family := mandatoryFiniteRejectingGuardedCanonicalFamily machine n T b
  let order : (index : family.Index) ->
      Fin (family.layers index) -> Fin n := fun index =>
    mandatoryBuiltRejectingGuardedCanonicalQueryOrder machine n index
  apply FiniteLayeredQueryProgramFamily.selectorWalk_queryVars_eq_univ_of_fixedMandatoryOrder
      family order
  · intro index
    exact mandatoryBuiltRejectingGuardedCanonicalComponent_hasFixedQueryOrder
      machine n index
  · intro index
    rfl
  · intro index
    exact mandatoryBuiltRejectingGuardedCanonicalQueryOrder_nodup
      machine n index

/-- Formal full-walk completeness of the mandatory selector is preserved by
every affine prefix used by the multi-round hybrid. -/
theorem mandatoryCanonicalUFBDD_affinePaddedRestrictByRounds_walk_queryVars_eq_univ
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (rounds : List (AffineRestrictionRound n))
    (walk : ((mandatoryCanonicalUFBDD machine n T b)
      |>.affinePaddedRestrictByRounds rounds).Walk
        ((mandatoryCanonicalUFBDD machine n T b)
          |>.affinePaddedRestrictByRounds rounds).start
        ((mandatoryCanonicalUFBDD machine n T b)
          |>.affinePaddedRestrictByRounds rounds).accept) :
    walk.queryVars = Finset.univ := by
  exact (mandatoryCanonicalUFBDD machine n T b)
    |>.affinePaddedRestrictByRounds_walk_queryVars_eq_univ rounds
      (mandatoryCanonicalUFBDD_walk_queryVars_eq_univ machine n T b) walk

/-- The exact local-completeness bridge for the affine-prefixed mandatory
selector (the program abbreviated elsewhere as
`prefixedMandatoryCanonicalSelector`, after replacing `n` by `2 ^ n`). -/
theorem mandatoryCanonicalUFBDD_affinePaddedRestrictByRounds_suffix_queryVars_eq_postVars
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (rounds : List (AffineRestrictionRound n))
    {vertex : ((mandatoryCanonicalUFBDD machine n T b)
      |>.affinePaddedRestrictByRounds rounds).Vertex}
    (prefixWalk : ((mandatoryCanonicalUFBDD machine n T b)
      |>.affinePaddedRestrictByRounds rounds).Walk
        ((mandatoryCanonicalUFBDD machine n T b)
          |>.affinePaddedRestrictByRounds rounds).start vertex)
    (suffixWalk : ((mandatoryCanonicalUFBDD machine n T b)
      |>.affinePaddedRestrictByRounds rounds).Walk vertex
        ((mandatoryCanonicalUFBDD machine n T b)
          |>.affinePaddedRestrictByRounds rounds).accept) :
    suffixWalk.queryVars =
      ((mandatoryCanonicalUFBDD machine n T b)
        |>.affinePaddedRestrictByRounds rounds).postVars vertex := by
  apply FiniteUnambiguousFBDD.Walk.queryVars_eq_postVars_of_append_queryVars_eq_univ
    ((mandatoryCanonicalUFBDD machine n T b)
      |>.affinePaddedRestrictByRounds rounds)
    prefixWalk suffixWalk
    ((mandatoryCanonicalUFBDD machine n T b)
      |>.affinePaddedRestrictByRounds_isSyntacticallyReadOnce rounds
        (mandatoryCanonicalUFBDD_isSyntacticallyReadOnce machine n T b))
  exact mandatoryCanonicalUFBDD_affinePaddedRestrictByRounds_walk_queryVars_eq_univ
    machine n T b rounds (prefixWalk.append suffixWalk)

/-- `2 ^ n` specialization in the exact definitional shape of
`MandatoryCanonicalSelectorPairCorrelation.prefixedMandatoryCanonicalSelector`.
It is kept independent of that analytic module so the latter can import this
geometry without creating an import cycle. -/
theorem prefixedMandatoryCanonicalSelector_suffix_queryVars_eq_postVars
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (rounds : List (AffineRestrictionRound (2 ^ n)))
    {vertex : ((mandatoryCanonicalUFBDD machine (2 ^ n) T b)
      |>.affinePaddedRestrictByRounds rounds).Vertex}
    (prefixWalk : ((mandatoryCanonicalUFBDD machine (2 ^ n) T b)
      |>.affinePaddedRestrictByRounds rounds).Walk
        ((mandatoryCanonicalUFBDD machine (2 ^ n) T b)
          |>.affinePaddedRestrictByRounds rounds).start vertex)
    (suffixWalk : ((mandatoryCanonicalUFBDD machine (2 ^ n) T b)
      |>.affinePaddedRestrictByRounds rounds).Walk vertex
        ((mandatoryCanonicalUFBDD machine (2 ^ n) T b)
          |>.affinePaddedRestrictByRounds rounds).accept) :
    suffixWalk.queryVars =
      ((mandatoryCanonicalUFBDD machine (2 ^ n) T b)
        |>.affinePaddedRestrictByRounds rounds).postVars vertex := by
  exact
    mandatoryCanonicalUFBDD_affinePaddedRestrictByRounds_suffix_queryVars_eq_postVars
      machine (2 ^ n) T b rounds prefixWalk suffixWalk

end

end OneTapeMagnification
end Frontier
end Pnp4
