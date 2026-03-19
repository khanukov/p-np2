import LowerBounds.SingletonDensityEndpoint
import LowerBounds.MCSPGapLocality
import Counting.ShannonCounting

/-!
  pnp3/LowerBounds/SingletonDensityContradiction.lean

  Formula-free contradiction staging layer for singleton density data.

  The previous module `SingletonDensityEndpoint` packages the active internal
  formula route. This file factors out the part that is genuinely independent
  of formula-specific source constructors:

  * one bounded atlas scenario `sc`,
  * one distinguished function `f ∈ sc.family`,
  * one bounded witness `S`,
  * one density/error bound `errU f S ≤ sc.atlas.epsilon`,
  * one numerical estimate `sc.atlas.epsilon ≤ 1 / (n + 2)`.

  The purpose of this module is to make the next positive frontier explicit in
  a DAG-robust form. The raw scenario-level payload is intentionally weak
  enough to be consistent on trivial examples, so any future contradiction
  theorem must consume a stronger formula-free target. The intermediate
  `AbstractLinkedSingletonDensityPayload` remains available as a compatibility
  wrapper, but it is too weak by itself because its target can be chosen to be
  the distinguished function itself. Even an externally targeted payload is
  still too weak when the target is arbitrary; the first semantically fixed
  frontier is therefore the gap-slice-targeted payload introduced below.
  The current consumer-side strengthening after the empty-witness no-go is a
  non-empty witness payload over that same fixed target. Even there, the
  strongest purely witness-level consequence is only existence of a covered
  point. The next semantic strengthening records one-sided YES-soundness of
  witness cubes; even that only yields existence of a YES-point / YES-input,
  so any future contradiction will have to use target semantics more deeply
  than witness admissibility and pointwise YES-soundness alone.
-/

namespace Pnp3
namespace LowerBounds

open Models
open ComplexityInterfaces

/--
Formula-free singleton density payload over an arbitrary bounded atlas
scenario.
-/
structure AbstractSingletonDensityPayload (n : Nat) where
  sc : BoundedAtlasScenario n
  f : Core.BitVec n → Bool
  hf : f ∈ sc.family
  S : List (Core.Subcube n)
  hlen : S.length ≤ sc.k
  hsub : Core.listSubset S sc.atlas.dict
  herr : Core.errU f S ≤ sc.atlas.epsilon
  hEpsLeInv : sc.atlas.epsilon ≤ (1 : Core.Q) / (n + 2)

/--
The raw abstract singleton-density payload is consistent: the empty dictionary
with the constant-zero function satisfies all fields.
-/
theorem nonempty_abstractSingletonDensityPayload_false
    (n : Nat) :
    Nonempty (AbstractSingletonDensityPayload n) := by
  classical
  let f : Core.BitVec n → Bool := fun _ => false
  let A : Core.Atlas n := { dict := [], epsilon := 0 }
  let sc : BoundedAtlasScenario n := {
    atlas := A
    family := [f]
    k := 0
    hε0 := by norm_num
    hε1 := by norm_num
    works := by
      intro g hg
      have hgEq : g = f := by
        simpa [f] using hg
      subst hgEq
      refine ⟨[], Core.listSubset_nil _, ?_⟩
      simpa [A, f] using (Core.errU_false_nil (n := n))
    bounded := by
      intro g hg
      have hgEq : g = f := by
        simpa [f] using hg
      subst hgEq
      refine ⟨[], by simp, Core.listSubset_nil _, ?_⟩
      simpa [A, f] using (Core.errU_false_nil (n := n))
  }
  have hInv :
      sc.atlas.epsilon ≤ (1 : Core.Q) / (n + 2) := by
    have hNonneg : (0 : Core.Q) ≤ (1 : Core.Q) / (n + 2) := by
      positivity
    simpa [sc, A] using hNonneg
  exact ⟨{
    sc := sc
    f := f
    hf := by simp [sc, f]
    S := []
    hlen := by simp [sc]
    hsub := Core.listSubset_nil _
    herr := by simpa [sc, A, f] using (Core.errU_false_nil (n := n))
    hEpsLeInv := hInv
  }⟩

/--
Compatibility wrapper around the abstract singleton-density payload with an
explicit target field. This is not yet a meaningful positive frontier, because
`target` can always be chosen to be `base.f`.
-/
structure AbstractLinkedSingletonDensityPayload (n : Nat) where
  base : AbstractSingletonDensityPayload n
  target : Core.BitVec n → Bool
  hLink : base.f = target

/--
The compatibility wrapper is vacuous: any abstract singleton-density payload
trivially yields a linked payload by choosing `target := f`.
-/
def abstractLinkedSingletonDensityPayload_of_abstract
    {n : Nat}
    (pkg : AbstractSingletonDensityPayload n) :
    AbstractLinkedSingletonDensityPayload n where
  base := pkg
  target := pkg.f
  hLink := rfl

/--
Consequently, the current linked wrapper is itself consistent on a trivial
scenario.
-/
theorem nonempty_abstractLinkedSingletonDensityPayload_false
    (n : Nat) :
    Nonempty (AbstractLinkedSingletonDensityPayload n) := by
  rcases nonempty_abstractSingletonDensityPayload_false n with ⟨pkg⟩
  exact ⟨abstractLinkedSingletonDensityPayload_of_abstract pkg⟩

/--
Externally targeted abstract singleton-density payload. Unlike the compatibility
wrapper above, this object is parameterized by a fixed target supplied from
outside the payload itself.
-/
structure AbstractTargetedSingletonDensityPayload
    (n : Nat)
    (target : Core.BitVec n → Bool) where
  base : AbstractSingletonDensityPayload n
  hLink : base.f = target

/--
Even the externally targeted payload is consistent for trivial targets such as
the constant-zero function.
-/
theorem nonempty_abstractTargetedSingletonDensityPayload_false
    (n : Nat) :
    Nonempty (AbstractTargetedSingletonDensityPayload n (fun _ => false)) := by
  classical
  let f : Core.BitVec n → Bool := fun _ => false
  let A : Core.Atlas n := { dict := [], epsilon := 0 }
  let sc : BoundedAtlasScenario n := {
    atlas := A
    family := [f]
    k := 0
    hε0 := by norm_num
    hε1 := by norm_num
    works := by
      intro g hg
      have hgEq : g = f := by
        simpa [f] using hg
      subst hgEq
      refine ⟨[], Core.listSubset_nil _, ?_⟩
      simpa [A, f] using (Core.errU_false_nil (n := n))
    bounded := by
      intro g hg
      have hgEq : g = f := by
        simpa [f] using hg
      subst hgEq
      refine ⟨[], by simp, Core.listSubset_nil _, ?_⟩
      simpa [A, f] using (Core.errU_false_nil (n := n))
  }
  have hInv :
      sc.atlas.epsilon ≤ (1 : Core.Q) / (n + 2) := by
    have hNonneg : (0 : Core.Q) ≤ (1 : Core.Q) / (n + 2) := by
      positivity
    simpa [sc, A] using hNonneg
  refine ⟨{
    base := {
      sc := sc
      f := f
      hf := by simp [sc, f]
      S := []
      hlen := by simp [sc]
      hsub := Core.listSubset_nil _
      herr := by simpa [sc, A, f] using (Core.errU_false_nil (n := n))
      hEpsLeInv := hInv
    }
    hLink := by
      funext x
      rfl
  }⟩

/--
Semantically fixed singleton-density payload for the concrete gap-PartialMCSP
slice. This is the first non-vacuous target that does not let the consumer
choose the target function internally.
-/
structure AbstractGapTargetedSingletonDensityPayload
    (p : GapPartialMCSPParams) where
  n : Nat
  hsame : n = Models.partialInputLen p
  base : AbstractSingletonDensityPayload n
  hLink :
    base.f = fun x =>
      Models.gapPartialMCSP_Language p (Models.partialInputLen p)
        (ThirdPartyFacts.castBitVec hsame x)

/--
Abstract non-empty witness strengthening of the fixed gap-target payload.

This is the next consumer-facing strengthening after the empty-witness branch
has been isolated as too weak: instead of asking only for admissibility of the
empty list, we assume one explicit non-empty bounded witness inside the same
scenario dictionary.
-/
structure AbstractGapWitnessedPayload
    (p : GapPartialMCSPParams) where
  base : AbstractGapTargetedSingletonDensityPayload p
  Rf : List (Core.Subcube base.n)
  hRf_ne : Rf ≠ []
  hRf_len : Rf.length ≤ base.base.sc.k
  hRf_sub : Core.listSubset Rf base.base.sc.atlas.dict
  hRf_err : Core.errU base.base.f Rf ≤ base.base.sc.atlas.epsilon

/--
Thin packaging lemma: once one has an explicit non-empty bounded witness for
the fixed gap-target payload, it can be reified as an `AbstractGapWitnessedPayload`.
-/
noncomputable def abstractGapWitnessedPayload_of_exists_nonemptyWitness
    {p : GapPartialMCSPParams}
    (pkg : AbstractGapTargetedSingletonDensityPayload p)
    (hWitness :
      ∃ Rf : List (Core.Subcube pkg.n),
        Rf ≠ [] ∧
        Rf.length ≤ pkg.base.sc.k ∧
        Core.listSubset Rf pkg.base.sc.atlas.dict ∧
        Core.errU pkg.base.f Rf ≤ pkg.base.sc.atlas.epsilon) :
    AbstractGapWitnessedPayload p := by
  classical
  let Rf := Classical.choose hWitness
  have hRf := Classical.choose_spec hWitness
  exact
    { base := pkg
      Rf := Rf
      hRf_ne := hRf.1
      hRf_len := hRf.2.1
      hRf_sub := hRf.2.2.1
      hRf_err := hRf.2.2.2 }

/--
Targeted producer-side probe for the non-empty witness lift.

This marks the exact missing bridge from the fixed gap-target payload to the
stronger non-empty witness payload layer.
-/
def nonemptyWitnessGoal_of_abstractGapTargetedPayload
    {p : GapPartialMCSPParams}
    (pkg : AbstractGapTargetedSingletonDensityPayload p) : Prop :=
  ∃ Rf : List (Core.Subcube pkg.n),
    Rf ≠ [] ∧
    Rf.length ≤ pkg.base.sc.k ∧
    Core.listSubset Rf pkg.base.sc.atlas.dict ∧
    Core.errU pkg.base.f Rf ≤ pkg.base.sc.atlas.epsilon

/--
Probe equivalence for the missing non-empty witness producer bridge.

This theorem makes explicit that deriving `AbstractGapWitnessedPayload` over a
fixed base payload is equivalent to proving one concrete non-empty witness
existence goal.
-/
theorem nonemptyWitnessGoal_iff_exists_witnessed_package_with_base
    {p : GapPartialMCSPParams}
    (pkg : AbstractGapTargetedSingletonDensityPayload p) :
    nonemptyWitnessGoal_of_abstractGapTargetedPayload pkg ↔
      ∃ q : AbstractGapWitnessedPayload p, q.base = pkg := by
  constructor
  · intro h
    refine ⟨abstractGapWitnessedPayload_of_exists_nonemptyWitness pkg h, rfl⟩
  · intro h
    rcases h with ⟨q, hq⟩
    subst hq
    exact ⟨q.Rf, q.hRf_ne, q.hRf_len, q.hRf_sub, q.hRf_err⟩


/--
Any non-empty witness bridge for a fixed payload forces a positive witness
budget `k` in that payload's scenario.

This is a first concrete mathematical obstruction for the earliest missing
bridge: if one can derive `k = 0` for a concrete payload, then
`nonemptyWitnessGoal_of_abstractGapTargetedPayload` is impossible for that
payload.
-/
theorem one_le_k_of_nonemptyWitnessGoal
    {p : GapPartialMCSPParams}
    (pkg : AbstractGapTargetedSingletonDensityPayload p)
    (hW : nonemptyWitnessGoal_of_abstractGapTargetedPayload pkg) :
    1 ≤ pkg.base.sc.k := by
  rcases hW with ⟨Rf, hRf_ne, hRf_len, -, -⟩
  have hRf_len_pos : 1 ≤ Rf.length := Nat.succ_le_of_lt (List.length_pos_iff.2 hRf_ne)
  exact le_trans hRf_len_pos hRf_len

/--
Equivalent strict form of the same obstruction: the witness budget must be
non-zero whenever the non-empty witness bridge holds.
-/
theorem k_ne_zero_of_nonemptyWitnessGoal
    {p : GapPartialMCSPParams}
    (pkg : AbstractGapTargetedSingletonDensityPayload p)
    (hW : nonemptyWitnessGoal_of_abstractGapTargetedPayload pkg) :
    pkg.base.sc.k ≠ 0 := by
  have hk : 1 ≤ pkg.base.sc.k := one_le_k_of_nonemptyWitnessGoal pkg hW
  exact Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 1) hk)

/--
Conversely, if a concrete fixed payload has witness budget `k = 0`, then the
non-empty witness bridge is impossible for that payload.

This theorem is useful as a no-go probe target on concrete DAG-produced
payloads: deriving `k = 0` immediately refutes the earliest bridge.
-/
theorem not_nonemptyWitnessGoal_of_k_eq_zero
    {p : GapPartialMCSPParams}
    (pkg : AbstractGapTargetedSingletonDensityPayload p)
    (hk0 : pkg.base.sc.k = 0) :
    ¬ nonemptyWitnessGoal_of_abstractGapTargetedPayload pkg := by
  intro hW
  exact (k_ne_zero_of_nonemptyWitnessGoal pkg hW) hk0


/--
If the distinguished stored witness `base.S` is already non-empty, then the
earliest bridge goal is immediate by reusing exactly that witness.

This is a concrete mathematical step (not wiring): it turns the bridge into a
simple property check on the existing payload witness.
-/
theorem nonemptyWitnessGoal_of_baseWitness_nonempty
    {p : GapPartialMCSPParams}
    (pkg : AbstractGapTargetedSingletonDensityPayload p)
    (hS : pkg.base.S ≠ []) :
    nonemptyWitnessGoal_of_abstractGapTargetedPayload pkg := by
  refine ⟨pkg.base.S, hS, pkg.base.hlen, pkg.base.hsub, ?_⟩
  simpa [pkg.hLink] using pkg.base.herr

/--
If a payload satisfies `k = S.length` and `S = []`, then the earliest bridge is
impossible.

This is the exact no-go branch used in the empty/non-empty case split on the
stored witness.
-/
theorem not_nonemptyWitnessGoal_of_baseWitness_nil_of_k_eq_baseWitnessLen
    {p : GapPartialMCSPParams}
    (pkg : AbstractGapTargetedSingletonDensityPayload p)
    (hkLen : pkg.base.sc.k = pkg.base.S.length)
    (hS : pkg.base.S = []) :
    ¬ nonemptyWitnessGoal_of_abstractGapTargetedPayload pkg := by
  have hk0 : pkg.base.sc.k = 0 := by
    simpa [hS] using hkLen
  exact not_nonemptyWitnessGoal_of_k_eq_zero pkg hk0

/--
Any non-empty witness list covers at least one point. This is the strongest
purely witness-level consequence available without using any target semantics.
-/
theorem exists_covered_point_of_abstractGapWitnessedPayload
    {p : GapPartialMCSPParams}
    (pkg : AbstractGapWitnessedPayload p) :
    ∃ x : Core.BitVec pkg.base.n, Core.coveredB pkg.Rf x = true := by
  rcases List.exists_cons_of_ne_nil pkg.hRf_ne with ⟨β, rest, hEq⟩
  rcases Core.exists_mem_subcube β with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  have hxB : Core.memB β x = true := hx
  have hxCov : Core.coveredB (β :: rest) x = true := by
    simpa [Core.coveredB_cons, hxB]
  simpa [hEq] using hxCov

/--
First genuinely semantic strengthening of the non-empty witness route: every
point covered by every witness cube is already a YES-point of the fixed gap
target.
-/
structure AbstractGapCubeSoundWitnessPayload
    (p : GapPartialMCSPParams) where
  base : AbstractGapWitnessedPayload p
  hCubeSound :
    ∀ β, β ∈ base.Rf →
      ∀ x : Core.BitVec base.base.n, Core.mem β x →
        Models.gapPartialMCSP_Language p (Models.partialInputLen p)
          (ThirdPartyFacts.castBitVec base.base.hsame x) = true

/--
Thin packaging helper for the first semantic witness strengthening.
-/
def abstractGapCubeSoundWitnessPayload_of_cubeSound
    {p : GapPartialMCSPParams}
    (pkg : AbstractGapWitnessedPayload p)
    (hCubeSound :
      ∀ β, β ∈ pkg.Rf →
        ∀ x : Core.BitVec pkg.base.n, Core.mem β x →
          Models.gapPartialMCSP_Language p (Models.partialInputLen p)
            (ThirdPartyFacts.castBitVec pkg.base.hsame x) = true) :
    AbstractGapCubeSoundWitnessPayload p where
  base := pkg
  hCubeSound := hCubeSound

/--
`AbstractGapWitnessedPayload` by itself does not contain the semantic
cube-soundness invariant. This equivalence isolates the exact additional
obligation needed to upgrade the current fixed-witness payload to the next
semantic frontier.

The shape is intentionally "probe-friendly":

* the left side asks for a cube-sound package whose `base` is exactly `pkg`;
* the right side is the concrete local theorem goal that has to be proved
  from whatever stronger hypotheses become available later.
-/
theorem exists_cubeSound_package_with_base_iff
    {p : GapPartialMCSPParams}
    (pkg : AbstractGapWitnessedPayload p) :
    (∃ q : AbstractGapCubeSoundWitnessPayload p, q.base = pkg) ↔
      (∀ β, β ∈ pkg.Rf →
        ∀ x : Core.BitVec pkg.base.n, Core.mem β x →
          Models.gapPartialMCSP_Language p (Models.partialInputLen p)
            (ThirdPartyFacts.castBitVec pkg.base.hsame x) = true) := by
  constructor
  · intro h
    rcases h with ⟨q, hq⟩
    subst hq
    exact q.hCubeSound
  · intro h
    refine ⟨abstractGapCubeSoundWitnessPayload_of_cubeSound pkg h, rfl⟩

/--
Targeted proof-probe wrapper for the next semantic red goal.

This is the exact theorem shape recommended for follow-up work: proving this
`hYes` cube-local property from `AbstractGapWitnessedPayload` is equivalent to
constructing the next semantic payload layer.
-/
def cubeYesGoal_of_abstractGapWitnessedPayload
    {p : GapPartialMCSPParams}
    (pkg : AbstractGapWitnessedPayload p) : Prop :=
  ∀ β, β ∈ pkg.Rf →
    ∀ x : Core.BitVec pkg.base.n, Core.mem β x →
      Models.gapPartialMCSP_Language p (Models.partialInputLen p)
        (ThirdPartyFacts.castBitVec pkg.base.hsame x) = true

/--
Probe equivalence in the exact `hYes` shape: this is the closest local target
to test when checking whether cube-soundness is derivable from the fixed
non-empty witness payload.
-/
theorem cubeYesGoal_iff_exists_cubeSound_package_with_base
    {p : GapPartialMCSPParams}
    (pkg : AbstractGapWitnessedPayload p) :
    cubeYesGoal_of_abstractGapWitnessedPayload pkg ↔
      ∃ q : AbstractGapCubeSoundWitnessPayload p, q.base = pkg := by
  simpa [cubeYesGoal_of_abstractGapWitnessedPayload] using
    (exists_cubeSound_package_with_base_iff (pkg := pkg)).symm

/--
Consumer form without extra wrappers: once both cube-local semantic halves are
given over the same non-empty witness payload, contradiction is immediate.

This theorem is intentionally kept close to the eventual probing workflow: one
can try to derive `hYes` and `hNo` separately from `pkg` and then close the
branch directly here.
-/
theorem false_of_abstractGapWitnessedPayload_of_cubeYes_and_cubeNo
    {p : GapPartialMCSPParams}
    (pkg : AbstractGapWitnessedPayload p)
    (hYes : cubeYesGoal_of_abstractGapWitnessedPayload pkg)
    (hNo :
      ∀ β, β ∈ pkg.Rf →
        ∃ x : Core.BitVec pkg.base.n,
          Core.mem β x ∧
          Models.gapPartialMCSP_Language p (Models.partialInputLen p)
            (ThirdPartyFacts.castBitVec pkg.base.hsame x) = false) :
    False := by
  rcases List.exists_cons_of_ne_nil pkg.hRf_ne with ⟨β, rest, hEq⟩
  have hβ : β ∈ pkg.Rf := by
    simpa [hEq]
  rcases hNo β hβ with ⟨x, hxmem, hxfalse⟩
  have hxtrue := hYes β hβ x hxmem
  cases (hxtrue.symm.trans hxfalse)

/--
Complementary local semantic red goal (`hNo`) for the non-empty witness layer.
-/
def cubeNoGoal_of_abstractGapWitnessedPayload
    {p : GapPartialMCSPParams}
    (pkg : AbstractGapWitnessedPayload p) : Prop :=
  ∀ β, β ∈ pkg.Rf →
    ∃ x : Core.BitVec pkg.base.n,
      Core.mem β x ∧
      Models.gapPartialMCSP_Language p (Models.partialInputLen p)
        (ThirdPartyFacts.castBitVec pkg.base.hsame x) = false

/--
Unified local semantic target over one fixed non-empty witness payload.

This states explicitly that the contradiction route currently needs two
independent cube-local semantic halves: `hYes` and `hNo`.
-/
def cubeSeparatedGoal_of_abstractGapWitnessedPayload
    {p : GapPartialMCSPParams}
    (pkg : AbstractGapWitnessedPayload p) : Prop :=
  cubeYesGoal_of_abstractGapWitnessedPayload pkg ∧
    cubeNoGoal_of_abstractGapWitnessedPayload pkg

/--
Direct closure from the unified local semantic target on one payload.
-/
theorem false_of_abstractGapWitnessedPayload_of_cubeSeparatedGoal
    {p : GapPartialMCSPParams}
    (pkg : AbstractGapWitnessedPayload p)
    (hSep : cubeSeparatedGoal_of_abstractGapWitnessedPayload pkg) :
    False := by
  exact false_of_abstractGapWitnessedPayload_of_cubeYes_and_cubeNo
    pkg hSep.1 hSep.2

/--
End-to-end local contradiction route over a fixed gap-target payload, factored
through the earliest missing bridge.

This theorem makes the current dependency chain explicit:

1. first produce a non-empty witness package over `pkg`;
2. then establish both cube-local semantic halves on that same witness package.

Only then can contradiction be closed.
-/
theorem false_of_abstractGapTargetedPayload_of_exists_witnessed_cubeSeparatedGoal
    {p : GapPartialMCSPParams}
    (pkg : AbstractGapTargetedSingletonDensityPayload p)
    (hWitnessed : ∃ q : AbstractGapWitnessedPayload p, q.base = pkg)
    (hSeparated :
      ∀ q : AbstractGapWitnessedPayload p, q.base = pkg →
        cubeSeparatedGoal_of_abstractGapWitnessedPayload q) :
    False := by
  rcases hWitnessed with ⟨q, hq⟩
  exact false_of_abstractGapWitnessedPayload_of_cubeSeparatedGoal
    q (hSeparated q hq)

/--
Variant of the same route where the first bridge is supplied in the probe form
`nonemptyWitnessGoal_of_abstractGapTargetedPayload`.
-/
theorem false_of_abstractGapTargetedPayload_of_nonemptyWitnessGoal_and_cubeSeparated
    {p : GapPartialMCSPParams}
    (pkg : AbstractGapTargetedSingletonDensityPayload p)
    (hW : nonemptyWitnessGoal_of_abstractGapTargetedPayload pkg)
    (hSeparated :
      ∀ q : AbstractGapWitnessedPayload p, q.base = pkg →
        cubeSeparatedGoal_of_abstractGapWitnessedPayload q) :
    False := by
  have hWitnessed : ∃ q : AbstractGapWitnessedPayload p, q.base = pkg :=
    (nonemptyWitnessGoal_iff_exists_witnessed_package_with_base (pkg := pkg)).1 hW
  exact false_of_abstractGapTargetedPayload_of_exists_witnessed_cubeSeparatedGoal
    pkg hWitnessed hSeparated



/--
Cube-soundness already closes the first semantic red goal: any covered point
is a YES-point of the fixed gap target.
-/
theorem gapTarget_true_of_covered_of_abstractGapCubeSoundWitnessPayload
    {p : GapPartialMCSPParams}
    (pkg : AbstractGapCubeSoundWitnessPayload p)
    {x : Core.BitVec pkg.base.base.n}
    (hx : Core.coveredB pkg.base.Rf x = true) :
    Models.gapPartialMCSP_Language p (Models.partialInputLen p)
      (ThirdPartyFacts.castBitVec pkg.base.base.hsame x) = true := by
  have hcov : Core.covered pkg.base.Rf x := (Core.covered_iff (Rset := pkg.base.Rf) x).2 hx
  rcases hcov with ⟨β, hβ, hmem⟩
  exact pkg.hCubeSound β hβ x hmem

/--
Consequently, the semantically strengthened non-empty witness route already
forces the existence of one YES-point for the fixed gap target.
-/
theorem exists_yes_point_of_abstractGapCubeSoundWitnessPayload
    {p : GapPartialMCSPParams}
    (pkg : AbstractGapCubeSoundWitnessPayload p) :
    ∃ x : Core.BitVec pkg.base.base.n,
      Models.gapPartialMCSP_Language p (Models.partialInputLen p)
        (ThirdPartyFacts.castBitVec pkg.base.base.hsame x) = true := by
  rcases exists_covered_point_of_abstractGapWitnessedPayload pkg.base with ⟨x, hx⟩
  exact ⟨x, gapTarget_true_of_covered_of_abstractGapCubeSoundWitnessPayload pkg hx⟩

/--
Semantic rephrasing of the same conclusion at the level of the PartialMCSP YES
predicate.
-/
theorem exists_yes_input_of_abstractGapCubeSoundWitnessPayload
    {p : GapPartialMCSPParams}
    (pkg : AbstractGapCubeSoundWitnessPayload p) :
    ∃ x : Core.BitVec pkg.base.base.n,
      Models.PartialMCSP_YES p
        (Models.decodePartial (ThirdPartyFacts.castBitVec pkg.base.base.hsame x)) := by
  rcases exists_yes_point_of_abstractGapCubeSoundWitnessPayload pkg with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  exact (Models.gapPartialMCSP_language_true_iff_yes p
    (ThirdPartyFacts.castBitVec pkg.base.base.hsame x)).1 hx

/--
If every witness cube is YES-sound and every witness cube also contains some
NO-point of the same fixed gap target, the non-empty witness route collapses to
an immediate contradiction.
-/
theorem contradiction_of_abstractGapCubeSoundWitnessPayload_of_cubeRefute
    {p : GapPartialMCSPParams}
    (pkg : AbstractGapCubeSoundWitnessPayload p)
    (hCubeRefute :
      ∀ β, β ∈ pkg.base.Rf →
        ∃ x : Core.BitVec pkg.base.base.n,
          Core.mem β x ∧
          Models.gapPartialMCSP_Language p (Models.partialInputLen p)
            (ThirdPartyFacts.castBitVec pkg.base.base.hsame x) = false) :
    False := by
  rcases List.exists_cons_of_ne_nil pkg.base.hRf_ne with ⟨β, rest, hEq⟩
  have hβ : β ∈ pkg.base.Rf := by
    simpa [hEq]
  rcases hCubeRefute β hβ with ⟨x, hxmem, hxfalse⟩
  have hxtrue :=
    pkg.hCubeSound β hβ x hxmem
  cases (hxtrue.symm.trans hxfalse)

/--
Unified consumer frontier for the non-empty witness route.

This packages both cube-local semantic halves explicitly:

* `hYes`: every point inside every selected witness cube is a YES-point;
* `hNo`: every selected witness cube contains at least one NO-point.

With both halves present simultaneously, contradiction is immediate.
-/
structure AbstractGapCubeSeparatedWitnessPayload
    (p : GapPartialMCSPParams) where
  base : AbstractGapWitnessedPayload p
  hYes :
    ∀ β, β ∈ base.Rf →
      ∀ x : Core.BitVec base.base.n, Core.mem β x →
        Models.gapPartialMCSP_Language p (Models.partialInputLen p)
          (ThirdPartyFacts.castBitVec base.base.hsame x) = true
  hNo :
    ∀ β, β ∈ base.Rf →
      ∃ x : Core.BitVec base.base.n,
        Core.mem β x ∧
        Models.gapPartialMCSP_Language p (Models.partialInputLen p)
          (ThirdPartyFacts.castBitVec base.base.hsame x) = false

/--
The unified cube-separated witness payload is already inconsistent.

Proof idea: package `hYes` as a cube-sound payload and then apply the existing
`cube-sound + cube-refute => False` thin consumer.
-/
theorem false_of_abstractGapCubeSeparatedWitnessPayload
    {p : GapPartialMCSPParams}
    (pkg : AbstractGapCubeSeparatedWitnessPayload p) :
    False := by
  let pkgSound : AbstractGapCubeSoundWitnessPayload p :=
    abstractGapCubeSoundWitnessPayload_of_cubeSound pkg.base pkg.hYes
  exact contradiction_of_abstractGapCubeSoundWitnessPayload_of_cubeRefute
    pkgSound pkg.hNo

/--
The current concrete singleton-density package factors through the abstract
scenario-level payload.
-/
def abstractSingletonDensityPayload_of_singletonDensityPackage
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (pkg : SemanticSwitchingSingletonDensityPackagePartial hFormula) :
    AbstractSingletonDensityPayload pkg.prov.pack.cert.ac0.n where
  sc := pkg.prov.pack.scenario
  f := pkg.prov.f
  hf := by
    have hfF : pkg.prov.f ∈ pkg.prov.pack.cert.F := by
      simpa [pkg.prov.hSingleton]
    simpa [pkg.prov.pack.family_eq] using hfF
  S := pkg.S
  hlen := by
    rw [pkg.prov.hk]
    exact pkg.hlen
  hsub := pkg.hsub
  herr := pkg.herr
  hEpsLeInv := pkg.hEpsLeInv

/--
The current singleton-density package also yields the minimally strengthened
formula-free payload: an abstract singleton-density object together with an
explicit target-link witness.
-/
noncomputable def abstractLinkedSingletonDensityPayload_of_singletonDensityPackage
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (pkg : SemanticSwitchingSingletonDensityPackagePartial hFormula) :
    AbstractLinkedSingletonDensityPayload pkg.prov.pack.cert.ac0.n where
  base := abstractSingletonDensityPayload_of_singletonDensityPackage pkg
  target := fun x =>
    ComplexityInterfaces.FormulaCircuit.eval
      ((Classical.choose hFormula).family (Models.partialInputLen p))
      (ThirdPartyFacts.castBitVec pkg.prov.pack.cert.hsame x)
  hLink := by
    funext x
    exact pkg.prov.hEval x

/--
The current singleton-density package also yields the externally targeted
abstract payload, with the target fixed by the formula witness.
-/
noncomputable def abstractTargetedSingletonDensityPayload_of_singletonDensityPackage
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (pkg : SemanticSwitchingSingletonDensityPackagePartial hFormula) :
    AbstractTargetedSingletonDensityPayload
      pkg.prov.pack.cert.ac0.n
      (fun x =>
        ComplexityInterfaces.FormulaCircuit.eval
          ((Classical.choose hFormula).family (Models.partialInputLen p))
          (ThirdPartyFacts.castBitVec pkg.prov.pack.cert.hsame x)) where
  base := abstractSingletonDensityPayload_of_singletonDensityPackage pkg
  hLink := by
    funext x
    exact pkg.prov.hEval x

/--
Current internal formula route also reaches the semantically fixed gap-target
payload.
-/
noncomputable def abstractGapTargetedSingletonDensityPayload_of_singletonDensityPackage
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (pkg : SemanticSwitchingSingletonDensityPackagePartial hFormula) :
    AbstractGapTargetedSingletonDensityPayload p where
  n := pkg.prov.pack.cert.ac0.n
  hsame := pkg.prov.pack.cert.hsame
  base := abstractSingletonDensityPayload_of_singletonDensityPackage pkg
  hLink := by
    funext x
    have hEval := pkg.prov.hEval x
    have hCorrect :=
      (Classical.choose hFormula).correct
        (Models.partialInputLen p)
        (ThirdPartyFacts.castBitVec pkg.prov.pack.cert.hsame x)
    exact hEval.trans hCorrect

/--
Current internal formula route also reaches the semantically fixed gap-target
payload.
-/
theorem abstractGapTargetedSingletonDensityPayload_of_internal_provider
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) :
    Nonempty (AbstractGapTargetedSingletonDensityPayload p) := by
  classical
  let pkg := Classical.choice (singletonDensityPackage_of_internal_provider hFormula)
  exact ⟨abstractGapTargetedSingletonDensityPayload_of_singletonDensityPackage pkg⟩

/--
The strict DAG witness for the same gap slice also realizes the semantically
fixed gap-target payload. This is the first source-side bridge that is shared
by both the formula route and the DAG route.
-/
theorem abstractGapTargetedSingletonDensityPayload_of_dag
    {p : GapPartialMCSPParams}
    (hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p)) :
    Nonempty (AbstractGapTargetedSingletonDensityPayload p) := by
  classical
  rcases hDag with ⟨wf, _⟩
  let n := Models.partialInputLen p
  let f : Core.BitVec n → Bool := fun x =>
    ComplexityInterfaces.DagCircuit.eval (wf.family n) x
  obtain ⟨A, hWorks, hεeq⟩ :=
    Magnification.AC0LocalityBridge.semanticSingletonAtlas_exact_epsilon f
  have hfF : f ∈ ([f] : Core.Family n) := by
    simp [f]
  rcases hWorks f hfF with ⟨S, hsub, herr⟩
  have hε0 : (0 : Core.Q) ≤ A.epsilon := by
    rw [hεeq]
    positivity
  have hε1 : A.epsilon ≤ (1 : Core.Q) / 2 := by
    rw [hεeq]
    have hpos : (0 : Core.Q) < (2 : Core.Q) := by norm_num
    have hNat : (2 : Core.Q) ≤ (n + 2 : Core.Q) := by
      norm_num
    exact one_div_le_one_div_of_le (a := (2 : Core.Q)) (b := (n + 2 : Core.Q)) hpos hNat
  let sc : BoundedAtlasScenario n := {
    atlas := A
    family := [f]
    k := S.length
    hε0 := hε0
    hε1 := hε1
    works := hWorks
    bounded := by
      intro g hg
      have hgEq : g = f := by
        simpa [f] using hg
      subst hgEq
      exact ⟨S, le_rfl, hsub, herr⟩
  }
  have hEpsLeInv : sc.atlas.epsilon ≤ (1 : Core.Q) / (n + 2) := by
    rw [hεeq]
    change (1 : Core.Q) / (n + 2) ≤ (1 : Core.Q) / (n + 2)
    rfl
  refine ⟨{
    n := n
    hsame := rfl
    base := {
      sc := sc
      f := f
      hf := by simp [sc, f]
      S := S
      hlen := by simp [sc]
      hsub := hsub
      herr := herr
      hEpsLeInv := hEpsLeInv
    }
    hLink := by
      funext x
      simpa [n, f] using (wf.correct n x)
  }⟩

/--
The fixed `gapPartialMCSP` slice always has at least one YES input: the fully
undefined partial table is consistent with the constant-false circuit.
-/
theorem gapPartialMCSP_exists_yes_input
    (p : GapPartialMCSPParams) :
    ∃ x : Core.BitVec (Models.partialInputLen p),
      Models.gapPartialMCSP_Language p (Models.partialInputLen p) x = true := by
  let T : Models.PartialTruthTable p.n := fun _ => none
  let x : Core.BitVec (Models.partialInputLen p) := Models.encodePartial T
  refine ⟨x, ?_⟩
  rw [Models.gapPartialMCSP_language_true_iff_yes]
  have hdecode : Models.decodePartial x = T := by
    simpa [x, T] using (Models.decodePartial_encodePartial T)
  rw [hdecode]
  refine ⟨Models.Circuit.const false, ?_, ?_⟩
  · simp [Models.Circuit.size]
    exact p.sYES_pos
  · simpa [T] using
      (LowerBounds.const_false_consistent_of_vals_false (n := p.n) T
        (h := by intro j; exact Or.inl rfl))

/--
DAG-side strengthened producer with explicit provenance for the stored witness.

In addition to `k = S.length`, this version records that the witness is exactly
the concrete singleton selector list produced by the semantic truth-table DNF
construction.
-/
theorem abstractGapTargetedSingletonDensityPayload_of_dag_with_baseWitness_provenance
    {p : GapPartialMCSPParams}
    (hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p)) :
    ∃ pkg : AbstractGapTargetedSingletonDensityPayload p,
      pkg.base.sc.k = pkg.base.S.length ∧
      pkg.base.S =
        Magnification.AC0LocalityBridge.semanticSingletonWitness pkg.base.f := by
  classical
  rcases hDag with ⟨wf, _⟩
  let n := Models.partialInputLen p
  let f : Core.BitVec n → Bool := fun x =>
    ComplexityInterfaces.DagCircuit.eval (wf.family n) x
  let S := Magnification.AC0LocalityBridge.semanticSingletonWitness f
  obtain ⟨A, hWorks, hεeq, hsub, herr⟩ :=
    Magnification.AC0LocalityBridge.semanticSingletonAtlas_exact_epsilon_with_witness f
  have hε0 : (0 : Core.Q) ≤ A.epsilon := by
    rw [hεeq]
    positivity
  have hε1 : A.epsilon ≤ (1 : Core.Q) / 2 := by
    rw [hεeq]
    have hpos : (0 : Core.Q) < (2 : Core.Q) := by norm_num
    have hNat : (2 : Core.Q) ≤ (n + 2 : Core.Q) := by
      norm_num
    exact one_div_le_one_div_of_le (a := (2 : Core.Q)) (b := (n + 2 : Core.Q)) hpos hNat
  let sc : BoundedAtlasScenario n := {
    atlas := A
    family := [f]
    k := S.length
    hε0 := hε0
    hε1 := hε1
    works := hWorks
    bounded := by
      intro g hg
      have hgEq : g = f := by
        simpa [f] using hg
      subst hgEq
      exact ⟨S, le_rfl, hsub, herr⟩
  }
  have hEpsLeInv : sc.atlas.epsilon ≤ (1 : Core.Q) / (n + 2) := by
    rw [hεeq]
    change (1 : Core.Q) / (n + 2) ≤ (1 : Core.Q) / (n + 2)
    rfl
  refine ⟨{
    n := n
    hsame := rfl
    base := {
      sc := sc
      f := f
      hf := by simp [sc, f]
      S := S
      hlen := by simp [sc]
      hsub := hsub
      herr := herr
      hEpsLeInv := hEpsLeInv
    }
    hLink := by
      funext x
      simpa [n, f] using (wf.correct n x)
  }, by simp [sc, S], rfl⟩


/--
DAG-side strengthened producer: besides returning a fixed gap-target payload,
it records the concrete identity `k = S.length` of the stored witness budget.

This identity is what makes the earliest bridge split mathematically sharp:
empty `S` implies `k = 0`, while non-empty `S` gives an immediate witness.
-/
theorem abstractGapTargetedSingletonDensityPayload_of_dag_with_k_eq_baseWitnessLen
    {p : GapPartialMCSPParams}
    (hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p)) :
    ∃ pkg : AbstractGapTargetedSingletonDensityPayload p,
      pkg.base.sc.k = pkg.base.S.length := by
  rcases abstractGapTargetedSingletonDensityPayload_of_dag_with_baseWitness_provenance
      (p := p) hDag with ⟨pkg, hk, _hProv⟩
  exact ⟨pkg, hk⟩

/--
Mathematical case split for the earliest bridge on a DAG-produced payload.

For the concrete payload returned by the strengthened DAG producer:

* if `S ≠ []`, the bridge holds immediately by taking `Rf := S`;
* if `S = []`, then `k = 0` and the bridge is impossible.
-/
theorem dag_payload_nonemptyWitness_bridge_split
    {p : GapPartialMCSPParams}
    (hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p)) :
    ∃ pkg : AbstractGapTargetedSingletonDensityPayload p,
      (pkg.base.S ≠ [] ∧ nonemptyWitnessGoal_of_abstractGapTargetedPayload pkg) ∨
      (pkg.base.S = [] ∧ ¬ nonemptyWitnessGoal_of_abstractGapTargetedPayload pkg) := by
  rcases abstractGapTargetedSingletonDensityPayload_of_dag_with_k_eq_baseWitnessLen (p := p) hDag with
      ⟨pkg, hkLen⟩
  by_cases hS : pkg.base.S = []
  · refine ⟨pkg, Or.inr ?_⟩
    exact ⟨hS, not_nonemptyWitnessGoal_of_baseWitness_nil_of_k_eq_baseWitnessLen pkg hkLen hS⟩
  · refine ⟨pkg, Or.inl ?_⟩
    exact ⟨hS, nonemptyWitnessGoal_of_baseWitness_nonempty pkg hS⟩


/--
Canonical fixed payload chosen from the strengthened DAG producer that also
records the concrete identity `k = S.length`.

Using a dedicated name avoids the normalization mismatch between different
`Classical.choice` representatives of DAG-produced payloads.
-/
noncomputable def dagCanonicalPayload
    {p : GapPartialMCSPParams}
    (hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p)) :
    AbstractGapTargetedSingletonDensityPayload p :=
  Classical.choose
    (abstractGapTargetedSingletonDensityPayload_of_dag_with_baseWitness_provenance (p := p) hDag)

/--
The canonical DAG-produced payload remembers exactly that its witness budget is
its stored witness length.
-/
theorem dagCanonicalPayload_k_eq_baseWitnessLen
    {p : GapPartialMCSPParams}
    (hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p)) :
    (dagCanonicalPayload hDag).base.sc.k = (dagCanonicalPayload hDag).base.S.length := by
  exact (Classical.choose_spec
    (abstractGapTargetedSingletonDensityPayload_of_dag_with_baseWitness_provenance (p := p) hDag)).1

/--
The canonical DAG payload stores the explicit singleton selector list coming
from the semantic truth-table DNF construction.
-/
theorem dagCanonicalPayload_baseWitness_eq_semanticSingletonWitness
    {p : GapPartialMCSPParams}
    (hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p)) :
    (dagCanonicalPayload hDag).base.S =
      Magnification.AC0LocalityBridge.semanticSingletonWitness (dagCanonicalPayload hDag).base.f := by
  exact (Classical.choose_spec
    (abstractGapTargetedSingletonDensityPayload_of_dag_with_baseWitness_provenance (p := p) hDag)).2

/--
For the canonical DAG-produced payload, the earliest bridge is equivalent to
plain non-emptiness of the already stored witness `S`.

This is the exact normalization step needed before attacking the first genuine
mathematical target: proving `S ≠ []` for the concrete DAG payload.
-/
theorem nonemptyWitnessGoal_iff_baseWitness_nonempty_of_dagCanonicalPayload
    {p : GapPartialMCSPParams}
    (hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p)) :
    nonemptyWitnessGoal_of_abstractGapTargetedPayload (dagCanonicalPayload hDag) ↔
      (dagCanonicalPayload hDag).base.S ≠ [] := by
  constructor
  · intro hW
    intro hS
    exact (not_nonemptyWitnessGoal_of_baseWitness_nil_of_k_eq_baseWitnessLen
      (dagCanonicalPayload hDag)
      (dagCanonicalPayload_k_eq_baseWitnessLen hDag) hS) hW
  · intro hS
    exact nonemptyWitnessGoal_of_baseWitness_nonempty (dagCanonicalPayload hDag) hS

/--
Canonical-form theorem target for the next real proof step on the DAG route:
show that the stored witness inside the concrete DAG-produced payload is
non-empty.
-/
def dag_payload_baseWitness_nonempty
    (p : GapPartialMCSPParams) : Prop :=
  ∀ hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p),
    (dagCanonicalPayload hDag).base.S ≠ []

/--
The structural DAG witness target is in fact provable: the canonical stored
witness is the explicit truth-table-DNF selector list for the gap language, and
that list is non-empty because the gap slice has a concrete YES input.
-/
theorem dag_payload_baseWitness_nonempty_holds
    (p : GapPartialMCSPParams) :
    dag_payload_baseWitness_nonempty p := by
  intro hDag
  have hYes : ∃ x : Core.BitVec (dagCanonicalPayload hDag).n,
      (dagCanonicalPayload hDag).base.f x = true := by
    rcases gapPartialMCSP_exists_yes_input p with ⟨x0, hx0⟩
    let x : Core.BitVec (dagCanonicalPayload hDag).n :=
      ThirdPartyFacts.castBitVec (dagCanonicalPayload hDag).hsame.symm x0
    refine ⟨x, ?_⟩
    have hLinkAt :=
      congrArg (fun g => g x) (dagCanonicalPayload hDag).hLink
    have hLinkAt' :
        (dagCanonicalPayload hDag).base.f x =
          Models.gapPartialMCSP_Language p (Models.partialInputLen p) x0 := by
      simpa [x] using hLinkAt
    exact hLinkAt'.trans hx0
  rw [dagCanonicalPayload_baseWitness_eq_semanticSingletonWitness hDag]
  exact Magnification.AC0LocalityBridge.semanticSingletonWitness_nonempty_of_exists_true
    ((dagCanonicalPayload hDag).base.f) hYes

/--
Earliest DAG-facing probe target: for each concrete DAG-produced fixed payload,
one can derive the non-empty witness bridge goal.

This packages the exact next theorem shape suggested by the current frontier
analysis, but keeps it abstract and non-committal: no claim is made here that
this probe is already provable.
-/
def dagNonemptyWitnessGoalProbe
    (p : GapPartialMCSPParams) : Prop :=
  ∀ hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p),
    nonemptyWitnessGoal_of_abstractGapTargetedPayload (dagCanonicalPayload hDag)

/--
Equivalent DAG-facing packaging of the same earliest bridge, expressed directly
as existence of a witnessed payload over the concrete DAG-produced fixed
payload.
-/
theorem dagNonemptyWitnessGoalProbe_iff_exists_witnessed_on_dag_payload
    (p : GapPartialMCSPParams) :
    dagNonemptyWitnessGoalProbe p ↔
      ∀ hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p),
        ∃ q : AbstractGapWitnessedPayload p, q.base = dagCanonicalPayload hDag := by
  constructor
  · intro h
    intro hDag
    exact (nonemptyWitnessGoal_iff_exists_witnessed_package_with_base
      (pkg := dagCanonicalPayload hDag)).1 (h hDag)
  · intro h
    intro hDag
    exact (nonemptyWitnessGoal_iff_exists_witnessed_package_with_base
      (pkg := dagCanonicalPayload hDag)).2 (h hDag)


/--
After normalization to the canonical DAG payload, the earliest bridge probe is
exactly equivalent to non-emptiness of the stored witness `S`.
-/
theorem dagNonemptyWitnessGoalProbe_iff_baseWitness_nonempty
    (p : GapPartialMCSPParams) :
    dagNonemptyWitnessGoalProbe p ↔ dag_payload_baseWitness_nonempty p := by
  constructor
  · intro h
    intro hDag
    exact (nonemptyWitnessGoal_iff_baseWitness_nonempty_of_dagCanonicalPayload hDag).1 (h hDag)
  · intro h
    intro hDag
    exact (nonemptyWitnessGoal_iff_baseWitness_nonempty_of_dagCanonicalPayload hDag).2 (h hDag)

/--
The normalized earliest DAG-facing bridge now really holds: the canonical
payload always carries a non-empty stored witness, hence the non-empty witness
goal itself is available on every DAG-produced payload.
-/
theorem dagNonemptyWitnessGoalProbe_holds
    (p : GapPartialMCSPParams) :
    dagNonemptyWitnessGoalProbe p := by
  exact (dagNonemptyWitnessGoalProbe_iff_baseWitness_nonempty p).2
    (dag_payload_baseWitness_nonempty_holds p)

/--
An abstract consumer ruling out the semantically fixed gap-target payload
already yields DAG non-uniform separation for the same fixed slice.
-/
theorem not_ppolyDAG_of_abstractGapTargeted_consumer
    {p : GapPartialMCSPParams}
    (hConsumer : ¬ Nonempty (AbstractGapTargetedSingletonDensityPayload p)) :
    ¬ ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p) := by
  intro hDag
  exact hConsumer (abstractGapTargetedSingletonDensityPayload_of_dag hDag)

/--
Fixed-slice NP plus the abstract gap-target consumer already imply strict DAG
non-uniform separation.
-/
theorem NP_not_subset_PpolyDAG_of_abstractGapTargeted_consumer
    {p : GapPartialMCSPParams}
    (hNP : ComplexityInterfaces.NP (gapPartialMCSP_Language p))
    (hConsumer : ¬ Nonempty (AbstractGapTargetedSingletonDensityPayload p)) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  refine ⟨gapPartialMCSP_Language p, hNP, ?_⟩
  exact not_ppolyDAG_of_abstractGapTargeted_consumer hConsumer

/--
TM-witness packaging version of the same reduction to DAG non-uniform
separation.
-/
theorem NP_not_subset_PpolyDAG_of_abstractGapTargeted_consumer_TM
    {p : GapPartialMCSPParams}
    (W : Models.GapPartialMCSP_TMWitness p)
    (hConsumer : ¬ Nonempty (AbstractGapTargetedSingletonDensityPayload p)) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  apply NP_not_subset_PpolyDAG_of_abstractGapTargeted_consumer
  exact
    Models.gapPartialMCSP_in_NP_of_TM p
      (Models.gapPartialMCSP_in_NP_TM_of_witness p W)
  exact hConsumer

/--
For the semantically fixed gap target, the YES-density of the distinguished
function is exactly the YES-density of the concrete `gapPartialMCSP` slice.
-/
theorem gapTarget_yesDensity_eq_yesInputSet_density
    {p : GapPartialMCSPParams}
    (pkg : AbstractGapTargetedSingletonDensityPayload p) :
    ((Finset.univ.filter (fun x => pkg.base.f x = true)).card : Core.Q) /
        (2 ^ pkg.n : Nat)
      =
    ((Counting.yesInputSet p).card : Core.Q) /
        (4 ^ Models.Partial.tableLen p.n : Nat) := by
  rcases pkg with ⟨n, hsame, base, hLink⟩
  subst hsame
  have hset :
      (Finset.univ.filter (fun x => base.f x = true)) = Counting.yesInputSet p := by
    ext x
    simp [Counting.yesInputSet, hLink]
  rw [hset]
  have hpow : (2 ^ Models.partialInputLen p : Nat) = 4 ^ Models.Partial.tableLen p.n := by
    simp [Models.partialInputLen, Models.Partial.inputLen, Models.Partial.tableLen, pow_mul]
  rw [hpow]

/--
If the stored witness on a fixed gap-target payload is empty, then the payload
already forces the concrete YES-density of the `gapPartialMCSP` slice under the
scenario budget `1 / (partialInputLen + 2)`.

This is the first honest mathematical consequence of the case `S = []`: the
abstract error guarantee collapses to the raw YES-density through
`Core.errU_nil_eq_yes_density`, and the inherited scenario budget finishes the
bound.
-/
theorem yesDensity_le_inv_of_abstractGapTargetedPayload_of_baseWitness_nil
    {p : GapPartialMCSPParams}
    (pkg : AbstractGapTargetedSingletonDensityPayload p)
    (hS : pkg.base.S = []) :
    ((Counting.yesInputSet p).card : Core.Q) /
        (4 ^ Models.Partial.tableLen p.n : Nat)
      ≤
    (1 : Core.Q) / (Models.partialInputLen p + 2) := by
  have hErrNil : Core.errU pkg.base.f [] ≤ pkg.base.sc.atlas.epsilon := by
    simpa [hS] using pkg.base.herr
  have hGapYesLe :
      ((Finset.univ.filter (fun x => pkg.base.f x = true)).card : Core.Q) /
          (2 ^ pkg.n : Nat)
        ≤ pkg.base.sc.atlas.epsilon := by
    simpa [Core.errU_nil_eq_yes_density] using hErrNil
  have hGapYesLeInv :
      ((Finset.univ.filter (fun x => pkg.base.f x = true)).card : Core.Q) /
          (2 ^ pkg.n : Nat)
        ≤ (1 : Core.Q) / (Models.partialInputLen p + 2) := by
    simpa [pkg.hsame] using le_trans hGapYesLe pkg.base.hEpsLeInv
  rw [← gapTarget_yesDensity_eq_yesInputSet_density pkg]
  exact hGapYesLeInv

/--
Specialized `S = []` reduction for the canonical DAG-produced payload.

This is the canonical form of the empty-witness branch on the DAG route: if the
stored witness list were empty, then the concrete YES-density of the target
slice would already have to lie below `1 / (partialInputLen + 2)`.
-/
theorem yesDensity_le_inv_of_dagCanonicalPayload_of_baseWitness_nil
    {p : GapPartialMCSPParams}
    (hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p))
    (hS : (dagCanonicalPayload hDag).base.S = []) :
    ((Counting.yesInputSet p).card : Core.Q) /
        (4 ^ Models.Partial.tableLen p.n : Nat)
      ≤
    (1 : Core.Q) / (Models.partialInputLen p + 2) := by
  exact
    yesDensity_le_inv_of_abstractGapTargetedPayload_of_baseWitness_nil
      (pkg := dagCanonicalPayload hDag) hS

/--
Contrapositive wrapper for the canonical DAG route: any strict lower bound on
the concrete YES-density beyond `1 / (partialInputLen + 2)` rules out the empty
stored witness case for every DAG-produced canonical payload.

This theorem isolates exactly what remains to prove in order to close the
earliest DAG-facing bridge: a density lower bound strong enough to contradict
the empty-witness consequence above.
-/
theorem dag_payload_baseWitness_nonempty_of_yesDensity_gt_inv
    {p : GapPartialMCSPParams}
    (hLower :
      (1 : Core.Q) / (Models.partialInputLen p + 2) <
        ((Counting.yesInputSet p).card : Core.Q) /
          (4 ^ Models.Partial.tableLen p.n : Nat)) :
    dag_payload_baseWitness_nonempty p := by
  intro hDag
  intro hS
  have hLe :=
    yesDensity_le_inv_of_dagCanonicalPayload_of_baseWitness_nil
      (p := p) hDag hS
  exact (lt_irrefl _) (lt_of_lt_of_le hLower hLe)

/--
Consequently, the YES-density of the semantically fixed gap target is bounded
by the Shannon counting estimate already available for the YES-input set.
-/
theorem gapTarget_yesDensity_le_circuitCountBound_mul_three_quarters_pow
    {p : GapPartialMCSPParams}
    (pkg : AbstractGapTargetedSingletonDensityPayload p) :
    ((Finset.univ.filter (fun x => pkg.base.f x = true)).card : Core.Q) /
        (2 ^ pkg.n : Nat)
      ≤
    (Models.circuitCountBound p.n p.sYES : Core.Q) *
      ((3 : Core.Q) / 4) ^ Models.Partial.tableLen p.n := by
  rw [gapTarget_yesDensity_eq_yesInputSet_density pkg]
  exact Counting.yesDensity_yesInputSet_le_circuitCountBound_mul_three_quarters_pow p

/--
Cheapest empty-witness consumer subroute: if the Shannon upper bound already
fits under the scenario error budget, then the empty witness list is
admissible for the fixed gap target.
-/
theorem empty_witness_admissible_of_gapTargetedSingletonDensityPayload_of_shannon_bound
    {p : GapPartialMCSPParams}
    (pkg : AbstractGapTargetedSingletonDensityPayload p)
    (hBound :
      (Models.circuitCountBound p.n p.sYES : Core.Q) *
        ((3 : Core.Q) / 4) ^ Models.Partial.tableLen p.n
          ≤ pkg.base.sc.atlas.epsilon) :
    ∃ Rf : List (Core.Subcube pkg.n),
      Rf = [] ∧
      Core.listSubset Rf pkg.base.sc.atlas.dict ∧
      Core.errU pkg.base.f Rf ≤ pkg.base.sc.atlas.epsilon := by
  refine ⟨[], rfl, Core.listSubset_nil _, ?_⟩
  have hYesLe :
      ((Finset.univ.filter (fun x => pkg.base.f x = true)).card : Core.Q) /
        (2 ^ pkg.n : Nat)
        ≤ pkg.base.sc.atlas.epsilon := by
    exact le_trans
      (gapTarget_yesDensity_le_circuitCountBound_mul_three_quarters_pow pkg)
      hBound
  simpa [Core.errU_nil_eq_yes_density] using hYesLe

/--
The natural mismatch testset attached to an abstract singleton-density payload.
-/
noncomputable def naturalMismatchTestsetOfAbstractSingletonDensityPayload
    {n : Nat}
    (pkg : AbstractSingletonDensityPayload n) :
    Finset (Core.BitVec n) :=
  Counting.mismatchSet (fun x => Core.coveredB pkg.S x) pkg.f

/--
The natural mismatch testset always witnesses `ApproxOnTestset`.
-/
theorem approxOnNaturalMismatchTestset_of_abstractSingletonDensityPayload
    {n : Nat}
    (pkg : AbstractSingletonDensityPayload n) :
    pkg.f ∈ Counting.ApproxOnTestset
      (R := pkg.sc.atlas.dict)
      (k := pkg.sc.k)
      (T := naturalMismatchTestsetOfAbstractSingletonDensityPayload pkg) := by
  exact Counting.approxOnTestset_of_mismatchSet pkg.hlen pkg.hsub

/--
`errU ≤ ε` gives the density bound on the natural mismatch testset already at
the abstract scenario level.
-/
theorem naturalMismatchTestset_density_le_of_abstractSingletonDensityPayload
    {n : Nat}
    (pkg : AbstractSingletonDensityPayload n) :
    ((((naturalMismatchTestsetOfAbstractSingletonDensityPayload pkg).card : Nat) : Core.Q) /
      (((Nat.pow 2 n : Nat) : Core.Q)))
      ≤ pkg.sc.atlas.epsilon := by
  simpa [naturalMismatchTestsetOfAbstractSingletonDensityPayload] using
    Counting.mismatchSet_density_le_of_errU_le pkg.f pkg.S
      pkg.sc.atlas.epsilon pkg.herr

/--
For an abstract singleton-density payload, the natural mismatch testset has
density at most `1 / (n + 2)`.
-/
theorem naturalMismatchTestset_density_le_inv_of_abstractSingletonDensityPayload
    {n : Nat}
    (pkg : AbstractSingletonDensityPayload n) :
    ((((naturalMismatchTestsetOfAbstractSingletonDensityPayload pkg).card : Nat) : Core.Q) /
      (((Nat.pow 2 n : Nat) : Core.Q)))
      ≤ (1 : Core.Q) / (n + 2) := by
  exact le_trans
    (naturalMismatchTestset_density_le_of_abstractSingletonDensityPayload pkg)
    pkg.hEpsLeInv

/--
Nat-crossmul form of the same abstract density bound.
-/
theorem naturalMismatchTestset_card_le_inv_mul_pow_of_abstractSingletonDensityPayload
    {n : Nat}
    (pkg : AbstractSingletonDensityPayload n) :
    (((naturalMismatchTestsetOfAbstractSingletonDensityPayload pkg).card : Nat) : Core.Q)
      ≤ ((1 : Core.Q) / (n + 2)) * (((Nat.pow 2 n : Nat) : Core.Q)) := by
  have hCardErr :
      (((naturalMismatchTestsetOfAbstractSingletonDensityPayload pkg).card : Nat) : Core.Q)
        ≤ pkg.sc.atlas.epsilon * (((Nat.pow 2 n : Nat) : Core.Q)) := by
    simpa [naturalMismatchTestsetOfAbstractSingletonDensityPayload] using
      Counting.mismatchSet_card_le_of_errU_le pkg.f pkg.S
        pkg.sc.atlas.epsilon pkg.herr
  have hPowNonneg : (0 : Core.Q) ≤ (((Nat.pow 2 n : Nat) : Core.Q)) := by
    positivity
  exact le_trans hCardErr <|
    mul_le_mul_of_nonneg_right pkg.hEpsLeInv hPowNonneg

/--
If one had `testsetCapacity < 1`, the old testset-capacity contradiction would
already follow from the abstract payload alone.
-/
theorem old_testset_endpoint_of_abstractSingletonDensityPayload_of_testsetCapacity_lt_one
    {n : Nat}
    (pkg : AbstractSingletonDensityPayload n)
    (hCap :
      LowerBounds.testsetCapacity
          (sc := pkg.sc)
          (T := naturalMismatchTestsetOfAbstractSingletonDensityPayload pkg)
        < 1) :
    False := by
  classical
  let T := naturalMismatchTestsetOfAbstractSingletonDensityPayload pkg
  let Y : Finset (Core.BitVec n → Bool) := {pkg.f}
  have hSubset : Y ⊆ LowerBounds.familyFinset (sc := pkg.sc) := by
    intro f hf
    have hfEq : f = pkg.f := by
      simpa [Y] using hf
    have hfFin : pkg.f ∈ LowerBounds.familyFinset (sc := pkg.sc) := by
      exact (LowerBounds.mem_familyFinset (sc := pkg.sc) (f := pkg.f)).2 pkg.hf
    simpa [Y, hfEq] using hfFin
  have hApprox :
      ∀ f ∈ Y,
        f ∈ Counting.ApproxOnTestset
          (R := pkg.sc.atlas.dict)
          (k := pkg.sc.k)
          (T := T) := by
    intro f hf
    have hfEq : f = pkg.f := by
      simpa [Y] using hf
    rw [hfEq]
    exact approxOnNaturalMismatchTestset_of_abstractSingletonDensityPayload pkg
  have hLarge :
      LowerBounds.testsetCapacity (sc := pkg.sc) (T := T) < Y.card := by
    simpa [Y, T] using hCap
  exact
    LowerBounds.no_bounded_atlas_on_testset_of_large_family
      (sc := pkg.sc)
      (T := T)
      (Y := Y)
      hSubset
      hApprox
      hLarge

/--
But the old testset-capacity hypothesis is impossible already for the abstract
payload, because it is impossible for every bounded atlas scenario.
-/
theorem naturalMismatchTestset_not_testsetCapacity_lt_one_of_abstractSingletonDensityPayload
    {n : Nat}
    (pkg : AbstractSingletonDensityPayload n) :
    ¬ LowerBounds.testsetCapacity
          (sc := pkg.sc)
          (T := naturalMismatchTestsetOfAbstractSingletonDensityPayload pkg)
        < 1 := by
  exact
    LowerBounds.not_testsetCapacity_lt_one
      (sc := pkg.sc)
      (T := naturalMismatchTestsetOfAbstractSingletonDensityPayload pkg)

/--
Current internal route reaches the abstract singleton-density payload.
-/
theorem abstractSingletonDensityPayload_of_internal_provider
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) :
    let pkg := Classical.choice (singletonDensityPackage_of_internal_provider hFormula)
    Nonempty (AbstractSingletonDensityPayload pkg.prov.pack.cert.ac0.n) := by
  classical
  intro pkg
  exact ⟨abstractSingletonDensityPayload_of_singletonDensityPackage pkg⟩

/--
Current internal route reaches the minimally strengthened abstract linked
singleton-density payload as well.
-/
theorem abstractLinkedSingletonDensityPayload_of_internal_provider
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) :
    let pkg := Classical.choice (singletonDensityPackage_of_internal_provider hFormula)
    Nonempty (AbstractLinkedSingletonDensityPayload pkg.prov.pack.cert.ac0.n) := by
  classical
  intro pkg
  exact ⟨abstractLinkedSingletonDensityPayload_of_singletonDensityPackage pkg⟩

/--
Current internal route also reaches the externally targeted abstract payload.
-/
theorem abstractTargetedSingletonDensityPayload_of_internal_provider
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) :
    let pkg := Classical.choice (singletonDensityPackage_of_internal_provider hFormula)
    Nonempty (
      AbstractTargetedSingletonDensityPayload
        pkg.prov.pack.cert.ac0.n
        (fun x =>
          ComplexityInterfaces.FormulaCircuit.eval
            ((Classical.choose hFormula).family (Models.partialInputLen p))
            (ThirdPartyFacts.castBitVec pkg.prov.pack.cert.hsame x))) := by
  classical
  intro pkg
  exact ⟨abstractTargetedSingletonDensityPayload_of_singletonDensityPackage pkg⟩

end LowerBounds
end Pnp3
