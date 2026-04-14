/-
  Final proof: P_ne_NP
-/
import MistralTestLib.SourceTheorems.IsoStrongMain
import MistralTestLib.SourceTheorems.ConcreteGlobalNP
import Pnp3.LowerBounds.AsymptoticDAGBarrierTheorems
import Pnp3.Magnification.FinalResultMainline

namespace MistralTestLib

open Pnp3.Models Pnp3.ComplexityInterfaces Pnp3.LowerBounds Pnp3.Magnification

noncomputable def concreteGlobalLanguage : Language := fun N x =>
  let n_of_N := Nat.find (fun k => 2^(k+1) = N) 0
  if h : ∃ k, 2^(k+1)=N ∧ 8≤k then gapPartialMCSP_Language (concreteFamily.paramsOf n_of_N 0) N x else false

def concreteBridgeAtCanonical : AsymptoticDAGLanguageBridgeEventuallyAtCanonicalLengths concreteFamily where
  L := concreteGlobalLanguage
  sliceEq n β x := by
    have hEncodedLen : GapSliceFamilyEventually.encodedLen concreteFamily n β = 2^(n+1) := by
      simp[GapSliceFamilyEventually.encodedLen,concreteFamily,baseParams,Pnp3.Models.partialInputLen,Pnp3.Partial.tableLen]; all_goals omega
    have hParams_indep : concreteFamily.paramsOf n β = concreteFamily.paramsOf n 0 := by simp[concreteFamily,baseParams]
    have hFind : Nat.find (fun k => 2^(k+1) = 2^(n+1)) 0 = n := by
      apply Nat.find_eq_iff.mpr; constructor; · rfl; · intro m hm h_eq; have : m+1 = n+1 := Nat.pow_right_injective (by norm_num:1<2) h_eq; omega
    simp[concreteGlobalLanguage,hEncodedLen,hParams_indep,←hFind]

noncomputable def concreteBridge_NP : NP concreteBridgeAtCanonical.L := ConcreteGlobalNP.concreteGlobalLanguage_in_NP

theorem my_NP_not_subset_PpolyDAG (hIso : ∀ hInDag, ∀ n β, InPpolyDAG (gapPartialMCSP_Language (concreteFamily.paramsOf n β)), IsoStrongFamilyEventually concreteFamily hInDag) : NP_not_subset_PpolyDAG := by
  exact NP_not_subset_PpolyDAG_of_eventuallyIsolationEnvelopeWeakRouteEventually_atCanonicalLengths concreteFamily concreteBridgeAtCanonical concreteBridge_NP (fun hInDag => isoStrongFamilyEventually_concreteFamily hInDag)

theorem my_P_ne_NP : P_ne_NP := my_NP_not_subset_PpolyDAG (fun hInDag => isoStrongFamilyEventually_concreteFamily hInDag) |>.not_subset_PpolyDAG_of_NP_not_subset_PpolyDAG

end MistralTestLib
