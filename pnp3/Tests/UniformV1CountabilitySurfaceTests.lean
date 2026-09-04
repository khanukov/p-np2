import Complexity.Uniform.V1.Countability

/-! Explicit P1c countability and direct-diagonal proposition surface. -/

namespace Pnp3.Tests.UniformV1Countability

open Pnp3.Complexity.Uniform.V1

#check UniformTM.data
#check UniformTM.data_injective
#check uniformTM_countable
#check machineLanguage
#check machineLanguage_eq_of_decidesAt
#check uniformP_exists_machineLanguage
#check uniformP_languages_countable
#check lengthOnly
#check lengthOnly_injective
#check exists_lengthOnly_not_mem
#check exists_lengthOnly_not_uniformP
#check not_forall_lengthOnly_uniformP

#synth Countable Move
#synth Countable UniformTM
#synth Countable (UniformTM × Nat)

theorem check_data_injective : Function.Injective UniformTM.data :=
  UniformTM.data_injective

theorem check_uniformTM_countable : Countable UniformTM :=
  uniformTM_countable

theorem check_machineLanguage_eq_of_decidesAt (M : UniformTM) (c : Nat)
    {n : Nat} (x : Bitstring n) (answer : Bool)
    (h : DecidesAt M (polyClock c n) (polyClock c n) x answer) :
    machineLanguage M c n x = answer :=
  machineLanguage_eq_of_decidesAt M c x answer h

theorem check_uniformP_exists_machineLanguage (L : Language) (h : UniformP L) :
    ∃ M c, L = machineLanguage M c :=
  uniformP_exists_machineLanguage L h

theorem check_uniformP_languages_countable :
    Set.Countable {L : Language | UniformP L} :=
  uniformP_languages_countable

theorem check_lengthOnly_injective : Function.Injective lengthOnly :=
  lengthOnly_injective

theorem check_exists_lengthOnly_not_mem {S : Set Language} (hS : S.Countable) :
    ∃ A : Nat → Bool, lengthOnly A ∉ S :=
  exists_lengthOnly_not_mem hS

theorem check_exists_lengthOnly_not_uniformP :
    ∃ A : Nat → Bool, ¬ UniformP (fun n _ => A n) :=
  exists_lengthOnly_not_uniformP

theorem check_not_forall_lengthOnly_uniformP :
    ¬ ∀ A : Nat → Bool, UniformP (fun n _ => A n) :=
  not_forall_lengthOnly_uniformP

end Pnp3.Tests.UniformV1Countability
