import Magnification.FinalResult
import ThirdPartyFacts.Facts_Switching

open Pnp3
open Pnp3.Magnification

-- Ключевые точки для аудита аксиом в финальной цепочке.
-- Если здесь всплывают проектные axioms, это сигнал, что цепочка ещё условная.
#print axioms ThirdPartyFacts.partial_shrinkage_for_AC0
#print axioms ThirdPartyFacts.shrinkage_for_localCircuit
#print axioms NP_not_subset_PpolyFormula_final
