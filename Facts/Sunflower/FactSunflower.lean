import FactSunflower.Proof.Sunflower
import FactSunflower.Proof.Sunflower.Aux
import FactSunflower.Proof.Sunflower.RSpread

/-!
# External fact: classical sunflower lemma

This wrapper exposes the key statements from the standalone sunflower
package.  Downstream projects can simply import `FactSunflower` to gain
access to the named threshold, the existence theorem, and the auxiliary
structures used in the cover algorithm without pulling in the historical
boolean complexity prototype.
-/

namespace Facts
namespace Sunflower

export Sunflower (threshold HasSunflower sunflower_exists_classic
  sunflower_exists_of_fixedSize removeSupersets)
export Sunflower (SunflowerFam)
export Sunflower SunflowerFam (exists_of_large_family_classic
  cover_step_if_large card_removeCovered_le_sub_t card_removeCovered_le_sub_t'
  uniform_of_removeCovered card_removeCovered_lt exists_cover_step_strict
  exists_cover_until_threshold removeCovered)
end Sunflower
end Facts
