import OldAttempts.Sunflower.Sunflower

/-! `sunflower.lean`
===================

This module simply re-exports `OldAttempts.Sunflower.Sunflower` under the shorter
path `OldAttempts.sunflower`.
-/

export Sunflower (threshold IsSunflower HasSunflower sunflower_exists_classic
  sunflower_exists_two sunflower_exists_of_fixedSize SunflowerFam)
