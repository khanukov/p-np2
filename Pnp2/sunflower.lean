import Pnp2.Sunflower.Sunflower

open Sunflower

/-! `sunflower.lean`
===================

This module simply re-exports `Pnp2.Sunflower.Sunflower` under the shorter
path `Pnp2.sunflower`.
-/

export Sunflower (IsSunflower HasSunflower sunflower_exists)
