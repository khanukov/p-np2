import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Card
import Pnp.Sunflower.Sunflower

/--!
This file re-exports the classical sunflower lemma from the legacy `Pnp` development. Importing `Pnp.Sunflower.Sunflower` provides the definitions `Sunflower.IsSunflower` and `Sunflower.HasSunflower` together with the theorem `Sunflower.sunflower_exists`. The goal is to keep the modern `Pnp2` library lightweight while relying on the proven result without duplicating its original proof or introducing an axiom.
-/

