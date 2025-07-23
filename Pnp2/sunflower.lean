import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Card
import Pnp2.Sunflower.Sunflower

/--!
This file re-exports the classical sunflower lemma now formalised within the
`Pnp2` namespace. Importing `Pnp2.Sunflower.Sunflower` provides the definitions
`Sunflower.IsSunflower` and `Sunflower.HasSunflower` together with the theorem
`Sunflower.sunflower_exists`.  Keeping a small wrapper avoids sprinkling the
longer path throughout the rest of the library.
-/

