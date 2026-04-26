import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace Pnp4
namespace AlgorithmsToLowerBounds

/--
The lower-bound schedule `lower` eventually beats every polynomial-size
schedule `N ↦ c * N^k`.
-/
def SuperPolynomialGrowth (lower : Nat → Nat) : Prop :=
  ∀ c k : Nat, ∃ N0 : Nat, ∀ N : Nat,
    N0 ≤ N →
      c * N ^ k < lower N

/--
Integer quasi-polynomial lower bound used as the normalized weak form of
published super-polynomial lower bounds.
-/
def QuasiPolyLower (N : Nat) : Nat :=
  N ^ Nat.log2 N

/-- Eventual domination between natural-number schedules. -/
def EventuallyDominates (f g : Nat → Nat) : Prop :=
  ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N → g N ≤ f N

/-- A concrete cutoff sufficient for `QuasiPolyLower` to beat `c * N^k`. -/
def quasiPolyThreshold (c k : Nat) : Nat :=
  2 ^ (k + c + 3)

/--
The quasi-polynomial schedule `N^log₂N` is super-polynomial.

This is the bridge arithmetic we want to keep unconditional: for every
polynomial witness `c * N^k`, sufficiently large `N` satisfies
`c * N^k < N^log₂N`.
-/
theorem quasiPolyLower_superPolynomialGrowth :
    SuperPolynomialGrowth QuasiPolyLower := by
  intro c k
  refine ⟨quasiPolyThreshold c k, ?_⟩
  intro N hN
  have hN_pos : 0 < N := by
    have hpow_pos : 0 < 2 ^ (k + c + 3) := Nat.two_pow_pos _
    exact lt_of_lt_of_le hpow_pos hN
  have hN_two : 2 ≤ N := by
    have hExp : 1 ≤ k + c + 3 := by omega
    have hTwoLeThreshold : 2 ≤ quasiPolyThreshold c k := by
      simpa [quasiPolyThreshold] using
        Nat.pow_le_pow_right (by decide : 0 < 2) hExp
    exact le_trans hTwoLeThreshold hN
  have hlog :
      k + c + 2 ≤ Nat.log2 N := by
    have hpow :
        2 ^ (k + c + 2) ≤ N := by
      have hstep :
          2 ^ (k + c + 2) ≤ 2 ^ (k + c + 3) := by
        exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
      exact le_trans hstep hN
    exact (Nat.le_log2 (Nat.ne_of_gt hN_pos)).2 hpow
  have hc_le_pow : c ≤ N ^ (c + 1) := by
    have hc_lt_two : c < 2 ^ c := by
      simpa using (Nat.lt_two_pow_self (n := c))
    have hc_le_two : c ≤ 2 ^ c := Nat.le_of_lt hc_lt_two
    have htwo_le_N : 2 ^ c ≤ N ^ c := by
      exact Nat.pow_le_pow_left hN_two c
    have hNc_le : N ^ c ≤ N ^ (c + 1) := by
      exact Nat.pow_le_pow_right (by omega : 0 < N) (by omega)
    exact le_trans hc_le_two (le_trans htwo_le_N hNc_le)
  have hmul :
      c * N ^ k ≤ N ^ (c + 1) * N ^ k := by
    exact Nat.mul_le_mul_right _ hc_le_pow
  have hpow_mul :
      N ^ (c + 1) * N ^ k = N ^ ((c + 1) + k) := by
    exact (Nat.pow_add N (c + 1) k).symm
  have hexp_lt :
      (c + 1) + k < Nat.log2 N := by
    omega
  have hpow_lt :
      N ^ ((c + 1) + k) < N ^ Nat.log2 N := by
    exact Nat.pow_lt_pow_right (by omega : 1 < N) hexp_lt
  calc
    c * N ^ k
        ≤ N ^ (c + 1) * N ^ k := hmul
    _ = N ^ ((c + 1) + k) := hpow_mul
    _ < N ^ Nat.log2 N := hpow_lt

end AlgorithmsToLowerBounds
end Pnp4
