import Pnp4.Frontier.SequentialMagnification.SizeParameterPadding

/-!
# The size-parameter gap, and why padding does not close it

## The frontier in two numbers

On the sequential route, the distance between the published state of the art
and `P ≠ NP` is *not* a missing technique and *not* a missing time exponent.
It is a gap between two constants in the MCSP **size parameter**.

| | size parameter | model | time exponent |
|---|---|---|---|
| McKay–Murray–Williams, magnification (needs) | `2 ^ (μ₁ · n)`, `μ₁` small | `DTIME₁` | `N ^ 1.01` |
| Cheraghchi–Hirahara–Myrisiotis–Yoshida, proved | `2 ^ (μ₂ · n)`, `μ₂ ≈ 1` | `BPTIME₁` | `N ^ 1.99` |

The *time* side is already won with room to spare: `1.99 > 1.01`, and the
proved bound even holds for randomised machines, which is stronger than the
deterministic bound the magnification needs.  `time_exponents_are_compatible`
below records that comparison.

What blocks the conclusion is `μ₂ > μ₁`.  In the authors' words: *"what is
missing for proving P ≠ NP is to decrease the size parameter from
`2 ^ ((1 - o(1)) · n)` to `2 ^ (o(n))` in Theorem 2, or to increase the size
parameter from `2 ^ (o(n))` to `2 ^ ((1 - o(1)) · n)` in Theorem 1."*

## Why the obvious fix fails

`SizeParameterPadding.lean` proves that padding a function with dummy variables
preserves circuit complexity *exactly*.  So a hard instance at `n` variables
with absolute threshold `T` becomes a hard instance at `n' = k · n` variables
with the *same* absolute threshold `T`, i.e. with relative exponent divided by
`k`.  Padding therefore moves in exactly the required direction: from the large
`μ₂` where hardness is proved, down towards the small `μ₁` where magnification
applies.

The catch is the input length.  A truth table of length `N = 2 ^ n` becomes one
of length `N' = 2 ^ (k · n) = N ^ k`.  A time-`N' ^ β` algorithm at the padded
slice is a time-`N ^ (k · β)` algorithm at the original slice, so a proved lower
bound of `N ^ α` at `μ₂` only survives as `N' ^ (α / k)` at `μ₁`.

Matching the exponents forces `μ₁ · k = μ₂`, hence `k ≥ 2` whenever
`μ₁ < μ₂`, hence a transferred exponent of at most `1.99 / 2 = 0.995`, which is
already **below** the magnification threshold `1.01`.

`padding_cannot_close_size_parameter_gap` states this as kernel-checked
arithmetic: a single doubling of the variable count already destroys the bound,
long before one gets anywhere near the true ratio `μ₂ / μ₁ = ω(1)`.

## Status of this module

This is a **no-go module**, in the same spirit as
`pnp3/LowerBounds/FailedRoute_FixedSliceSupportHalfCore.lean`.  It closes the
cheapest idea for bridging the gap, so that future work is not spent on it.

The arithmetic model here is *generous* to the padding route: it charges only
the exponent blowup and ignores the cost of physically producing the padded
truth table on a one-tape machine, which can only make the transfer worse.
Since the conclusion is negative, being generous is the right direction.
-/

namespace Pnp4
namespace Frontier
namespace SequentialMagnification

/-!
### The published constants

Exponents are recorded as integers scaled by `exponentDenom = 100`, so that all
comparisons are decidable natural-number arithmetic.
-/

/-- Common denominator for the recorded time exponents. -/
def exponentDenom : Nat := 100

/-- `1.01`: the time exponent in the MMW/CHMY magnification hypothesis. -/
def mmwTimeExponentNum : Nat := 101

/-- `1.99`: the time exponent of the CHMY unconditional lower bound. -/
def chmyTimeExponentNum : Nat := 199

/--
The *time* side of the frontier is already settled: the proved exponent
strictly exceeds the exponent that magnification requires.

This is why the remaining obstruction is entirely in the size parameter.
-/
theorem time_exponents_are_compatible :
    mmwTimeExponentNum < chmyTimeExponentNum := by
  decide

/-!
### Padding arithmetic
-/

/--
Padding from `n` to `k * n` variables raises the truth-table length to the
`k`-th power: `N' = N ^ k`.
-/
theorem padded_table_length (n k : Nat) :
    Pnp3.Models.Partial.tableLen (k * n)
      = (Pnp3.Models.Partial.tableLen n) ^ k := by
  simp [Pnp3.Models.Partial.tableLen, Nat.mul_comm k n, Nat.pow_mul]

/--
Size-parameter matching equation.

Padding turns the threshold `2 ^ (μ₂ · n)` at `n` variables into the threshold
`2 ^ (μ₁ · n')` at `n' = k · n` variables exactly when `μ₁ · k = μ₂`.
-/
theorem size_parameter_match (mu1 mu2 k n : Nat) (hmatch : mu1 * k = mu2) :
    2 ^ (mu1 * (k * n)) = 2 ^ (mu2 * n) := by
  rw [← Nat.mul_assoc, hmatch]

/--
Strictly decreasing the size-parameter exponent forces at least a doubling of
the variable count.
-/
theorem blowup_at_least_two (mu1 mu2 k : Nat)
    (hmatch : mu1 * k = mu2) (hlt : mu1 < mu2) :
    2 ≤ k := by
  by_contra hk
  have hk1 : k ≤ 1 := by omega
  have : mu1 * k ≤ mu1 * 1 := Nat.mul_le_mul_left mu1 hk1
  omega

/--
**Padding no-go, arithmetic core.**

After a `k`-fold blowup of the variable count the proved exponent `1.99` is
transferred as `1.99 / k`; for `k ≥ 2` that is strictly below the required
`1.01`, i.e. `chmyTimeExponentNum < mmwTimeExponentNum * k`.
-/
theorem transferred_exponent_too_small (k : Nat) (hk : 2 ≤ k) :
    chmyTimeExponentNum < mmwTimeExponentNum * k := by
  unfold chmyTimeExponentNum mmwTimeExponentNum
  have : 101 * 2 ≤ 101 * k := Nat.mul_le_mul_left 101 hk
  omega

/--
**Padding no-go.**

If padding is used to move a lower bound from size-parameter exponent `μ₂` down
to `μ₁ < μ₂`, the required variable blowup `k` satisfies `μ₁ · k = μ₂` and
`k ≥ 2`, and therefore the transferred time exponent falls strictly below the
magnification threshold.

Consequently the exact padding lemma of `SizeParameterPadding.lean`, although
it moves in the right direction on the size parameter, cannot combine the two
published theorems into `P ≠ NP`.
-/
theorem padding_cannot_close_size_parameter_gap
    (mu1 mu2 k : Nat) (hmatch : mu1 * k = mu2)
    (hlt : mu1 < mu2) :
    chmyTimeExponentNum < mmwTimeExponentNum * k :=
  transferred_exponent_too_small k (blowup_at_least_two mu1 mu2 k hmatch hlt)

/--
The only blowup factor that preserves the time exponent is the trivial one,
and it preserves the size parameter too — i.e. it does nothing.
-/
theorem trivial_blowup_is_useless (mu1 mu2 : Nat) (hmatch : mu1 * 1 = mu2) :
    mu1 = mu2 := by
  omega

/-!
### What would actually close the gap

The no-go above is specific to *padding*.  It leaves exactly the two moves that
the source authors themselves name, plus one structural alternative:

1. **Lower `μ₂`.**  Prove a one-tape / streaming lower bound for `MCSP[2 ^ (μ · n)]`
   at a small `μ`.  The published proof goes through a *local* hitting-set
   generator whose seed length is `Õ(√N)`, which forces `μ ≥ 1/2`; lowering `μ`
   means constructing a local HSG with seed length `N ^ o(1)` against read-once
   oblivious branching programs.
2. **Raise `μ₁`.**  Extend magnification to larger size parameters.  CHMY
   Theorem 3 shows this is impossible for `μ > 1/2` *by the existing technique*
   (near-linear-time oracle algorithms with `N ^ o(1)`-length queries), so any
   such extension needs a genuinely new magnification mechanism.
3. **Change the weak model.**  The magnification theorem is stated for one-pass
   streaming algorithms; the lower-bound literature is strongest for read-once
   models.  `StreamingLowerBounds.lean` shows the streaming model admits
   unconditional exponential memory lower bounds by elementary means, which is
   not true of the non-uniform classes used elsewhere in this repository.

Note that (1) and (2) meet at `μ = 1/2`, and that `1/2` is exactly the seed-length
exponent of the best known pseudorandom generators for read-once oblivious
branching programs.  The size-parameter gap is, in that precise sense, a
pseudorandomness question rather than a circuit-complexity question.
-/

end SequentialMagnification
end Frontier
end Pnp4
