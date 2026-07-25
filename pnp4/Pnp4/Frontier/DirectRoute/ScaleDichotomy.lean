import Pnp4.Frontier.DirectRoute.SimulationCalculus

/-!
# The whole difficulty in one parameter

`SimulationCalculus.lean` proved that the direct route is governed by a single
inequality,

```text
(1 - δ) · c ^ k   vs   1
```

where `c` is the exponent of the assumed `SAT` algorithm and `δ` is the gain of
the speedup arrow.  This module reads that inequality carefully, and the reading
is sharper than "the barriers make it hard".

## The reading

* **`c = 1` — the assumption is free.**  Then `(1-δ)·1^k = 1-δ`, and *any*
  positive gain closes the loop (`unit_cost_any_gain`).  At `δ = 0` the
  inequality is exactly tight (`boundary_at_unit_cost`): the calculus is silent,
  and the sub-polynomial (logarithmic) analysis decides the case.
* **`c > 1` — the assumption is paid for.**  The required gain is exactly
  `δ > 1 - c^(-k)` (`gain_threshold_exact`), which tends to `1` as `c` grows
  (`required_gain_unbounded`).

Now line this up with the literature.

| result | effective `c` | outcome |
|---|---|---|
| Paul–Pippenger–Szemerédi–Trotter, `NTIME[n] ≠ TIME[n]` | `1` by hypothesis | succeeds, at the boundary, using the `log`-level analysis |
| Williams, `NEXP ⊄ ACC⁰` | `1` by scale: at ambient resource `2^n`, a `poly(n)` overhead is `2^(o(n))`, i.e. negligible | succeeds |
| time–space tradeoffs for `SAT` | bounded, because the extra space hypothesis bounds it | succeeds partially: `n^1.8`, not superpolynomial |
| **`P` vs `NP`** | **unbounded** — `P = NP` supplies only *some* polynomial | `fixed_gain_insufficient` |

**Every direct separation ever obtained is a `c → 1` argument.**  That is not a
coincidence and it is not a list of unrelated barriers; it is one inequality.

## The consequence for where to look

To get a direct proof one must engineer `c → 1`.  There are exactly two ways to
do that, and only one of them is available:

1. **Bootstrap `c` downwards** — use `P = NP` to produce a *near-linear-time*
   `SAT` algorithm.  Not available: padding enlarges instances, so it moves the
   exponent the wrong way, and the Cook–Levin route is circular.
2. **Raise the ambient scale** until `poly(n)` is negligible.  At resource
   `2^(n^a)` an invocation of the assumed algorithm costs `poly(n)`, which is
   sub-polynomial in the resource — the effective `c` is `1`.  This is exactly
   why the algorithmic method works where it works.

Option 2 is real, and it has a price: the separation one proves at that scale is
`EXP ≠ NEXP`, which is *sufficient* for `P ≠ NP` (by padding) but strictly
stronger as far as anyone knows.  `ExponentialScalePort.lean` records that trade
explicitly.

Nothing here proves `P ≠ NP`.  What is proved is that the search should be
directed at regimes where the assumption is free, and that there is exactly one
such regime currently reachable.
-/

namespace Pnp4
namespace Frontier
namespace DirectRoute

open Resource

/-!
### `c = 1`: the assumption is free
-/

/--
**At unit cost any positive gain suffices.**

If the assumption costs nothing (`c = 1`), then every speedup arrow with a
strictly positive gain refutes it.  This is the regime of every successful
direct separation.
-/
theorem unit_cost_any_gain {k : Nat} {δ α : ℚ} (hδ : 0 < δ) (hα : 0 < α) :
    ∃ β : ℚ, β < α ∧ Derives 1 k δ (dtime α) (dtime β) := by
  refine contradiction_of_below_threshold (c := 1) (k := k) (δ := δ) ?_ hα
  have : (1 : ℚ) ^ k = 1 := one_pow k
  rw [this, mul_one]
  linarith

/--
**The boundary case.**

At `c = 1` and `δ = 0` the governing inequality is exactly tight, so the
exponent-level calculus says nothing either way.  This is precisely where
Paul–Pippenger–Szemerédi–Trotter and the algorithmic method operate: their gain
is a logarithmic factor, invisible at this resolution, and it is the finer
analysis that decides the case.
-/
theorem boundary_at_unit_cost {k : Nat} :
    (1 : ℚ) ≤ (1 - 0) * (1 : ℚ) ^ k := by
  simp

/-!
### `c > 1`: the exact price
-/

/--
**The exact gain threshold.**

A contradiction is derivable precisely when the gain exceeds `1 - c^(-k)`.
-/
theorem gain_threshold_exact {c δ : ℚ} {k : Nat} (hc : 0 < c) :
    (1 - δ) * c ^ k < 1 ↔ 1 - 1 / c ^ k < δ := by
  have hck : (0 : ℚ) < c ^ k := pow_pos hc k
  constructor
  · intro h
    have h1 : 1 - δ < 1 / c ^ k := by
      rw [lt_div_iff₀ hck]
      linarith
    linarith
  · intro h
    have h1 : 1 - δ < 1 / c ^ k := by linarith
    have h2 : (1 - δ) * c ^ k < (1 / c ^ k) * c ^ k :=
      mul_lt_mul_of_pos_right h1 hck
    have h3 : (1 / c ^ k) * c ^ k = 1 :=
      one_div_mul_cancel (ne_of_gt hck)
    linarith

/--
**The required gain is unbounded below `1`.**

For every target `g < 1` there is an assumption exponent `c` at which the
required gain exceeds `g`.  Combined with `gain_threshold_exact`, this is the
quantitative form of `fixed_gain_insufficient`: as the assumed `SAT` algorithm
gets slower, the speedup one would need approaches a *total* collapse of the
exponent.
-/
theorem required_gain_unbounded {k : Nat} (hk : 1 ≤ k) (g : ℚ)
    (hg0 : 0 ≤ g) (hg1 : g < 1) :
    ∃ c : ℚ, 1 ≤ c ∧ g ≤ 1 - 1 / c ^ k := by
  have hpos : (0 : ℚ) < 1 - g := by linarith
  refine ⟨1 / (1 - g), ?_, ?_⟩
  · rw [le_div_iff₀ hpos]; linarith
  · have hpow : (1 / (1 - g)) ^ k = 1 / (1 - g) ^ k := by
      rw [div_pow, one_pow]
    rw [hpow, one_div_one_div]
    have hbase : (0 : ℚ) < (1 - g) ^ k := pow_pos hpos k
    have hle : (1 - g) ^ k ≤ (1 - g) ^ 1 :=
      pow_le_pow_of_le_one (le_of_lt hpos) (by linarith) hk
    have : (1 - g) ^ k ≤ 1 - g := by simpa using hle
    linarith

/-!
### Summary predicate

The two escape routes, named so that a proposed technique can be classified
before any effort is spent on it.
-/

/--
A direct technique is *cost-free* at exponent `c` when the assumption does not
multiply the exponent, i.e. `c = 1`.

Every successful direct separation in the literature satisfies this, either by
hypothesis (PPST) or by ambient scale (the algorithmic method).
-/
def CostFree (c : ℚ) : Prop := c = 1

/-- At a cost-free exponent, any positive gain refutes the assumption. -/
theorem refutes_of_costFree {c : ℚ} (hc : CostFree c) {k : Nat} {δ α : ℚ}
    (hδ : 0 < δ) (hα : 0 < α) :
    ∃ β : ℚ, β < α ∧ Derives c k δ (dtime α) (dtime β) := by
  subst hc
  exact unit_cost_any_gain hδ hα

end DirectRoute
end Frontier
end Pnp4
