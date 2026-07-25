import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.EquivFin
import Pnp4.Frontier.SequentialMagnification.LocalHSG

/-!
# The window test: why the local-HSG route needs a seed longer than the memory budget

`LocalHSG.lean` reduces the port's hypothesis to the existence of a local
hitting-set generator secure against space-bounded one-pass tests.  This module
audits that reduction and finds a hard constraint on its parameters.

## The test

A one-pass device can remember the **last `w` bits** of its input with a shift
register and nothing else: `2 ^ w` states, no counter needed.  Given a generator
with `2 ^ seedLen` seeds, take `w = seedLen + 1`.  The set `P` of last-`w`
windows realised by generator outputs has `|P| ≤ 2 ^ seedLen = 2 ^ w / 2`, so the
test

> accept iff the last `w` bits are **not** a realised window

rejects every output of the generator and still accepts at least half of all
truth tables.

Hence `HitsStreamingTests G space` is **false** as soon as
`space ≥ seedLen + 1`.

## Consequence for the route

Combining with `seedLength_bound_of_injective_localGenerator`
(`2 ^ seedLen ≤ circuitCountBound n s`, the price of locality), a usable local
HSG must satisfy

```text
space  <  seedLen + 1   ≤   log₂(circuitCountBound n s) + 1  ≈  Õ(s)
```

i.e. **the memory budget it defeats must be smaller than its own seed length.**

But the budget supplied by the magnification contract is `space = p(s)` for the
polynomial `p` of McKay–Murray–Williams, and `p(s) ≥ s` (the algorithm has to
hold a size-`s` circuit at all).  So the route survives only in the knife-edge
regime where `p` is essentially linear; for any `p` of degree `> 1` it is
closed.

This matches the published convention exactly.  Cheraghchi–Hirahara–Myrisiotis–
Yoshida define a local generator as `G : {0,1}^s → {0,1}^N` whose output bits are
computed by circuits of size at most `s` — *the seed length and the size
parameter are the same `s`*.  Their generator therefore cannot fool a class
whose resource bound exceeds `s`, which is precisely what the theorem below
says in the space-bounded setting.

## What this does and does not kill

* It closes the **local-HSG sufficient condition** of `LocalHSG.lean` at the
  parameters the port needs, in the *non-uniform space-bounded* test class used
  here.  `LocalHSG.MCSPStreamingHard_of_localHSG` remains true; its hypothesis
  is just unreachable at those parameters.
* It does **not** touch `MCSPStreamingHard` itself, which is the port's actual
  obligation.  The window test rejects one finite set; it does not decide MCSP.
* The escape hatch is the test class.  The window test is non-uniform: `P` is
  hardwired.  McKay–Murray–Williams produce a *uniform* streaming algorithm with
  bounded update time, and a uniform test cannot hardwire an arbitrary `P`.
  Restricting `SpaceBoundedStreaming` to bounded-update-time / uniform devices
  is therefore the repair, and it is also the more faithful model.

This is a **no-go module**: it exists to stop the local-HSG route from being
pursued at the wrong parameters.
-/

namespace Pnp4
namespace Frontier
namespace SequentialMagnification

open Pnp4.AlgorithmsToLowerBounds

/-!
### The shift register
-/

/-- Shift a new bit into a window of the last `w` bits (index `w-1` is newest). -/
def shiftIn {w : Nat} (arr : Fin w → Bool) (b : Bool) : Fin w → Bool :=
  fun i => if h : (i : Nat) + 1 < w then arr ⟨(i : Nat) + 1, h⟩ else b

/-- The one-pass test "the last `w` bits do not form a window in `P`". -/
def windowAlgo {w : Nat} (P : Finset (Fin w → Bool)) :
    StreamingAlgo (Fin w → Bool) where
  init := fun _ => false
  step := shiftIn
  accept := fun arr => decide (arr ∉ P)

/--
State of the shift register after reading `l` from `arr`: coordinate `i` holds
the input bit `l[i + |l| - w]` once enough bits have been read, and otherwise
still holds the initial content.
-/
lemma runFrom_windowAlgo {w : Nat} (P : Finset (Fin w → Bool))
    (arr : Fin w → Bool) (l : List Bool) (i : Fin w) :
    (windowAlgo P).runFrom arr l i
      = if h : (i : Nat) + l.length < w then arr ⟨(i : Nat) + l.length, h⟩
        else l.getD ((i : Nat) + l.length - w) false := by
  induction l generalizing arr with
  | nil => simp
  | cons b bs ih =>
      have hstep : (windowAlgo P).runFrom arr (b :: bs)
          = (windowAlgo P).runFrom (shiftIn arr b) bs := rfl
      rw [hstep, ih (shiftIn arr b)]
      by_cases h₁ : (i : Nat) + bs.length < w
      · rw [dif_pos h₁]
        by_cases h₂ : (i : Nat) + (b :: bs).length < w
        · rw [dif_pos h₂]
          have hlt : ((i : Nat) + bs.length) + 1 < w := by
            simp [List.length_cons] at h₂; omega
          simp only [shiftIn, dif_pos hlt]
          refine congrArg arr (Fin.ext ?_)
          have hlen : (b :: bs).length = bs.length + 1 := rfl
          simp only [hlen]
          omega
        · rw [dif_neg h₂]
          have hlen : (b :: bs).length = bs.length + 1 := rfl
          have heq : (i : Nat) + bs.length + 1 = w := by
            rw [hlen] at h₂; omega
          have hnot : ¬ ((i : Nat) + bs.length + 1 < w) := by omega
          have hidx : (i : Nat) + (b :: bs).length - w = 0 := by
            rw [hlen]; omega
          simp only [shiftIn, dif_neg hnot]
          rw [show (i : Nat) + (b :: bs).length - w = 0 from hidx]
          simp
      · rw [dif_neg h₁]
        have hlen : (b :: bs).length = bs.length + 1 := rfl
        have h₂ : ¬ ((i : Nat) + (b :: bs).length < w) := by
          rw [hlen]; omega
        rw [dif_neg h₂]
        have hpos : 0 < (i : Nat) + (b :: bs).length - w := by
          rw [hlen]; omega
        have hidx : (i : Nat) + (b :: bs).length - w
            = ((i : Nat) + bs.length - w) + 1 := by
          rw [hlen]; omega
        rw [hidx]
        simp

/-- On inputs at least `w` long the register holds exactly the last `w` bits. -/
lemma run_windowAlgo {w : Nat} (P : Finset (Fin w → Bool))
    (l : List Bool) (hl : w ≤ l.length) (i : Fin w) :
    (windowAlgo P).run l i = l.getD ((i : Nat) + l.length - w) false := by
  have hnot : ¬ ((i : Nat) + l.length < w) := by
    have := i.2; omega
  simpa [StreamingAlgo.run, hnot] using
    runFrom_windowAlgo P (fun _ => false) l i


/-!
### The window of a truth table
-/

open Pnp3.Models.Partial in
/-- The last `w` coordinates of a truth table. -/
def windowOf {n w : Nat} (hw : w ≤ tableLen n) (tt : TruthTable n) :
    Fin w → Bool :=
  fun i => tt ⟨(i : Nat) + tableLen n - w, by have := i.2; omega⟩

open Pnp3.Models.Partial in
/-- Overwrite the last `w` coordinates of a truth table. -/
def replaceWindow {n w : Nat} (hw : w ≤ tableLen n) (tt : TruthTable n)
    (v : Fin w → Bool) : TruthTable n :=
  fun j =>
    if h : tableLen n - w ≤ (j : Nat) then
      v ⟨(j : Nat) - (tableLen n - w), by have := j.2; omega⟩
    else tt j

open Pnp3.Models.Partial in
@[simp] lemma windowOf_replaceWindow {n w : Nat} (hw : w ≤ tableLen n)
    (tt : TruthTable n) (v : Fin w → Bool) :
    windowOf hw (replaceWindow hw tt v) = v := by
  funext i
  have hi := i.2
  have hle : tableLen n - w ≤ (i : Nat) + tableLen n - w := by omega
  simp only [windowOf, replaceWindow, dif_pos hle]
  refine congrArg v (Fin.ext ?_)
  show (i : Nat) + tableLen n - w - (tableLen n - w) = (i : Nat)
  omega

open Pnp3.Models.Partial in
lemma replaceWindow_lo {n w : Nat} (hw : w ≤ tableLen n) (tt : TruthTable n)
    (v : Fin w → Bool) (j : Fin (tableLen n)) (hj : (j : Nat) < tableLen n - w) :
    replaceWindow hw tt v j = tt j := by
  simp only [replaceWindow, dif_neg (by omega : ¬ tableLen n - w ≤ (j : Nat))]

open Pnp3.Models.Partial in
lemma eq_windowOf_hi {n w : Nat} (hw : w ≤ tableLen n) (tt : TruthTable n)
    (j : Fin (tableLen n)) (hj : tableLen n - w ≤ (j : Nat)) :
    tt j = windowOf hw tt ⟨(j : Nat) - (tableLen n - w), by have := j.2; omega⟩ := by
  have hj2 := j.2
  simp only [windowOf]
  refine congrArg tt (Fin.ext ?_)
  show (j : Nat) = (j : Nat) - (tableLen n - w) + tableLen n - w
  omega

/-!
### The window test as a space-bounded solver
-/

/-- The window test packaged with its `w`-bit memory budget. -/
def windowSolver {w : Nat} (P : Finset (Fin w → Bool)) :
    SpaceBoundedStreaming w where
  State := Fin w → Bool
  fintypeState := inferInstance
  card_le := by simp
  algo := windowAlgo P

open Pnp3.Models.Partial in
lemma decideOn_windowSolver {n w : Nat} (hw : w ≤ tableLen n)
    (P : Finset (Fin w → Bool)) (tt : TruthTable n) :
    (windowSolver P).decideOn (tableStream tt)
      = decide (windowOf hw tt ∉ P) := by
  have hlen : (tableStream tt).length = tableLen n := by simp
  have hrun : (windowAlgo P).run (tableStream tt) = windowOf hw tt := by
    funext i
    have hi := i.2
    have hge : w ≤ (tableStream tt).length := by rw [hlen]; omega
    rw [run_windowAlgo P (tableStream tt) hge i, hlen]
    have hlt : (i : Nat) + tableLen n - w < (tableStream tt).length := by
      rw [hlen]; omega
    rw [List.getD_eq_getElem (tableStream tt) false hlt]
    simp [tableStream, windowOf]
  show (windowAlgo P).accept ((windowAlgo P).run (tableStream tt)) = _
  rw [hrun]
  rfl

/-!
### Largeness of the window test
-/

open Pnp3.Models.Partial in
/-- Truth tables whose last-`w` window lies in `P`. -/
noncomputable def windowRejected {n w : Nat} (hw : w ≤ tableLen n)
    (P : Finset (Fin w → Bool)) : Finset (TruthTable n) :=
  Finset.univ.filter (fun tt => windowOf hw tt ∈ P)

open Pnp3.Models.Partial in
lemma acceptedTables_windowSolver {n w : Nat} (hw : w ≤ tableLen n)
    (P : Finset (Fin w → Bool)) :
    acceptedTables (windowSolver P) n
      = Finset.univ.filter (fun tt : TruthTable n => ¬ (windowOf hw tt ∈ P)) := by
  ext tt
  simp [acceptedTables, decideOn_windowSolver hw]

open Pnp3.Models.Partial in
lemma card_windowRejected_add {n w : Nat} (hw : w ≤ tableLen n)
    (P : Finset (Fin w → Bool)) :
    (acceptedTables (windowSolver P) n).card + (windowRejected hw P).card
      = Fintype.card (TruthTable n) := by
  classical
  have h := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (TruthTable n)))
      (p := fun tt => windowOf hw tt ∈ P)
  rw [Finset.card_univ] at h
  rw [acceptedTables_windowSolver hw, windowRejected]
  omega

open Pnp3.Models.Partial in
/--
**The window test is large.**

If `P` covers at most half of the `2 ^ w` possible windows, the test accepts at
least half of all truth tables.

The proof is an injection: replace the window of a rejected table by its image
under an injection `P ↪ Pᶜ`, which exists because `|P| ≤ 2 ^ w - |P|`.
-/
theorem largeAcceptance_windowSolver {n w : Nat} (hw : w ≤ tableLen n)
    (P : Finset (Fin w → Bool)) (hP : 2 * P.card ≤ 2 ^ w) :
    LargeAcceptance (windowSolver P) n := by
  classical
  -- `Pᶜ` has at least as many elements as `P`.
  have hcompl : P.card + Pᶜ.card = 2 ^ w := by
    have := Finset.card_add_card_compl P
    simpa [Fintype.card_fun] using this
  have hle : P.card ≤ Pᶜ.card := by omega
  obtain ⟨Q, hQsub, hQcard⟩ := Finset.exists_subset_card_eq hle
  -- an injection `P → Q`
  let e : {x // x ∈ P} ≃ {x // x ∈ Q} := Finset.equivOfCardEq hQcard.symm
  have he_inj : Function.Injective e := e.injective
  let iota : (Fin w → Bool) → (Fin w → Bool) := fun v =>
    if h : v ∈ P then ((e ⟨v, h⟩ : {x // x ∈ Q}) : Fin w → Bool) else v
  have hiota_notP : ∀ v, ∀ h : v ∈ P, iota v ∉ P := by
    intro v h
    have hmem : ((e ⟨v, h⟩ : {x // x ∈ Q}) : Fin w → Bool) ∈ Q :=
      (e ⟨v, h⟩).2
    have : ((e ⟨v, h⟩ : {x // x ∈ Q}) : Fin w → Bool) ∈ Pᶜ := hQsub hmem
    simpa [iota, h] using Finset.mem_compl.mp this
  have hiota_inj : ∀ v₁ ∈ P, ∀ v₂ ∈ P, iota v₁ = iota v₂ → v₁ = v₂ := by
    intro v₁ h₁ v₂ h₂ hv
    simp only [iota, dif_pos h₁, dif_pos h₂] at hv
    have : e ⟨v₁, h₁⟩ = e ⟨v₂, h₂⟩ := Subtype.ext hv
    exact congrArg Subtype.val (he_inj this)
  -- the table-level injection
  let F : TruthTable n → TruthTable n :=
    fun tt => replaceWindow hw tt (iota (windowOf hw tt))
  have hmaps : ∀ tt ∈ windowRejected hw P,
      F tt ∈ acceptedTables (windowSolver P) n := by
    intro tt htt
    have hmem : windowOf hw tt ∈ P := by
      simpa [windowRejected] using htt
    rw [acceptedTables_windowSolver hw]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, F,
      windowOf_replaceWindow]
    exact hiota_notP _ hmem
  have hinj : Set.InjOn F (windowRejected hw P) := by
    intro tt₁ h₁ tt₂ h₂ hF
    have hm₁ : windowOf hw tt₁ ∈ P := by
      simpa [windowRejected] using h₁
    have hm₂ : windowOf hw tt₂ ∈ P := by
      simpa [windowRejected] using h₂
    have hwin : windowOf hw tt₁ = windowOf hw tt₂ := by
      have := congrArg (windowOf hw) hF
      simp only [F, windowOf_replaceWindow] at this
      exact hiota_inj _ hm₁ _ hm₂ this
    funext j
    by_cases hj : tableLen n - w ≤ (j : Nat)
    · rw [eq_windowOf_hi hw tt₁ j hj, eq_windowOf_hi hw tt₂ j hj, hwin]
    · have e₁ : F tt₁ j = tt₁ j := replaceWindow_lo hw _ _ j (by omega)
      have e₂ : F tt₂ j = tt₂ j := replaceWindow_lo hw _ _ j (by omega)
      rw [← e₁, ← e₂, hF]
  have hcard : (windowRejected hw P).card
      ≤ (acceptedTables (windowSolver P) n).card :=
    Finset.card_le_card_of_injOn F hmaps hinj
  have hsum := card_windowRejected_add hw P
  unfold LargeAcceptance
  omega

/-!
### The no-go
-/

open Pnp3.Models.Partial in
/-- Windows realised by the outputs of a generator. -/
noncomputable def generatorWindows {n s seedLen w : Nat} (hw : w ≤ tableLen n)
    (G : LocalGenerator n s seedLen) : Finset (Fin w → Bool) :=
  Finset.univ.image (fun z : Fin seedLen → Bool => windowOf hw (G.gen z))

open Pnp3.Models.Partial in
lemma card_generatorWindows_le {n s seedLen w : Nat} (hw : w ≤ tableLen n)
    (G : LocalGenerator n s seedLen) :
    (generatorWindows hw G).card ≤ 2 ^ seedLen := by
  have h := Finset.card_image_le
    (s := (Finset.univ : Finset (Fin seedLen → Bool)))
    (f := fun z => windowOf hw (G.gen z))
  have huniv : (Finset.univ : Finset (Fin seedLen → Bool)).card = 2 ^ seedLen := by
    simp
  rw [huniv] at h
  exact h

open Pnp3.Models.Partial in
/--
**No-go for the local-HSG sufficient condition.**

A generator with `2 ^ seedLen` seeds cannot hit the window test at width
`seedLen + 1`.  Hence `HitsStreamingTests G space` fails for every memory budget
`space ≥ seedLen + 1`, as long as the window fits inside the truth table.

Consequence: a usable local hitting-set generator must have a seed **longer**
than the memory budget it defeats.  Combined with
`seedLength_bound_of_injective_localGenerator`
(`2 ^ seedLen ≤ circuitCountBound n s`), the local-HSG route to
`MCSPStreamingHard` is available only when the magnification budget `p(s)`
stays below `log₂ (circuitCountBound n s) + 1`.
-/
theorem not_hitsStreamingTests_of_space_ge_seed
    {n s seedLen space : Nat} (G : LocalGenerator n s seedLen)
    (hfit : seedLen + 1 ≤ tableLen n) (hspace : seedLen + 1 ≤ space) :
    ¬ HitsStreamingTests G space := by
  classical
  intro hHit
  set w := seedLen + 1 with hwdef
  have hw : w ≤ tableLen n := hfit
  set P := generatorWindows (w := w) hw G with hPdef
  have hPcard : P.card ≤ 2 ^ seedLen := card_generatorWindows_le hw G
  have hhalf : 2 * P.card ≤ 2 ^ w := by
    have : 2 * P.card ≤ 2 * 2 ^ seedLen := by omega
    simpa [hwdef, pow_succ, Nat.mul_comm] using this
  -- the window test, widened to the ambient budget
  have hlarge : LargeAcceptance (windowSolver P) n :=
    largeAcceptance_windowSolver hw P hhalf
  have hlarge' : LargeAcceptance ((windowSolver P).widen hspace) n := by
    unfold LargeAcceptance acceptedTables at hlarge ⊢
    simp only [SpaceBoundedStreaming.decideOn_widen]
    exact hlarge
  obtain ⟨z, hz⟩ := hHit ((windowSolver P).widen hspace) hlarge'
  have hz' : (windowSolver P).decideOn (tableStream (G.gen z)) = true := by
    simpa using hz
  rw [decideOn_windowSolver hw] at hz'
  have hmem : windowOf hw (G.gen z) ∈ P := by
    refine Finset.mem_image.mpr ⟨z, Finset.mem_univ z, rfl⟩
  simp [hmem] at hz'

open Pnp3.Models.Partial in
/--
Contrapositive, stated as the parameter constraint the route must satisfy.
-/
theorem hitsStreamingTests_forces_short_budget
    {n s seedLen space : Nat} (G : LocalGenerator n s seedLen)
    (hfit : seedLen + 1 ≤ tableLen n) (hHit : HitsStreamingTests G space) :
    space < seedLen + 1 := by
  by_contra hcon
  exact not_hitsStreamingTests_of_space_ge_seed G hfit (by omega) hHit

open Pnp3.Models.Partial in
/--
**The single inequality that governs the local-HSG route.**

Combining the window no-go (`space < seedLen + 1`) with the price of locality
(`2 ^ seedLen ≤ circuitCountBound n s`):

```text
2 ^ space ≤ circuitCountBound n s
```

The memory budget a local hitting-set generator can defeat is at most the
logarithm of the number of circuits of size `≤ s`.  Since the magnification
contract supplies `space = p(s)` for a polynomial `p`, and
`circuitCountBound n s = 2 ^ Õ(s)`, the route is available only when `p(s)`
stays within `Õ(s)`.
-/
theorem localHSG_budget_bound {n s seedLen space : Nat}
    (G : LocalGenerator n s seedLen) (hinj : Function.Injective G.gen)
    (hfit : seedLen + 1 ≤ tableLen n)
    (hHit : HitsStreamingTests G space) :
    2 ^ space ≤ Pnp3.Models.circuitCountBound n s := by
  have h1 : space < seedLen + 1 :=
    hitsStreamingTests_forces_short_budget G hfit hHit
  have h2 : 2 ^ seedLen ≤ Pnp3.Models.circuitCountBound n s :=
    seedLength_bound_of_injective_localGenerator G hinj
  have h3 : (2 : Nat) ^ space ≤ 2 ^ seedLen :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

open Pnp3.Models.Partial in
/--
Sharp form: when the memory budget exceeds the circuit-count budget, no usable
local hitting-set generator exists at all.
-/
theorem no_localHSG_of_budget_too_large {n s seedLen space : Nat}
    (hfit : seedLen + 1 ≤ tableLen n)
    (hbig : Pnp3.Models.circuitCountBound n s < 2 ^ space) :
    ¬ ∃ G : LocalGenerator n s seedLen,
        Function.Injective G.gen ∧ HitsStreamingTests G space := by
  rintro ⟨G, hinj, hHit⟩
  have := localHSG_budget_bound G hinj hfit hHit
  omega

end SequentialMagnification
end Frontier
end Pnp4
