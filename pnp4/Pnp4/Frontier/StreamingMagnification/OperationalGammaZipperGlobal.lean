import Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper
import Mathlib.Tactic.Ring

/-!
# Exact global composition for the value-preserving gamma zipper

`OperationalGammaZipper` proves the arbitrary-list backward and forward
passes and both cycle handoffs using spatial tape predicates.  This module
specializes those kernels to the canonical finite frames and composes all
payload cycles.  The endpoint remains a natural-coordinate theorem; lifting
it to the repository `TM` and to the tagged three-field wrapper is kept as a
separate obligation.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace OperationalGammaZipper

@[simp] theorem encR_append (left right : List Bool) :
    encR (left ++ right) = encR left ++ encR right := by
  induction left with
  | nil => rfl
  | cons bit bits ih => simp [encR, ih]

theorem encFinal_append_singleton (bits : List Bool) (last : Bool) :
    encFinal (bits ++ [last]) = encR bits ++ [last, true] := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      cases bits with
      | nil => rfl
      | cons next rest =>
          simpa [encFinal, encR, List.append_assoc] using
            congrArg (fun tail => bit :: false :: tail) ih

/-- Splitting a finite frame turns its right part into the new suffix. -/
theorem framedTape_append (left right : List Bool) (suffix : Nat -> Bool) :
    framedTape (left ++ right) suffix =
      framedTape left (framedTape right suffix) := by
  funext position
  simp only [framedTape, List.getElem?_append, List.length_append]
  by_cases hleft : position < left.length
  · simp [hleft]
  · simp [hleft]
    split <;> congr 1 <;> omega

/-- Read a cell in a finite middle block after an arbitrary prefix. -/
theorem framedTape_middle (pre frame : List Bool) (suffix : Nat -> Bool)
    (position : Nat) (hposition : position < frame.length) :
    framedTape (pre ++ frame) suffix (pre.length + position) =
      frame[position] := by
  rw [framedTape_append, framedTape_suffix]
  exact framedTape_prefix frame suffix position hposition

/-- Replacing a finite middle block by an equally long block changes no cell
strictly before it or at/after its right boundary. -/
theorem framedTape_replace_middle_outside (pre before after tail : List Bool)
    (suffix : Nat -> Bool) (hlength : after.length = before.length) :
    EqOutside
      (framedTape (pre ++ after ++ tail) suffix)
      (framedTape (pre ++ before ++ tail) suffix)
      pre.length (pre.length + before.length) := by
  intro position hposition
  rcases hposition with hleft | hright
  · rw [show pre ++ after ++ tail = pre ++ (after ++ tail) by simp]
    rw [show pre ++ before ++ tail = pre ++ (before ++ tail) by simp]
    rw [framedTape_prefix _ _ position (by simp; omega)]
    rw [framedTape_prefix _ _ position (by simp; omega)]
    rw [List.getElem_append_left hleft]
    rw [List.getElem_append_left hleft]
  · have hpre : pre.length <= position := by omega
    obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hpre
    have hbefore : before.length <= offset := by omega
    have hafter : after.length <= offset := by omega
    have hbeforeOffset : before.length + (offset - before.length) = offset :=
      Nat.add_sub_of_le hbefore
    have hafterOffset : after.length + (offset - before.length) = offset := by
      rw [hlength]
      exact hbeforeOffset
    have hdropAfter :
        framedTape (pre ++ after ++ tail) suffix (pre.length + offset) =
          framedTape (after ++ tail) suffix offset := by
      rw [show pre ++ after ++ tail = pre ++ (after ++ tail) by simp]
      rw [framedTape_append, framedTape_suffix]
    have hdropBefore :
        framedTape (pre ++ before ++ tail) suffix (pre.length + offset) =
          framedTape (before ++ tail) suffix offset := by
      rw [show pre ++ before ++ tail = pre ++ (before ++ tail) by simp]
      rw [framedTape_append, framedTape_suffix]
    rw [hdropAfter, hdropBefore]
    calc
      framedTape (after ++ tail) suffix offset =
          framedTape tail suffix (offset - after.length) := by
        rw [← hafterOffset, framedTape_append, framedTape_suffix]
        congr 1
        omega
      _ = framedTape tail suffix (offset - before.length) := by
        rw [hlength]
      _ = framedTape (before ++ tail) suffix offset := by
        rw [← hbeforeOffset, framedTape_append, framedTape_suffix]
        congr 1
        omega

/-- A literal `encR` block satisfies the spatial predicate at its offset. -/
theorem rightPairsAt_framedTape (pre bits tail : List Bool)
    (suffix : Nat -> Bool) :
    RightPairsAt
      (framedTape (pre ++ encR bits ++ tail) suffix)
      pre.length bits := by
  induction bits generalizing pre with
  | nil => trivial
  | cons bit bits ih =>
      refine ⟨?_, ?_, ?_⟩
      · have h := framedTape_middle pre
          (encR (bit :: bits) ++ tail) suffix 0 (by simp [encR])
        simpa [encR] using h
      · have h := framedTape_middle pre
          (encR (bit :: bits) ++ tail) suffix 1 (by simp [encR])
        simpa [encR] using h
      · have htail := ih (pre ++ [bit, false])
        simpa [encR, List.append_assoc] using htail

/-- Pointwise form of the right-pair spatial predicate. -/
theorem RightPairsAt.getElem {tape : Nat -> Bool} {start : Nat}
    {bits : List Bool} (hpairs : RightPairsAt tape start bits)
    (offset : Nat) (hoffset : offset < 2 * bits.length) :
    tape (start + offset) =
      (encR bits)[offset]'(by simpa [encR_length] using hoffset) := by
  induction bits generalizing start offset with
  | nil => simp at hoffset
  | cons bit bits ih =>
      rcases hpairs with ⟨hbit, hzero, htail⟩
      cases offset with
      | zero => simpa [encR] using hbit
      | succ offset =>
          cases offset with
          | zero => simpa [encR] using hzero
          | succ offset =>
              have hrest : offset < 2 * bits.length := by
                simp at hoffset
                omega
              have h := ih htail offset hrest
              rw [show start + (offset + 2) = (start + 2) + offset by omega]
              exact h

theorem RightPairsAt.eqOn {left right : Nat -> Bool} {start : Nat}
    {bits : List Bool} (hleft : RightPairsAt left start bits)
    (hright : RightPairsAt right start bits) (position : Nat)
    (hstart : start <= position)
    (hfinish : position < start + 2 * bits.length) :
    left position = right position := by
  let offset := position - start
  have hoffset : offset < 2 * bits.length := by
    dsimp [offset]
    omega
  have hposition : start + offset = position := by
    dsimp [offset]
    omega
  rw [← hposition]
  exact (hleft.getElem offset hoffset).trans
    (hright.getElem offset hoffset).symm

/-- Prefix ending at the cycle delimiter, immediately before `encR`. -/
def cyclePairPrefix (remaining : Nat) : List Bool :=
  true :: (List.replicate remaining false ++ [true])

@[simp] theorem cyclePairPrefix_length (remaining : Nat) :
    (cyclePairPrefix remaining).length = remaining + 2 := by
  simp [cyclePairPrefix]

theorem cycleFrame_eq_pairFrame (remaining : Nat)
    (processed unprocessed : List Bool) :
    cycleFrame remaining processed unprocessed =
      cyclePairPrefix remaining ++ (encR processed ++ true :: unprocessed) := by
  simp [cycleFrame, cyclePairPrefix, List.append_assoc]

theorem framedCycle_rightPairs (remaining : Nat)
    (processed unprocessed : List Bool) (suffix : Nat -> Bool) :
    RightPairsAt
      (framedTape (cycleFrame remaining processed unprocessed) suffix)
      (remaining + 2) processed := by
  rw [cycleFrame_eq_pairFrame]
  simpa using rightPairsAt_framedTape
    (cyclePairPrefix remaining) processed (true :: unprocessed) suffix

@[simp] theorem cycleFrame_getElem?_new_zero (remaining : Nat)
    (processed unprocessed : List Bool) (hremaining : 0 < remaining) :
    (cycleFrame remaining processed unprocessed)[remaining]? = some false := by
  rw [cycleFrame_eq_pairFrame]
  rw [List.getElem?_append_left (by simp [cyclePairPrefix]; omega)]
  unfold cyclePairPrefix
  rw [show remaining = (remaining - 1) + 1 by omega]
  rw [List.getElem?_cons_succ]
  rw [List.getElem?_append_left (by simp)]
  rw [List.getElem?_replicate, if_pos (by omega)]

@[simp] theorem cycleFrame_getElem?_probe_more (remaining : Nat)
    (processed unprocessed : List Bool) (hremaining : 2 <= remaining) :
    (cycleFrame remaining processed unprocessed)[remaining - 1]? =
      some false := by
  rw [cycleFrame_eq_pairFrame]
  rw [List.getElem?_append_left (by simp [cyclePairPrefix]; omega)]
  unfold cyclePairPrefix
  rw [show remaining - 1 = (remaining - 2) + 1 by omega]
  rw [List.getElem?_cons_succ]
  rw [List.getElem?_append_left (by simp <;> omega)]
  rw [List.getElem?_replicate, if_pos (by omega)]

@[simp] theorem cycleFrame_getElem?_marker (remaining : Nat)
    (processed unprocessed : List Bool) :
    (cycleFrame remaining processed unprocessed)[remaining + 2 +
      2 * processed.length]? = some true := by
  rw [cycleFrame_eq_pairFrame]
  simp [encR_length]

@[simp] theorem cycleFrame_getElem?_next (remaining : Nat)
    (processed rest : List Bool) (next : Bool) :
    (cycleFrame remaining processed (next :: rest))[remaining + 3 +
      2 * processed.length]? = some next := by
  rw [cycleFrame_eq_pairFrame]
  rw [List.getElem?_append_right (by simp [cyclePairPrefix]; omega)]
  rw [List.getElem?_append_right (by simp [encR_length]; omega)]
  rw [show remaining + 3 + 2 * processed.length -
      (cyclePairPrefix remaining).length - (encR processed).length = 1 by
    simp [cyclePairPrefix, encR_length]
    omega]
  simp

theorem framedCycle_new_zero (remaining : Nat)
    (processed unprocessed : List Bool) (suffix : Nat -> Bool)
    (hremaining : 0 < remaining) :
    framedTape (cycleFrame remaining processed unprocessed) suffix remaining =
      false := by
  unfold framedTape
  rw [cycleFrame_getElem?_new_zero _ _ _ hremaining]

theorem framedCycle_probe_more (remaining : Nat)
    (processed unprocessed : List Bool) (suffix : Nat -> Bool)
    (hremaining : 2 <= remaining) :
    framedTape (cycleFrame remaining processed unprocessed) suffix
        (remaining - 1) = false := by
  unfold framedTape
  rw [cycleFrame_getElem?_probe_more _ _ _ hremaining]

theorem framedCycle_marker (remaining : Nat)
    (processed unprocessed : List Bool) (suffix : Nat -> Bool) :
    framedTape (cycleFrame remaining processed unprocessed) suffix
        (remaining + 2 + 2 * processed.length) = true := by
  unfold framedTape
  rw [cycleFrame_getElem?_marker]

theorem framedCycle_next (remaining : Nat) (processed rest : List Bool)
    (next : Bool) (suffix : Nat -> Bool) :
    framedTape (cycleFrame remaining processed (next :: rest)) suffix
        (remaining + 3 + 2 * processed.length) = next := by
  unfold framedTape
  rw [cycleFrame_getElem?_next]

/-! ## Exact canonical cycle frames -/

def canonicalCycleConfig (remaining : Nat) (processed : List Bool)
    (current : Bool) (unprocessed : List Bool) (suffix : Nat -> Bool) :
    NatConfig :=
  ⟨.backStart current,
    remaining + 2 + 2 * processed.length,
    framedTape (cycleFrame remaining processed unprocessed) suffix⟩

theorem cycleFrame_nonfinal_before (remaining : Nat)
    (processed rest : List Bool) (next : Bool) (hremaining : 0 < remaining) :
    cycleFrame remaining processed (next :: rest) =
      (true :: List.replicate (remaining - 1) false) ++
        ([false, true] ++ encR processed ++ [true, next]) ++ rest := by
  unfold cycleFrame
  rw [show remaining = (remaining - 1) + 1 by omega]
  rw [List.replicate_add]
  simp [List.append_assoc]

theorem cycleFrame_nonfinal_after (remaining : Nat)
    (processed rest : List Bool) (current : Bool) :
    cycleFrame (remaining - 1) (processed ++ [current]) rest =
      (true :: List.replicate (remaining - 1) false) ++
        ([true] ++ encR processed ++ [current, false, true]) ++ rest := by
  simp [cycleFrame, encR_append, encR, List.append_assoc]

theorem framedCycle_nonfinal_target_outside (remaining : Nat)
    (processed rest : List Bool) (current next : Bool)
    (suffix : Nat -> Bool) (hremaining : 0 < remaining) :
    EqOutside
      (framedTape
        (cycleFrame (remaining - 1) (processed ++ [current]) rest) suffix)
      (framedTape
        (cycleFrame remaining processed (next :: rest)) suffix)
      remaining (remaining + 2 * processed.length + 4) := by
  rw [cycleFrame_nonfinal_before remaining processed rest next hremaining]
  rw [cycleFrame_nonfinal_after]
  have h := framedTape_replace_middle_outside
    (true :: List.replicate (remaining - 1) false)
    ([false, true] ++ encR processed ++ [true, next])
    ([true] ++ encR processed ++ [current, false, true])
    rest suffix (by simp [encR_length])
  convert h using 1 <;> simp [encR_length] <;> omega

/-- One complete nonfinal cycle sends the canonical frame to the next
canonical frame, including pointwise equality of the entire infinite tape. -/
theorem natRun_canonicalCycle_nonfinal
    (remaining : Nat) (processed rest : List Bool)
    (current next : Bool) (suffix : Nat -> Bool)
    (hremaining : 2 <= remaining) :
    natRun
        (canonicalCycleConfig remaining processed current (next :: rest)
          suffix)
        (10 * processed.length + 8) =
      canonicalCycleConfig (remaining - 1) (processed ++ [current]) next rest
        suffix := by
  let sourceTape :=
    framedTape (cycleFrame remaining processed (next :: rest)) suffix
  let targetTape :=
    framedTape (cycleFrame (remaining - 1) (processed ++ [current]) rest)
      suffix
  have hD : sourceTape (remaining + 1) = true := by
    simpa [sourceTape] using
      framedCycle_delimiter remaining processed (next :: rest) suffix
  have hnew : sourceTape remaining = false := by
    simpa [sourceTape] using
      framedCycle_new_zero remaining processed (next :: rest) suffix (by omega)
  have hprobe : sourceTape (remaining - 1) = false := by
    simpa [sourceTape] using
      framedCycle_probe_more remaining processed (next :: rest) suffix
        hremaining
  have hpairs : RightPairsAt sourceTape (remaining + 2) processed := by
    simpa [sourceTape] using
      framedCycle_rightPairs remaining processed (next :: rest) suffix
  have hmarker :
      sourceTape (remaining + 2 + 2 * processed.length) = true := by
    simpa [sourceTape] using
      framedCycle_marker remaining processed (next :: rest) suffix
  have hnext :
      sourceTape (remaining + 3 + 2 * processed.length) = next := by
    simpa [sourceTape] using
      framedCycle_next remaining processed rest next suffix
  have hnextInput :
      sourceTape (remaining + 1 + 2 * processed.length + 2) = next := by
    have hposition :
        remaining + 1 + 2 * processed.length + 2 =
          remaining + 3 + 2 * processed.length := by omega
    rw [hposition]
    exact hnext
  obtain ⟨resultTape, hrun, hresultD, hresultProbe, hresultPairs,
      hresultMarker, hresultOutside⟩ :=
    natRun_nonfinalCycle current next (remaining + 1) processed sourceTape
      (by omega) hD (by simpa using hnew) (by simpa using hprobe)
      (by simpa using hpairs) (by simpa using hmarker)
      hnextInput
  have htargetOutside :
      EqOutside targetTape sourceTape remaining
        (remaining + 2 * processed.length + 4) := by
    simpa [targetTape, sourceTape] using
      framedCycle_nonfinal_target_outside remaining processed rest current next
        suffix (by omega)
  have htargetD : targetTape remaining = true := by
    have h := framedCycle_delimiter (remaining - 1)
      (processed ++ [current]) rest suffix
    change framedTape
      (cycleFrame (remaining - 1) (processed ++ [current]) rest) suffix
        remaining = true
    have hposition : remaining - 1 + 1 = remaining := by omega
    rw [← hposition]
    exact h
  have htargetPairs :
      RightPairsAt targetTape (remaining + 1) (processed ++ [current]) := by
    have h := framedCycle_rightPairs (remaining - 1)
      (processed ++ [current]) rest suffix
    change RightPairsAt
      (framedTape
        (cycleFrame (remaining - 1) (processed ++ [current]) rest) suffix)
      (remaining + 1) (processed ++ [current])
    have hstart : remaining - 1 + 2 = remaining + 1 := by omega
    rw [← hstart]
    exact h
  have htargetMarker :
      targetTape (remaining + 2 * processed.length + 3) = true := by
    have h := framedCycle_marker (remaining - 1)
      (processed ++ [current]) rest suffix
    change framedTape
      (cycleFrame (remaining - 1) (processed ++ [current]) rest) suffix
      (remaining + 2 * processed.length + 3) = true
    have hposition :
        remaining - 1 + 2 + 2 * (processed ++ [current]).length =
          remaining + 2 * processed.length + 3 := by
      simp only [List.length_append, List.length_singleton]
      omega
    rw [← hposition]
    exact h
  have htape : resultTape = targetTape := by
    funext position
    by_cases hleft : position < remaining
    · exact (hresultOutside position (by left; omega)).trans
        (htargetOutside position (by left; omega)).symm
    by_cases hright : remaining + 2 * processed.length + 4 <= position
    · exact (hresultOutside position (by right; omega)).trans
        (htargetOutside position (by right; omega)).symm
    by_cases hdelimiter : position = remaining
    · subst position
      have hresult : resultTape remaining = true := by
        convert hresultD using 1 <;> omega
      exact hresult.trans htargetD.symm
    by_cases hmark : position = remaining + 2 * processed.length + 3
    · subst position
      have hresult :
          resultTape (remaining + 2 * processed.length + 3) = true := by
        have hposition :
            remaining + 1 + 2 * processed.length + 2 =
              remaining + 2 * processed.length + 3 := by omega
        rw [← hposition]
        exact hresultMarker
      exact hresult.trans htargetMarker.symm
    · apply hresultPairs.eqOn htargetPairs position
      · omega
      · simp only [List.length_append, List.length_singleton]
        omega
  have hrun' :
      natRun
          (canonicalCycleConfig remaining processed current (next :: rest)
            suffix)
          (10 * processed.length + 8) =
        ⟨.backStart next, remaining + 2 * processed.length + 3,
          resultTape⟩ := by
    convert hrun using 1 <;> simp [canonicalCycleConfig, sourceTape] <;> omega
  rw [hrun', htape]
  unfold canonicalCycleConfig
  congr 1 <;> simp <;> omega

theorem cycleFrame_final_before (processed : List Bool) :
    cycleFrame 1 processed [] =
      [true] ++ ([false, true] ++ encR processed) ++ [true] := by
  simp [cycleFrame, List.append_assoc]

theorem finalFrame_append_singleton (processed : List Bool)
    (current : Bool) :
    finalFrame (processed ++ [current]) =
      [true, true] ++ encR processed ++ [current, true] := by
  simp [finalFrame, encChain, encFinal_append_singleton, List.append_assoc]

theorem framedCycle_final_target_outside (processed : List Bool)
    (current : Bool) (suffix : Nat -> Bool) :
    EqOutside
      (framedTape (finalFrame (processed ++ [current])) suffix)
      (framedTape (cycleFrame 1 processed []) suffix)
      1 (2 * processed.length + 3) := by
  rw [cycleFrame_final_before, finalFrame_append_singleton]
  have h := framedTape_replace_middle_outside
    [true]
    ([false, true] ++ encR processed)
    ([true] ++ encR processed ++ [current])
    [true] suffix (by simp [encR_length])
  convert h using 1 <;> simp [List.append_assoc, encR_length] <;> omega

def canonicalFinalConfig (payload : List Bool) (suffix : Nat -> Bool) :
    NatConfig :=
  ⟨.done, (finalFrame payload).length, framedTape (finalFrame payload) suffix⟩

/-- The last canonical cycle produces the literal final frame and leaves the
entire supplied suffix untouched. -/
theorem natRun_canonicalCycle_final (processed : List Bool)
    (current : Bool) (suffix : Nat -> Bool) :
    natRun (canonicalCycleConfig 1 processed current [] suffix)
        (10 * processed.length + 7) =
      canonicalFinalConfig (processed ++ [current]) suffix := by
  let sourceTape := framedTape (cycleFrame 1 processed []) suffix
  let targetTape :=
    framedTape (finalFrame (processed ++ [current])) suffix
  have hD : sourceTape 2 = true := by
    simpa [sourceTape] using framedCycle_delimiter 1 processed [] suffix
  have hnew : sourceTape 1 = false := by
    simpa [sourceTape] using
      framedCycle_new_zero 1 processed [] suffix (by omega)
  have hprobe : sourceTape 0 = true := by
    simpa [sourceTape] using framedCycle_sentinel 1 processed [] suffix
  have hpairs : RightPairsAt sourceTape 3 processed := by
    simpa [sourceTape] using framedCycle_rightPairs 1 processed [] suffix
  have hmarker : sourceTape (3 + 2 * processed.length) = true := by
    simpa [sourceTape] using framedCycle_marker 1 processed [] suffix
  obtain ⟨resultTape, hrun, hresultD, hresultPairs, hresultMobile,
      hresultMarker, hresultOutside⟩ :=
    natRun_finalCycle current 2 processed sourceTape (by omega) hD hnew
      hprobe hpairs (by simpa using hmarker)
  have htargetOutside :
      EqOutside targetTape sourceTape 1 (2 * processed.length + 3) := by
    simpa [targetTape, sourceTape] using
      framedCycle_final_target_outside processed current suffix
  have htargetTape :
      targetTape =
        framedTape ([true, true] ++ encR processed ++ [current, true])
          suffix := by
    simp [targetTape, finalFrame_append_singleton]
  have htargetD : targetTape 1 = true := by
    rw [htargetTape]
    rw [show [true, true] ++ encR processed ++ [current, true] =
      [true] ++ ([true] ++ encR processed ++ [current, true]) by simp]
    have h := framedTape_middle [true]
      ([true] ++ encR processed ++ [current, true]) suffix 0 (by simp)
    simpa using h
  have htargetPairs : RightPairsAt targetTape 2 processed := by
    rw [htargetTape]
    simpa [List.append_assoc] using
      rightPairsAt_framedTape [true, true] processed [current, true] suffix
  have htargetMobile :
      targetTape (2 + 2 * processed.length) = current := by
    rw [htargetTape]
    have h := framedTape_middle ([true, true] ++ encR processed)
      [current, true] suffix 0 (by simp)
    have hposition :
        2 * processed.length + 1 + 1 = 2 + 2 * processed.length := by omega
    rw [← hposition]
    simpa [encR_length, List.append_assoc] using h
  have htape : resultTape = targetTape := by
    funext position
    by_cases hleft : position < 1
    · exact (hresultOutside position (by left; omega)).trans
        (htargetOutside position (by left; omega)).symm
    by_cases hright : 2 * processed.length + 3 <= position
    · exact (hresultOutside position (by right; omega)).trans
        (htargetOutside position (by right; omega)).symm
    by_cases hdelimiter : position = 1
    · subst position
      exact hresultD.trans htargetD.symm
    by_cases hpairsFinish : position < 2 + 2 * processed.length
    · apply hresultPairs.eqOn htargetPairs position <;> omega
    · have hposition : position = 2 + 2 * processed.length := by omega
      subst position
      exact hresultMobile.trans htargetMobile.symm
  have hrun' :
      natRun (canonicalCycleConfig 1 processed current [] suffix)
          (10 * processed.length + 7) =
        ⟨.done, 2 * processed.length + 4, resultTape⟩ := by
    convert hrun using 1 <;> simp [canonicalCycleConfig, sourceTape] <;> omega
  rw [hrun', htape]
  unfold canonicalFinalConfig
  congr 1 <;> simp <;> omega

/-! ## Composition of all payload cycles -/

def cycleFinishTime (processedCount : Nat) : List Bool -> Nat
  | [] => 10 * processedCount + 7
  | _ :: rest =>
      10 * processedCount + 8 + cycleFinishTime (processedCount + 1) rest

@[simp] theorem cycleFinishTime_closed (processedCount : Nat)
    (unprocessed : List Bool) :
    cycleFinishTime processedCount unprocessed =
      10 * (unprocessed.length + 1) * processedCount +
        5 * unprocessed.length * unprocessed.length +
        13 * unprocessed.length + 7 := by
  induction unprocessed generalizing processedCount with
  | nil => simp [cycleFinishTime]
  | cons bit rest ih =>
      rw [cycleFinishTime, ih]
      simp only [List.length_cons]
      ring

/-- Starting at any canonical cycle boundary, all remaining cycles compose to
the exact final frame for the reconstructed payload. -/
theorem natRun_cycles_to_final (processed unprocessed : List Bool)
    (current : Bool) (suffix : Nat -> Bool) :
    natRun
        (canonicalCycleConfig (unprocessed.length + 1) processed current
          unprocessed suffix)
        (cycleFinishTime processed.length unprocessed) =
      canonicalFinalConfig (processed ++ current :: unprocessed) suffix := by
  induction unprocessed generalizing processed current with
  | nil =>
      simpa [cycleFinishTime] using
        natRun_canonicalCycle_final processed current suffix
  | cons next rest ih =>
      rw [cycleFinishTime, natRun_add]
      have hcycle := natRun_canonicalCycle_nonfinal
        (rest.length + 2) processed rest current next suffix (by omega)
      have hcycle' :
          natRun
              (canonicalCycleConfig ((next :: rest).length + 1) processed
                current (next :: rest) suffix)
              (10 * processed.length + 8) =
            canonicalCycleConfig (rest.length + 1) (processed ++ [current])
              next rest suffix := by
        convert hcycle using 1 <;> simp <;> omega
      rw [hcycle']
      simpa [List.append_assoc] using
        ih (processed := processed ++ [current]) (current := next)

/-! ## Startup scan and the standalone natural-coordinate theorem -/

theorem natRun_scanZeros (head count : Nat) (tape : Nat -> Bool)
    (hzeros : forall offset, offset < count ->
      tape (head + offset) = false) :
    natRun ⟨.scanZeros, head, tape⟩ count =
      ⟨.scanZeros, head + count, tape⟩ := by
  induction count with
  | zero => simp [natRun]
  | succ count ih =>
      rw [natRun_succ]
      rw [ih (fun offset hoffset => hzeros offset (by omega))]
      have hlast : tape (head + count) = false :=
        hzeros count (by omega)
      have hstep := natStep_scanZeros_zero (head + count) tape hlast
      convert hstep using 1 <;> omega

theorem framedInitial_sentinel (k : Nat) (payload : List Bool)
    (suffix : Nat -> Bool) :
    framedTape (initialFrame k payload) suffix 0 = true := by
  unfold framedTape initialFrame
  simp

theorem framedInitial_zero (k : Nat) (payload : List Bool)
    (suffix : Nat -> Bool) (offset : Nat) (hoffset : offset < k) :
    framedTape (initialFrame k payload) suffix (1 + offset) = false := by
  unfold framedTape initialFrame
  rw [List.getElem?_append_left (by simp; omega)]
  rw [show 1 + offset = offset + 1 by omega]
  rw [List.getElem?_cons_succ]
  rw [List.getElem?_replicate]
  simp [hoffset]

theorem framedInitial_delimiter (k : Nat) (payload : List Bool)
    (suffix : Nat -> Bool) :
    framedTape (initialFrame k payload) suffix (k + 1) = true := by
  have hmiddle := framedTape_middle
    ([true] ++ List.replicate k false) (true :: payload) suffix 0 (by simp)
  simpa [initialFrame, List.append_assoc] using hmiddle

theorem framedInitial_firstPayload (k : Nat) (current : Bool)
    (rest : List Bool) (suffix : Nat -> Bool) :
    framedTape (initialFrame k (current :: rest)) suffix (k + 2) =
      current := by
  have hmiddle := framedTape_middle
    ([true] ++ List.replicate k false ++ [true]) (current :: rest) suffix 0
      (by simp)
  simpa [initialFrame, List.append_assoc] using hmiddle

theorem writeNat_framedTape_replace (pre tail : List Bool)
    (old new : Bool) (suffix : Nat -> Bool) :
    writeNat (framedTape (pre ++ old :: tail) suffix) pre.length new =
      framedTape (pre ++ new :: tail) suffix := by
  funext position
  by_cases hposition : position = pre.length
  · subst position
    rw [writeNat_same]
    have hmiddle := framedTape_middle pre (new :: tail) suffix 0 (by simp)
    have htarget :
        framedTape (pre ++ new :: tail) suffix pre.length = new := by
      simpa using hmiddle
    exact htarget.symm
  · rw [writeNat_other _ _ _ _ hposition]
    have houtside := framedTape_replace_middle_outside pre [old] [new] tail
      suffix (by simp)
    have hregion :
        position < pre.length ∨ pre.length + [old].length <= position := by
      by_cases hbefore : position < pre.length
      · exact Or.inl hbefore
      · right
        simp only [List.length_singleton]
        omega
    simpa using (houtside position hregion).symm

theorem writeNat_initialFrame_first (k : Nat) (current : Bool)
    (rest : List Bool) (suffix : Nat -> Bool) :
    writeNat (framedTape (initialFrame k (current :: rest)) suffix)
        (k + 2) true =
      framedTape (cycleFrame k [] rest) suffix := by
  have h := writeNat_framedTape_replace
    ([true] ++ List.replicate k false ++ [true]) rest current true suffix
  convert h using 1 <;>
    simp [initialFrame, cycleFrame, List.append_assoc] <;> omega

/-- From the first unary-count cell, startup consumes exactly `k + 2` steps
for a nonempty payload and reaches the first canonical cycle boundary. -/
theorem natRun_scanFirst_to_firstCycle (current : Bool) (rest : List Bool)
    (suffix : Nat -> Bool) :
    natRun
        ⟨.scanFirst, 1,
          framedTape (initialFrame (rest.length + 1) (current :: rest))
            suffix⟩
        (rest.length + 3) =
      canonicalCycleConfig (rest.length + 1) [] current rest suffix := by
  let tape :=
    framedTape (initialFrame (rest.length + 1) (current :: rest)) suffix
  have hfirst : tape 1 = false := by
    simpa [tape] using framedInitial_zero (rest.length + 1)
      (current :: rest) suffix 0 (by omega)
  have hfirstRun :
      natRun ⟨.scanFirst, 1, tape⟩ 1 = ⟨.scanZeros, 2, tape⟩ := by
    simpa [natRun] using natStep_scanFirst_zero 1 tape hfirst
  have hzeros : forall offset, offset < rest.length ->
      tape (2 + offset) = false := by
    intro offset hoffset
    have h := framedInitial_zero (rest.length + 1) (current :: rest)
      suffix (offset + 1) (by omega)
    change framedTape
      (initialFrame (rest.length + 1) (current :: rest)) suffix
        (2 + offset) = false
    rw [show 2 + offset = 1 + (offset + 1) by omega]
    exact h
  have hzerosRun :
      natRun ⟨.scanZeros, 2, tape⟩ rest.length =
        ⟨.scanZeros, rest.length + 2, tape⟩ := by
    simpa [Nat.add_comm] using natRun_scanZeros 2 rest.length tape hzeros
  have hdelimiter : tape (rest.length + 2) = true := by
    simpa [tape] using framedInitial_delimiter (rest.length + 1)
      (current :: rest) suffix
  have hdelimiterRun :
      natRun ⟨.scanZeros, rest.length + 2, tape⟩ 1 =
        ⟨.initRead, rest.length + 3, tape⟩ := by
    simpa [natRun] using
      natStep_scanZeros_one (rest.length + 2) tape hdelimiter
  have hpayload : tape (rest.length + 3) = current := by
    simpa [tape] using framedInitial_firstPayload (rest.length + 1)
      current rest suffix
  have hwrite :
      writeNat tape (rest.length + 3) true =
        framedTape (cycleFrame (rest.length + 1) [] rest) suffix := by
    simpa [tape] using
      writeNat_initialFrame_first (rest.length + 1) current rest suffix
  have hinitRun :
      natRun ⟨.initRead, rest.length + 3, tape⟩ 1 =
        canonicalCycleConfig (rest.length + 1) [] current rest suffix := by
    have hstep := natStep_initRead (rest.length + 3) tape
    simpa [natRun, canonicalCycleConfig, hpayload, hwrite] using hstep
  change natRun ⟨.scanFirst, 1, tape⟩ (rest.length + 3) = _
  rw [show rest.length + 3 = 1 + (rest.length + (1 + 1)) by omega]
  rw [natRun_add, hfirstRun, natRun_add, hzerosRun, natRun_add,
    hdelimiterRun, hinitRun]

def gammaBodyTime (k : Nat) : Nat := 5 * k * k + 4 * k + 1

def gammaFinishTime (k : Nat) : Nat := 1 + gammaBodyTime k

@[simp] theorem gammaFinishTime_closed (k : Nat) :
    gammaFinishTime k = 5 * k * k + 4 * k + 2 := by
  simp [gammaFinishTime, gammaBodyTime]
  omega

theorem natRun_scanFirst_nonempty (current : Bool) (rest : List Bool)
    (suffix : Nat -> Bool) :
    natRun
        ⟨.scanFirst, 1,
          framedTape (initialFrame (rest.length + 1) (current :: rest))
            suffix⟩
        (gammaBodyTime (rest.length + 1)) =
      canonicalFinalConfig (current :: rest) suffix := by
  have htime :
      gammaBodyTime (rest.length + 1) =
        (rest.length + 3) + cycleFinishTime 0 rest := by
    rw [cycleFinishTime_closed]
    simp [gammaBodyTime]
    ring
  rw [htime, natRun_add, natRun_scanFirst_to_firstCycle]
  simpa using natRun_cycles_to_final [] rest current suffix

theorem natRun_scanFirst_empty (suffix : Nat -> Bool) :
    natRun
        ⟨.scanFirst, 1, framedTape (initialFrame 0 []) suffix⟩
        (gammaBodyTime 0) =
      canonicalFinalConfig [] suffix := by
  let tape := framedTape (initialFrame 0 []) suffix
  have hbit : tape 1 = true := by
    simpa [tape] using framedInitial_delimiter 0 [] suffix
  have hrun :
      natRun ⟨.scanFirst, 1, tape⟩ 1 = ⟨.done, 2, tape⟩ := by
    simpa [natRun] using natStep_scanFirst_one 1 tape hbit
  have htape : tape = framedTape (finalFrame []) suffix := by
    simp [tape, initialFrame, finalFrame, encChain, encFinal]
  change natRun ⟨.scanFirst, 1, tape⟩ (gammaBodyTime 0) = _
  rw [show gammaBodyTime 0 = 1 by rfl, hrun, htape]
  unfold canonicalFinalConfig
  congr 1 <;> simp

theorem natRun_scanFirst_payload (payload : List Bool)
    (suffix : Nat -> Bool) :
    natRun
        ⟨.scanFirst, 1,
          framedTape (initialFrame payload.length payload) suffix⟩
        (gammaBodyTime payload.length) =
      canonicalFinalConfig payload suffix := by
  cases payload with
  | nil => simpa using natRun_scanFirst_empty suffix
  | cons current rest =>
      simpa using natRun_scanFirst_nonempty current rest suffix

def canonicalInitialConfig (payload : List Bool) (suffix : Nat -> Bool) :
    NatConfig :=
  ⟨.sentinel, 0,
    framedTape (initialFrame payload.length payload) suffix⟩

/-- Exact end-to-end theorem for the fixed 57-state natural-coordinate
zipper: it preserves every payload bit, halts at the first suffix cell, and
runs for the explicit quadratic clock `5*k^2 + 4*k + 2`. -/
theorem natRun_gammaZipper_standalone (payload : List Bool)
    (suffix : Nat -> Bool) :
    natRun (canonicalInitialConfig payload suffix)
        (gammaFinishTime payload.length) =
      canonicalFinalConfig payload suffix := by
  let tape := framedTape (initialFrame payload.length payload) suffix
  have hsentinel : tape 0 = true := by
    simpa [tape] using
      framedInitial_sentinel payload.length payload suffix
  have hfirst :
      natRun (canonicalInitialConfig payload suffix) 1 =
        ⟨.scanFirst, 1, tape⟩ := by
    simpa [natRun, canonicalInitialConfig, tape] using
      natStep_sentinel_one 0 tape hsentinel
  rw [gammaFinishTime, natRun_add, hfirst]
  simpa [tape] using natRun_scanFirst_payload payload suffix

end OperationalGammaZipper
end StreamingMagnification
end Frontier
end Pnp4

#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.framedTape_append
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.rightPairsAt_framedTape
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.natRun_canonicalCycle_nonfinal
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.natRun_canonicalCycle_final
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.cycleFinishTime_closed
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.natRun_cycles_to_final
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.natRun_scanFirst_to_firstCycle
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.natRun_gammaZipper_standalone
