import Pnp4.Frontier.StreamingMagnification.OperationalGammaZipperGlobal
import Pnp4.Frontier.StreamingMagnification.OperationalGammaZipperActive

/-!
# Shifted contextual execution for the value-preserving gamma zipper

The natural-coordinate zipper theorem in `OperationalGammaZipperGlobal`
starts at coordinate zero.  This module places the same finite frame after an
arbitrary finite `front`, retains an arbitrary finite `tail` after it, and
proves the real natural-coordinate run at the shifted heads.  The proof uses
the arbitrary-coordinate local kernels rather than an invalid blanket shift
argument: `moveNat` reflects at zero, so translation is not an unconditional
symmetry of malformed runs.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace OperationalGammaZipper

/-- A finite zipper frame embedded between an arbitrary finite front and
tail, followed by an arbitrary infinite suffix. -/
def contextualTape (front frame tail : List Bool)
    (suffix : Nat -> Bool) : Nat -> Bool :=
  framedTape (front ++ frame ++ tail) suffix

/-- Dropping the finite front from a contextual tape recovers the framed
zipper tape, with the supplied tail incorporated into its suffix. -/
theorem contextualTape_at (front frame tail : List Bool)
    (suffix : Nat -> Bool) (position : Nat) :
    contextualTape front frame tail suffix (front.length + position) =
      framedTape frame (framedTape tail suffix) position := by
  unfold contextualTape
  rw [show front ++ frame ++ tail = front ++ (frame ++ tail) by simp]
  rw [framedTape_append, framedTape_suffix, framedTape_append]

/-- Function-level rebase identity used by clients that need to reason about
the embedded frame independently of the untouched finite front. -/
theorem contextualTape_rebase (front frame tail : List Bool)
    (suffix : Nat -> Bool) :
    (fun position =>
      contextualTape front frame tail suffix (front.length + position)) =
      framedTape frame (framedTape tail suffix) := by
  funext position
  exact contextualTape_at front frame tail suffix position

/-- Canonical shifted cycle boundary inside a surrounding tape context. -/
def contextualCycleConfig (front : List Bool) (remaining : Nat)
    (processed : List Bool) (current : Bool) (unprocessed tail : List Bool)
    (suffix : Nat -> Bool) : NatConfig :=
  ⟨.backStart current,
    front.length + remaining + 2 + 2 * processed.length,
    contextualTape front (cycleFrame remaining processed unprocessed) tail
      suffix⟩

/-- Canonical shifted final boundary inside the same tape context. -/
def contextualFinalConfig (front payload tail : List Bool)
    (suffix : Nat -> Bool) : NatConfig :=
  ⟨.done, front.length + (finalFrame payload).length,
    contextualTape front (finalFrame payload) tail suffix⟩

theorem contextualCycle_delimiter (front : List Bool) (remaining : Nat)
    (processed unprocessed tail : List Bool) (suffix : Nat -> Bool) :
    contextualTape front (cycleFrame remaining processed unprocessed) tail
        suffix (front.length + remaining + 1) = true := by
  rw [show front.length + remaining + 1 =
    front.length + (remaining + 1) by omega]
  rw [contextualTape_at]
  exact framedCycle_delimiter remaining processed unprocessed
    (framedTape tail suffix)

theorem contextualCycle_new_zero (front : List Bool) (remaining : Nat)
    (processed unprocessed tail : List Bool) (suffix : Nat -> Bool)
    (hremaining : 0 < remaining) :
    contextualTape front (cycleFrame remaining processed unprocessed) tail
        suffix (front.length + remaining) = false := by
  rw [contextualTape_at]
  exact framedCycle_new_zero remaining processed unprocessed
    (framedTape tail suffix) hremaining

theorem contextualCycle_probe_more (front : List Bool) (remaining : Nat)
    (processed unprocessed tail : List Bool) (suffix : Nat -> Bool)
    (hremaining : 2 <= remaining) :
    contextualTape front (cycleFrame remaining processed unprocessed) tail
        suffix (front.length + remaining - 1) = false := by
  rw [show front.length + remaining - 1 =
    front.length + (remaining - 1) by omega]
  rw [contextualTape_at]
  exact framedCycle_probe_more remaining processed unprocessed
    (framedTape tail suffix) hremaining

theorem contextualCycle_marker (front : List Bool) (remaining : Nat)
    (processed unprocessed tail : List Bool) (suffix : Nat -> Bool) :
    contextualTape front (cycleFrame remaining processed unprocessed) tail
        suffix
        (front.length + remaining + 2 + 2 * processed.length) = true := by
  rw [show front.length + remaining + 2 + 2 * processed.length =
    front.length + (remaining + 2 + 2 * processed.length) by omega]
  rw [contextualTape_at]
  exact framedCycle_marker remaining processed unprocessed
    (framedTape tail suffix)

theorem contextualCycle_next (front : List Bool) (remaining : Nat)
    (processed rest tail : List Bool) (next : Bool)
    (suffix : Nat -> Bool) :
    contextualTape front (cycleFrame remaining processed (next :: rest))
        tail suffix
        (front.length + remaining + 3 + 2 * processed.length) = next := by
  rw [show front.length + remaining + 3 + 2 * processed.length =
    front.length + (remaining + 3 + 2 * processed.length) by omega]
  rw [contextualTape_at]
  exact framedCycle_next remaining processed rest next
    (framedTape tail suffix)

theorem contextualCycle_rightPairs (front : List Bool) (remaining : Nat)
    (processed unprocessed tail : List Bool) (suffix : Nat -> Bool) :
    RightPairsAt
      (contextualTape front
        (cycleFrame remaining processed unprocessed) tail suffix)
      (front.length + remaining + 2) processed := by
  rw [cycleFrame_eq_pairFrame]
  have h := rightPairsAt_framedTape
    (front ++ cyclePairPrefix remaining) processed
    ((true :: unprocessed) ++ tail) suffix
  convert h using 1 <;>
    simp [contextualTape, List.append_assoc, cyclePairPrefix_length] <;>
    omega

/-- The contextual target of a nonfinal cycle differs from its source only
on the same shifted finite work interval. -/
theorem contextualCycle_nonfinal_target_outside (front : List Bool)
    (remaining : Nat) (processed rest : List Bool) (current next : Bool)
    (tail : List Bool) (suffix : Nat -> Bool) (hremaining : 0 < remaining) :
    EqOutside
      (contextualTape front
        (cycleFrame (remaining - 1) (processed ++ [current]) rest) tail
        suffix)
      (contextualTape front
        (cycleFrame remaining processed (next :: rest)) tail suffix)
      (front.length + remaining)
      (front.length + remaining + 2 * processed.length + 4) := by
  rw [cycleFrame_nonfinal_before remaining processed rest next hremaining]
  rw [cycleFrame_nonfinal_after]
  have h := framedTape_replace_middle_outside
    (front ++ (true :: List.replicate (remaining - 1) false))
    ([false, true] ++ encR processed ++ [true, next])
    ([true] ++ encR processed ++ [current, false, true])
    (rest ++ tail) suffix (by simp [encR_length])
  convert h using 1 <;>
    simp [contextualTape, List.append_assoc, encR_length] <;> omega

/-- One complete nonfinal cycle at an arbitrary contextual offset. -/
theorem natRun_contextualCycle_nonfinal (front : List Bool)
    (remaining : Nat) (processed rest : List Bool)
    (current next : Bool) (tail : List Bool) (suffix : Nat -> Bool)
    (hremaining : 2 <= remaining) :
    natRun
        (contextualCycleConfig front remaining processed current
          (next :: rest) tail suffix)
        (10 * processed.length + 8) =
      contextualCycleConfig front (remaining - 1) (processed ++ [current])
        next rest tail suffix := by
  let sourceTape :=
    contextualTape front (cycleFrame remaining processed (next :: rest))
      tail suffix
  let targetTape :=
    contextualTape front
      (cycleFrame (remaining - 1) (processed ++ [current]) rest) tail suffix
  let delimiter := front.length + remaining + 1
  have hD : sourceTape delimiter = true := by
    simpa [sourceTape, delimiter] using
      contextualCycle_delimiter front remaining processed (next :: rest)
        tail suffix
  have hnew : sourceTape (delimiter - 1) = false := by
    have h := contextualCycle_new_zero front remaining processed
      (next :: rest) tail suffix (by omega)
    simpa [sourceTape, delimiter] using h
  have hprobe : sourceTape (delimiter - 2) = false := by
    have h := contextualCycle_probe_more front remaining processed
      (next :: rest) tail suffix hremaining
    simpa [sourceTape, delimiter] using h
  have hpairs : RightPairsAt sourceTape (delimiter + 1) processed := by
    have h := contextualCycle_rightPairs front remaining processed
      (next :: rest) tail suffix
    simpa [sourceTape, delimiter] using h
  have hmarker :
      sourceTape (delimiter + 1 + 2 * processed.length) = true := by
    have h := contextualCycle_marker front remaining processed
      (next :: rest) tail suffix
    simpa [sourceTape, delimiter] using h
  have hnext :
      sourceTape (delimiter + 2 * processed.length + 2) = next := by
    have h := contextualCycle_next front remaining processed rest tail next
      suffix
    have hposition :
        delimiter + 2 * processed.length + 2 =
          front.length + remaining + 3 + 2 * processed.length := by
      dsimp [delimiter]
      omega
    rw [hposition]
    exact h
  obtain ⟨resultTape, hrun, hresultD, hresultProbe, hresultPairs,
      hresultMarker, hresultOutside⟩ :=
    natRun_nonfinalCycle current next delimiter processed sourceTape
      (by simp [delimiter]; omega) hD hnew hprobe hpairs hmarker hnext
  have htargetOutside :
      EqOutside targetTape sourceTape
        (front.length + remaining)
        (front.length + remaining + 2 * processed.length + 4) := by
    simpa [targetTape, sourceTape] using
      contextualCycle_nonfinal_target_outside front remaining processed rest
        current next tail suffix (by omega)
  have htargetD : targetTape (front.length + remaining) = true := by
    have h := contextualCycle_delimiter front (remaining - 1)
      (processed ++ [current]) rest tail suffix
    have hposition :
        front.length + (remaining - 1) + 1 = front.length + remaining := by
      omega
    rw [← hposition]
    exact h
  have htargetPairs :
      RightPairsAt targetTape (front.length + remaining + 1)
        (processed ++ [current]) := by
    have h := contextualCycle_rightPairs front (remaining - 1)
      (processed ++ [current]) rest tail suffix
    convert h using 1 <;> simp [targetTape] <;> omega
  have htargetMarker :
      targetTape
        (front.length + remaining + 2 * processed.length + 3) = true := by
    have h := contextualCycle_marker front (remaining - 1)
      (processed ++ [current]) rest tail suffix
    have hposition :
        front.length + (remaining - 1) + 2 +
            2 * (processed ++ [current]).length =
          front.length + remaining + 2 * processed.length + 3 := by
      simp only [List.length_append, List.length_singleton]
      omega
    rw [← hposition]
    exact h
  have htape : resultTape = targetTape := by
    funext position
    by_cases hleft : position < front.length + remaining
    · exact (hresultOutside position (by left; simp [delimiter]; omega)).trans
        (htargetOutside position (by left; omega)).symm
    by_cases hright :
        front.length + remaining + 2 * processed.length + 4 <= position
    · exact (hresultOutside position (by right; simp [delimiter]; omega)).trans
        (htargetOutside position (by right; omega)).symm
    by_cases hdelimiter : position = front.length + remaining
    · subst position
      have hresult : resultTape (front.length + remaining) = true := by
        convert hresultD using 1 <;> simp [delimiter] <;> omega
      exact hresult.trans htargetD.symm
    by_cases hmark :
        position = front.length + remaining + 2 * processed.length + 3
    · subst position
      have hresult :
          resultTape
            (front.length + remaining + 2 * processed.length + 3) = true := by
        have hposition :
            delimiter + 2 * processed.length + 2 =
              front.length + remaining + 2 * processed.length + 3 := by
          dsimp [delimiter]
          omega
        rw [← hposition]
        exact hresultMarker
      exact hresult.trans htargetMarker.symm
    · apply hresultPairs.eqOn htargetPairs position
      · simp [delimiter]
        omega
      · simp only [List.length_append, List.length_singleton]
        simp [delimiter]
        omega
  have hrun' :
      natRun
          (contextualCycleConfig front remaining processed current
            (next :: rest) tail suffix)
          (10 * processed.length + 8) =
        ⟨.backStart next,
          front.length + remaining + 2 * processed.length + 3,
          resultTape⟩ := by
    convert hrun using 1 <;>
      simp [contextualCycleConfig, sourceTape, delimiter] <;> omega
  rw [hrun', htape]
  unfold contextualCycleConfig
  congr 1 <;> simp <;> omega

/-- The contextual final target differs from the last cycle source only on
the shifted zipper work interval. -/
theorem contextualCycle_final_target_outside (front processed : List Bool)
    (current : Bool) (tail : List Bool) (suffix : Nat -> Bool) :
    EqOutside
      (contextualTape front (finalFrame (processed ++ [current])) tail suffix)
      (contextualTape front (cycleFrame 1 processed []) tail suffix)
      (front.length + 1) (front.length + 2 * processed.length + 3) := by
  rw [cycleFrame_final_before, finalFrame_append_singleton]
  have h := framedTape_replace_middle_outside
    (front ++ [true])
    ([false, true] ++ encR processed)
    ([true] ++ encR processed ++ [current])
    ([true] ++ tail) suffix (by simp [encR_length])
  convert h using 1 <;>
    simp [contextualTape, List.append_assoc, encR_length] <;> omega

/-- The last cycle at an arbitrary contextual offset produces the exact
literal final frame and preserves both sides of its surrounding context. -/
theorem natRun_contextualCycle_final (front processed : List Bool)
    (current : Bool) (tail : List Bool) (suffix : Nat -> Bool) :
    natRun
        (contextualCycleConfig front 1 processed current [] tail suffix)
        (10 * processed.length + 7) =
      contextualFinalConfig front (processed ++ [current]) tail suffix := by
  let sourceTape :=
    contextualTape front (cycleFrame 1 processed []) tail suffix
  let targetTape :=
    contextualTape front (finalFrame (processed ++ [current])) tail suffix
  let delimiter := front.length + 2
  have hD : sourceTape delimiter = true := by
    have h := contextualCycle_delimiter front 1 processed [] tail suffix
    simpa [sourceTape, delimiter] using h
  have hnew : sourceTape (delimiter - 1) = false := by
    have h := contextualCycle_new_zero front 1 processed [] tail suffix
      (by omega)
    simpa [sourceTape, delimiter] using h
  have hprobe : sourceTape (delimiter - 2) = true := by
    have hbase := framedCycle_sentinel 1 processed [] (framedTape tail suffix)
    have hcontext := contextualTape_at front (cycleFrame 1 processed []) tail
      suffix 0
    have hzero : front.length + 0 = front.length := by omega
    rw [hzero] at hcontext
    have hcell : sourceTape front.length = true := by
      rw [show sourceTape front.length =
        framedTape (cycleFrame 1 processed []) (framedTape tail suffix) 0 by
          exact hcontext]
      exact hbase
    simpa [delimiter] using hcell
  have hpairs : RightPairsAt sourceTape (delimiter + 1) processed := by
    have h := contextualCycle_rightPairs front 1 processed [] tail suffix
    simpa [sourceTape, delimiter] using h
  have hmarker :
      sourceTape (delimiter + 1 + 2 * processed.length) = true := by
    have h := contextualCycle_marker front 1 processed [] tail suffix
    simpa [sourceTape, delimiter] using h
  obtain ⟨resultTape, hrun, hresultD, hresultPairs, hresultMobile,
      hresultMarker, hresultOutside⟩ :=
    natRun_finalCycle current delimiter processed sourceTape
      (by simp [delimiter]) hD hnew hprobe hpairs hmarker
  have htargetOutside :
      EqOutside targetTape sourceTape (front.length + 1)
        (front.length + 2 * processed.length + 3) := by
    simpa [targetTape, sourceTape] using
      contextualCycle_final_target_outside front processed current tail suffix
  have htargetTape :
      targetTape =
        framedTape
          (front ++ [true, true] ++ encR processed ++ [current, true] ++ tail)
          suffix := by
    simp [targetTape, contextualTape, finalFrame_append_singleton,
      List.append_assoc]
  have htargetD : targetTape (front.length + 1) = true := by
    rw [htargetTape]
    have h := framedTape_middle (front ++ [true])
      ([true] ++ encR processed ++ [current, true] ++ tail) suffix 0 (by simp)
    simpa using h
  have htargetPairs :
      RightPairsAt targetTape (front.length + 2) processed := by
    rw [htargetTape]
    have h := rightPairsAt_framedTape (front ++ [true, true]) processed
      ([current, true] ++ tail) suffix
    convert h using 1 <;> simp [List.append_assoc] <;> omega
  have htargetMobile :
      targetTape (front.length + 2 + 2 * processed.length) = current := by
    rw [htargetTape]
    have h := framedTape_middle
      (front ++ [true, true] ++ encR processed)
      ([current, true] ++ tail) suffix 0 (by simp)
    have hposition :
        (front ++ [true, true] ++ encR processed).length + 0 =
          front.length + 2 + 2 * processed.length := by
      simp [encR_length]
      omega
    rw [← hposition]
    simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using h
  have htape : resultTape = targetTape := by
    funext position
    by_cases hleft : position < front.length + 1
    · exact (hresultOutside position (by left; simp [delimiter]; omega)).trans
        (htargetOutside position (by left; omega)).symm
    by_cases hright :
        front.length + 2 * processed.length + 3 <= position
    · exact (hresultOutside position (by right; simp [delimiter]; omega)).trans
        (htargetOutside position (by right; omega)).symm
    by_cases hdelimiter : position = front.length + 1
    · subst position
      have hresult : resultTape (front.length + 1) = true := by
        convert hresultD using 1 <;> simp [delimiter] <;> omega
      exact hresult.trans htargetD.symm
    by_cases hpairsFinish :
        position < front.length + 2 + 2 * processed.length
    · apply hresultPairs.eqOn htargetPairs position
      · simp [delimiter]
        omega
      · omega
    · have hposition :
          position = front.length + 2 + 2 * processed.length := by omega
      subst position
      have hresult :
          resultTape (front.length + 2 + 2 * processed.length) = current := by
        convert hresultMobile using 1 <;> simp [delimiter] <;> omega
      exact hresult.trans htargetMobile.symm
  have hrun' :
      natRun
          (contextualCycleConfig front 1 processed current [] tail suffix)
          (10 * processed.length + 7) =
        ⟨.done, front.length + 2 * processed.length + 4, resultTape⟩ := by
    convert hrun using 1 <;>
      simp [contextualCycleConfig, sourceTape, delimiter] <;> omega
  rw [hrun', htape]
  unfold contextualFinalConfig
  congr 1 <;> simp <;> omega

/-! ## Composition of shifted cycles -/

/-- Starting at any shifted canonical cycle boundary, every remaining cycle
composes to the exact contextual final frame. -/
theorem natRun_contextualCycles_to_final (front processed unprocessed :
    List Bool) (current : Bool) (tail : List Bool)
    (suffix : Nat -> Bool) :
    natRun
        (contextualCycleConfig front (unprocessed.length + 1) processed
          current unprocessed tail suffix)
        (cycleFinishTime processed.length unprocessed) =
      contextualFinalConfig front (processed ++ current :: unprocessed) tail
        suffix := by
  induction unprocessed generalizing processed current with
  | nil =>
      simpa [cycleFinishTime] using
        natRun_contextualCycle_final front processed current tail suffix
  | cons next rest ih =>
      rw [cycleFinishTime, natRun_add]
      have hcycle := natRun_contextualCycle_nonfinal front
        (rest.length + 2) processed rest current next tail suffix (by omega)
      have hcycle' :
          natRun
              (contextualCycleConfig front ((next :: rest).length + 1)
                processed current (next :: rest) tail suffix)
              (10 * processed.length + 8) =
            contextualCycleConfig front (rest.length + 1)
              (processed ++ [current]) next rest tail suffix := by
        convert hcycle using 1 <;> simp <;> omega
      rw [hcycle']
      simpa [List.append_assoc] using
        ih (processed := processed ++ [current]) (current := next)

/-! ## Shifted startup scan -/

theorem contextualInitial_zero (front : List Bool) (k : Nat)
    (payload tail : List Bool) (suffix : Nat -> Bool) (offset : Nat)
    (hoffset : offset < k) :
    contextualTape front (initialFrame k payload) tail suffix
        (front.length + 1 + offset) = false := by
  rw [show front.length + 1 + offset =
    front.length + (1 + offset) by omega]
  rw [contextualTape_at]
  exact framedInitial_zero k payload (framedTape tail suffix) offset hoffset

theorem contextualInitial_delimiter (front : List Bool) (k : Nat)
    (payload tail : List Bool) (suffix : Nat -> Bool) :
    contextualTape front (initialFrame k payload) tail suffix
        (front.length + k + 1) = true := by
  rw [show front.length + k + 1 =
    front.length + (k + 1) by omega]
  rw [contextualTape_at]
  exact framedInitial_delimiter k payload (framedTape tail suffix)

theorem contextualInitial_firstPayload (front : List Bool) (k : Nat)
    (current : Bool) (rest tail : List Bool) (suffix : Nat -> Bool) :
    contextualTape front (initialFrame k (current :: rest)) tail suffix
        (front.length + k + 2) = current := by
  rw [show front.length + k + 2 =
    front.length + (k + 2) by omega]
  rw [contextualTape_at]
  exact framedInitial_firstPayload k current rest (framedTape tail suffix)

theorem writeNat_contextualInitial_first (front : List Bool) (k : Nat)
    (current : Bool) (rest tail : List Bool) (suffix : Nat -> Bool) :
    writeNat
        (contextualTape front (initialFrame k (current :: rest)) tail suffix)
        (front.length + k + 2) true =
      contextualTape front (cycleFrame k [] rest) tail suffix := by
  let pre := front ++ [true] ++ List.replicate k false ++ [true]
  have h := writeNat_framedTape_replace
    pre (rest ++ tail) current true suffix
  have hsource :
      contextualTape front (initialFrame k (current :: rest)) tail suffix =
        framedTape (pre ++ current :: (rest ++ tail)) suffix := by
    simp [contextualTape, initialFrame, pre, List.append_assoc]
  have htarget :
      contextualTape front (cycleFrame k [] rest) tail suffix =
        framedTape (pre ++ true :: (rest ++ tail)) suffix := by
    simp [contextualTape, cycleFrame, pre, List.append_assoc]
  have hposition : front.length + k + 2 = pre.length := by
    simp [pre]
    omega
  rw [hsource, htarget, hposition]
  exact h

/-- From the first unary-count cell at an arbitrary positive head, startup
reaches the first contextual cycle boundary in the same exact time. -/
theorem natRun_contextualScanFirst_to_firstCycle (front : List Bool)
    (current : Bool) (rest tail : List Bool) (suffix : Nat -> Bool) :
    natRun
        ⟨.scanFirst, front.length + 1,
          contextualTape front
            (initialFrame (rest.length + 1) (current :: rest)) tail suffix⟩
        (rest.length + 3) =
      contextualCycleConfig front (rest.length + 1) [] current rest tail
        suffix := by
  let tape := contextualTape front
    (initialFrame (rest.length + 1) (current :: rest)) tail suffix
  have hfirst : tape (front.length + 1) = false := by
    simpa [tape] using contextualInitial_zero front (rest.length + 1)
      (current :: rest) tail suffix 0 (by omega)
  have hfirstRun :
      natRun ⟨.scanFirst, front.length + 1, tape⟩ 1 =
        ⟨.scanZeros, front.length + 2, tape⟩ := by
    simpa [natRun] using
      natStep_scanFirst_zero (front.length + 1) tape hfirst
  have hzeros : forall offset, offset < rest.length ->
      tape (front.length + 2 + offset) = false := by
    intro offset hoffset
    have h := contextualInitial_zero front (rest.length + 1)
      (current :: rest) tail suffix (offset + 1) (by omega)
    have hposition :
        front.length + 1 + (offset + 1) =
          front.length + 2 + offset := by omega
    rw [← hposition]
    exact h
  have hzerosRun :
      natRun ⟨.scanZeros, front.length + 2, tape⟩ rest.length =
        ⟨.scanZeros, front.length + rest.length + 2, tape⟩ := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      natRun_scanZeros (front.length + 2) rest.length tape hzeros
  have hdelimiter : tape (front.length + rest.length + 2) = true := by
    simpa [tape] using contextualInitial_delimiter front (rest.length + 1)
      (current :: rest) tail suffix
  have hdelimiterRun :
      natRun ⟨.scanZeros, front.length + rest.length + 2, tape⟩ 1 =
        ⟨.initRead, front.length + rest.length + 3, tape⟩ := by
    simpa [natRun] using natStep_scanZeros_one
      (front.length + rest.length + 2) tape hdelimiter
  have hpayload : tape (front.length + rest.length + 3) = current := by
    simpa [tape] using contextualInitial_firstPayload front
      (rest.length + 1) current rest tail suffix
  have hwrite :
      writeNat tape (front.length + rest.length + 3) true =
        contextualTape front (cycleFrame (rest.length + 1) [] rest) tail
          suffix := by
    simpa [tape] using writeNat_contextualInitial_first front
      (rest.length + 1) current rest tail suffix
  have hinitRun :
      natRun ⟨.initRead, front.length + rest.length + 3, tape⟩ 1 =
        contextualCycleConfig front (rest.length + 1) [] current rest tail
          suffix := by
    have hstep := natStep_initRead
      (front.length + rest.length + 3) tape
    change natStep
      ⟨.initRead, front.length + rest.length + 3, tape⟩ = _
    rw [hstep]
    unfold contextualCycleConfig
    rw [hpayload, hwrite]
    congr 1 <;> simp <;> omega
  change natRun ⟨.scanFirst, front.length + 1, tape⟩
    (rest.length + 3) = _
  rw [show rest.length + 3 = 1 + (rest.length + (1 + 1)) by omega]
  rw [natRun_add, hfirstRun, natRun_add, hzerosRun, natRun_add,
    hdelimiterRun, hinitRun]

/-- Canonical scan-first input embedded in a finite two-sided context. -/
def contextualScanFirstConfig (front payload tail : List Bool)
    (suffix : Nat -> Bool) : NatConfig :=
  ⟨.scanFirst, front.length + 1,
    contextualTape front (initialFrame payload.length payload) tail suffix⟩

theorem natRun_contextualScanFirst_nonempty (front : List Bool)
    (current : Bool) (rest tail : List Bool) (suffix : Nat -> Bool) :
    natRun
        (contextualScanFirstConfig front (current :: rest) tail suffix)
        (gammaBodyTime (rest.length + 1)) =
      contextualFinalConfig front (current :: rest) tail suffix := by
  change natRun
      ⟨.scanFirst, front.length + 1,
        contextualTape front
          (initialFrame (rest.length + 1) (current :: rest)) tail suffix⟩
      (gammaBodyTime (rest.length + 1)) = _
  have htime :
      gammaBodyTime (rest.length + 1) =
        (rest.length + 3) + cycleFinishTime 0 rest := by
    rw [cycleFinishTime_closed]
    simp [gammaBodyTime]
    ring
  rw [htime, natRun_add,
    natRun_contextualScanFirst_to_firstCycle front current rest tail suffix]
  have hcycles := natRun_contextualCycles_to_final front [] rest current tail
    suffix
  simpa only [List.length_nil, List.nil_append] using hcycles

theorem natRun_contextualScanFirst_empty (front tail : List Bool)
    (suffix : Nat -> Bool) :
    natRun (contextualScanFirstConfig front [] tail suffix)
        (gammaBodyTime 0) =
      contextualFinalConfig front [] tail suffix := by
  let tape := contextualTape front (initialFrame 0 []) tail suffix
  have hbit : tape (front.length + 1) = true := by
    simpa [tape] using contextualInitial_delimiter front 0 [] tail suffix
  have hrun :
      natRun ⟨.scanFirst, front.length + 1, tape⟩ 1 =
        ⟨.done, front.length + 2, tape⟩ := by
    simpa [natRun] using
      natStep_scanFirst_one (front.length + 1) tape hbit
  have htape : tape = contextualTape front (finalFrame []) tail suffix := by
    simp [tape, contextualTape, initialFrame, finalFrame, encChain, encFinal]
  change natRun ⟨.scanFirst, front.length + 1, tape⟩
    (gammaBodyTime 0) = _
  rw [show gammaBodyTime 0 = 1 by rfl, hrun, htape]
  unfold contextualFinalConfig
  congr 1 <;> simp

/-- Exact shifted/contextual body theorem.  The fixed zipper begins at the
first unary-count cell after `front`, preserves `front`, `tail`, and `suffix`
pointwise, and halts at the first cell after the rewritten final frame. -/
theorem natRun_contextualScanFirst (front payload tail : List Bool)
    (suffix : Nat -> Bool) :
    natRun (contextualScanFirstConfig front payload tail suffix)
        (gammaBodyTime payload.length) =
      contextualFinalConfig front payload tail suffix := by
  cases payload with
  | nil => simpa using natRun_contextualScanFirst_empty front tail suffix
  | cons current rest =>
      simpa using natRun_contextualScanFirst_nonempty front current rest tail
        suffix

/-! ## Shifted first-hit control -/

/-- One step before the contextual final cycle halts, control is at the
successful final-marker branch. -/
theorem natRun_contextualCycle_penultimate (front processed : List Bool)
    (current : Bool) (tail : List Bool) (suffix : Nat -> Bool) :
    exists resultTape,
      natRun
          (contextualCycleConfig front 1 processed current [] tail suffix)
          (10 * processed.length + 6) =
        ⟨.forwardBlockStart true current,
          front.length + 2 * processed.length + 3, resultTape⟩ := by
  let sourceTape :=
    contextualTape front (cycleFrame 1 processed []) tail suffix
  let delimiter := front.length + 2
  have hD : sourceTape delimiter = true := by
    have h := contextualCycle_delimiter front 1 processed [] tail suffix
    simpa [sourceTape, delimiter] using h
  have hnew : sourceTape (delimiter - 1) = false := by
    have h := contextualCycle_new_zero front 1 processed [] tail suffix
      (by omega)
    simpa [sourceTape, delimiter] using h
  have hprobe : sourceTape (delimiter - 2) = true := by
    have hbase := framedCycle_sentinel 1 processed [] (framedTape tail suffix)
    have hcontext := contextualTape_at front (cycleFrame 1 processed []) tail
      suffix 0
    have hcell : sourceTape front.length = true := by
      rw [show sourceTape front.length =
        framedTape (cycleFrame 1 processed []) (framedTape tail suffix) 0 by
          simpa using hcontext]
      exact hbase
    simpa [delimiter] using hcell
  have hpairs : RightPairsAt sourceTape (delimiter + 1) processed := by
    have h := contextualCycle_rightPairs front 1 processed [] tail suffix
    simpa [sourceTape, delimiter] using h
  have hmarker :
      sourceTape (delimiter + 1 + 2 * processed.length) = true := by
    have h := contextualCycle_marker front 1 processed [] tail suffix
    simpa [sourceTape, delimiter] using h
  obtain ⟨resultTape, hrun, _⟩ :=
    natRun_cycleToMarker true current delimiter processed sourceTape
      (by simp [delimiter]) hD hnew hprobe hpairs hmarker
  refine ⟨resultTape, ?_⟩
  convert hrun using 1 <;>
    simp [contextualCycleConfig, sourceTape, delimiter] <;> omega

/-- All nonfinal contextual cycles compose while stopping exactly one step
before the final cycle halts. -/
theorem natRun_contextualCycles_penultimate (front processed unprocessed :
    List Bool) (current : Bool) (tail : List Bool)
    (suffix : Nat -> Bool) :
    exists finalCurrent head resultTape,
      natRun
          (contextualCycleConfig front (unprocessed.length + 1) processed
            current unprocessed tail suffix)
          (cycleFinishTime processed.length unprocessed - 1) =
        ⟨.forwardBlockStart true finalCurrent, head, resultTape⟩ := by
  induction unprocessed generalizing processed current with
  | nil =>
      obtain ⟨resultTape, hrun⟩ :=
        natRun_contextualCycle_penultimate front processed current tail suffix
      refine ⟨current, front.length + 2 * processed.length + 3,
        resultTape, ?_⟩
      simpa [cycleFinishTime] using hrun
  | cons next rest ih =>
      have hcycle := natRun_contextualCycle_nonfinal front
        (rest.length + 2) processed rest current next tail suffix (by omega)
      have hcycle' :
          natRun
              (contextualCycleConfig front ((next :: rest).length + 1)
                processed current (next :: rest) tail suffix)
              (10 * processed.length + 8) =
            contextualCycleConfig front (rest.length + 1)
              (processed ++ [current]) next rest tail suffix := by
        convert hcycle using 1 <;> simp <;> omega
      obtain ⟨finalCurrent, head, resultTape, hpenultimate⟩ :=
        ih (processed := processed ++ [current]) (current := next)
      have htailPositive :
          0 < cycleFinishTime (processed ++ [current]).length rest := by
        rw [cycleFinishTime_closed]
        omega
      have htime :
          cycleFinishTime processed.length (next :: rest) - 1 =
            (10 * processed.length + 8) +
              (cycleFinishTime (processed ++ [current]).length rest - 1) := by
        rw [cycleFinishTime]
        simp only [List.length_append, List.length_singleton]
        have htailPositive' :
            0 < cycleFinishTime (processed.length + 1) rest := by
          simpa only [List.length_append, List.length_singleton] using
            htailPositive
        omega
      refine ⟨finalCurrent, head, resultTape, ?_⟩
      rw [htime, natRun_add, hcycle', hpenultimate]

theorem natRun_contextualScanFirst_penultimate_nonempty (front : List Bool)
    (current : Bool) (rest tail : List Bool) (suffix : Nat -> Bool) :
    exists finalCurrent head resultTape,
      natRun
          (contextualScanFirstConfig front (current :: rest) tail suffix)
          (gammaBodyTime (rest.length + 1) - 1) =
        ⟨.forwardBlockStart true finalCurrent, head, resultTape⟩ := by
  obtain ⟨finalCurrent, head, resultTape, hcycles⟩ :=
    natRun_contextualCycles_penultimate front [] rest current tail suffix
  have htotal :
      gammaBodyTime (rest.length + 1) =
        (rest.length + 3) + cycleFinishTime 0 rest := by
    rw [cycleFinishTime_closed]
    simp [gammaBodyTime]
    ring
  have hcyclesPositive : 0 < cycleFinishTime 0 rest := by
    rw [cycleFinishTime_closed]
    omega
  have htime :
      gammaBodyTime (rest.length + 1) - 1 =
        (rest.length + 3) + (cycleFinishTime 0 rest - 1) := by
    omega
  refine ⟨finalCurrent, head, resultTape, ?_⟩
  change natRun
      ⟨.scanFirst, front.length + 1,
        contextualTape front
          (initialFrame (rest.length + 1) (current :: rest)) tail suffix⟩
      (gammaBodyTime (rest.length + 1) - 1) = _
  rw [htime, natRun_add,
    natRun_contextualScanFirst_to_firstCycle front current rest tail suffix]
  simpa only [List.length_nil] using hcycles

theorem natRun_contextualScanFirst_penultimate_not_done
    (front payload tail : List Bool) (suffix : Nat -> Bool) :
    (natRun (contextualScanFirstConfig front payload tail suffix)
      (gammaBodyTime payload.length - 1)).state ≠ .done := by
  cases payload with
  | nil => simp [contextualScanFirstConfig, gammaBodyTime, natRun]
  | cons current rest =>
      obtain ⟨finalCurrent, head, resultTape, hrun⟩ :=
        natRun_contextualScanFirst_penultimate_nonempty front current rest tail
          suffix
      have hrun' :
          natRun
              (contextualScanFirstConfig front (current :: rest) tail suffix)
              (gammaBodyTime (current :: rest).length - 1) =
            ⟨.forwardBlockStart true finalCurrent, head, resultTape⟩ := by
        simpa only [List.length_cons] using hrun
      rw [hrun']
      simp

/-- The contextual endpoint is a first hit: at every strictly earlier time
the shifted zipper is in neither absorbing terminal control. -/
theorem natRun_contextualScanFirst_active (front payload tail : List Bool)
    (suffix : Nat -> Bool) (elapsed : Nat)
    (helapsed : elapsed < gammaBodyTime payload.length) :
    let config :=
      natRun (contextualScanFirstConfig front payload tail suffix) elapsed
    config.state ≠ .done ∧ config.state ≠ .reject := by
  dsimp only
  let initial := contextualScanFirstConfig front payload tail suffix
  have hpositive : 0 < gammaBodyTime payload.length := by
    simp [gammaBodyTime]
  constructor
  · intro hdone
    have hpersist := natRun_state_done hdone
      (gammaBodyTime payload.length - 1 - elapsed)
    have htime :
        gammaBodyTime payload.length - 1 =
          elapsed + (gammaBodyTime payload.length - 1 - elapsed) := by
      omega
    have hpenultimate :=
      natRun_contextualScanFirst_penultimate_not_done front payload tail suffix
    apply hpenultimate
    rw [htime, natRun_add]
    exact hpersist
  · intro hreject
    have hpersist := natRun_state_reject hreject
      (gammaBodyTime payload.length - elapsed)
    have htime :
        gammaBodyTime payload.length =
          elapsed + (gammaBodyTime payload.length - elapsed) := by
      omega
    have hfinal := natRun_contextualScanFirst front payload tail suffix
    have hfinalState := congrArg NatConfig.state hfinal
    rw [htime, natRun_add] at hfinalState
    rw [hpersist] at hfinalState
    simp [contextualFinalConfig] at hfinalState

end OperationalGammaZipper
end StreamingMagnification
end Frontier
end Pnp4

#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.natRun_contextualCycle_nonfinal
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.natRun_contextualCycle_final
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.natRun_contextualCycles_to_final
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.natRun_contextualScanFirst
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.natRun_contextualScanFirst_active
