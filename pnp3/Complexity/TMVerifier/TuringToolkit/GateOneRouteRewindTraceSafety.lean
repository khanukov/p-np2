import Complexity.TMVerifier.TuringToolkit.GateOnePassBDriverTraceSafety
import Complexity.TMVerifier.TuringToolkit.GateOneAResult

/-!
# GN-3B2fA unary/constant route-rewind trace safety (2026-09-01)

**Progress classification: infrastructure, not P-vs-NP mainline progress.**

This module closes trace safety for the two read-only pass-B routes omitted by
the binary driver slice.  A tag-independent forward-route theorem composes the
merged validation/rewind prefix with any strict valid frame route.  The generic
zero-rewrite rewind then executes exactly one `readAResetStart` bridge, scans a
caller-supplied `G1RepairSkip` run in reverse repair mode, and finishes with the
stationary `bof` and `bRepairDone` rows.  Its exact horizon is
`4 * left.length + 6`; there is no spent rewrite cycle and no left clamp.

The unary (`input`/`not`) and constant routes instantiate those two generic
pieces at their canonical frame splits.  Their real-initial trace capstones
meet the existing exact endpoints at `g1UReadASteps` and
`g1ConstReadASteps`.  One further stationary step safely activates unary at
`g1ABofConfig r false` and constant at `g1CombineConfig r b`.

Empty unary values and later unary install/driver/repair/output behavior remain
separate.  For canonical constants, `spec = some b` names the result carried to
combine; this slice stops there and does not execute the output kernel.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

private theorem g1RouteAligned_stay_local_safe {W h : Nat}
    (hh : h < G1M.tapeLength W) (tape : Fin (G1M.tapeLength W) -> Bool)
    (mode mode' : G1Mode) (position position' : G1FramePosition)
    (b0 b1 b2 b0' b1' b2' : Bool) (ctx ctx' : G1Ctx)
    (hspan : h < gnLocalSpan W)
    (hstep : g1Transition (0 : Fin 1)
      (g1State mode position b0 b1 b2 ctx) (tape ⟨h, hh⟩) =
      (0, g1State mode' position' b0' b1' b2' ctx',
        tape ⟨h, hh⟩, Move.stay)) :
    G1LocalStepSafe
      (g1AlignedConfig W h hh tape mode position b0 b1 b2 ctx) := by
  simp only [G1LocalStepSafe, g1AlignedConfig_head_val,
    g1AlignedConfig_state, g1AlignedConfig_tape]
  refine ⟨hspan, ?_, ?_⟩
  · intro hleft
    change (g1Transition (0 : Fin 1) (g1State mode position b0 b1 b2 ctx)
      (tape ⟨h, hh⟩)).snd.snd.snd = Move.left at hleft
    rw [hstep] at hleft
    exact Move.noConfusion hleft
  · intro hright
    change (g1Transition (0 : Fin 1) (g1State mode position b0 b1 b2 ctx)
      (tape ⟨h, hh⟩)).snd.snd.snd = Move.right at hright
    rw [hstep] at hright
    exact Move.noConfusion hright

/-! ## Tag-independent forward-route safety -/

/-- Validation/rewind followed by any strict non-rejecting pass-B frame route.
The route is read-only and the theorem has no tag-specific premise. -/
theorem g1CS_readB_forward_route_runSafe (r : G1Request) (hc : r.Canonical)
    (route suffix : List G1Frame)
    (hsplit : route ++ suffix = encodeG1Frames r ++ [G1Frame.blank])
    (hpath : G1ValidPath .readBStart route)
    (hroom : 4 * route.length < gnLocalSpan (encodeG1 r).length) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1ReadBHandoffSteps r + 4 * route.length) := by
  have htape : g1ListTape (n := (encodeG1 r).length)
      ((route ++ suffix).flatMap G1Frame.bits) =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape := by
    rw [hsplit]
    exact g1ListTape_validation_eq_initial r
  have hscan0 := g1Forward_scanFrom_runSafe
    (W := (encodeG1 r).length) ([] : List G1Frame) route suffix
    .readBStart g1Ctx0 hpath (by simpa using hroom)
  have hscan : G1RunSafe
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBHandoffSteps r)) (4 * route.length) := by
    apply G1RunSafe.transport _ hscan0
    rw [g1CS_validate_rewind_readB_exact r hc]
    simp only [List.length_nil, Nat.mul_zero]
    rw [show ([] : List G1Frame) ++ route ++ suffix = route ++ suffix by simp,
      htape]
  exact G1RunSafe.add (g1ValidationRewind_run_safe_to_readB r hc) hscan

/-! ## Generic zero-rewrite rewind -/

/-- The pure route rewind is safe for its exact existing horizon.  The room
premise is about the concrete route footprint, not `vals.length`; the proof
uses only the bridge, a `G1RepairSkip` scan, and the two stationary finish
rows. -/
theorem g1CS_route_rewind_runSafe (r : G1Request) (left tail : List G1Frame)
    (hleft : ∀ f ∈ left, G1RepairSkip f)
    (hsplit : [G1Frame.bof] ++ left ++ tail =
      encodeG1Frames r ++ [G1Frame.blank])
    (hroom : 4 * (1 + left.length) + 3 <
      gnLocalSpan (encodeG1 r).length) (ctx : G1Ctx) :
    G1RunSafe
      (g1AlignedConfig (encodeG1 r).length (4 * (1 + left.length)) (by
        apply lt_of_lt_of_le (b := gnLocalSpan (encodeG1 r).length)
        · omega
        · exact gnLocalSpan_le_g1_tapeLength (encodeG1 r).length)
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .readAResetStart .p0 false false false ctx)
      (4 * left.length + 6) := by
  have hsafe : 4 * (1 + left.length) <
      G1M.tapeLength (encodeG1 r).length := by
    apply lt_of_lt_of_le (b := gnLocalSpan (encodeG1 r).length)
    · omega
    · exact gnLocalSpan_le_g1_tapeLength (encodeG1 r).length
  let start := g1AlignedConfig (encodeG1 r).length
    (4 * (1 + left.length)) hsafe
    (G1M.initialConfig (g1Point (encodeG1 r))).tape
    .readAResetStart .p0 false false false ctx
  have hbridgeSafe : G1RunSafe start 1 := by
    apply G1RunSafe.succ (G1RunSafe.empty start)
    apply g1LocalStepSafe_of_interior
    · change 0 < 4 * (1 + left.length)
      omega
    · change 4 * (1 + left.length) + 1 <
        gnLocalSpan (encodeG1 r).length
      omega
  have hbridge := g1CS_step_readAReset_bridge (encodeG1 r).length
    (4 * (1 + left.length)) hsafe (by omega)
    (G1M.initialConfig (g1Point (encodeG1 r))).tape ctx
  have htape : g1ListTape (n := (encodeG1 r).length)
      (([G1Frame.bof] ++ left ++ tail).flatMap G1Frame.bits) =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape := by
    rw [hsplit]
    exact g1ListTape_validation_eq_initial r
  have hstart : TM.runConfig (M := G1M) start 1 =
      g1AlignedConfig (encodeG1 r).length
        (4 * (1 + left.length) - 1) (by omega)
        (g1ListTape (([G1Frame.bof] ++ left ++ tail).flatMap G1Frame.bits))
        .bRepairSeek .p3 false false false ctx := by
    rw [htape]
    simpa [start] using hbridge
  have hscan0 := g1CS_repair_scan_skip_runSafe
    (W := (encodeG1 r).length) [G1Frame.bof] left tail ctx
    (by simp) hleft (by simpa using hroom)
  have hscan : G1RunSafe (TM.runConfig (M := G1M) start 1)
      (4 * left.length) := by
    rw [hstart]
    simpa using hscan0
  have hprefix := G1RunSafe.add hbridgeSafe hscan
  have hscanExact := g1CS_repair_scan_skip (encodeG1 r).length
    [G1Frame.bof] left tail ctx (by simp) hleft (by
      apply lt_of_lt_of_le (b := gnLocalSpan (encodeG1 r).length)
      · simp only [List.length_singleton]
        omega
      · exact gnLocalSpan_le_g1_tapeLength (encodeG1 r).length)
  have hafter : TM.runConfig (M := G1M)
      (TM.runConfig (M := G1M) start 1) (4 * left.length) =
      g1AlignedConfig (encodeG1 r).length 3 (by omega)
        (g1ListTape (([G1Frame.bof] ++ left ++ tail).flatMap G1Frame.bits))
        .bRepairSeek .p3 false false false ctx := by
    rw [hstart]
    simpa using hscanExact
  have hfinish0 := g1CS_repair_finish_runSafe
    (W := (encodeG1 r).length) (left ++ tail) ctx (by omega)
  have hfinish : G1RunSafe
      (TM.runConfig (M := G1M)
        (TM.runConfig (M := G1M) start 1) (4 * left.length)) 5 := by
    rw [hafter]
    simpa [List.append_assoc] using hfinish0
  have hall := G1RunSafe.add hprefix (by
    simpa only [runConfig_add] using hfinish)
  change G1RunSafe start (4 * left.length + 6)
  simpa only [show 1 + 4 * left.length + 5 =
    4 * left.length + 6 by omega] using hall

/-! ## Unary and constant real-initial trace safety -/

/-- `input` and `not` are safe through their exact repaired read-A endpoint.
No value-list premise is needed, so the empty-value/OOB case remains intact. -/
theorem g1CS_readA_unary_repaired_trace_safe (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .input ∨ r.tag = .not) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1UReadASteps r) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1UReadASteps r) = g1ReadAConfig r false := by
  have hroute : G1RunSafe
      (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1ReadARouteSteps r) := by
    simpa [g1ReadARouteSteps] using
      g1CS_readB_forward_route_runSafe r hc
        (g1TagRouteFrames r) (g1TagRouteRest r) (g1TagRoute_split r)
        (g1TagRoute_validPath r) (by
          simp [gnLocalSpan, encodeG1_length]
          omega)
  have hrew0 := g1CS_route_rewind_runSafe r (g1AUnaryLeft r)
    (g1TagRouteRest r) (g1AUnaryLeft_skip r) (g1AUnaryLeft_split r) (by
      simp [gnLocalSpan, encodeG1_length]
      omega) g1Ctx0
  have hrew : G1RunSafe
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadARouteSteps r)) (g1AUnaryRewindSteps r) := by
    rw [g1CS_readB_route_unary_exact r hc ht]
    simpa only [g1AUnaryLeft_length,
      show 4 * (1 + (r.tag.units + 1)) = 4 * (r.tag.units + 2) by omega,
      show 4 * (r.tag.units + 1) + 6 = g1AUnaryRewindSteps r by
        simp [g1AUnaryRewindSteps]
        omega] using hrew0
  constructor
  · simpa [g1UReadASteps] using G1RunSafe.add hroute hrew
  · exact g1CS_readA_unary_repaired_exact r hc ht

/-- `const` is safe through literal store and its pure rewind, ending with the
exact result context at the pre-dispatch boundary. -/
theorem g1CS_const_repaired_trace_safe (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .const) (b : Bool) (hs : r.spec = some b) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ConstReadASteps r) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1ConstReadASteps r) = g1ReadAResultConfig r b := by
  obtain ⟨harg, -⟩ := g1_const_fields_of_spec ht hs
  have hscan : G1RunSafe
      (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1FieldRouteSteps r) := by
    simpa [g1FieldRouteSteps] using
      g1CS_readB_forward_route_runSafe r hc
        (g1FieldRouteFrames r) (g1FieldRouteRest r) (g1FieldRoute_split r)
        (g1FieldRoute_validPath_const r ht b harg) (by
          simp [gnLocalSpan, encodeG1_length]
          omega)
  have hscanExact := g1CS_readB_scan r hc (g1FieldRouteFrames r)
    (g1FieldRouteRest r) (g1FieldRoute_split r)
    (g1FieldRoute_validPath_const r ht b harg)
    (g1_route_lt_tapeLength r _ (by
      rw [g1FieldRouteFrames_length]
      omega))
  rw [g1FieldRoute_advance_const r ht b harg] at hscanExact
  have hstore0 : G1RunSafe
      (g1AlignedConfig (encodeG1 r).length
        (4 * (g1FieldRouteFrames r).length)
        (g1_route_lt_tapeLength r _ (by
          rw [g1FieldRouteFrames_length]
          omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        (g1ConstMode b) .p0 false false false g1Ctx0) 1 := by
    apply G1RunSafe.succ (G1RunSafe.empty _)
    apply g1LocalStepSafe_of_interior
    · simp [g1FieldRouteFrames_length, ht]
    · simp [g1FieldRouteFrames_length, gnLocalSpan, encodeG1_length]
      omega
  have hstore : G1RunSafe
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1FieldRouteSteps r)) 1 := by
    apply G1RunSafe.transport _ hstore0
    exact (by simpa [g1FieldRouteSteps] using hscanExact.symm)
  have hroute : G1RunSafe
      (G1M.initialConfig (g1Point (encodeG1 r))) (g1ConstRouteSteps r) := by
    simpa [g1ConstRouteSteps] using G1RunSafe.add hscan hstore
  have hrew0 := g1CS_route_rewind_runSafe r (g1AConstLeft r)
    (g1FieldRouteRest r) (g1AConstLeft_skip r) (g1AConstLeft_split r) (by
      simp [gnLocalSpan, encodeG1_length]
      omega) (g1ResultCtx b)
  have hrew : G1RunSafe
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ConstRouteSteps r)) (g1AConstRewindSteps r) := by
    rw [g1CS_readB_route_const_exact r hc ht b hs]
    simpa only [g1AConstLeft_length,
      show 4 * (1 + (r.tag.units + r.arg1 + 2)) =
        4 * (r.tag.units + r.arg1 + 3) by omega,
      show 4 * (r.tag.units + r.arg1 + 2) + 6 =
        g1AConstRewindSteps r by
          simp [g1AConstRewindSteps]
          omega] using hrew0
  constructor
  · simpa [g1ConstReadASteps] using G1RunSafe.add hroute hrew
  · exact g1CS_const_repaired_exact r hc ht b hs

/-! ## Safe live activation -/

/-- The unary pre-dispatch endpoint takes its stationary entry row safely. -/
theorem g1CS_readA_unary_activate_runSafe (r : G1Request) :
    G1RunSafe (g1ReadAConfig r false) 1 := by
  apply G1RunSafe.succ (G1RunSafe.empty _)
  simp only [runConfig_zero, g1ReadAConfig]
  apply g1RouteAligned_stay_local_safe
  · simp [gnLocalSpan]
  · exact g1Transition_readAStart_entry (0 : Fin 1) .p0 false false false _
      (g1Ctx0.withVB false) rfl

/-- The constant result-context endpoint takes its stationary result row
safely. -/
theorem g1CS_readA_const_activate_runSafe (r : G1Request) (b : Bool) :
    G1RunSafe (g1ReadAResultConfig r b) 1 := by
  apply G1RunSafe.succ (G1RunSafe.empty _)
  simp only [runConfig_zero, g1ReadAResultConfig]
  apply g1RouteAligned_stay_local_safe
  · simp [gnLocalSpan]
  · exact g1Transition_readAStart_result (0 : Fin 1) .p0 false false false _
      (g1ResultCtx b) rfl

/-- Unary is safe through the one-step live activation at its exact existing
`g1UActivatedSteps` schedule. -/
theorem g1CS_activate_unary_trace_safe (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .input ∨ r.tag = .not) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1UActivatedSteps r) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1UActivatedSteps r) = g1ABofConfig r false := by
  have hprefix := g1CS_readA_unary_repaired_trace_safe r hc ht
  have hlast : G1RunSafe
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1UReadASteps r)) 1 := by
    rw [hprefix.2]
    exact g1CS_readA_unary_activate_runSafe r
  constructor
  · simpa [g1UActivatedSteps] using G1RunSafe.add hprefix.1 hlast
  · exact g1CS_activate_unary_exact r hc ht

/-- Constant is safe through the one-step live activation and stops at
`combineStart`; the output door is not executed. -/
theorem g1CS_activate_const_trace_safe (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .const) (b : Bool) (hs : r.spec = some b) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ConstActivatedSteps r) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1ConstActivatedSteps r) = g1CombineConfig r b := by
  have hprefix := g1CS_const_repaired_trace_safe r hc ht b hs
  have hlast : G1RunSafe
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ConstReadASteps r)) 1 := by
    rw [hprefix.2]
    exact g1CS_readA_const_activate_runSafe r b
  constructor
  · simpa [g1ConstActivatedSteps] using G1RunSafe.add hprefix.1 hlast
  · exact g1CS_activate_const_exact r hc ht b hs

/-! ## Existing literal requests, at the merged route/activation totals -/

namespace G1RouteRewindTraceProbes

open G1AResultProbes

/-- Actual merged schedules: validation/rewind, forward route, pure rewind,
and (for the second number in each pair) the one live stationary activation. -/
theorem literal_route_activation_steps :
    g1UReadASteps reqInputT = 99 ∧ g1UActivatedSteps reqInputT = 100 ∧
      g1UReadASteps reqNotF = 131 ∧ g1UActivatedSteps reqNotF = 132 ∧
      g1ConstReadASteps reqConstF = 116 ∧
        g1ConstActivatedSteps reqConstF = 117 ∧
      g1ConstReadASteps reqConstT = 132 ∧
        g1ConstActivatedSteps reqConstT = 133 := by
  decide

theorem literal_input_trace_safe :
    (G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqInputT))) 99 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqInputT))) 99 =
        g1ReadAConfig reqInputT false) ∧
    (G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqInputT))) 100 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqInputT))) 100 =
        g1ABofConfig reqInputT false) := by
  have hr := g1CS_readA_unary_repaired_trace_safe reqInputT
    literal_canonical.1 (Or.inl rfl)
  have ha := g1CS_activate_unary_trace_safe reqInputT
    literal_canonical.1 (Or.inl rfl)
  rw [literal_route_activation_steps.1] at hr
  rw [literal_route_activation_steps.2.1] at ha
  exact ⟨hr, ha⟩

theorem literal_not_trace_safe :
    (G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqNotF))) 131 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqNotF))) 131 =
        g1ReadAConfig reqNotF false) ∧
    (G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqNotF))) 132 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqNotF))) 132 =
        g1ABofConfig reqNotF false) := by
  have hr := g1CS_readA_unary_repaired_trace_safe reqNotF
    literal_canonical.2.1 (Or.inr rfl)
  have ha := g1CS_activate_unary_trace_safe reqNotF
    literal_canonical.2.1 (Or.inr rfl)
  rw [literal_route_activation_steps.2.2.1] at hr
  rw [literal_route_activation_steps.2.2.2.1] at ha
  exact ⟨hr, ha⟩

theorem literal_const_false_trace_safe :
    (G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqConstF))) 116 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqConstF))) 116 =
        g1ReadAResultConfig reqConstF false) ∧
    (G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqConstF))) 117 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqConstF))) 117 =
        g1CombineConfig reqConstF false) := by
  have hr := g1CS_const_repaired_trace_safe reqConstF
    literal_canonical.2.2.2.2.1 rfl false literal_specs.2.2.2.2.1
  have ha := g1CS_activate_const_trace_safe reqConstF
    literal_canonical.2.2.2.2.1 rfl false literal_specs.2.2.2.2.1
  rw [literal_route_activation_steps.2.2.2.2.1] at hr
  rw [literal_route_activation_steps.2.2.2.2.2.1] at ha
  exact ⟨hr, ha⟩

theorem literal_const_true_trace_safe :
    (G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqConstT))) 132 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqConstT))) 132 =
        g1ReadAResultConfig reqConstT true) ∧
    (G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqConstT))) 133 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqConstT))) 133 =
        g1CombineConfig reqConstT true) := by
  have hr := g1CS_const_repaired_trace_safe reqConstT
    literal_canonical.2.2.2.2.2 rfl true literal_specs.2.2.2.2.2
  have ha := g1CS_activate_const_trace_safe reqConstT
    literal_canonical.2.2.2.2.2 rfl true literal_specs.2.2.2.2.2
  rw [literal_route_activation_steps.2.2.2.2.2.2.1] at hr
  rw [literal_route_activation_steps.2.2.2.2.2.2.2] at ha
  exact ⟨hr, ha⟩

end G1RouteRewindTraceProbes

end Pnp3.Internal.PsubsetPpoly.TM
