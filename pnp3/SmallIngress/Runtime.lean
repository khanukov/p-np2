import Stream.Kernel
import Stream.Prototype
import Lean
namespace SmallIngress
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
/-- Finite controls only; these rows receive neither a decoded n nor a tape initializer. -/
def q (i : Nat) : Fin 288 := ⟨i%288,Nat.mod_lt _ (by decide)⟩
def rows (s : Fin 288) (b : Option Bool) : Fin 288 × Option Bool × Move :=
  match s.val,b with
  | 216,some false => (q 256,some false,.right)
  | 256,some true => (q 257,some true,.left)
  | 256,some false => (q 260,some false,.right)
  | 257,some false => (q 258,none,.right)
  | 258,some true => (q 259,some true,.right)
  | 259,some b => (q 259,some b,.right)
  | 259,none => (q 270,none,.right)
  | 270,some true => (q 271,some false,.right)
  | 271,none => (q 254,none,.stay)
  | 260,some true => (q 261,none,.right)
  | 261,some false => (q 262,some true,.right)
  | 261,some true => (q 263,some true,.right)
  | 262,some b => (q 262,some b,.right)
  | 262,none => (q 266,none,.right)
  | 266,some true => (q 267,some false,.right)
  | 267,some _ => (q 268,some false,.right)
  | 268,none => (q 269,none,.right)
  | 269,none => (q 272,some true,.left)
  | 272,none => (q 254,none,.stay)
  | 263,some b => (q 263,some b,.right)
  | 263,none => (q 273,none,.right)
  | 273,some true => (q 274,some false,.right)
  | 274,some _ => (q 275,some false,.right)
  | 275,none => (q 276,none,.right)
  | 276,none => (q 277,some true,.right)
  | 277,none => (q 278,some true,.left)
  | 278,some true => (q 279,some true,.left)
  | 279,none => (q 254,none,.stay)
  | i,b => if h : i < 256 then
      let a := FixedRawLengthFence.prefixed.step ⟨i,h⟩ b
      (q a.1.val,a.2)
    else (q 255,b,.stay)
def producer : UniformTM where
  stateCount := 288
  start := q 0
  accept := q 254
  reject := q 255
  accept_ne_reject := by decide
  rawStep := rows
/-- The exact existing Stream table is the suffix, including its all-n kernel. -/
def machine : UniformTM := producer.seq Stream.machine
/-- Complete source frame: n=0 uses consumed tag cell 7 as the seek hole. -/
def prepared {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) (z n : Nat) :
    Fin (tapeLength (pairLength a m) B) → Option Bool := fun i =>
  if n=0 ∧ i.val=7 then none else FixedRawLengthFence.countdownTape B x w z 0 n i
namespace Target
/-- Frozen full accepted raw target, with the SAME dependent parsed input and
all arities. Work exits are explicitly not semantic acceptance. -/
def AcceptedOrbit (k : Nat) : Prop :=
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true →
    ∃ pr : AcceptedBody.Parsed k,
      contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr ∧
      Pnp3.Models.Partial.tableLen pr.2.n ≤ a+m ∧
      ∃ (z T : Nat)
        (hH : a+m+z+pr.2.n+3 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
        FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
        T ≤ 4096*(pairLength a m+1)^2 ∧
        let U := Body.extend (Body.installedTape (prepared
          (FixedRawLengthFence.allocation (pairLength a m)) x w z pr.2.n) (a+m+z+2) pr.2.n)
        (∀ r, r<2^pr.2.n → ∃ t, t ≤ T ∧
          machine.run t (initialConfig machine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
            producer.seqEmbedRight Stream.machine
              ⟨Stream.paid (Stream.Target.mode U (Stream.Target.cursor (9+2*z) (a+m) r) (a+m)),⟨a+m+z+pr.2.n+3,hH⟩,
                fun i => Stream.Target.image U (a+m) z pr.2.n (9+2*z) r (r+1) true i.val⟩) ∧
        ∃ hp : Stream.Target.cursor (9+2*z) (a+m) (2^pr.2.n) <
          tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)),
          machine.run T (initialConfig machine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
            producer.seqEmbedRight Stream.machine
              ⟨Stream.q (if Stream.Target.cursor (9+2*z) (a+m) (2^pr.2.n)=a+m then 57 else 58),
                ⟨Stream.Target.cursor (9+2*z) (a+m) (2^pr.2.n),hp⟩,
                fun i => Stream.Target.image U (a+m) z pr.2.n (9+2*z) (2^pr.2.n) (2^pr.2.n) false i.val⟩
end Target
end SmallIngress

namespace SmallIngress
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
private abbrev Old := FixedRawLengthFence.prefixed
/-- Whole-Config injection, keeping head and every tape cell. -/
def liftOld {N B : Nat} (c : Config Old.stateCount N B) : Config producer.stateCount N B :=
  ⟨q c.state.val,c.head,c.tape⟩
private theorem inherited_rows : ∀ (s : Fin 256) (b : Option Bool),
    ¬ (s.val=216 ∧ b=some false) →
    producer.step (q s.val) b =
      (q (Old.step s b).1.val,(Old.step s b).2) := by
  decide
private theorem redirected_reject : Old.step ⟨216,by decide⟩ (some false) =
    (Old.reject,some false,.stay) := by decide
private theorem lift_step {N B : Nat} (c : Config Old.stateCount N B)
    (safe : (Old.step c.state (c.tape c.head)).1 ≠ Old.reject) :
    producer.stepConfig (liftOld c) = liftOld (Old.stepConfig c) := by
  have row := inherited_rows c.state (c.tape c.head) (by
    rintro ⟨hs,hb⟩
    have he : c.state=(⟨216,by decide⟩ : Fin 256) := Fin.ext hs
    rw [he,hb,redirected_reject] at safe
    exact safe rfl)
  apply Config.ext_parts
  · exact congrArg Prod.fst row
  · change moveHead c.head (producer.step (q c.state.val) (c.tape c.head)).2.2 = _
    rw [row]; rfl
  · funext i
    change (if i=c.head then (producer.step (q c.state.val) (c.tape c.head)).2.1 else c.tape i) = _
    rw [row]; rfl
/-- Any old run whose endpoint is nonreject survives on the new producer,
including the complete tape, all earlier times, and the old nonreject endpoint. -/
theorem preserves_nonreject {N B : Nat} (c : Config Old.stateCount N B) (T : Nat)
    (safe : (Old.run T c).state ≠ Old.reject) :
    producer.run T (liftOld c) = liftOld (Old.run T c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    have prior : (Old.run T c).state ≠ Old.reject := by
      intro h
      have eq := Old.run_reject_of_le c h (show T ≤ T+1 by omega)
      exact safe (by rw [eq]; exact h)
    rw [UniformTM.run,ih prior]
    exact lift_step _ safe

end SmallIngress

namespace SmallIngress
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open PairEncoding
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
attribute [local irreducible] UniformTM.run
private abbrev Gate := FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
private abbrev gateStart := @FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
private def liftGate {R B : Nat} (c : Config Gate.stateCount R B) : Config Old.stateCount R B :=
  FixedRawLengthFence.machine.seqEmbedRight FixedRawLengthFence.G (
  FixedPairConcatSentinel.machine.seqEmbedRight FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.tailMachine (
  FixedPairSeparatorCursor.machine.seqEmbedRight FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.tailMachine (
  FixedPairSeparatorHole.machine.seqEmbedRight FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.tailMachine (
  FixedPairTagRemoval.machine.seqEmbedRight FixedPairTagRemovalShiftAlignmentCountdown.tailMachine (
  FixedPairOriginShiftBootstrap.machine.seqEmbedRight FixedPairOriginShiftAlignmentCountdown.tailMachine (
  FixedPairOriginAlignment.machine.seqEmbedRight FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.tailMachine (
  FixedPairContentMarkerErase.machine.seqEmbedRight FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.tailMachine (
  c))))))))
private theorem raw_gate {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (hroom : 2*pairLength a m+2 ≤ B) (s : Nat) :
    Old.run (FixedRawLengthFence.installClock (pairLength a m)+FixedRawLengthFence.contentClock a m+s) (initialConfig Old B (encodePair x w)) =
      liftGate (Gate.run s {gateStart B x w with tape := FixedRawLengthFence.fencedContentTape B x w}) := by
  rw [Old.run_add, FixedRawLengthFence.raw_fenced_content_exact x w hroom]
  have he : (⟨⟨109, by decide⟩, ⟨a+m, by simp only [tapeLength,pairLength]; omega⟩,
      FixedRawLengthFence.fencedContentTape B x w⟩ : Config Old.stateCount (pairLength a m) B) =
      liftGate {gateStart B x w with tape := FixedRawLengthFence.fencedContentTape B x w} := by rfl
  rw [he]
  simp only [liftGate, FixedRawLengthFence.prefixed,
    FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.machine,
    FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.machine,
    FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.machine,
    FixedPairTagRemovalShiftAlignmentCountdown.machine,
    FixedPairOriginShiftAlignmentCountdown.machine,
    FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine,
    FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine,
    UniformTM.seq_run_right]

end SmallIngress
namespace SmallIngress
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open PairEncoding
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
attribute [local irreducible] UniformTM.run
private theorem raw_tag_old {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true) :
    Old.run (FixedRawLengthFence.installClock (pairLength a m)+FixedRawLengthFence.contentClock a m+3*(a+m)+7)
      (initialConfig Old (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
      ⟨⟨124,by decide⟩,⟨8,by
        have h := (FixedRawLengthFence.resource_bounds (pairLength a m)).1
        have hN := (FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.gate_first_arrival (B := 0) x w tag).2.2.2.2
        simp only [tapeLength,pairLength] at *; omega⟩,
        FixedRawLengthFence.fencedContentTape (FixedRawLengthFence.allocation (pairLength a m)) x w⟩ := by
  let B := FixedRawLengthFence.allocation (pairLength a m)
  have resource := (FixedRawLengthFence.resource_bounds (pairLength a m)).1
  let f : Fin (tapeLength (pairLength a m) B) :=
    ⟨FixedRawLengthFence.fencePos (pairLength a m),by
      simp only [FixedRawLengthFence.fencePos,tapeLength] at *; dsimp [B]; omega⟩
  have hframe : {gateStart B x w with tape := FixedRawLengthFence.fencedContentTape B x w} =
      {gateStart B x w with tape := Function.update (gateStart B x w).tape f (some false)} := by
    apply Config.ext_parts
    · rfl
    · rfl
    funext i
    change FixedRawLengthFence.fencedContentTape B x w i =
      Function.update (FixedPairContentMarkerErase.contentTape B x w) f (some false) i
    by_cases hi : i.val < a+m
    · have hn : i.val ≠ FixedRawLengthFence.fencePos (pairLength a m) := by
        simp only [FixedRawLengthFence.fencePos,pairLength]; omega
      simp [FixedRawLengthFence.fencedContentTape,FixedPairContentMarkerErase.contentTape,hi,Fin.ext_iff,f,hn]
    · simp [FixedRawLengthFence.fencedContentTape,FixedPairContentMarkerErase.contentTape,hi,Function.update_apply,Fin.ext_iff,f]
  have chain := FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.handoff_exact (B := B) x w tag
  have bound : ∀ t, t < 3*(a+m)+7 → (Gate.run t (gateStart B x w)).head.val < f.val := by
    intro t ht
    have e := chain.2.1 t (by exact Nat.le_of_lt ht)
    rw [e]
    have hb := (FixedContentTagGate.phase_contract x w).1 B t (by exact Nat.le_of_lt ht)
    change (FixedContentTagGate.machine.run t (FixedContentTagGate.startConfig B x w)).head.val < f.val
    dsimp [f,FixedRawLengthFence.fencePos]; simp only [pairLength] at *; omega
  have frameRun := Gate.run_update_of_unvisited (gateStart B x w) f (some false) (3*(a+m)+7)
    (fun t ht he => (ne_of_lt (bound t ht)) (congrArg Fin.val he))
  rw [← hframe] at frameRun
  have endPins := FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.handoff_endpoint_pins (B := B) x w tag
  have endpoint : Gate.run (3*(a+m)+7) {gateStart B x w with tape := FixedRawLengthFence.fencedContentTape B x w} =
      ⟨⟨15,by decide⟩,⟨8,by
        have hlen := (FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.gate_first_arrival (B := 0) x w tag).2.2.2.2
        simp only [tapeLength,pairLength]; omega⟩,FixedRawLengthFence.fencedContentTape B x w⟩ := by
    rw [frameRun]
    apply Config.ext_parts
    · exact endPins.1
    · exact Fin.ext endPins.2.2.2.1
    · change Function.update (Gate.run (3*(a+m)+7) (gateStart B x w)).tape f (some false) = _
      have plainTape : (Gate.run (3*(a+m)+7) (gateStart B x w)).tape =
          FixedPairContentMarkerErase.contentTape B x w := endPins.2.2.2.2.1
      rw [plainTape]
      exact congrArg Config.tape hframe.symm
  have he := raw_gate x w resource (3*(a+m)+7)
  rw [endpoint] at he
  simpa only [B,Nat.add_assoc] using he
/-- Physical raw framing followed by the verified tag gate, on the new producer. -/
theorem raw_gamma_start {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true) :
    producer.run (FixedRawLengthFence.installClock (pairLength a m)+FixedRawLengthFence.contentClock a m+3*(a+m)+7)
      (initialConfig producer (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
      ⟨q 124,⟨8,by
        have h := (FixedRawLengthFence.resource_bounds (pairLength a m)).1
        have hN := (FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.gate_first_arrival (B := 0) x w tag).2.2.2.2
        simp only [tapeLength,pairLength] at *; omega⟩,
        FixedRawLengthFence.fencedContentTape (FixedRawLengthFence.allocation (pairLength a m)) x w⟩ := by
  have he := raw_tag_old x w tag
  have safe : (Old.run (FixedRawLengthFence.installClock (pairLength a m)+FixedRawLengthFence.contentClock a m+3*(a+m)+7)
      (initialConfig Old (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state ≠ Old.reject := by
    rw [he]; change (⟨124,by decide⟩ : Fin 256) ≠ Old.reject; decide
  have ht := preserves_nonreject _ _ safe
  have init : liftOld (initialConfig Old (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
      initialConfig producer (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w) := rfl
  rw [init,he] at ht
  exact ht
end SmallIngress

namespace SmallIngress
open Pnp3.Complexity.Uniform.V1
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
private structure Node (M : UniformTM) where
  state : Fin M.stateCount
  head : Nat
  tape : Nat → Option Bool

private def put (T : Nat → Option Bool) (h : Nat) (b : Option Bool) : Nat → Option Bool :=
  fun i => if i = h then b else T i

private def embed {M : UniformTM} {N B : Nat} (c : Node M) (h : c.head < tapeLength N B) : Config M.stateCount N B :=
  ⟨c.state,⟨c.head,h⟩,fun i => c.tape i.val⟩

private def dest (h : Nat) : Move → Nat
  | .left => h-1
  | .stay => h
  | .right => h+1

private structure Edge {M : UniformTM} (P : Nat) (c d : Node M) : Prop where
  before : c.head ≤ P
  after : d.head ≤ P
  row : (M.step c.state (c.tape c.head)).1 = d.state
  move : dest c.head (M.step c.state (c.tape c.head)).2.2 = d.head
  tape : d.tape = put c.tape c.head (M.step c.state (c.tape c.head)).2.1

private inductive Path {M : UniformTM} (P : Nat) : Nat → Node M → Node M → Prop
  | nil (c) (h : c.head ≤ P) : Path (M := M) P 0 c c
  | cons {t c d e} : Edge (M := M) P c d → Path (M := M) P t d e → Path (M := M) P (t+1) c e

namespace Path
private theorem bounds {M : UniformTM} {P t c d} (h : Path (M := M) P t c d) : c.head ≤ P ∧ d.head ≤ P := by
  induction h with
  | nil _ h => exact ⟨h,h⟩
  | cons e _ ih => exact ⟨e.before,ih.2⟩

private theorem append {M : UniformTM} {P t u c d e} (h : Path (M := M) P t c d) (g : Path (M := M) P u d e) :
    Path (M := M) P (t+u) c e := by
  induction h with
  | nil => simpa using g
  | cons ed _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Path.cons ed (ih g)

private theorem execute {M : UniformTM} {N B P t c d} (h : Path (M := M) P t c d) (hp : P < tapeLength N B) :
    M.run t (embed c (lt_of_le_of_lt h.bounds.1 hp)) =
      embed d (lt_of_le_of_lt h.bounds.2 hp) := by
  have step {c d} (e : Edge (M := M) P c d) :
      M.stepConfig (embed c (lt_of_le_of_lt e.before hp)) =
        embed d (lt_of_le_of_lt e.after hp) := by
    apply Config.ext_parts
    · exact e.row
    · apply Fin.ext
      change (moveHead _ (M.step c.state (c.tape c.head)).2.2).val = d.head
      have hm := e.move
      cases mv : (M.step c.state (c.tape c.head)).2.2 with
      | left => simpa only [mv,moveHead,embed,dest] using hm
      | stay => simpa only [mv,moveHead,embed,dest] using hm
      | right =>
        rw [mv] at hm
        simp only [dest] at hm
        have hd := e.after
        have hr : c.head+1 < tapeLength N B := by omega
        simp only [moveHead,embed,hr,↓reduceDIte]
        exact hm
    · funext i
      dsimp only [UniformTM.stepConfig,embed]
      rw [e.tape]
      simp only [put,Fin.ext_iff]
  suffices aux : ∀ (hc : c.head < tapeLength N B) (hd : d.head < tapeLength N B),
      M.run t (embed c hc) = embed d hd by exact aux _ _
  induction h with
  | nil => intro _ _; rfl
  | @cons t c d e ed path ih =>
    intro hc he
    rw [show t+1=1+t by omega,M.run_add]
    change M.run t (M.stepConfig (embed c hc)) = embed e he
    rw [step ed]
    exact ih _ _
end Path

private theorem hop {M : UniformTM} {P : Nat} (s s' : Fin M.stateCount) (h h' : Nat) (T : Nat → Option Bool)
    (b : Option Bool) (m : Move) (hb : h ≤ P) (ha : h' ≤ P)
    (row : M.step s (T h) = (s',b,m)) (hm : dest h m = h') :
    Path (M := M) P 1 ⟨s,h,T⟩ ⟨s',h',put T h b⟩ := by
  apply Path.cons (d := ⟨s',h',put T h b⟩)
  · exact ⟨hb,ha,by rw [row],by rw [row]; exact hm,by rw [row]⟩
  · exact Path.nil _ ha

private theorem put_same (T : Nat → Option Bool) (h : Nat) : put T h (T h) = T := by
  funext i; by_cases hi : i=h <;> simp [put,hi]

/-- One exact public row that preserves the scanned symbol. -/
private theorem keep {M : UniformTM} {P : Nat} (s s' : Fin M.stateCount) (h h' : Nat) (T : Nat → Option Bool)
    (m : Move) (hb : h ≤ P) (ha : h' ≤ P)
    (row : M.step s (T h) = (s',T h,m)) (hm : dest h m=h') :
    Path (M := M) P 1 ⟨s,h,T⟩ ⟨s',h',T⟩ := by
  have one := hop (M := M) s s' h h' T (T h) m hb ha row hm
  rwa [put_same] at one

private theorem sweepR {M : UniformTM} {P : Nat} (s : Fin M.stateCount) (T : Nat → Option Bool) (h r : Nat)
    (fit : h+r ≤ P)
    (rows : ∀ i, h ≤ i → i < h+r → M.step s (T i)=(s,T i,.right)) :
    Path (M := M) P r ⟨s,h,T⟩ ⟨s,h+r,T⟩ := by
  induction r generalizing h with
  | zero => simpa using Path.nil ⟨s,h,T⟩ fit
  | succ r ih =>
    have one := keep (M := M) s s h (h+1) T .right (P := P) (by omega) (by omega)
      (rows h le_rfl (by omega)) rfl
    have rest := ih (h+1) (by omega) (by intro i hl hu; exact rows i (by omega) (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using one.append rest

private theorem sweepL {M : UniformTM} {P : Nat} (s : Fin M.stateCount) (T : Nat → Option Bool) (low r : Nat)
    (fit : low+r ≤ P)
    (rows : ∀ i, low < i → i ≤ low+r → M.step s (T i)=(s,T i,.left)) :
    Path (M := M) P r ⟨s,low+r,T⟩ ⟨s,low,T⟩ := by
  induction r with
  | zero => simpa using Path.nil ⟨s,low,T⟩ fit
  | succ r ih =>
    have one := keep (M := M) s s (low+(r+1)) (low+r) T .left (P := P) (by omega) (by omega)
      (rows _ (by omega) le_rfl) (by simp [dest])
    have rest := ih (by omega) (by intro i hl hu; exact rows i hl (by omega))
    simpa [Nat.add_comm] using one.append rest

end SmallIngress
namespace SmallIngress
open Pnp3.Complexity.Uniform.V1
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
def seeded (T : Nat → Option Bool) (S n : Nat) : Nat → Option Bool := fun i =>
  let z := if n=0 then 0 else 1
  if n=0 ∧ i=7 then none
  else if n≠0 ∧ i=9 then none
  else if n≠0 ∧ i=10 then some true
  else if S < i ∧ i < S+z+2 then some false
  else if S+z+2 < i ∧ i < S+z+n+3 then some true
  else T i
end SmallIngress
namespace SmallIngress
open Pnp3.Complexity.Uniform.V1
set_option maxRecDepth 2000
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option diagnostics false
end SmallIngress





namespace SmallIngress
open Pnp3.Complexity.Uniform.V1
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
private def applyWrites (T : Nat → Option Bool) (ws : List (Nat × Option Bool)) : Nat → Option Bool :=
  ws.foldl (fun U w => put U w.1 w.2) T
private theorem postframe_0 (T : Nat → Option Bool) (S : Nat) (full : 9 ≤ S)
    (_h6 : T 6=some true) (_h7 : T 7=some false) (h8 : T 8=some true) :
    applyWrites T [(7,none),(7,some false),(8,none),(S+1,some true),(8,some true),(8,none),(7,none),(8,some true),(7,some false),(7,none),(7,some false),(7,none),(S+1,some false)]=seeded T S 0 := by
  funext i
  have high_ne (d l : Nat) (hl : l < 9) : S+d≠l := by omega
  have low_ne (l d : Nat) (hl : l < 9) : l≠S+d := by omega
  have reg : (S < i ∧ i < S+2) ↔ (i=S+1) := by omega
  have assn : ¬(S+2 < i ∧ i < S+3) := by omega
  by_cases a0 : i=(7)
  · subst i; simp (disch := omega) [applyWrites,List.foldl,put,seeded,Nat.add_assoc,high_ne,low_ne,reg,assn,h8] <;> (try split_ifs) <;> first | rfl | omega | (intro h; exfalso; omega)
  by_cases a1 : i=(8)
  · subst i; simp (disch := omega) [applyWrites,List.foldl,put,seeded,Nat.add_assoc,high_ne,low_ne,reg,assn,h8] <;> (try split_ifs) <;> first | rfl | omega | (intro h; exfalso; omega)
  by_cases a2 : i=(S+1)
  · subst i; simp (disch := omega) [applyWrites,List.foldl,put,seeded,Nat.add_assoc,high_ne,low_ne,reg,assn,h8] <;> (try split_ifs) <;> first | rfl | omega | (intro h; exfalso; omega)
  by_cases a3 : i=(9)
  · subst i; simp (disch := omega) [applyWrites,List.foldl,put,seeded,Nat.add_assoc,high_ne,low_ne,reg,assn,h8] <;> (try split_ifs) <;> first | rfl | omega | (intro h; exfalso; omega)
  by_cases a4 : i=(10)
  · subst i; simp (disch := omega) [applyWrites,List.foldl,put,seeded,Nat.add_assoc,high_ne,low_ne,reg,assn,h8] <;> (try split_ifs) <;> first | rfl | omega | (intro h; exfalso; omega)
  by_cases a5 : i=(S+2)
  · subst i; simp (disch := omega) [applyWrites,List.foldl,put,seeded,Nat.add_assoc,high_ne,low_ne,reg,assn,h8] <;> (try split_ifs) <;> first | rfl | omega | (intro h; exfalso; omega)
  by_cases a6 : i=(S+4)
  · subst i; simp (disch := omega) [applyWrites,List.foldl,put,seeded,Nat.add_assoc,high_ne,low_ne,reg,assn,h8] <;> (try split_ifs) <;> first | rfl | omega | (intro h; exfalso; omega)
  by_cases a7 : i=(S+5)
  · subst i; simp (disch := omega) [applyWrites,List.foldl,put,seeded,Nat.add_assoc,high_ne,low_ne,reg,assn,h8] <;> (try split_ifs) <;> first | rfl | omega | (intro h; exfalso; omega)
  simp (disch := omega) [applyWrites,List.foldl,put,seeded,Nat.add_assoc,high_ne,low_ne,reg,assn,h8,a0,a1,a2,a3,a4,a5,a6,a7] <;> (try split_ifs) <;> first | rfl | omega | (intro h; exfalso; omega)
private theorem posttag_0 (T : Nat → Option Bool) (S : Nat) (full : 9 ≤ S)
    (h6 : T 6=some true) (h7 : T 7=some false) (h8 : T 8=some true)
    (source : ∀ i, i < S → ∃ b, T i=some b)
    (clear : ∀ i, S ≤ i → i ≤ S+6 → T i=none) :
    ∃ t, t ≤ 6*S+100 ∧ Path (M := producer) (S+6) t ⟨q 124,8,T⟩ ⟨producer.accept,S+2,seeded T S 0⟩ := by
  have low (i : Nat) (hi : i ≤ 12) : i ≤ S+6 := by omega
  have b0 : S+0 ≤ S+6 := by omega
  have b1 : S+1 ≤ S+6 := by omega
  have b2 : S+2 ≤ S+6 := by omega
  have b3 : S+3 ≤ S+6 := by omega
  have b4 : S+4 ≤ S+6 := by omega
  have b5 : S+5 ≤ S+6 := by omega
  have b6 : S+6 ≤ S+6 := by omega
  have bm1 : S-1 ≤ S+6 := by omega
  have bm2 : S-2 ≤ S+6 := by omega
  have hC0 := clear (S+0) (by omega) (by omega)
  have hC1 := clear (S+1) (by omega) (by omega)
  have hC2 := clear (S+2) (by omega) (by omega)
  have hC3 := clear (S+3) (by omega) (by omega)
  have hC4 := clear (S+4) (by omega) (by omega)
  have hC5 := clear (S+5) (by omega) (by omega)
  have hC6 := clear (S+6) (by omega) (by omega)
  have r0 : T (8)=some true := by dsimp only [put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p0 := keep (M := producer) (q 124) (q 127) (8) (8) T .stay (P := S+6) (low 8 (by decide)) (low 8 (by decide)) (by rw [r0]; rfl) rfl
  have r1 : T (8)=some true := by (try clear p0 r0); dsimp only [put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p1 := keep (M := producer) (q 127) (q 128) (8) (7) T .left (P := S+6) (low 8 (by decide)) (low 7 (by decide)) (by rw [r1]; rfl) rfl
  have r2 : T (7)=some false := by (try clear p0 p1 r0 r1); dsimp only [put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p2 := keep (M := producer) (q 128) (q 128) (7) (6) T .left (P := S+6) (low 7 (by decide)) (low 6 (by decide)) (by rw [r2]; rfl) rfl
  have r3 : T (6)=some true := by (try clear p0 p1 p2 r0 r1 r2); dsimp only [put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p3 := keep (M := producer) (q 128) (q 129) (6) (7) T .right (P := S+6) (low 6 (by decide)) (low 7 (by decide)) (by rw [r3]; rfl) rfl
  have r4 : T (7)=some false := by (try clear p0 p1 p2 p3 r0 r1 r2 r3); dsimp only [put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U1 := put T (7) (none)
  have p4 := hop (M := producer) (q 129) (q 130) (7) (8) T (none) .right (P := S+6) (low 7 (by decide)) (low 8 (by decide)) (by rw [r4]; rfl) rfl
  have r5 : U1 (8)=some true := by (try clear p0 p1 p2 p3 p4 r0 r1 r2 r3 r4); dsimp only [U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p5 := keep (M := producer) (q 130) (q 133) (8) (8) U1 .stay (P := S+6) (low 8 (by decide)) (low 8 (by decide)) (by rw [r5]; rfl) rfl
  have r6 : U1 (8)=some true := by (try clear p0 p1 p2 p3 p4 p5 r0 r1 r2 r3 r4 r5); dsimp only [U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p6 := keep (M := producer) (q 133) (q 134) (8) (7) U1 .left (P := S+6) (low 8 (by decide)) (low 7 (by decide)) (by rw [r6]; rfl) rfl
  have r7 : U1 (7)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 r0 r1 r2 r3 r4 r5 r6); dsimp only [U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U2 := put U1 (7) (some false)
  have p7 := hop (M := producer) (q 134) (q 161) (7) (7) U1 (some false) .stay (P := S+6) (low 7 (by decide)) (low 7 (by decide)) (by rw [r7]; rfl) rfl
  have r8 : U2 (7)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 r0 r1 r2 r3 r4 r5 r6 r7); dsimp only [U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p8 := keep (M := producer) (q 161) (q 162) (7) (7) U2 .stay (P := S+6) (low 7 (by decide)) (low 7 (by decide)) (by rw [r8]; rfl) rfl
  have r9 : U2 (7)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 r0 r1 r2 r3 r4 r5 r6 r7 r8); dsimp only [U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p9 := keep (M := producer) (q 162) (q 163) (7) (8) U2 .right (P := S+6) (low 7 (by decide)) (low 8 (by decide)) (by rw [r9]; rfl) rfl
  have r10 : U2 (8)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9); dsimp only [U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U3 := put U2 (8) (none)
  have p10 := hop (M := producer) (q 163) (q 164) (8) (9) U2 (none) .right (P := S+6) (low 8 (by decide)) (low 9 (by decide)) (by rw [r10]; rfl) rfl
  have p11 := sweepR (M := producer) (q 164) U3 (9) ((S)-(9)) (P := S+6) (by clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10; omega) (by
    clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10; skip
    intro i lo hi
    obtain ⟨b,hb⟩ := source i (by omega)
    have occ : ∃ v, U3 i=some v := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10); dsimp only [U3,U2,U1,put]; (try split_ifs) <;> first | exact ⟨false,rfl⟩ | exact ⟨true,rfl⟩ | exact ⟨b,hb⟩ | (exfalso; omega)
    obtain ⟨v,hv⟩ := occ; rw [hv]; cases v <;> rfl)
  rw [show (9)+((S)-(9))=(S) by clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10; omega] at p11
  have r12 : U3 (S)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10); dsimp only [U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p12 := keep (M := producer) (q 164) (q 165) (S) (S+1) U3 .right (P := S+6) b0 b1 (by rw [r12]; rfl) rfl
  have r13 : U3 (S+1)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12); dsimp only [U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U4 := put U3 (S+1) (some true)
  have p13 := hop (M := producer) (q 165) (q 166) (S+1) (S) U3 (some true) .left (P := S+6) b1 b0 (by rw [r13]; rfl) rfl
  have r14 : U4 (S)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12 r13); dsimp only [U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p14 := keep (M := producer) (q 166) (q 167) (S) (S-1) U4 .left (P := S+6) b0 bm1 (by rw [r14]; rfl) rfl
  have p15 := sweepL (M := producer) (q 167) U4 (8) ((S-1)-(8)) (P := S+6) (by clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12 r13 r14; omega) (by
    clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12 r13 r14; skip
    intro i lo hi
    obtain ⟨b,hb⟩ := source i (by omega)
    have occ : ∃ v, U4 i=some v := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12 r13 r14); dsimp only [U4,U3,U2,U1,put]; (try split_ifs) <;> first | exact ⟨false,rfl⟩ | exact ⟨true,rfl⟩ | exact ⟨b,hb⟩ | (exfalso; omega)
    obtain ⟨v,hv⟩ := occ; rw [hv]; cases v <;> rfl)
  rw [show (8)+((S-1)-(8))=(S-1) by clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12 r13 r14; omega] at p15
  have r16 : U4 (8)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12 r13 r14); dsimp only [U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U5 := put U4 (8) (some true)
  have p16 := hop (M := producer) (q 167) (q 170) (8) (8) U4 (some true) .stay (P := S+6) (low 8 (by decide)) (low 8 (by decide)) (by rw [r16]; rfl) rfl
  have r17 : U5 (8)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12 r13 r14 r16); dsimp only [U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U6 := put U5 (8) (none)
  have p17 := hop (M := producer) (q 170) (q 171) (8) (7) U5 (none) .left (P := S+6) (low 8 (by decide)) (low 7 (by decide)) (by rw [r17]; rfl) rfl
  have r18 : U6 (7)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12 r13 r14 r16 r17); dsimp only [U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p18 := keep (M := producer) (q 171) (q 171) (7) (6) U6 .left (P := S+6) (low 7 (by decide)) (low 6 (by decide)) (by rw [r18]; rfl) rfl
  have r19 : U6 (6)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12 r13 r14 r16 r17 r18); dsimp only [U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p19 := keep (M := producer) (q 171) (q 172) (6) (7) U6 .right (P := S+6) (low 6 (by decide)) (low 7 (by decide)) (by rw [r19]; rfl) rfl
  have r20 : U6 (7)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12 r13 r14 r16 r17 r18 r19); dsimp only [U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U7 := put U6 (7) (none)
  have p20 := hop (M := producer) (q 172) (q 173) (7) (8) U6 (none) .right (P := S+6) (low 7 (by decide)) (low 8 (by decide)) (by rw [r20]; rfl) rfl
  have r21 : U7 (8)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12 r13 r14 r16 r17 r18 r19 r20); dsimp only [U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U8 := put U7 (8) (some true)
  have p21 := hop (M := producer) (q 173) (q 185) (8) (7) U7 (some true) .left (P := S+6) (low 8 (by decide)) (low 7 (by decide)) (by rw [r21]; rfl) rfl
  have r22 : U8 (7)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12 r13 r14 r16 r17 r18 r19 r20 r21); dsimp only [U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U9 := put U8 (7) (some false)
  have p22 := hop (M := producer) (q 185) (q 188) (7) (7) U8 (some false) .stay (P := S+6) (low 7 (by decide)) (low 7 (by decide)) (by rw [r22]; rfl) rfl
  have r23 : U9 (7)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12 r13 r14 r16 r17 r18 r19 r20 r21 r22); dsimp only [U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U10 := put U9 (7) (none)
  have p23 := hop (M := producer) (q 188) (q 189) (7) (8) U9 (none) .right (P := S+6) (low 7 (by decide)) (low 8 (by decide)) (by rw [r23]; rfl) rfl
  have r24 : U10 (8)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12 r13 r14 r16 r17 r18 r19 r20 r21 r22 r23); dsimp only [U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p24 := keep (M := producer) (q 189) (q 199) (8) (7) U10 .left (P := S+6) (low 8 (by decide)) (low 7 (by decide)) (by rw [r24]; rfl) rfl
  have r25 : U10 (7)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12 r13 r14 r16 r17 r18 r19 r20 r21 r22 r23 r24); dsimp only [U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U11 := put U10 (7) (some false)
  have p25 := hop (M := producer) (q 199) (q 202) (7) (7) U10 (some false) .stay (P := S+6) (low 7 (by decide)) (low 7 (by decide)) (by rw [r25]; rfl) rfl
  have r26 : U11 (7)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12 r13 r14 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25); dsimp only [U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p26 := keep (M := producer) (q 202) (q 203) (7) (8) U11 .right (P := S+6) (low 7 (by decide)) (low 8 (by decide)) (by rw [r26]; rfl) rfl
  have r27 : U11 (8)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12 r13 r14 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26); dsimp only [U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p27 := keep (M := producer) (q 203) (q 216) (8) (7) U11 .left (P := S+6) (low 8 (by decide)) (low 7 (by decide)) (by rw [r27]; rfl) rfl
  have r28 : U11 (7)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12 r13 r14 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27); dsimp only [U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p28 := keep (M := producer) (q 216) (q 256) (7) (8) U11 .right (P := S+6) (low 7 (by decide)) (low 8 (by decide)) (by rw [r28]; rfl) rfl
  have r29 : U11 (8)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12 r13 r14 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28); dsimp only [U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p29 := keep (M := producer) (q 256) (q 257) (8) (7) U11 .left (P := S+6) (low 8 (by decide)) (low 7 (by decide)) (by rw [r29]; rfl) rfl
  have r30 : U11 (7)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12 r13 r14 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29); dsimp only [U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U12 := put U11 (7) (none)
  have p30 := hop (M := producer) (q 257) (q 258) (7) (8) U11 (none) .right (P := S+6) (low 7 (by decide)) (low 8 (by decide)) (by rw [r30]; rfl) rfl
  have r31 : U12 (8)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12 r13 r14 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30); dsimp only [U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p31 := keep (M := producer) (q 258) (q 259) (8) (9) U12 .right (P := S+6) (low 8 (by decide)) (low 9 (by decide)) (by rw [r31]; rfl) rfl
  have p32 := sweepR (M := producer) (q 259) U12 (9) ((S)-(9)) (P := S+6) (by clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12 r13 r14 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31; omega) (by
    clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12 r13 r14 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31; skip
    intro i lo hi
    obtain ⟨b,hb⟩ := source i (by omega)
    have occ : ∃ v, U12 i=some v := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12 r13 r14 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31); dsimp only [U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | exact ⟨false,rfl⟩ | exact ⟨true,rfl⟩ | exact ⟨b,hb⟩ | (exfalso; omega)
    obtain ⟨v,hv⟩ := occ; rw [hv]; cases v <;> rfl)
  rw [show (9)+((S)-(9))=(S) by clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12 r13 r14 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31; omega] at p32
  have r33 : U12 (S)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12 r13 r14 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31); dsimp only [U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p33 := keep (M := producer) (q 259) (q 270) (S) (S+1) U12 .right (P := S+6) b0 b1 (by rw [r33]; rfl) rfl
  have r34 : U12 (S+1)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12 r13 r14 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 r33); dsimp only [U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U13 := put U12 (S+1) (some false)
  have p34 := hop (M := producer) (q 270) (q 271) (S+1) (S+2) U12 (some false) .right (P := S+6) b1 b2 (by rw [r34]; rfl) rfl
  have r35 : U13 (S+2)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12 r13 r14 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 r33 r34); dsimp only [U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p35 := keep (M := producer) (q 271) (q 254) (S+2) (S+2) U13 .stay (P := S+6) b2 b2 (by rw [r35]; rfl) rfl
  have path := p0 |>.append p1 |>.append p2 |>.append p3 |>.append p4 |>.append p5 |>.append p6 |>.append p7 |>.append p8 |>.append p9 |>.append p10 |>.append p11 |>.append p12 |>.append p13 |>.append p14 |>.append p15 |>.append p16 |>.append p17 |>.append p18 |>.append p19 |>.append p20 |>.append p21 |>.append p22 |>.append p23 |>.append p24 |>.append p25 |>.append p26 |>.append p27 |>.append p28 |>.append p29 |>.append p30 |>.append p31 |>.append p32 |>.append p33 |>.append p34 |>.append p35
  change Path (M := producer) (S+6) _ ⟨q 124,8,T⟩ ⟨q 254,S+2,U13⟩ at path
  have frame : U13=seeded T S 0 := postframe_0 T S full h6 h7 h8
  rw [frame] at path
  refine ⟨_, ?_, path⟩
  clear path p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12 r13 r14 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 r33 r34 r35
  omega
private theorem postframe_1 (T : Nat → Option Bool) (S : Nat) (full : 11 ≤ S)
    (_h6 : T 6=some true) (h7 : T 7=some false) (h8 : T 8=some false)
    (_h9 : T 9=some true) (_h10 : T 10=some false) :
    applyWrites T [(7,none),(8,none),(10,none),(10,some false),(8,some false),(7,some false),(9,none),(S+1,some true),(9,some true),(9,none),(7,none),(S+2,some false),(9,some true),(7,some false),(7,none),(7,some false),(8,some true),(8,some false),(9,none),(10,some true),(S+1,some false),(S+4,some true)]=seeded T S 1 := by
  funext i
  have high_ne (d l : Nat) (hl : l < 11) : S+d≠l := by omega
  have low_ne (l d : Nat) (hl : l < 11) : l≠S+d := by omega
  have reg : (S < i ∧ i < S+3) ↔ (i=S+1 ∨ i=S+2) := by omega
  have assn : (S+3 < i ∧ i < S+5) ↔ (i=S+4) := by omega
  by_cases a0 : i=(7)
  · subst i; simp (disch := omega) [applyWrites,List.foldl,put,seeded,Nat.add_assoc,high_ne,low_ne,reg,assn,h7,h8] <;> (try split_ifs) <;> first | rfl | omega | (intro h; exfalso; omega)
  by_cases a1 : i=(8)
  · subst i; simp (disch := omega) [applyWrites,List.foldl,put,seeded,Nat.add_assoc,high_ne,low_ne,reg,assn,h7,h8] <;> (try split_ifs) <;> first | rfl | omega | (intro h; exfalso; omega)
  by_cases a2 : i=(10)
  · subst i; simp (disch := omega) [applyWrites,List.foldl,put,seeded,Nat.add_assoc,high_ne,low_ne,reg,assn,h7,h8] <;> (try split_ifs) <;> first | rfl | omega | (intro h; exfalso; omega)
  by_cases a3 : i=(9)
  · subst i; simp (disch := omega) [applyWrites,List.foldl,put,seeded,Nat.add_assoc,high_ne,low_ne,reg,assn,h7,h8] <;> (try split_ifs) <;> first | rfl | omega | (intro h; exfalso; omega)
  by_cases a4 : i=(S+1)
  · subst i; simp (disch := omega) [applyWrites,List.foldl,put,seeded,Nat.add_assoc,high_ne,low_ne,reg,assn,h7,h8] <;> (try split_ifs) <;> first | rfl | omega | (intro h; exfalso; omega)
  by_cases a5 : i=(S+2)
  · subst i; simp (disch := omega) [applyWrites,List.foldl,put,seeded,Nat.add_assoc,high_ne,low_ne,reg,assn,h7,h8] <;> (try split_ifs) <;> first | rfl | omega | (intro h; exfalso; omega)
  by_cases a6 : i=(S+4)
  · subst i; simp (disch := omega) [applyWrites,List.foldl,put,seeded,Nat.add_assoc,high_ne,low_ne,reg,assn,h7,h8] <;> (try split_ifs) <;> first | rfl | omega | (intro h; exfalso; omega)
  by_cases a7 : i=(S+5)
  · subst i; simp (disch := omega) [applyWrites,List.foldl,put,seeded,Nat.add_assoc,high_ne,low_ne,reg,assn,h7,h8] <;> (try split_ifs) <;> first | rfl | omega | (intro h; exfalso; omega)
  simp (disch := omega) [applyWrites,List.foldl,put,seeded,Nat.add_assoc,high_ne,low_ne,reg,assn,h7,h8,a0,a1,a2,a3,a4,a5,a6,a7] <;> (try split_ifs) <;> first | rfl | omega | (intro h; exfalso; omega)
private theorem posttag_1 (T : Nat → Option Bool) (S : Nat) (full : 11 ≤ S)
    (h6 : T 6=some true) (h7 : T 7=some false) (h8 : T 8=some false)
    (h9 : T 9=some true) (h10 : T 10=some false)
    (source : ∀ i, i < S → ∃ b, T i=some b)
    (clear : ∀ i, S ≤ i → i ≤ S+6 → T i=none) :
    ∃ t, t ≤ 6*S+100 ∧ Path (M := producer) (S+6) t ⟨q 124,8,T⟩ ⟨producer.accept,S+3,seeded T S 1⟩ := by
  have low (i : Nat) (hi : i ≤ 12) : i ≤ S+6 := by omega
  have b0 : S+0 ≤ S+6 := by omega
  have b1 : S+1 ≤ S+6 := by omega
  have b2 : S+2 ≤ S+6 := by omega
  have b3 : S+3 ≤ S+6 := by omega
  have b4 : S+4 ≤ S+6 := by omega
  have b5 : S+5 ≤ S+6 := by omega
  have b6 : S+6 ≤ S+6 := by omega
  have bm1 : S-1 ≤ S+6 := by omega
  have bm2 : S-2 ≤ S+6 := by omega
  have hC0 := clear (S+0) (by omega) (by omega)
  have hC1 := clear (S+1) (by omega) (by omega)
  have hC2 := clear (S+2) (by omega) (by omega)
  have hC3 := clear (S+3) (by omega) (by omega)
  have hC4 := clear (S+4) (by omega) (by omega)
  have hC5 := clear (S+5) (by omega) (by omega)
  have hC6 := clear (S+6) (by omega) (by omega)
  have r0 : T (8)=some false := by dsimp only [put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p0 := keep (M := producer) (q 124) (q 124) (8) (9) T .right (P := S+6) (low 8 (by decide)) (low 9 (by decide)) (by rw [r0]; rfl) rfl
  have r1 : T (9)=some true := by (try clear p0 r0); dsimp only [put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p1 := keep (M := producer) (q 124) (q 127) (9) (9) T .stay (P := S+6) (low 9 (by decide)) (low 9 (by decide)) (by rw [r1]; rfl) rfl
  have r2 : T (9)=some true := by (try clear p0 p1 r0 r1); dsimp only [put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p2 := keep (M := producer) (q 127) (q 128) (9) (8) T .left (P := S+6) (low 9 (by decide)) (low 8 (by decide)) (by rw [r2]; rfl) rfl
  have r3 : T (8)=some false := by (try clear p0 p1 p2 r0 r1 r2); dsimp only [put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p3 := keep (M := producer) (q 128) (q 128) (8) (7) T .left (P := S+6) (low 8 (by decide)) (low 7 (by decide)) (by rw [r3]; rfl) rfl
  have r4 : T (7)=some false := by (try clear p0 p1 p2 p3 r0 r1 r2 r3); dsimp only [put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p4 := keep (M := producer) (q 128) (q 128) (7) (6) T .left (P := S+6) (low 7 (by decide)) (low 6 (by decide)) (by rw [r4]; rfl) rfl
  have r5 : T (6)=some true := by (try clear p0 p1 p2 p3 p4 r0 r1 r2 r3 r4); dsimp only [put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p5 := keep (M := producer) (q 128) (q 129) (6) (7) T .right (P := S+6) (low 6 (by decide)) (low 7 (by decide)) (by rw [r5]; rfl) rfl
  have r6 : T (7)=some false := by (try clear p0 p1 p2 p3 p4 p5 r0 r1 r2 r3 r4 r5); dsimp only [put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U1 := put T (7) (none)
  have p6 := hop (M := producer) (q 129) (q 130) (7) (8) T (none) .right (P := S+6) (low 7 (by decide)) (low 8 (by decide)) (by rw [r6]; rfl) rfl
  have r7 : U1 (8)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 r0 r1 r2 r3 r4 r5 r6); dsimp only [U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p7 := keep (M := producer) (q 130) (q 130) (8) (9) U1 .right (P := S+6) (low 8 (by decide)) (low 9 (by decide)) (by rw [r7]; rfl) rfl
  have r8 : U1 (9)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 r0 r1 r2 r3 r4 r5 r6 r7); dsimp only [U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p8 := keep (M := producer) (q 130) (q 133) (9) (9) U1 .stay (P := S+6) (low 9 (by decide)) (low 9 (by decide)) (by rw [r8]; rfl) rfl
  have r9 : U1 (9)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 r0 r1 r2 r3 r4 r5 r6 r7 r8); dsimp only [U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p9 := keep (M := producer) (q 133) (q 134) (9) (8) U1 .left (P := S+6) (low 9 (by decide)) (low 8 (by decide)) (by rw [r9]; rfl) rfl
  have r10 : U1 (8)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9); dsimp only [U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p10 := keep (M := producer) (q 134) (q 135) (8) (7) U1 .left (P := S+6) (low 8 (by decide)) (low 7 (by decide)) (by rw [r10]; rfl) rfl
  have r11 : U1 (7)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10); dsimp only [U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p11 := keep (M := producer) (q 135) (q 136) (7) (8) U1 .right (P := S+6) (low 7 (by decide)) (low 8 (by decide)) (by rw [r11]; rfl) rfl
  have r12 : U1 (8)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11); dsimp only [U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U2 := put U1 (8) (none)
  have p12 := hop (M := producer) (q 136) (q 137) (8) (9) U1 (none) .right (P := S+6) (low 8 (by decide)) (low 9 (by decide)) (by rw [r12]; rfl) rfl
  have r13 : U2 (9)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12); dsimp only [U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p13 := keep (M := producer) (q 137) (q 138) (9) (10) U2 .right (P := S+6) (low 9 (by decide)) (low 10 (by decide)) (by rw [r13]; rfl) rfl
  have r14 : U2 (10)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13); dsimp only [U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U3 := put U2 (10) (none)
  have p14 := hop (M := producer) (q 138) (q 143) (10) (10) U2 (none) .stay (P := S+6) (low 10 (by decide)) (low 10 (by decide)) (by rw [r14]; rfl) rfl
  have r15 : U3 (10)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14); dsimp only [U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p15 := keep (M := producer) (q 143) (q 144) (10) (9) U3 .left (P := S+6) (low 10 (by decide)) (low 9 (by decide)) (by rw [r15]; rfl) rfl
  have r16 : U3 (9)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15); dsimp only [U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p16 := keep (M := producer) (q 144) (q 145) (9) (8) U3 .left (P := S+6) (low 9 (by decide)) (low 8 (by decide)) (by rw [r16]; rfl) rfl
  have r17 : U3 (8)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16); dsimp only [U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p17 := keep (M := producer) (q 145) (q 146) (8) (9) U3 .right (P := S+6) (low 8 (by decide)) (low 9 (by decide)) (by rw [r17]; rfl) rfl
  have r18 : U3 (9)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17); dsimp only [U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p18 := keep (M := producer) (q 146) (q 150) (9) (9) U3 .stay (P := S+6) (low 9 (by decide)) (low 9 (by decide)) (by rw [r18]; rfl) rfl
  have r19 : U3 (9)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18); dsimp only [U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p19 := keep (M := producer) (q 150) (q 150) (9) (10) U3 .right (P := S+6) (low 9 (by decide)) (low 10 (by decide)) (by rw [r19]; rfl) rfl
  have r20 : U3 (10)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19); dsimp only [U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U4 := put U3 (10) (some false)
  have p20 := hop (M := producer) (q 150) (q 151) (10) (9) U3 (some false) .left (P := S+6) (low 10 (by decide)) (low 9 (by decide)) (by rw [r20]; rfl) rfl
  have r21 : U4 (9)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20); dsimp only [U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p21 := keep (M := producer) (q 151) (q 151) (9) (8) U4 .left (P := S+6) (low 9 (by decide)) (low 8 (by decide)) (by rw [r21]; rfl) rfl
  have r22 : U4 (8)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21); dsimp only [U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U5 := put U4 (8) (some false)
  have p22 := hop (M := producer) (q 151) (q 152) (8) (7) U4 (some false) .left (P := S+6) (low 8 (by decide)) (low 7 (by decide)) (by rw [r22]; rfl) rfl
  have r23 : U5 (7)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22); dsimp only [U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U6 := put U5 (7) (some false)
  have p23 := hop (M := producer) (q 152) (q 152) (7) (6) U5 (some false) .left (P := S+6) (low 7 (by decide)) (low 6 (by decide)) (by rw [r23]; rfl) rfl
  have r24 : U6 (6)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23); dsimp only [U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p24 := keep (M := producer) (q 152) (q 161) (6) (6) U6 .stay (P := S+6) (low 6 (by decide)) (low 6 (by decide)) (by rw [r24]; rfl) rfl
  have r25 : U6 (6)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24); dsimp only [U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p25 := keep (M := producer) (q 161) (q 162) (6) (7) U6 .right (P := S+6) (low 6 (by decide)) (low 7 (by decide)) (by rw [r25]; rfl) rfl
  have r26 : U6 (7)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25); dsimp only [U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p26 := keep (M := producer) (q 162) (q 163) (7) (8) U6 .right (P := S+6) (low 7 (by decide)) (low 8 (by decide)) (by rw [r26]; rfl) rfl
  have r27 : U6 (8)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26); dsimp only [U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p27 := keep (M := producer) (q 163) (q 163) (8) (9) U6 .right (P := S+6) (low 8 (by decide)) (low 9 (by decide)) (by rw [r27]; rfl) rfl
  have r28 : U6 (9)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27); dsimp only [U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U7 := put U6 (9) (none)
  have p28 := hop (M := producer) (q 163) (q 164) (9) (10) U6 (none) .right (P := S+6) (low 9 (by decide)) (low 10 (by decide)) (by rw [r28]; rfl) rfl
  have p29 := sweepR (M := producer) (q 164) U7 (10) ((S)-(10)) (P := S+6) (by clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28; omega) (by
    clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28; skip
    intro i lo hi
    obtain ⟨b,hb⟩ := source i (by omega)
    have occ : ∃ v, U7 i=some v := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28); dsimp only [U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | exact ⟨false,rfl⟩ | exact ⟨true,rfl⟩ | exact ⟨b,hb⟩ | (exfalso; omega)
    obtain ⟨v,hv⟩ := occ; rw [hv]; cases v <;> rfl)
  rw [show (10)+((S)-(10))=(S) by clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28; omega] at p29
  have r30 : U7 (S)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28); dsimp only [U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p30 := keep (M := producer) (q 164) (q 165) (S) (S+1) U7 .right (P := S+6) b0 b1 (by rw [r30]; rfl) rfl
  have r31 : U7 (S+1)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30); dsimp only [U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U8 := put U7 (S+1) (some true)
  have p31 := hop (M := producer) (q 165) (q 166) (S+1) (S) U7 (some true) .left (P := S+6) b1 b0 (by rw [r31]; rfl) rfl
  have r32 : U8 (S)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31); dsimp only [U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p32 := keep (M := producer) (q 166) (q 167) (S) (S-1) U8 .left (P := S+6) b0 bm1 (by rw [r32]; rfl) rfl
  have p33 := sweepL (M := producer) (q 167) U8 (9) ((S-1)-(9)) (P := S+6) (by clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32; omega) (by
    clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32; skip
    intro i lo hi
    obtain ⟨b,hb⟩ := source i (by omega)
    have occ : ∃ v, U8 i=some v := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32); dsimp only [U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | exact ⟨false,rfl⟩ | exact ⟨true,rfl⟩ | exact ⟨b,hb⟩ | (exfalso; omega)
    obtain ⟨v,hv⟩ := occ; rw [hv]; cases v <;> rfl)
  rw [show (9)+((S-1)-(9))=(S-1) by clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32; omega] at p33
  have r34 : U8 (9)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32); dsimp only [U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U9 := put U8 (9) (some true)
  have p34 := hop (M := producer) (q 167) (q 170) (9) (9) U8 (some true) .stay (P := S+6) (low 9 (by decide)) (low 9 (by decide)) (by rw [r34]; rfl) rfl
  have r35 : U9 (9)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34); dsimp only [U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U10 := put U9 (9) (none)
  have p35 := hop (M := producer) (q 170) (q 171) (9) (8) U9 (none) .left (P := S+6) (low 9 (by decide)) (low 8 (by decide)) (by rw [r35]; rfl) rfl
  have r36 : U10 (8)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35); dsimp only [U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p36 := keep (M := producer) (q 171) (q 171) (8) (7) U10 .left (P := S+6) (low 8 (by decide)) (low 7 (by decide)) (by rw [r36]; rfl) rfl
  have r37 : U10 (7)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36); dsimp only [U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p37 := keep (M := producer) (q 171) (q 171) (7) (6) U10 .left (P := S+6) (low 7 (by decide)) (low 6 (by decide)) (by rw [r37]; rfl) rfl
  have r38 : U10 (6)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37); dsimp only [U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p38 := keep (M := producer) (q 171) (q 172) (6) (7) U10 .right (P := S+6) (low 6 (by decide)) (low 7 (by decide)) (by rw [r38]; rfl) rfl
  have r39 : U10 (7)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38); dsimp only [U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U11 := put U10 (7) (none)
  have p39 := hop (M := producer) (q 172) (q 173) (7) (8) U10 (none) .right (P := S+6) (low 7 (by decide)) (low 8 (by decide)) (by rw [r39]; rfl) rfl
  have r40 : U11 (8)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39); dsimp only [U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p40 := keep (M := producer) (q 173) (q 174) (8) (9) U11 .right (P := S+6) (low 8 (by decide)) (low 9 (by decide)) (by rw [r40]; rfl) rfl
  have r41 : U11 (9)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40); dsimp only [U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p41 := keep (M := producer) (q 174) (q 175) (9) (10) U11 .right (P := S+6) (low 9 (by decide)) (low 10 (by decide)) (by rw [r41]; rfl) rfl
  have r42 : U11 (10)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41); dsimp only [U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p42 := keep (M := producer) (q 175) (q 176) (10) (11) U11 .right (P := S+6) (low 10 (by decide)) (low 11 (by decide)) (by rw [r42]; rfl) rfl
  have p43 := sweepR (M := producer) (q 176) U11 (11) ((S)-(11)) (P := S+6) (by clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42; omega) (by
    clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42; skip
    intro i lo hi
    obtain ⟨b,hb⟩ := source i (by omega)
    have occ : ∃ v, U11 i=some v := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42); dsimp only [U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | exact ⟨false,rfl⟩ | exact ⟨true,rfl⟩ | exact ⟨b,hb⟩ | (exfalso; omega)
    obtain ⟨v,hv⟩ := occ; rw [hv]; cases v <;> rfl)
  rw [show (11)+((S)-(11))=(S) by clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42; omega] at p43
  have r44 : U11 (S)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42); dsimp only [U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p44 := keep (M := producer) (q 176) (q 178) (S) (S+1) U11 .right (P := S+6) b0 b1 (by rw [r44]; rfl) rfl
  have r45 : U11 (S+1)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44); dsimp only [U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p45 := keep (M := producer) (q 178) (q 180) (S+1) (S+2) U11 .right (P := S+6) b1 b2 (by rw [r45]; rfl) rfl
  have r46 : U11 (S+2)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45); dsimp only [U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U12 := put U11 (S+2) (some false)
  have p46 := hop (M := producer) (q 180) (q 182) (S+2) (S+1) U11 (some false) .left (P := S+6) b2 b1 (by rw [r46]; rfl) rfl
  have r47 : U12 (S+1)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46); dsimp only [U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p47 := keep (M := producer) (q 182) (q 183) (S+1) (S) U12 .left (P := S+6) b1 b0 (by rw [r47]; rfl) rfl
  have r48 : U12 (S)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47); dsimp only [U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p48 := keep (M := producer) (q 183) (q 184) (S) (S-1) U12 .left (P := S+6) b0 bm1 (by rw [r48]; rfl) rfl
  have p49 := sweepL (M := producer) (q 184) U12 (9) ((S-1)-(9)) (P := S+6) (by clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48; omega) (by
    clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48; skip
    intro i lo hi
    obtain ⟨b,hb⟩ := source i (by omega)
    have occ : ∃ v, U12 i=some v := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48); dsimp only [U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | exact ⟨false,rfl⟩ | exact ⟨true,rfl⟩ | exact ⟨b,hb⟩ | (exfalso; omega)
    obtain ⟨v,hv⟩ := occ; rw [hv]; cases v <;> rfl)
  rw [show (9)+((S-1)-(9))=(S-1) by clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48; omega] at p49
  have r50 : U12 (9)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48); dsimp only [U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U13 := put U12 (9) (some true)
  have p50 := hop (M := producer) (q 184) (q 185) (9) (8) U12 (some true) .left (P := S+6) (low 9 (by decide)) (low 8 (by decide)) (by rw [r50]; rfl) rfl
  have r51 : U13 (8)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48 r50); dsimp only [U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p51 := keep (M := producer) (q 185) (q 185) (8) (7) U13 .left (P := S+6) (low 8 (by decide)) (low 7 (by decide)) (by rw [r51]; rfl) rfl
  have r52 : U13 (7)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48 r50 r51); dsimp only [U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U14 := put U13 (7) (some false)
  have p52 := hop (M := producer) (q 185) (q 188) (7) (7) U13 (some false) .stay (P := S+6) (low 7 (by decide)) (low 7 (by decide)) (by rw [r52]; rfl) rfl
  have r53 : U14 (7)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48 r50 r51 r52); dsimp only [U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U15 := put U14 (7) (none)
  have p53 := hop (M := producer) (q 188) (q 189) (7) (8) U14 (none) .right (P := S+6) (low 7 (by decide)) (low 8 (by decide)) (by rw [r53]; rfl) rfl
  have r54 : U15 (8)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48 r50 r51 r52 r53); dsimp only [U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p54 := keep (M := producer) (q 189) (q 190) (8) (9) U15 .right (P := S+6) (low 8 (by decide)) (low 9 (by decide)) (by rw [r54]; rfl) rfl
  have r55 : U15 (9)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48 r50 r51 r52 r53 r54); dsimp only [U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p55 := keep (M := producer) (q 190) (q 199) (9) (8) U15 .left (P := S+6) (low 9 (by decide)) (low 8 (by decide)) (by rw [r55]; rfl) rfl
  have r56 : U15 (8)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48 r50 r51 r52 r53 r54 r55); dsimp only [U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p56 := keep (M := producer) (q 199) (q 199) (8) (7) U15 .left (P := S+6) (low 8 (by decide)) (low 7 (by decide)) (by rw [r56]; rfl) rfl
  have r57 : U15 (7)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48 r50 r51 r52 r53 r54 r55 r56); dsimp only [U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U16 := put U15 (7) (some false)
  have p57 := hop (M := producer) (q 199) (q 202) (7) (7) U15 (some false) .stay (P := S+6) (low 7 (by decide)) (low 7 (by decide)) (by rw [r57]; rfl) rfl
  have r58 : U16 (7)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48 r50 r51 r52 r53 r54 r55 r56 r57); dsimp only [U16,U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p58 := keep (M := producer) (q 202) (q 203) (7) (8) U16 .right (P := S+6) (low 7 (by decide)) (low 8 (by decide)) (by rw [r58]; rfl) rfl
  have r59 : U16 (8)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48 r50 r51 r52 r53 r54 r55 r56 r57 r58); dsimp only [U16,U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U17 := put U16 (8) (some true)
  have p59 := hop (M := producer) (q 203) (q 204) (8) (9) U16 (some true) .right (P := S+6) (low 8 (by decide)) (low 9 (by decide)) (by rw [r59]; rfl) rfl
  have r60 : U17 (9)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48 r50 r51 r52 r53 r54 r55 r56 r57 r58 r59); dsimp only [U17,U16,U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p60 := keep (M := producer) (q 204) (q 213) (9) (8) U17 .left (P := S+6) (low 9 (by decide)) (low 8 (by decide)) (by rw [r60]; rfl) rfl
  have r61 : U17 (8)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48 r50 r51 r52 r53 r54 r55 r56 r57 r58 r59 r60); dsimp only [U17,U16,U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U18 := put U17 (8) (some false)
  have p61 := hop (M := producer) (q 213) (q 213) (8) (7) U17 (some false) .left (P := S+6) (low 8 (by decide)) (low 7 (by decide)) (by rw [r61]; rfl) rfl
  have r62 : U18 (7)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48 r50 r51 r52 r53 r54 r55 r56 r57 r58 r59 r60 r61); dsimp only [U18,U17,U16,U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p62 := keep (M := producer) (q 213) (q 216) (7) (7) U18 .stay (P := S+6) (low 7 (by decide)) (low 7 (by decide)) (by rw [r62]; rfl) rfl
  have r63 : U18 (7)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48 r50 r51 r52 r53 r54 r55 r56 r57 r58 r59 r60 r61 r62); dsimp only [U18,U17,U16,U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p63 := keep (M := producer) (q 216) (q 256) (7) (8) U18 .right (P := S+6) (low 7 (by decide)) (low 8 (by decide)) (by rw [r63]; rfl) rfl
  have r64 : U18 (8)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48 r50 r51 r52 r53 r54 r55 r56 r57 r58 r59 r60 r61 r62 r63); dsimp only [U18,U17,U16,U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p64 := keep (M := producer) (q 256) (q 260) (8) (9) U18 .right (P := S+6) (low 8 (by decide)) (low 9 (by decide)) (by rw [r64]; rfl) rfl
  have r65 : U18 (9)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48 r50 r51 r52 r53 r54 r55 r56 r57 r58 r59 r60 r61 r62 r63 r64); dsimp only [U18,U17,U16,U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U19 := put U18 (9) (none)
  have p65 := hop (M := producer) (q 260) (q 261) (9) (10) U18 (none) .right (P := S+6) (low 9 (by decide)) (low 10 (by decide)) (by rw [r65]; rfl) rfl
  have r66 : U19 (10)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48 r50 r51 r52 r53 r54 r55 r56 r57 r58 r59 r60 r61 r62 r63 r64 r65); dsimp only [U19,U18,U17,U16,U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U20 := put U19 (10) (some true)
  have p66 := hop (M := producer) (q 261) (q 262) (10) (11) U19 (some true) .right (P := S+6) (low 10 (by decide)) (low 11 (by decide)) (by rw [r66]; rfl) rfl
  have p67 := sweepR (M := producer) (q 262) U20 (11) ((S)-(11)) (P := S+6) (by clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48 r50 r51 r52 r53 r54 r55 r56 r57 r58 r59 r60 r61 r62 r63 r64 r65 r66; omega) (by
    clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48 r50 r51 r52 r53 r54 r55 r56 r57 r58 r59 r60 r61 r62 r63 r64 r65 r66; skip
    intro i lo hi
    obtain ⟨b,hb⟩ := source i (by omega)
    have occ : ∃ v, U20 i=some v := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48 r50 r51 r52 r53 r54 r55 r56 r57 r58 r59 r60 r61 r62 r63 r64 r65 r66); dsimp only [U20,U19,U18,U17,U16,U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | exact ⟨false,rfl⟩ | exact ⟨true,rfl⟩ | exact ⟨b,hb⟩ | (exfalso; omega)
    obtain ⟨v,hv⟩ := occ; rw [hv]; cases v <;> rfl)
  rw [show (11)+((S)-(11))=(S) by clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48 r50 r51 r52 r53 r54 r55 r56 r57 r58 r59 r60 r61 r62 r63 r64 r65 r66; omega] at p67
  have r68 : U20 (S)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48 r50 r51 r52 r53 r54 r55 r56 r57 r58 r59 r60 r61 r62 r63 r64 r65 r66); dsimp only [U20,U19,U18,U17,U16,U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p68 := keep (M := producer) (q 262) (q 266) (S) (S+1) U20 .right (P := S+6) b0 b1 (by rw [r68]; rfl) rfl
  have r69 : U20 (S+1)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48 r50 r51 r52 r53 r54 r55 r56 r57 r58 r59 r60 r61 r62 r63 r64 r65 r66 r68); dsimp only [U20,U19,U18,U17,U16,U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U21 := put U20 (S+1) (some false)
  have p69 := hop (M := producer) (q 266) (q 267) (S+1) (S+2) U20 (some false) .right (P := S+6) b1 b2 (by rw [r69]; rfl) rfl
  have r70 : U21 (S+2)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48 r50 r51 r52 r53 r54 r55 r56 r57 r58 r59 r60 r61 r62 r63 r64 r65 r66 r68 r69); dsimp only [U21,U20,U19,U18,U17,U16,U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p70 := keep (M := producer) (q 267) (q 268) (S+2) (S+3) U21 .right (P := S+6) b2 b3 (by rw [r70]; rfl) rfl
  have r71 : U21 (S+3)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48 r50 r51 r52 r53 r54 r55 r56 r57 r58 r59 r60 r61 r62 r63 r64 r65 r66 r68 r69 r70); dsimp only [U21,U20,U19,U18,U17,U16,U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p71 := keep (M := producer) (q 268) (q 269) (S+3) (S+4) U21 .right (P := S+6) b3 b4 (by rw [r71]; rfl) rfl
  have r72 : U21 (S+4)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48 r50 r51 r52 r53 r54 r55 r56 r57 r58 r59 r60 r61 r62 r63 r64 r65 r66 r68 r69 r70 r71); dsimp only [U21,U20,U19,U18,U17,U16,U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U22 := put U21 (S+4) (some true)
  have p72 := hop (M := producer) (q 269) (q 272) (S+4) (S+3) U21 (some true) .left (P := S+6) b4 b3 (by rw [r72]; rfl) rfl
  have r73 : U22 (S+3)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48 r50 r51 r52 r53 r54 r55 r56 r57 r58 r59 r60 r61 r62 r63 r64 r65 r66 r68 r69 r70 r71 r72); dsimp only [U22,U21,U20,U19,U18,U17,U16,U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p73 := keep (M := producer) (q 272) (q 254) (S+3) (S+3) U22 .stay (P := S+6) b3 b3 (by rw [r73]; rfl) rfl
  have path := p0 |>.append p1 |>.append p2 |>.append p3 |>.append p4 |>.append p5 |>.append p6 |>.append p7 |>.append p8 |>.append p9 |>.append p10 |>.append p11 |>.append p12 |>.append p13 |>.append p14 |>.append p15 |>.append p16 |>.append p17 |>.append p18 |>.append p19 |>.append p20 |>.append p21 |>.append p22 |>.append p23 |>.append p24 |>.append p25 |>.append p26 |>.append p27 |>.append p28 |>.append p29 |>.append p30 |>.append p31 |>.append p32 |>.append p33 |>.append p34 |>.append p35 |>.append p36 |>.append p37 |>.append p38 |>.append p39 |>.append p40 |>.append p41 |>.append p42 |>.append p43 |>.append p44 |>.append p45 |>.append p46 |>.append p47 |>.append p48 |>.append p49 |>.append p50 |>.append p51 |>.append p52 |>.append p53 |>.append p54 |>.append p55 |>.append p56 |>.append p57 |>.append p58 |>.append p59 |>.append p60 |>.append p61 |>.append p62 |>.append p63 |>.append p64 |>.append p65 |>.append p66 |>.append p67 |>.append p68 |>.append p69 |>.append p70 |>.append p71 |>.append p72 |>.append p73
  change Path (M := producer) (S+6) _ ⟨q 124,8,T⟩ ⟨q 254,S+3,U22⟩ at path
  have frame : U22=seeded T S 1 := postframe_1 T S full h6 h7 h8 h9 h10
  rw [frame] at path
  refine ⟨_, ?_, path⟩
  clear path p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r30 r31 r32 r34 r35 r36 r37 r38 r39 r40 r41 r42 r44 r45 r46 r47 r48 r50 r51 r52 r53 r54 r55 r56 r57 r58 r59 r60 r61 r62 r63 r64 r65 r66 r68 r69 r70 r71 r72 r73
  omega
private theorem postframe_2 (T : Nat → Option Bool) (S : Nat) (full : 11 ≤ S)
    (_h6 : T 6=some true) (h7 : T 7=some false) (h8 : T 8=some false)
    (_h9 : T 9=some true) (h10 : T 10=some true) :
    applyWrites T [(7,none),(8,none),(8,some false),(7,some false),(9,none),(S+1,some true),(9,some true),(9,none),(7,none),(S+2,some true),(9,some true),(7,some false),(7,none),(7,some false),(8,some true),(8,some false),(9,none),(S+1,some false),(S+2,some false),(S+4,some true),(S+5,some true)]=seeded T S 2 := by
  funext i
  have high_ne (d l : Nat) (hl : l < 11) : S+d≠l := by omega
  have low_ne (l d : Nat) (hl : l < 11) : l≠S+d := by omega
  have reg : (S < i ∧ i < S+3) ↔ (i=S+1 ∨ i=S+2) := by omega
  have assn : (S+3 < i ∧ i < S+6) ↔ (i=S+4 ∨ i=S+5) := by omega
  by_cases a0 : i=(7)
  · subst i; simp (disch := omega) [applyWrites,List.foldl,put,seeded,Nat.add_assoc,high_ne,low_ne,reg,assn,h7,h8,h10] <;> (try split_ifs) <;> first | rfl | omega | (intro h; exfalso; omega)
  by_cases a1 : i=(8)
  · subst i; simp (disch := omega) [applyWrites,List.foldl,put,seeded,Nat.add_assoc,high_ne,low_ne,reg,assn,h7,h8,h10] <;> (try split_ifs) <;> first | rfl | omega | (intro h; exfalso; omega)
  by_cases a2 : i=(9)
  · subst i; simp (disch := omega) [applyWrites,List.foldl,put,seeded,Nat.add_assoc,high_ne,low_ne,reg,assn,h7,h8,h10] <;> (try split_ifs) <;> first | rfl | omega | (intro h; exfalso; omega)
  by_cases a3 : i=(S+1)
  · subst i; simp (disch := omega) [applyWrites,List.foldl,put,seeded,Nat.add_assoc,high_ne,low_ne,reg,assn,h7,h8,h10] <;> (try split_ifs) <;> first | rfl | omega | (intro h; exfalso; omega)
  by_cases a4 : i=(S+2)
  · subst i; simp (disch := omega) [applyWrites,List.foldl,put,seeded,Nat.add_assoc,high_ne,low_ne,reg,assn,h7,h8,h10] <;> (try split_ifs) <;> first | rfl | omega | (intro h; exfalso; omega)
  by_cases a5 : i=(S+4)
  · subst i; simp (disch := omega) [applyWrites,List.foldl,put,seeded,Nat.add_assoc,high_ne,low_ne,reg,assn,h7,h8,h10] <;> (try split_ifs) <;> first | rfl | omega | (intro h; exfalso; omega)
  by_cases a6 : i=(S+5)
  · subst i; simp (disch := omega) [applyWrites,List.foldl,put,seeded,Nat.add_assoc,high_ne,low_ne,reg,assn,h7,h8,h10] <;> (try split_ifs) <;> first | rfl | omega | (intro h; exfalso; omega)
  by_cases a7 : i=(10)
  · subst i; simp (disch := omega) [applyWrites,List.foldl,put,seeded,Nat.add_assoc,high_ne,low_ne,reg,assn,h7,h8,h10] <;> (try split_ifs) <;> first | rfl | omega | (intro h; exfalso; omega)
  simp (disch := omega) [applyWrites,List.foldl,put,seeded,Nat.add_assoc,high_ne,low_ne,reg,assn,h7,h8,h10,a0,a1,a2,a3,a4,a5,a6,a7] <;> (try split_ifs) <;> first | rfl | omega | (intro h; exfalso; omega)
private theorem posttag_2 (T : Nat → Option Bool) (S : Nat) (full : 11 ≤ S)
    (h6 : T 6=some true) (h7 : T 7=some false) (h8 : T 8=some false)
    (h9 : T 9=some true) (h10 : T 10=some true)
    (source : ∀ i, i < S → ∃ b, T i=some b)
    (clear : ∀ i, S ≤ i → i ≤ S+6 → T i=none) :
    ∃ t, t ≤ 6*S+100 ∧ Path (M := producer) (S+6) t ⟨q 124,8,T⟩ ⟨producer.accept,S+3,seeded T S 2⟩ := by
  have low (i : Nat) (hi : i ≤ 12) : i ≤ S+6 := by omega
  have b0 : S+0 ≤ S+6 := by omega
  have b1 : S+1 ≤ S+6 := by omega
  have b2 : S+2 ≤ S+6 := by omega
  have b3 : S+3 ≤ S+6 := by omega
  have b4 : S+4 ≤ S+6 := by omega
  have b5 : S+5 ≤ S+6 := by omega
  have b6 : S+6 ≤ S+6 := by omega
  have bm1 : S-1 ≤ S+6 := by omega
  have bm2 : S-2 ≤ S+6 := by omega
  have hC0 := clear (S+0) (by omega) (by omega)
  have hC1 := clear (S+1) (by omega) (by omega)
  have hC2 := clear (S+2) (by omega) (by omega)
  have hC3 := clear (S+3) (by omega) (by omega)
  have hC4 := clear (S+4) (by omega) (by omega)
  have hC5 := clear (S+5) (by omega) (by omega)
  have hC6 := clear (S+6) (by omega) (by omega)
  have r0 : T (8)=some false := by dsimp only [put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p0 := keep (M := producer) (q 124) (q 124) (8) (9) T .right (P := S+6) (low 8 (by decide)) (low 9 (by decide)) (by rw [r0]; rfl) rfl
  have r1 : T (9)=some true := by (try clear p0 r0); dsimp only [put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p1 := keep (M := producer) (q 124) (q 127) (9) (9) T .stay (P := S+6) (low 9 (by decide)) (low 9 (by decide)) (by rw [r1]; rfl) rfl
  have r2 : T (9)=some true := by (try clear p0 p1 r0 r1); dsimp only [put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p2 := keep (M := producer) (q 127) (q 128) (9) (8) T .left (P := S+6) (low 9 (by decide)) (low 8 (by decide)) (by rw [r2]; rfl) rfl
  have r3 : T (8)=some false := by (try clear p0 p1 p2 r0 r1 r2); dsimp only [put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p3 := keep (M := producer) (q 128) (q 128) (8) (7) T .left (P := S+6) (low 8 (by decide)) (low 7 (by decide)) (by rw [r3]; rfl) rfl
  have r4 : T (7)=some false := by (try clear p0 p1 p2 p3 r0 r1 r2 r3); dsimp only [put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p4 := keep (M := producer) (q 128) (q 128) (7) (6) T .left (P := S+6) (low 7 (by decide)) (low 6 (by decide)) (by rw [r4]; rfl) rfl
  have r5 : T (6)=some true := by (try clear p0 p1 p2 p3 p4 r0 r1 r2 r3 r4); dsimp only [put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p5 := keep (M := producer) (q 128) (q 129) (6) (7) T .right (P := S+6) (low 6 (by decide)) (low 7 (by decide)) (by rw [r5]; rfl) rfl
  have r6 : T (7)=some false := by (try clear p0 p1 p2 p3 p4 p5 r0 r1 r2 r3 r4 r5); dsimp only [put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U1 := put T (7) (none)
  have p6 := hop (M := producer) (q 129) (q 130) (7) (8) T (none) .right (P := S+6) (low 7 (by decide)) (low 8 (by decide)) (by rw [r6]; rfl) rfl
  have r7 : U1 (8)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 r0 r1 r2 r3 r4 r5 r6); dsimp only [U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p7 := keep (M := producer) (q 130) (q 130) (8) (9) U1 .right (P := S+6) (low 8 (by decide)) (low 9 (by decide)) (by rw [r7]; rfl) rfl
  have r8 : U1 (9)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 r0 r1 r2 r3 r4 r5 r6 r7); dsimp only [U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p8 := keep (M := producer) (q 130) (q 133) (9) (9) U1 .stay (P := S+6) (low 9 (by decide)) (low 9 (by decide)) (by rw [r8]; rfl) rfl
  have r9 : U1 (9)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 r0 r1 r2 r3 r4 r5 r6 r7 r8); dsimp only [U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p9 := keep (M := producer) (q 133) (q 134) (9) (8) U1 .left (P := S+6) (low 9 (by decide)) (low 8 (by decide)) (by rw [r9]; rfl) rfl
  have r10 : U1 (8)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9); dsimp only [U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p10 := keep (M := producer) (q 134) (q 135) (8) (7) U1 .left (P := S+6) (low 8 (by decide)) (low 7 (by decide)) (by rw [r10]; rfl) rfl
  have r11 : U1 (7)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10); dsimp only [U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p11 := keep (M := producer) (q 135) (q 136) (7) (8) U1 .right (P := S+6) (low 7 (by decide)) (low 8 (by decide)) (by rw [r11]; rfl) rfl
  have r12 : U1 (8)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11); dsimp only [U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U2 := put U1 (8) (none)
  have p12 := hop (M := producer) (q 136) (q 137) (8) (9) U1 (none) .right (P := S+6) (low 8 (by decide)) (low 9 (by decide)) (by rw [r12]; rfl) rfl
  have r13 : U2 (9)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12); dsimp only [U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p13 := keep (M := producer) (q 137) (q 138) (9) (10) U2 .right (P := S+6) (low 9 (by decide)) (low 10 (by decide)) (by rw [r13]; rfl) rfl
  have r14 : U2 (10)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13); dsimp only [U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p14 := keep (M := producer) (q 138) (q 139) (10) (9) U2 .left (P := S+6) (low 10 (by decide)) (low 9 (by decide)) (by rw [r14]; rfl) rfl
  have r15 : U2 (9)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14); dsimp only [U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p15 := keep (M := producer) (q 139) (q 139) (9) (8) U2 .left (P := S+6) (low 9 (by decide)) (low 8 (by decide)) (by rw [r15]; rfl) rfl
  have r16 : U2 (8)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15); dsimp only [U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U3 := put U2 (8) (some false)
  have p16 := hop (M := producer) (q 139) (q 141) (8) (7) U2 (some false) .left (P := S+6) (low 8 (by decide)) (low 7 (by decide)) (by rw [r16]; rfl) rfl
  have r17 : U3 (7)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16); dsimp only [U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U4 := put U3 (7) (some false)
  have p17 := hop (M := producer) (q 141) (q 161) (7) (6) U3 (some false) .left (P := S+6) (low 7 (by decide)) (low 6 (by decide)) (by rw [r17]; rfl) rfl
  have r18 : U4 (6)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17); dsimp only [U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p18 := keep (M := producer) (q 161) (q 162) (6) (7) U4 .right (P := S+6) (low 6 (by decide)) (low 7 (by decide)) (by rw [r18]; rfl) rfl
  have r19 : U4 (7)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18); dsimp only [U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p19 := keep (M := producer) (q 162) (q 163) (7) (8) U4 .right (P := S+6) (low 7 (by decide)) (low 8 (by decide)) (by rw [r19]; rfl) rfl
  have r20 : U4 (8)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19); dsimp only [U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p20 := keep (M := producer) (q 163) (q 163) (8) (9) U4 .right (P := S+6) (low 8 (by decide)) (low 9 (by decide)) (by rw [r20]; rfl) rfl
  have r21 : U4 (9)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20); dsimp only [U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U5 := put U4 (9) (none)
  have p21 := hop (M := producer) (q 163) (q 164) (9) (10) U4 (none) .right (P := S+6) (low 9 (by decide)) (low 10 (by decide)) (by rw [r21]; rfl) rfl
  have p22 := sweepR (M := producer) (q 164) U5 (10) ((S)-(10)) (P := S+6) (by clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21; omega) (by
    clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21; skip
    intro i lo hi
    obtain ⟨b,hb⟩ := source i (by omega)
    have occ : ∃ v, U5 i=some v := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21); dsimp only [U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | exact ⟨false,rfl⟩ | exact ⟨true,rfl⟩ | exact ⟨b,hb⟩ | (exfalso; omega)
    obtain ⟨v,hv⟩ := occ; rw [hv]; cases v <;> rfl)
  rw [show (10)+((S)-(10))=(S) by clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21; omega] at p22
  have r23 : U5 (S)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21); dsimp only [U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p23 := keep (M := producer) (q 164) (q 165) (S) (S+1) U5 .right (P := S+6) b0 b1 (by rw [r23]; rfl) rfl
  have r24 : U5 (S+1)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23); dsimp only [U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U6 := put U5 (S+1) (some true)
  have p24 := hop (M := producer) (q 165) (q 166) (S+1) (S) U5 (some true) .left (P := S+6) b1 b0 (by rw [r24]; rfl) rfl
  have r25 : U6 (S)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24); dsimp only [U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p25 := keep (M := producer) (q 166) (q 167) (S) (S-1) U6 .left (P := S+6) b0 bm1 (by rw [r25]; rfl) rfl
  have p26 := sweepL (M := producer) (q 167) U6 (9) ((S-1)-(9)) (P := S+6) (by clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25; omega) (by
    clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25; skip
    intro i lo hi
    obtain ⟨b,hb⟩ := source i (by omega)
    have occ : ∃ v, U6 i=some v := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25); dsimp only [U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | exact ⟨false,rfl⟩ | exact ⟨true,rfl⟩ | exact ⟨b,hb⟩ | (exfalso; omega)
    obtain ⟨v,hv⟩ := occ; rw [hv]; cases v <;> rfl)
  rw [show (9)+((S-1)-(9))=(S-1) by clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25; omega] at p26
  have r27 : U6 (9)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25); dsimp only [U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U7 := put U6 (9) (some true)
  have p27 := hop (M := producer) (q 167) (q 170) (9) (9) U6 (some true) .stay (P := S+6) (low 9 (by decide)) (low 9 (by decide)) (by rw [r27]; rfl) rfl
  have r28 : U7 (9)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27); dsimp only [U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U8 := put U7 (9) (none)
  have p28 := hop (M := producer) (q 170) (q 171) (9) (8) U7 (none) .left (P := S+6) (low 9 (by decide)) (low 8 (by decide)) (by rw [r28]; rfl) rfl
  have r29 : U8 (8)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28); dsimp only [U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p29 := keep (M := producer) (q 171) (q 171) (8) (7) U8 .left (P := S+6) (low 8 (by decide)) (low 7 (by decide)) (by rw [r29]; rfl) rfl
  have r30 : U8 (7)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29); dsimp only [U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p30 := keep (M := producer) (q 171) (q 171) (7) (6) U8 .left (P := S+6) (low 7 (by decide)) (low 6 (by decide)) (by rw [r30]; rfl) rfl
  have r31 : U8 (6)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30); dsimp only [U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p31 := keep (M := producer) (q 171) (q 172) (6) (7) U8 .right (P := S+6) (low 6 (by decide)) (low 7 (by decide)) (by rw [r31]; rfl) rfl
  have r32 : U8 (7)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31); dsimp only [U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U9 := put U8 (7) (none)
  have p32 := hop (M := producer) (q 172) (q 173) (7) (8) U8 (none) .right (P := S+6) (low 7 (by decide)) (low 8 (by decide)) (by rw [r32]; rfl) rfl
  have r33 : U9 (8)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32); dsimp only [U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p33 := keep (M := producer) (q 173) (q 174) (8) (9) U9 .right (P := S+6) (low 8 (by decide)) (low 9 (by decide)) (by rw [r33]; rfl) rfl
  have r34 : U9 (9)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33); dsimp only [U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p34 := keep (M := producer) (q 174) (q 175) (9) (10) U9 .right (P := S+6) (low 9 (by decide)) (low 10 (by decide)) (by rw [r34]; rfl) rfl
  have r35 : U9 (10)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34); dsimp only [U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p35 := keep (M := producer) (q 175) (q 177) (10) (11) U9 .right (P := S+6) (low 10 (by decide)) (low 11 (by decide)) (by rw [r35]; rfl) rfl
  have p36 := sweepR (M := producer) (q 177) U9 (11) ((S)-(11)) (P := S+6) (by clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35; omega) (by
    clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35; skip
    intro i lo hi
    obtain ⟨b,hb⟩ := source i (by omega)
    have occ : ∃ v, U9 i=some v := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35); dsimp only [U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | exact ⟨false,rfl⟩ | exact ⟨true,rfl⟩ | exact ⟨b,hb⟩ | (exfalso; omega)
    obtain ⟨v,hv⟩ := occ; rw [hv]; cases v <;> rfl)
  rw [show (11)+((S)-(11))=(S) by clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35; omega] at p36
  have r37 : U9 (S)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35); dsimp only [U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p37 := keep (M := producer) (q 177) (q 179) (S) (S+1) U9 .right (P := S+6) b0 b1 (by rw [r37]; rfl) rfl
  have r38 : U9 (S+1)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37); dsimp only [U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p38 := keep (M := producer) (q 179) (q 181) (S+1) (S+2) U9 .right (P := S+6) b1 b2 (by rw [r38]; rfl) rfl
  have r39 : U9 (S+2)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38); dsimp only [U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U10 := put U9 (S+2) (some true)
  have p39 := hop (M := producer) (q 181) (q 182) (S+2) (S+1) U9 (some true) .left (P := S+6) b2 b1 (by rw [r39]; rfl) rfl
  have r40 : U10 (S+1)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39); dsimp only [U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p40 := keep (M := producer) (q 182) (q 183) (S+1) (S) U10 .left (P := S+6) b1 b0 (by rw [r40]; rfl) rfl
  have r41 : U10 (S)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40); dsimp only [U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p41 := keep (M := producer) (q 183) (q 184) (S) (S-1) U10 .left (P := S+6) b0 bm1 (by rw [r41]; rfl) rfl
  have p42 := sweepL (M := producer) (q 184) U10 (9) ((S-1)-(9)) (P := S+6) (by clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41; omega) (by
    clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41; skip
    intro i lo hi
    obtain ⟨b,hb⟩ := source i (by omega)
    have occ : ∃ v, U10 i=some v := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41); dsimp only [U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | exact ⟨false,rfl⟩ | exact ⟨true,rfl⟩ | exact ⟨b,hb⟩ | (exfalso; omega)
    obtain ⟨v,hv⟩ := occ; rw [hv]; cases v <;> rfl)
  rw [show (9)+((S-1)-(9))=(S-1) by clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41; omega] at p42
  have r43 : U10 (9)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41); dsimp only [U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U11 := put U10 (9) (some true)
  have p43 := hop (M := producer) (q 184) (q 185) (9) (8) U10 (some true) .left (P := S+6) (low 9 (by decide)) (low 8 (by decide)) (by rw [r43]; rfl) rfl
  have r44 : U11 (8)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41 r43); dsimp only [U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p44 := keep (M := producer) (q 185) (q 185) (8) (7) U11 .left (P := S+6) (low 8 (by decide)) (low 7 (by decide)) (by rw [r44]; rfl) rfl
  have r45 : U11 (7)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41 r43 r44); dsimp only [U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U12 := put U11 (7) (some false)
  have p45 := hop (M := producer) (q 185) (q 188) (7) (7) U11 (some false) .stay (P := S+6) (low 7 (by decide)) (low 7 (by decide)) (by rw [r45]; rfl) rfl
  have r46 : U12 (7)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41 r43 r44 r45); dsimp only [U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U13 := put U12 (7) (none)
  have p46 := hop (M := producer) (q 188) (q 189) (7) (8) U12 (none) .right (P := S+6) (low 7 (by decide)) (low 8 (by decide)) (by rw [r46]; rfl) rfl
  have r47 : U13 (8)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41 r43 r44 r45 r46); dsimp only [U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p47 := keep (M := producer) (q 189) (q 190) (8) (9) U13 .right (P := S+6) (low 8 (by decide)) (low 9 (by decide)) (by rw [r47]; rfl) rfl
  have r48 : U13 (9)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41 r43 r44 r45 r46 r47); dsimp only [U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p48 := keep (M := producer) (q 190) (q 199) (9) (8) U13 .left (P := S+6) (low 9 (by decide)) (low 8 (by decide)) (by rw [r48]; rfl) rfl
  have r49 : U13 (8)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41 r43 r44 r45 r46 r47 r48); dsimp only [U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p49 := keep (M := producer) (q 199) (q 199) (8) (7) U13 .left (P := S+6) (low 8 (by decide)) (low 7 (by decide)) (by rw [r49]; rfl) rfl
  have r50 : U13 (7)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41 r43 r44 r45 r46 r47 r48 r49); dsimp only [U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U14 := put U13 (7) (some false)
  have p50 := hop (M := producer) (q 199) (q 202) (7) (7) U13 (some false) .stay (P := S+6) (low 7 (by decide)) (low 7 (by decide)) (by rw [r50]; rfl) rfl
  have r51 : U14 (7)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41 r43 r44 r45 r46 r47 r48 r49 r50); dsimp only [U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p51 := keep (M := producer) (q 202) (q 203) (7) (8) U14 .right (P := S+6) (low 7 (by decide)) (low 8 (by decide)) (by rw [r51]; rfl) rfl
  have r52 : U14 (8)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41 r43 r44 r45 r46 r47 r48 r49 r50 r51); dsimp only [U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U15 := put U14 (8) (some true)
  have p52 := hop (M := producer) (q 203) (q 204) (8) (9) U14 (some true) .right (P := S+6) (low 8 (by decide)) (low 9 (by decide)) (by rw [r52]; rfl) rfl
  have r53 : U15 (9)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41 r43 r44 r45 r46 r47 r48 r49 r50 r51 r52); dsimp only [U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p53 := keep (M := producer) (q 204) (q 213) (9) (8) U15 .left (P := S+6) (low 9 (by decide)) (low 8 (by decide)) (by rw [r53]; rfl) rfl
  have r54 : U15 (8)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41 r43 r44 r45 r46 r47 r48 r49 r50 r51 r52 r53); dsimp only [U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U16 := put U15 (8) (some false)
  have p54 := hop (M := producer) (q 213) (q 213) (8) (7) U15 (some false) .left (P := S+6) (low 8 (by decide)) (low 7 (by decide)) (by rw [r54]; rfl) rfl
  have r55 : U16 (7)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41 r43 r44 r45 r46 r47 r48 r49 r50 r51 r52 r53 r54); dsimp only [U16,U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p55 := keep (M := producer) (q 213) (q 216) (7) (7) U16 .stay (P := S+6) (low 7 (by decide)) (low 7 (by decide)) (by rw [r55]; rfl) rfl
  have r56 : U16 (7)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41 r43 r44 r45 r46 r47 r48 r49 r50 r51 r52 r53 r54 r55); dsimp only [U16,U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p56 := keep (M := producer) (q 216) (q 256) (7) (8) U16 .right (P := S+6) (low 7 (by decide)) (low 8 (by decide)) (by rw [r56]; rfl) rfl
  have r57 : U16 (8)=some false := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41 r43 r44 r45 r46 r47 r48 r49 r50 r51 r52 r53 r54 r55 r56); dsimp only [U16,U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p57 := keep (M := producer) (q 256) (q 260) (8) (9) U16 .right (P := S+6) (low 8 (by decide)) (low 9 (by decide)) (by rw [r57]; rfl) rfl
  have r58 : U16 (9)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41 r43 r44 r45 r46 r47 r48 r49 r50 r51 r52 r53 r54 r55 r56 r57); dsimp only [U16,U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U17 := put U16 (9) (none)
  have p58 := hop (M := producer) (q 260) (q 261) (9) (10) U16 (none) .right (P := S+6) (low 9 (by decide)) (low 10 (by decide)) (by rw [r58]; rfl) rfl
  have r59 : U17 (10)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41 r43 r44 r45 r46 r47 r48 r49 r50 r51 r52 r53 r54 r55 r56 r57 r58); dsimp only [U17,U16,U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p59 := keep (M := producer) (q 261) (q 263) (10) (11) U17 .right (P := S+6) (low 10 (by decide)) (low 11 (by decide)) (by rw [r59]; rfl) rfl
  have p60 := sweepR (M := producer) (q 263) U17 (11) ((S)-(11)) (P := S+6) (by clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41 r43 r44 r45 r46 r47 r48 r49 r50 r51 r52 r53 r54 r55 r56 r57 r58 r59; omega) (by
    clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41 r43 r44 r45 r46 r47 r48 r49 r50 r51 r52 r53 r54 r55 r56 r57 r58 r59; skip
    intro i lo hi
    obtain ⟨b,hb⟩ := source i (by omega)
    have occ : ∃ v, U17 i=some v := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41 r43 r44 r45 r46 r47 r48 r49 r50 r51 r52 r53 r54 r55 r56 r57 r58 r59); dsimp only [U17,U16,U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | exact ⟨false,rfl⟩ | exact ⟨true,rfl⟩ | exact ⟨b,hb⟩ | (exfalso; omega)
    obtain ⟨v,hv⟩ := occ; rw [hv]; cases v <;> rfl)
  rw [show (11)+((S)-(11))=(S) by clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41 r43 r44 r45 r46 r47 r48 r49 r50 r51 r52 r53 r54 r55 r56 r57 r58 r59; omega] at p60
  have r61 : U17 (S)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41 r43 r44 r45 r46 r47 r48 r49 r50 r51 r52 r53 r54 r55 r56 r57 r58 r59); dsimp only [U17,U16,U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p61 := keep (M := producer) (q 263) (q 273) (S) (S+1) U17 .right (P := S+6) b0 b1 (by rw [r61]; rfl) rfl
  have r62 : U17 (S+1)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41 r43 r44 r45 r46 r47 r48 r49 r50 r51 r52 r53 r54 r55 r56 r57 r58 r59 r61); dsimp only [U17,U16,U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U18 := put U17 (S+1) (some false)
  have p62 := hop (M := producer) (q 273) (q 274) (S+1) (S+2) U17 (some false) .right (P := S+6) b1 b2 (by rw [r62]; rfl) rfl
  have r63 : U18 (S+2)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41 r43 r44 r45 r46 r47 r48 r49 r50 r51 r52 r53 r54 r55 r56 r57 r58 r59 r61 r62); dsimp only [U18,U17,U16,U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U19 := put U18 (S+2) (some false)
  have p63 := hop (M := producer) (q 274) (q 275) (S+2) (S+3) U18 (some false) .right (P := S+6) b2 b3 (by rw [r63]; rfl) rfl
  have r64 : U19 (S+3)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41 r43 r44 r45 r46 r47 r48 r49 r50 r51 r52 r53 r54 r55 r56 r57 r58 r59 r61 r62 r63); dsimp only [U19,U18,U17,U16,U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p64 := keep (M := producer) (q 275) (q 276) (S+3) (S+4) U19 .right (P := S+6) b3 b4 (by rw [r64]; rfl) rfl
  have r65 : U19 (S+4)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41 r43 r44 r45 r46 r47 r48 r49 r50 r51 r52 r53 r54 r55 r56 r57 r58 r59 r61 r62 r63 r64); dsimp only [U19,U18,U17,U16,U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U20 := put U19 (S+4) (some true)
  have p65 := hop (M := producer) (q 276) (q 277) (S+4) (S+5) U19 (some true) .right (P := S+6) b4 b5 (by rw [r65]; rfl) rfl
  have r66 : U20 (S+5)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41 r43 r44 r45 r46 r47 r48 r49 r50 r51 r52 r53 r54 r55 r56 r57 r58 r59 r61 r62 r63 r64 r65); dsimp only [U20,U19,U18,U17,U16,U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  let U21 := put U20 (S+5) (some true)
  have p66 := hop (M := producer) (q 277) (q 278) (S+5) (S+4) U20 (some true) .left (P := S+6) b5 b4 (by rw [r66]; rfl) rfl
  have r67 : U21 (S+4)=some true := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41 r43 r44 r45 r46 r47 r48 r49 r50 r51 r52 r53 r54 r55 r56 r57 r58 r59 r61 r62 r63 r64 r65 r66); dsimp only [U21,U20,U19,U18,U17,U16,U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p67 := keep (M := producer) (q 278) (q 279) (S+4) (S+3) U21 .left (P := S+6) b4 b3 (by rw [r67]; rfl) rfl
  have r68 : U21 (S+3)=none := by (try clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41 r43 r44 r45 r46 r47 r48 r49 r50 r51 r52 r53 r54 r55 r56 r57 r58 r59 r61 r62 r63 r64 r65 r66 r67); dsimp only [U21,U20,U19,U18,U17,U16,U15,U14,U13,U12,U11,U10,U9,U8,U7,U6,U5,U4,U3,U2,U1,put]; (try split_ifs) <;> first | rfl | assumption | (symm; assumption) | omega
  have p68 := keep (M := producer) (q 279) (q 254) (S+3) (S+3) U21 .stay (P := S+6) b3 b3 (by rw [r68]; rfl) rfl
  have path := p0 |>.append p1 |>.append p2 |>.append p3 |>.append p4 |>.append p5 |>.append p6 |>.append p7 |>.append p8 |>.append p9 |>.append p10 |>.append p11 |>.append p12 |>.append p13 |>.append p14 |>.append p15 |>.append p16 |>.append p17 |>.append p18 |>.append p19 |>.append p20 |>.append p21 |>.append p22 |>.append p23 |>.append p24 |>.append p25 |>.append p26 |>.append p27 |>.append p28 |>.append p29 |>.append p30 |>.append p31 |>.append p32 |>.append p33 |>.append p34 |>.append p35 |>.append p36 |>.append p37 |>.append p38 |>.append p39 |>.append p40 |>.append p41 |>.append p42 |>.append p43 |>.append p44 |>.append p45 |>.append p46 |>.append p47 |>.append p48 |>.append p49 |>.append p50 |>.append p51 |>.append p52 |>.append p53 |>.append p54 |>.append p55 |>.append p56 |>.append p57 |>.append p58 |>.append p59 |>.append p60 |>.append p61 |>.append p62 |>.append p63 |>.append p64 |>.append p65 |>.append p66 |>.append p67 |>.append p68
  change Path (M := producer) (S+6) _ ⟨q 124,8,T⟩ ⟨q 254,S+3,U21⟩ at path
  have frame : U21=seeded T S 2 := postframe_2 T S full h6 h7 h8 h9 h10
  rw [frame] at path
  refine ⟨_, ?_, path⟩
  clear path p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r25 r27 r28 r29 r30 r31 r32 r33 r34 r35 r37 r38 r39 r40 r41 r43 r44 r45 r46 r47 r48 r49 r50 r51 r52 r53 r54 r55 r56 r57 r58 r59 r61 r62 r63 r64 r65 r66 r67 r68
  omega
end SmallIngress
namespace SmallIngress
open Pnp3.Complexity.Uniform.V1
set_option maxRecDepth 4000
set_option maxHeartbeats 500000
/-- Literal execution on the actual new producer, with a length-only linear
phase bound. The Nat tape and counters below are proof specifications. -/
theorem producer_small_modes (N B S : Nat) (n : Fin 3) (T : Nat → Option Bool)
    (full : (if n.val=0 then 9 else 11) ≤ S) (fit : S+6 < tapeLength N B)
    (h6 : T 6=some true) (h7 : T 7=some false) (h8 : T 8=some (n.val==0))
    (h9 : n.val≠0 → T 9=some true) (h10 : n.val≠0 → T 10=some (n.val==2))
    (source : ∀ i, i < S → ∃ b, T i=some b)
    (clear : ∀ i, S ≤ i → i ≤ S+6 → T i=none) :
    ∃ t, t ≤ 6*S+100 ∧
      producer.run (n := N) (budget := B) t ⟨q 124,⟨8,by split_ifs at full <;> omega⟩,fun i => T i.val⟩ =
        ⟨producer.accept,⟨S+(if n.val=0 then 0 else 1)+2,by split_ifs <;> omega⟩,
          fun i => seeded T S n.val i.val⟩ := by
  rcases n with ⟨n,hn⟩
  interval_cases n
  · obtain ⟨t,ht,path⟩ := posttag_0 T S (by simpa using full) h6 h7 (by simpa using h8) source clear
    refine ⟨t,ht,?_⟩
    exact path.execute (N := N) (B := B) fit
  · obtain ⟨t,ht,path⟩ := posttag_1 T S (by simpa using full) h6 h7 (by simpa using h8)
      (h9 (by simp)) (by simpa using h10 (by simp)) source clear
    refine ⟨t,ht,?_⟩
    exact path.execute (N := N) (B := B) fit
  · obtain ⟨t,ht,path⟩ := posttag_2 T S (by simpa using full) h6 h7 (by simpa using h8)
      (h9 (by simp)) (by simpa using h10 (by simp)) source clear
    refine ⟨t,ht,?_⟩
    exact path.execute (N := N) (B := B) fit
end SmallIngress
namespace SmallIngress
open Pnp3.Complexity.Uniform.V1
open PairEncoding
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
attribute [local irreducible] UniformTM.run
/-- General physical small-header ingress, including false content and arbitrary
unread data. The endpoint is a literal composable Stream entry, not a verdict. -/
theorem raw_small_physical {a m : Nat} (x : Bitstring a) (w : Bitstring m) (n : Fin 3)
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (full : (if n.val=0 then 9 else 11) ≤ a+m)
    (h8 : FixedContentTagGate.physicalSymbol (Fin.append x w) 8=some (n.val==0))
    (h9 : n.val≠0 → FixedContentTagGate.physicalSymbol (Fin.append x w) 9=some true)
    (h10 : n.val≠0 → FixedContentTagGate.physicalSymbol (Fin.append x w) 10=some (n.val==2)) :
    let R := pairLength a m
    let B := FixedRawLengthFence.allocation R
    let S := a+m
    let T := Body.extend (FixedRawLengthFence.fencedContentTape B x w)
    let L := S+(if n.val=0 then 0 else 1)+2
    ∃ (t : Nat) (hL : L < tapeLength R B), t ≤ 64*(R+1)^2 ∧ ∀ s,
      machine.run (t+s) (initialConfig machine B (encodePair x w)) =
        producer.seqEmbedRight Stream.machine
          (Stream.machine.run s ⟨Stream.machine.start,⟨L,hL⟩,fun i => seeded T S n.val i.val⟩) := by
  let R := pairLength a m
  let B := FixedRawLengthFence.allocation R
  let S := a+m
  let T := Body.extend (FixedRawLengthFence.fencedContentTape B x w)
  let L := S+(if n.val=0 then 0 else 1)+2
  have hS : 9 ≤ S := by dsimp [S]; split_ifs at full <;> omega
  have hSR : S ≤ R := by dsimp [S,R,pairLength]; omega
  have resource := (FixedRawLengthFence.resource_bounds R).1
  have fit : S+6 < tapeLength R B := by simp only [tapeLength]; dsimp [B] at *; omega
  have hF : S+6 < FixedRawLengthFence.fencePos R := by dsimp [FixedRawLengthFence.fencePos]; omega
  have read (i : Nat) (hi : i < tapeLength R B) :
      T i=FixedRawLengthFence.fencedContentTape B x w ⟨i,hi⟩ := by
    have hj : i < tapeLength (pairLength a m) B := hi
    simp only [T,Body.extend,dif_pos hj]
  have low (i : Nat) (hi : i < S) : T i=FixedContentTagGate.physicalSymbol (Fin.append x w) i := by
    rw [read i (by omega)]
    simp [FixedRawLengthFence.fencedContentTape,FixedContentTagGate.physicalSymbol,show i < a+m from hi]
  have source (i : Nat) (hi : i < S) : ∃ b, T i=some b := by
    rw [low i hi]
    exact ⟨Fin.append x w ⟨i,hi⟩,by simp [FixedContentTagGate.physicalSymbol,show i<a+m from hi]⟩
  have clear (i : Nat) (lo : S ≤ i) (hi : i ≤ S+6) : T i=none := by
    rw [read i (by omega)]
    simp [FixedRawLengthFence.fencedContentTape,show ¬i<a+m by omega,
      show i≠FixedRawLengthFence.fencePos (pairLength a m) by change i≠FixedRawLengthFence.fencePos R; omega]
  obtain ⟨_,_,_,_,_,_,bit6,bit7,iff,_⟩ := FixedContentTagGate.tag_contract (Fin.append x w)
  have h6 : T 6=some true := by rw [low 6 (by omega)]; simpa only [bit6] using iff.mp tag ⟨6,by decide⟩
  have h7 : T 7=some false := by rw [low 7 (by omega)]; simpa only [bit7] using iff.mp tag ⟨7,by decide⟩
  obtain ⟨u,hu,he⟩ := producer_small_modes R B S n T full fit h6 h7
    (by rw [low 8 (by omega)]; exact h8)
    (by intro hn; rw [low 9 (by dsimp [S]; split_ifs at full <;> omega)]; exact h9 hn)
    (by intro hn; rw [low 10 (by dsimp [S]; split_ifs at full <;> omega)]; exact h10 hn) source clear
  let g := FixedRawLengthFence.installClock R+FixedRawLengthFence.contentClock a m+3*S+7
  let c := initialConfig producer B (encodePair x w)
  have initEq : (⟨q 124,⟨8,by omega⟩,FixedRawLengthFence.fencedContentTape B x w⟩ : Config 288 R B)=
      ⟨q 124,⟨8,by omega⟩,fun i => T i.val⟩ := by
    apply Config.ext_parts
    · rfl
    · rfl
    · funext i; exact (Body.extend_read _ i).symm
  have combined : producer.run (g+u) c =
      ⟨producer.accept,⟨L,by change L < tapeLength R B; dsimp only [L]; split_ifs <;> omega⟩,fun i => seeded T S n.val i.val⟩ := by
    rw [producer.run_add]
    have gamma := raw_gamma_start x w tag
    change producer.run g c = _ at gamma
    rw [gamma,initEq]
    exact he
  have clock : g+u ≤ 64*(R+1)^2 := by
    have pre := (FixedRawLengthFence.content_prefix_resources a m).2
    change FixedRawLengthFence.installClock R+FixedRawLengthFence.contentClock a m ≤ B at pre
    have sq : R+1 ≤ (R+1)^2 := by
      simpa only [pow_two,Nat.mul_one] using Nat.mul_le_mul_left (R+1) (show 1≤R+1 by omega)
    dsimp [g,B,FixedRawLengthFence.allocation] at *
    nlinarith
  obtain ⟨t,ht,first,arrived⟩ := Body.first_accept_whole producer c _ _ combined rfl
  refine ⟨t,by change S+(if n.val=0 then 0 else 1)+2 < tapeLength R B; split_ifs <;> omega,ht.trans clock,?_⟩
  intro s
  have hand := producer.seq_handoff Stream.machine c first (by rw [arrived]) s
  have initial : producer.seqEmbedRouted Stream.machine c=initialConfig machine B (encodePair x w) := rfl
  rw [initial,arrived] at hand
  exact hand
end SmallIngress

namespace SmallIngress.Audit
open SmallIngress Pnp3.Complexity.Uniform.V1 PairEncoding
set_option maxRecDepth 40000
def pin_q (i : Nat) : Fin 288 := @SmallIngress.q i
def pin_rows (s : Fin 288) (b : Option Bool) : Fin 288 × Option Bool × Move := @SmallIngress.rows s b
def pin_producer : UniformTM := @SmallIngress.producer
def pin_machine : UniformTM := @SmallIngress.machine
def pin_prepared {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) (z n : Nat) : Fin (tapeLength (pairLength a m) B) → Option Bool := @SmallIngress.prepared a m B x w z n
def pin_Target_AcceptedOrbit (k : Nat) : Prop := @SmallIngress.Target.AcceptedOrbit k
def pin_liftOld {N B : Nat} (c : Config FixedRawLengthFence.prefixed.stateCount N B) : Config SmallIngress.producer.stateCount N B := @SmallIngress.liftOld N B c
def pin_seeded (T : Nat → Option Bool) (S n : Nat) : Nat → Option Bool := @SmallIngress.seeded T S n
theorem check_preserves_nonreject {N B : Nat} (c : Config FixedRawLengthFence.prefixed.stateCount N B) (T : Nat)
    (safe : (FixedRawLengthFence.prefixed.run T c).state ≠ FixedRawLengthFence.prefixed.reject) :
    producer.run T (liftOld c) = liftOld (FixedRawLengthFence.prefixed.run T c) := @SmallIngress.preserves_nonreject N B c T safe
theorem check_raw_gamma_start {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true) :
    producer.run (FixedRawLengthFence.installClock (pairLength a m)+FixedRawLengthFence.contentClock a m+3*(a+m)+7)
      (initialConfig producer (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
      ⟨q 124,⟨8,by
        have h := (FixedRawLengthFence.resource_bounds (pairLength a m)).1
        have hN := (FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.gate_first_arrival (B := 0) x w tag).2.2.2.2
        simp only [tapeLength,pairLength] at *; omega⟩,
        FixedRawLengthFence.fencedContentTape (FixedRawLengthFence.allocation (pairLength a m)) x w⟩ := @SmallIngress.raw_gamma_start a m x w tag
theorem check_producer_small_modes (N B S : Nat) (n : Fin 3) (T : Nat → Option Bool)
    (full : (if n.val=0 then 9 else 11) ≤ S) (fit : S+6 < tapeLength N B)
    (h6 : T 6=some true) (h7 : T 7=some false) (h8 : T 8=some (n.val==0))
    (h9 : n.val≠0 → T 9=some true) (h10 : n.val≠0 → T 10=some (n.val==2))
    (source : ∀ i, i < S → ∃ b, T i=some b)
    (clear : ∀ i, S ≤ i → i ≤ S+6 → T i=none) :
    ∃ t, t ≤ 6*S+100 ∧
      producer.run (n := N) (budget := B) t ⟨q 124,⟨8,by split_ifs at full <;> omega⟩,fun i => T i.val⟩ =
        ⟨producer.accept,⟨S+(if n.val=0 then 0 else 1)+2,by split_ifs <;> omega⟩,
          fun i => seeded T S n.val i.val⟩ := @SmallIngress.producer_small_modes N B S n T full fit h6 h7 h8 h9 h10 source clear
theorem check_raw_small_physical {a m : Nat} (x : Bitstring a) (w : Bitstring m) (n : Fin 3)
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (full : (if n.val=0 then 9 else 11) ≤ a+m)
    (h8 : FixedContentTagGate.physicalSymbol (Fin.append x w) 8=some (n.val==0))
    (h9 : n.val≠0 → FixedContentTagGate.physicalSymbol (Fin.append x w) 9=some true)
    (h10 : n.val≠0 → FixedContentTagGate.physicalSymbol (Fin.append x w) 10=some (n.val==2)) :
    let R := pairLength a m
    let B := FixedRawLengthFence.allocation R
    let S := a+m
    let T := Body.extend (FixedRawLengthFence.fencedContentTape B x w)
    let L := S+(if n.val=0 then 0 else 1)+2
    ∃ (t : Nat) (hL : L < tapeLength R B), t ≤ 64*(R+1)^2 ∧ ∀ s,
      machine.run (t+s) (initialConfig machine B (encodePair x w)) =
        producer.seqEmbedRight Stream.machine
          (Stream.machine.run s ⟨Stream.machine.start,⟨L,hL⟩,fun i => seeded T S n.val i.val⟩) := @SmallIngress.raw_small_physical a m x w n tag full h8 h9 h10
end SmallIngress.Audit
#print axioms SmallIngress.q
#print axioms SmallIngress.Audit.pin_q
#print axioms SmallIngress.rows
#print axioms SmallIngress.Audit.pin_rows
#print axioms SmallIngress.producer
#print axioms SmallIngress.Audit.pin_producer
#print axioms SmallIngress.machine
#print axioms SmallIngress.Audit.pin_machine
#print axioms SmallIngress.prepared
#print axioms SmallIngress.Audit.pin_prepared
#print axioms SmallIngress.Target.AcceptedOrbit
#print axioms SmallIngress.Audit.pin_Target_AcceptedOrbit
#print axioms SmallIngress.liftOld
#print axioms SmallIngress.Audit.pin_liftOld
#print axioms SmallIngress.seeded
#print axioms SmallIngress.Audit.pin_seeded
#print axioms SmallIngress.preserves_nonreject
#print axioms SmallIngress.Audit.check_preserves_nonreject
#print axioms SmallIngress.raw_gamma_start
#print axioms SmallIngress.Audit.check_raw_gamma_start
#print axioms SmallIngress.producer_small_modes
#print axioms SmallIngress.Audit.check_producer_small_modes
#print axioms SmallIngress.raw_small_physical
#print axioms SmallIngress.Audit.check_raw_small_physical
open Lean in
run_cmd do
  let e ← getEnv
  for (n, _) in e.constants.toList do
    if n.toString.startsWith "SmallIngress." then logInfo m!"surface|{n}"
  for n in e.header.moduleNames do logInfo m!"imported|{n}"
