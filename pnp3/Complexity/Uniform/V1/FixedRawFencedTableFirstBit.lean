import Complexity.Uniform.V1.FixedRawLengthFenceCountdown

/-! G3v Infrastructure: a fixed symbol-driven suffix executes exactly the first table bit.
Raw composition uses strict first arrival at the actual fenced countdown endpoint.
A positive physical payload is essential: without its blank trail this suffix can loop.
Only cell `a+m+1` changes; the low marked content, target tally and fence remain intact. -/
namespace Pnp3.Complexity.Uniform.V1.FixedRawFencedTableFirstBit
open PairEncoding FixedRawLengthFence
open FixedGammaTargetRegisterDecrement (borrow decBit)
abbrev stateCount : Nat := 11
def qStart : Fin stateCount := ⟨0, by decide⟩
def qRegL : Fin stateCount := ⟨1, by decide⟩
def qContentL : Fin stateCount := ⟨2, by decide⟩
def qOnTerm : Fin stateCount := ⟨3, by decide⟩
def qRead : Fin stateCount := ⟨4, by decide⟩
def qSeekFalse : Fin stateCount := ⟨5, by decide⟩
def qSeekTrue : Fin stateCount := ⟨6, by decide⟩
def qWriteFalse : Fin stateCount := ⟨7, by decide⟩
def qWriteTrue : Fin stateCount := ⟨8, by decide⟩
def qDone : Fin stateCount := ⟨9, by decide⟩
def qReject : Fin stateCount := ⟨10, by decide⟩
def raw (q : Fin stateCount) (s : Option Bool) : Fin stateCount × Option Bool × Move :=
  match q.val, s with
  | 0, none => (qRegL, none, .left)
  | 1, none => (qContentL, none, .left)
  | 1, some false => (qRegL, s, .left)
  | 2, none => (qOnTerm, none, .right)
  | 2, some _ => (qContentL, s, .left)
  | 3, some true => (qRead, s, .right)
  | 4, none | 5, none => (qWriteFalse, none, .right)
  | 4, some false => (qSeekFalse, s, .right)
  | 4, some true => (qSeekTrue, s, .right)
  | 5, some _ => (qSeekFalse, s, .right)
  | 6, none => (qWriteTrue, none, .right)
  | 6, some _ => (qSeekTrue, s, .right)
  | 7, some false => (qDone, some false, .stay)
  | 8, some false => (qDone, some true, .stay)
  | 9, _ => (qDone, s, .stay)
  | _, _ => (qReject, s, .stay)
def suffix : UniformTM := ⟨11,qStart,qDone,qReject,by decide,raw⟩
def machine : UniformTM := prefixed.seq suffix
def sourceOffset (z : Nat) : Nat := 9+2*z
def sourceCursor (a m z : Nat) : Nat := min (a+m) (sourceOffset z)
def sourceBit {a m : Nat} (x : Bitstring a) (w : Bitstring m) (z : Nat) : Bool :=
  (FixedContentTagGate.physicalSymbol (Fin.append x w) (sourceOffset z)).getD false
def outputTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) (z v : Nat) (b : Bool) :
    Fin (tapeLength (pairLength a m) B) → Option Bool :=
  fun i => if i.val = a+m+1 then some b else countdownTape B x w z 0 v i
def cursorClock (a m z : Nat) : Nat := z+6+(a+m-sourceCursor a m z)
def copyClock (a m z : Nat) : Nat := z+8+2*(a+m-sourceCursor a m z)
def rawClock (a m z C d v : Nat) : Nat := countdownSuccessClock a m z C d v+copyClock a m z
def deadline (R : Nat) : Nat := 144*(R+1)^2

private theorem layout {a m B z v : Nat} (x : Bitstring a) (w : Bitstring m)
    (hz : 2 ≤ z) (htrail : 9+z < a+m) :
    let H := sourceCursor a m z
    0 < FixedGammaTargetPayloadExhaustion.termWalk (a+m) z ∧
    8+z+FixedGammaTargetPayloadExhaustion.termWalk (a+m) z = H-1 ∧
    ∀ i : Fin (tapeLength (pairLength a m) B),
      (i.val = H-2 → countdownTape B x w z 0 v i = none) ∧
      (i.val = H-1 → countdownTape B x w z 0 v i = some true) ∧
      (H ≤ i.val → i.val < a+m → countdownTape B x w z 0 v i =
        FixedContentTagGate.physicalSymbol (Fin.append x w) i.val) := by
  dsimp only
  have hwalk : 0 < FixedGammaTargetPayloadExhaustion.termWalk (a+m) z := by
    unfold FixedGammaTargetPayloadExhaustion.termWalk FixedGammaTargetPayloadLoopFoundation.walk; omega
  have hterm : 8+z+FixedGammaTargetPayloadExhaustion.termWalk (a+m) z = sourceCursor a m z-1 := by
    unfold sourceCursor sourceOffset FixedGammaTargetPayloadExhaustion.termWalk FixedGammaTargetPayloadLoopFoundation.walk; omega
  have hb : 10+z ≤ sourceCursor a m z ∧ sourceCursor a m z ≤ a+m := by
    unfold sourceCursor sourceOffset; omega
  refine ⟨hwalk,hterm,fun i => ?_⟩
  simp only [countdownTape,FixedGammaTargetUnaryCountdown.loopTape,
    FixedGammaTargetPayloadExhaustion.finishTape,FixedPairContentMarkerErase.contentTape,
    FixedContentTagGate.physicalSymbol]
  constructor
  · intro hi; rw [if_neg (by simp only [fencePos,pairLength]; omega),if_pos (by omega),if_pos (by omega)]
  constructor
  · intro hi; rw [if_neg (by simp only [fencePos,pairLength]; omega),if_pos (by omega),if_neg (by omega),if_pos (by omega)]
  · intro hlo hhi
    rw [if_neg (by simp only [fencePos,pairLength]; omega),if_pos hhi,if_neg (by omega),if_neg (by omega),if_neg (by omega),dif_pos hhi]

private def At {n B : Nat} (c : Config 11 n B) (q : Fin 11) (h : Nat)
    (T : Fin (tapeLength n B) → Option Bool) : Prop := c.state = q ∧ c.head.val = h ∧ c.tape = T
private def shift (h : Nat) : Move → Nat | .left => h-1 | .stay => h | .right => h+1
private theorem one {n B t k k' : Nat} {c : Config 11 n B} {q q' : Fin 11}
    {T : Fin (tapeLength n B) → Option Bool} {mv : Move}
    (hc : At (suffix.run t c) q k T)
    (hr : ∀ i, i.val = k → suffix.step q (T i) = (q',T i,mv))
    (hm : shift k mv = k') (hb : k+1 < tapeLength n B) : At (suffix.run (t+1) c) q' k' T := by
  obtain ⟨hq,hh,ht⟩ := hc
  have row := hr (suffix.run t c).head hh
  have ha : suffix.step (suffix.run t c).state ((suffix.run t c).tape (suffix.run t c).head) =
      (q',T (suffix.run t c).head,mv) := by rw [hq,ht]; exact row
  refine ⟨congrArg Prod.fst ha,?_,?_⟩
  · change (moveHead (suffix.run t c).head (suffix.step _ _).2.2).val = k'
    rw [ha,← hm]; cases mv <;> simp [moveHead,shift,hh,hb]
  · funext i; change (if i = (suffix.run t c).head then (suffix.step _ _).2.1 else (suffix.run t c).tape i) = T i
    rw [ha,ht]; split_ifs with hi <;> simp_all
private theorem scan {n B t : Nat} {c : Config 11 n B} {q : Fin 11}
    {T : Fin (tapeLength n B) → Option Bool} (pos : Nat → Nat) (mv : Move) (d : Nat)
    (hc : At (suffix.run t c) q (pos 0) T)
    (hr : ∀ j, j < d → ∀ i, i.val = pos j → suffix.step q (T i) = (q,T i,mv))
    (hm : ∀ j, j < d → shift (pos j) mv = pos (j+1))
    (hb : ∀ j, j < d → pos j+1 < tapeLength n B) : At (suffix.run (t+d) c) q (pos d) T := by
  induction d with
  | zero => simpa using hc
  | succ d ih =>
    have he := ih (fun j hj => hr j (by omega)) (fun j hj => hm j (by omega)) (fun j hj => hb j (by omega))
    simpa only [Nat.add_assoc] using one he (hr d (by omega)) (hm d (by omega)) (hb d (by omega))

private theorem retime {n B t u k h : Nat} {c : Config 11 n B} {q : Fin 11}
    {T : Fin (tapeLength n B) → Option Bool} (he : At (suffix.run t c) q k T)
    (ht : t = u) (hh : k = h) : At (suffix.run u c) q h T := by subst ht; subst hh; exact he
private theorem seek_layout {n B L z H : Nat} {T : Fin (tapeLength n B) → Option Bool}
    (c : Config 11 n B) (hc : At c qStart (L+2+z) T) (hH : 2 ≤ H ∧ H ≤ L)
    (hroom : L+3+z < tapeLength n B)
    (hsep : ∀ i, i.val = L+2+z → T i = none) (hgap : ∀ i, i.val = L → T i = none)
    (hreg : ∀ i, L < i.val → i.val ≤ L+1+z → T i = some false)
    (hblank : ∀ i, i.val = H-2 → T i = none) (hterm : ∀ i, i.val = H-1 → T i = some true)
    (hp : ∀ i, H-1 ≤ i.val → i.val < L → T i ≠ none) :
    At (suffix.run (z+6+(L-H)) c) qRead H T := by
  have h1 : At (suffix.run 1 c) qRegL (L+1+z) T :=
    one (t := 0) hc (fun i hi => by rw [hsep i hi]; rfl) (by dsimp [shift]; omega) (by omega)
  have h2 : At (suffix.run (z+2) c) qRegL L T := by
    have he := scan (fun j => L+1+z-j) Move.left (z+1) h1
      (fun j hj i hi => by dsimp at hi; rw [hreg i (by omega) (by omega)]; rfl)
      (fun j hj => by dsimp [shift]; omega) (fun j hj => by dsimp; omega)
    exact retime he (by omega) (by dsimp; omega)
  have h3 : At (suffix.run (z+3) c) qContentL (L-1) T := by
    simpa using one h2 (fun i hi => by rw [hgap i hi]; rfl) rfl (by omega)
  have h4 : At (suffix.run (z+4+(L-H)) c) qContentL (H-2) T := by
    have he := scan (fun j => L-1-j) Move.left (L-H+1) h3
      (fun j hj i hi => by dsimp at hi; cases hs : T i with
        | none => exact False.elim (hp i (by omega) (by omega) hs)
        | some b => rfl)
      (fun j hj => by dsimp [shift]; omega) (fun j hj => by dsimp; omega)
    exact retime he (by omega) (by dsimp; omega)
  have h5 : At (suffix.run (z+5+(L-H)) c) qOnTerm (H-1) T := by
    have he := one h4 (fun i hi => by rw [hblank i hi]; rfl)
      (show shift (H-2) Move.right = H-1 by dsimp [shift]; omega) (by omega)
    exact retime he (by omega) rfl
  have he := one h5 (fun i hi => by rw [hterm i hi]; rfl)
    (show shift (H-1) Move.right = H by dsimp [shift]; omega) (by omega)
  exact retime he (by omega) rfl

private theorem actual_seek {a m B z v : Nat} (x : Bitstring a) (w : Bitstring m)
    (hr : 2*pairLength a m+2 ≤ B)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z)
    (hz : 2 ≤ z) (htrail : 9+z < a+m)
    (c : Config 11 (pairLength a m) B)
    (hc : At c qStart (a+m+2+z) (countdownTape B x w z 0 v)) :
    At (suffix.run (cursorClock a m z) c) qRead (sourceCursor a m z) (countdownTape B x w z 0 v) := by
  have hb : 10+z ≤ sourceCursor a m z ∧ sourceCursor a m z ≤ a+m := by unfold sourceCursor sourceOffset; omega
  have hl := (layout (B := B) (v := v) x w hz htrail).2.2
  have hroom : a+m+3+z < tapeLength (pairLength a m) B := by
    have hw := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z hg).1
    clear htrail hz hc hb hl
    simp only [pairLength,tapeLength] at *; omega
  apply seek_layout c hc (by omega) hroom ?_ ?_ ?_
    (fun i hi => (hl i).1 hi) (fun i hi => (hl i).2.1 hi) ?_
  · intro i hi; simp [countdownTape,FixedGammaTargetUnaryCountdown.loopTape,hi,
      show a+m+2+z ≠ fencePos (pairLength a m) by simp [fencePos,pairLength]; omega]; omega
  · intro i hi; simp [countdownTape,FixedGammaTargetUnaryCountdown.loopTape,hi,fencePos,pairLength]; omega
  · intro i hi hj; simp only [countdownTape,FixedGammaTargetUnaryCountdown.loopTape]
    rw [if_neg (by simp [fencePos,pairLength]; omega),if_neg (by omega),if_neg (by omega),if_pos hj]; simp
  · intro i hi hj; by_cases he : i.val = sourceCursor a m z-1
    · rw [(hl i).2.1 he]; decide
    · rw [(hl i).2.2 (by omega) hj]; simp [FixedContentTagGate.physicalSymbol,hj]

private theorem copy_read {n B t L H : Nat} {T : Fin (tapeLength n B) → Option Bool} (b : Bool)
    (c : Config 11 n B) (hc : At (suffix.run t c) qRead H T) (hH : H ≤ L)
    (hroom : L+2 < tapeLength n B) (hgap : ∀ i, i.val = L → T i = none)
    (hreg : ∀ i, i.val = L+1 → T i = some false)
    (hp : ∀ i, H ≤ i.val → i.val < L → T i ≠ none)
    (hsrc : ∀ i, i.val = H → T i = if H < L then some b else none)
    (hvirtual : H = L → b = false) :
    suffix.run (t+(L-H)+2) c =
      ⟨qDone,⟨L+1,by omega⟩,fun i => if i.val = L+1 then some b else T i⟩ := by
  have hw : At (suffix.run (t+(L-H)+1) c) (if b then qWriteTrue else qWriteFalse) (L+1) T := by
    by_cases hphys : H < L
    · have h1 : At (suffix.run (t+1) c) (if b then qSeekTrue else qSeekFalse) (H+1) T :=
        one hc (fun i hi => by rw [hsrc i hi,if_pos hphys]; cases b <;> rfl) rfl (by omega)
      have h2 : At (suffix.run (t+(L-H)) c) (if b then qSeekTrue else qSeekFalse) L T := by
        have he := scan (fun j => H+1+j) Move.right (L-H-1) h1
          (fun j hj i hi => by dsimp at hi; cases hs : T i with
            | none => exact False.elim (hp i (by omega) (by omega) hs)
            | some v => cases b <;> rfl)
          (fun j hj => by dsimp [shift]; omega) (fun j hj => by dsimp; omega)
        exact retime he (by omega) (by dsimp; omega)
      exact one h2 (fun i hi => by rw [hgap i hi]; cases b <;> rfl) rfl (by omega)
    · have he := one hc (fun i hi => by rw [hsrc i hi,if_neg hphys]; rfl)
        (show shift H Move.right = L+1 by dsimp [shift]; omega) (by omega)
      simpa [show L-H=0 by omega,hvirtual (by omega)] using he
  have row : suffix.step (suffix.run (t+(L-H)+1) c).state
      ((suffix.run (t+(L-H)+1) c).tape (suffix.run (t+(L-H)+1) c).head) = (qDone,some b,Move.stay) := by
    rw [hw.1,hw.2.2,hreg _ hw.2.1]; cases b <;> rfl
  change suffix.stepConfig (suffix.run (t+(L-H)+1) c) = _
  apply Config.ext_parts (congrArg Prod.fst row)
  · apply Fin.ext; change (moveHead _ (suffix.step _ _).2.2).val = _; rw [row]; exact hw.2.1
  · funext i; change (if i = (suffix.run (t+(L-H)+1) c).head then (suffix.step _ _).2.1 else _) = _
    rw [row,hw.2.2]; simp only [Fin.ext_iff,hw.2.1]

private theorem source_read {a m B z v : Nat} (x : Bitstring a) (w : Bitstring m)
    (hz : 2 ≤ z) (htrail : 9+z < a+m) (i : Fin (tapeLength (pairLength a m) B))
    (hi : i.val = sourceCursor a m z) :
    countdownTape B x w z 0 v i = FixedContentTagGate.physicalSymbol (Fin.append x w) (sourceOffset z) := by
  by_cases h : sourceOffset z < a+m
  · have hH : sourceCursor a m z = sourceOffset z := Nat.min_eq_right (Nat.le_of_lt h)
    rw [(layout (B := B) (v := v) x w hz htrail).2.2 i |>.2.2 (by omega) (by omega),hi,hH]
  · have hH : sourceCursor a m z = a+m := Nat.min_eq_left (by omega)
    simp [countdownTape,FixedGammaTargetUnaryCountdown.loopTape,hi,hH,
      FixedContentTagGate.physicalSymbol,h,show a+m ≠ fencePos (pairLength a m) by simp [fencePos,pairLength]; omega]

/-- The closed finite table and composition carry no input, proof, address or clock parameter. -/
theorem table_and_resource_pins :
    suffix.stateCount = 11 ∧ Fintype.card (Fin suffix.stateCount × Option Bool) = 33 ∧
    suffix.start = qStart ∧ suffix.accept = qDone ∧ suffix.reject = qReject ∧
    suffix.rawStep = raw ∧ machine = FixedRawLengthFence.prefixed.seq suffix ∧
    machine.stateCount = 267 ∧ machine.accept.val = 265 ∧ machine.reject.val = 266 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Exact first source cursor, including a boundary blank for virtual false. -/
theorem seek_first_exact {a m B z v : Nat} (x : Bitstring a) (w : Bitstring m)
    (hr : 2*pairLength a m+2 ≤ B)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z)
    (hz : 2 ≤ z) (htrail : 9+z < a+m)
    (c : Config suffix.stateCount (pairLength a m) B) (hq : c.state = qStart)
    (hh : c.head.val = a+m+2+z) (ht : c.tape = countdownTape B x w z 0 v) :
    let e := suffix.run (cursorClock a m z) c
    (e = ⟨qRead,⟨sourceCursor a m z,by have h := Nat.min_le_left (a+m) (sourceOffset z); simp only [sourceCursor,tapeLength,pairLength] at *; omega⟩,
      countdownTape B x w z 0 v⟩) ∧
    e.tape e.head = FixedContentTagGate.physicalSymbol (Fin.append x w) (sourceOffset z) := by
  have he := actual_seek x w hr hg hz htrail c ⟨hq,hh,ht⟩
  exact ⟨Config.ext_parts he.1 (Fin.ext he.2.1) he.2.2,
    by rw [he.2.2]; exact source_read x w hz htrail _ he.2.1⟩

/-- Only the first cleared register cell is overwritten; persistence is explicit. -/
theorem copy_first_exact {a m B z v : Nat} (x : Bitstring a) (w : Bitstring m)
    (hr : 2*pairLength a m+2 ≤ B)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z)
    (hz : 2 ≤ z) (htrail : 9+z < a+m)
    (c : Config suffix.stateCount (pairLength a m) B) (hq : c.state = qStart)
    (hh : c.head.val = a+m+2+z) (ht : c.tape = countdownTape B x w z 0 v) (s : Nat) :
    suffix.run (copyClock a m z+s) c =
      ⟨suffix.accept,⟨a+m+1,by simp only [tapeLength,pairLength]; omega⟩,outputTape B x w z v (sourceBit x w z)⟩ := by
  have hH := Nat.min_le_left (a+m) (sourceOffset z)
  have he := actual_seek x w hr hg hz htrail c ⟨hq,hh,ht⟩
  have hcopy := copy_read (L := a+m) (sourceBit x w z) c he hH (by simp only [tapeLength,pairLength] at *; omega)
    (by intro i hi; simp [countdownTape,FixedGammaTargetUnaryCountdown.loopTape,hi,fencePos,pairLength]; omega)
    (by intro i hi; simp [countdownTape,FixedGammaTargetUnaryCountdown.loopTape,hi,
        show a+m+1 ≠ fencePos (pairLength a m) by simp [fencePos,pairLength]; omega])
    (by intro i hi hj; rw [(layout (B := B) (v := v) x w hz htrail).2.2 i |>.2.2 hi hj]; simp [FixedContentTagGate.physicalSymbol,hj])
    (by intro i hi; rw [source_read x w hz htrail i hi]; unfold sourceBit
        by_cases h : sourceOffset z < a+m
        · simp [FixedContentTagGate.physicalSymbol,h,sourceCursor,Nat.min_eq_right (Nat.le_of_lt h)]
        · simp [FixedContentTagGate.physicalSymbol,h,sourceCursor,Nat.min_eq_left (by omega : a+m ≤ sourceOffset z)])
    (by intro h; have hb : a+m ≤ sourceOffset z := by unfold sourceCursor at h; omega
        simp [sourceBit,FixedContentTagGate.physicalSymbol,Nat.not_lt_of_ge hb])
  have hc : copyClock a m z = cursorClock a m z+(a+m-sourceCursor a m z)+2 := by unfold copyClock cursorClock; omega
  rw [suffix.run_add,hc,hcopy,suffix.run_accept _ rfl]; rfl

theorem raw_first_bit_exact {a m B z C v : Nat}
    {q : Fin FixedGammaPayloadDispatcher.stateCount}
    (x : Bitstring a) (w : Bitstring m)
    (hr : 2*pairLength a m+2 ≤ B)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z)
    (hz : 2 ≤ z)
    (hfirst : FixedGammaPayloadDispatcherFirstArrival.StrictFirstTerminalAt B x w C q)
    (hv : ∀ j, j ≤ z → v.testBit (z-j) = decBit x w z (borrow x w z) j)
    (hhigh : ∀ b, z < b → v.testBit b = false)
    (hcap : v ≤ capacity a m z) (htrail : 9+z < a+m) (s : Nat) :
    machine.run (rawClock a m z C (borrow x w z) v+s)
      (initialConfig machine B (encodePair x w)) =
      ⟨machine.accept, ⟨a+m+1, by simp only [tapeLength, pairLength]; omega⟩,
        outputTape B x w z v (sourceBit x w z)⟩ := by
  have he := raw_fenced_countdown_success_exact x w hr htag hg hz hfirst hv hhigh hcap 0
  have hs := raw_fenced_countdown_success_strict x w hr htag hg hz hfirst hv hhigh hcap
  simp only [Nat.add_zero] at he
  rw [machine,rawClock,Nat.add_assoc,UniformTM.seq_initialConfig,
    UniformTM.seq_handoff prefixed suffix _ (fun t ht => (hs t ht).1) (congrArg Config.state he),he]
  rw [copy_first_exact x w hr hg hz htrail _ rfl rfl rfl s]; rfl

theorem raw_overflow_exact {a m B z C v : Nat}
    {q : Fin FixedGammaPayloadDispatcher.stateCount}
    (x : Bitstring a) (w : Bitstring m)
    (hr : 2*pairLength a m+2 ≤ B)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z)
    (hz : 2 ≤ z)
    (hfirst : FixedGammaPayloadDispatcherFirstArrival.StrictFirstTerminalAt B x w C q)
    (hv : ∀ j, j ≤ z → v.testBit (z-j) = decBit x w z (borrow x w z) j)
    (hhigh : ∀ b, z < b → v.testBit b = false)
    (hover : capacity a m z < v) (s : Nat) :
    machine.run (countdownRejectClock a m z C (borrow x w z)+s)
      (initialConfig machine B (encodePair x w)) =
      ⟨machine.reject,
        ⟨fencePos (pairLength a m), by
          simp only [fencePos, tapeLength] at *; omega⟩,
        countdownTape B x w z (v-capacity a m z-1) (capacity a m z)⟩ := by
  have he := raw_fenced_countdown_reject_exact x w hr htag hg hz hfirst hv hhigh hover 0
  simp only [Nat.add_zero] at he
  rw [machine,UniformTM.seq_initialConfig,
    UniformTM.seq_reject_handoff prefixed suffix _ (congrArg Config.state he) s,he]

theorem raw_clock_bound {a m z C d v : Nat}
    (hw : 9+z ≤ a+m) (hz : 2 ≤ z) (hd : d ≤ z)
    (hC : C ≤ 2*(a+m)*(a+m)) (hv : v ≤ capacity a m z) :
    rawClock a m z C d v ≤ deadline (pairLength a m) ∧
    countdownRejectClock a m z C d ≤ deadline (pairLength a m) ∧
    allocation (pairLength a m) ≤ deadline (pairLength a m) := by
  obtain ⟨hS,hR,hB⟩ := countdown_clock_bound hw hz hd hC hv
  have hL : a+m ≤ pairLength a m := by unfold pairLength; omega
  have hcopy : copyClock a m z ≤ 3*pairLength a m+8 := by unfold copyClock; omega
  have hsq : pairLength a m ≤ (pairLength a m+1)^2 := by nlinarith [Nat.zero_le (pairLength a m*pairLength a m)]
  unfold rawClock deadline countdownDeadline at *
  exact ⟨by omega,by omega,by omega⟩


end Pnp3.Complexity.Uniform.V1.FixedRawFencedTableFirstBit
