import PhysicalCallerClosure.InitialRows
import PhysicalCallerClosure.TableReadRows
import PhysicalCallerClosure.WriteReset
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
private def select (owner : Name) (leaf kind : String) : TacticM Unit := do
  let e←getEnv
  let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure")
  let some ci:=e.find? n | throwError "Missing exact paid-row support {n}"
  let actual:=match ci with | .defnInfo _=>"definition" | .thmInfo _=>"theorem" | .ctorInfo _=>"constructor" | _=>"other"
  unless actual==kind do throwError "Wrong paid-row support kind"
  let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
  unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
  unless e.header.moduleNames[i]! == owner do throwError "Wrong paid-row support owner"
  logInfo m!"paid-row-adapter|{n}|{ci.type}"
  closeMainGoal `select (mkConst n (ci.levelParams.map Level.param))
run_cmd do
  let e←getEnv
  for (owner,leaves) in [(`PhysicalCallerClosure.Engine,["Node","Path","put","keep","ns","NativeSafe","ns_safe"]),
      (`PhysicalCallerClosure.InitialNative,["InitialRows","GammaStopRows","initial_lift","gamma_stop","gamma_scan"]),
      (`PhysicalCallerClosure.ShiftSource,["PlainSeekRows","plain_seek"]),
      (`PhysicalCallerClosure.TableRead,["boolTag","TableReadRows","read_table"]),
      (`PhysicalCallerClosure.WriteReset,["writerEntry"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing paid-row term {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong paid-row owner"
      logInfo m!"paid-row-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac select `PhysicalCallerClosure.Engine "Node.mk" "constructor"
private abbrev ini_code_0 : ∀ k : Nat,InitialRows (M:=callerMachine k) (Safe:=NativeSafe k) false (ns k 5)
    (fun a=>if a then ns k 488 else ns k 9) := by
  run_tac select `PhysicalCallerClosure.InitialRows "code_0" "definition"
private abbrev ini_code_1 : ∀ k : Nat,InitialRows (M:=callerMachine k) (Safe:=NativeSafe k) true (ns k 962)
    (fun a=>if a then ns k 488 else ns k 9) := by
  run_tac select `PhysicalCallerClosure.InitialRows "code_1" "definition"
private abbrev ini_virtual_seek : ∀ k : Nat,PlainSeekRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 971) (ns k 968) := by
  run_tac select `PhysicalCallerClosure.InitialRows "virtual_seek" "theorem"
private abbrev ini_stop_9 : ∀ k : Nat,GammaStopRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 9) (ns k 11) := by
  run_tac select `PhysicalCallerClosure.InitialRows "stop_9" "theorem"
private abbrev ini_loop_9 : ∀ k : Nat,∀ b,(callerMachine k).step (ns k 9) (some b)=(ns k 9,some b,.left) := by
  run_tac select `PhysicalCallerClosure.InitialRows "loop_9" "theorem"
private abbrev ini_stop_488 : ∀ k : Nat,GammaStopRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 488) (ns k 490) := by
  run_tac select `PhysicalCallerClosure.InitialRows "stop_488" "theorem"
private abbrev ini_loop_488 : ∀ k : Nat,∀ b,(callerMachine k).step (ns k 488) (some b)=(ns k 488,some b,.left) := by
  run_tac select `PhysicalCallerClosure.InitialRows "loop_488" "theorem"
private abbrev ini_stop_968 : ∀ k : Nat,GammaStopRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 968) (ns k 975) := by
  run_tac select `PhysicalCallerClosure.InitialRows "stop_968" "theorem"
private abbrev ini_start_0 : ∀ k : Nat,∀ b,(callerMachine k).step (ns k 7) b=(ns k 5,b,.stay) := by
  run_tac select `PhysicalCallerClosure.InitialRows "start_0" "theorem"
private abbrev ini_start_1 : ∀ k : Nat,∀ b,(callerMachine k).step (ns k 964) b=(ns k 962,b,.stay) := by
  run_tac select `PhysicalCallerClosure.InitialRows "start_1" "theorem"
private abbrev ini_start_2 : ∀ k : Nat,∀ b,(callerMachine k).step (ns k 973) b=(ns k 971,b,.stay) := by
  run_tac select `PhysicalCallerClosure.InitialRows "start_2" "theorem"
private abbrev rd_code_11 : ∀ k : Nat,TableReadRows (M:=callerMachine k) (Safe:=NativeSafe k) true (ns k 11)
    (fun j:Fin 3=>ns k (#[399,440,481][j.val]!)) := by
  run_tac select `PhysicalCallerClosure.TableReadRows "code_11" "definition"
private abbrev rd_code_490 : ∀ k : Nat,TableReadRows (M:=callerMachine k) (Safe:=NativeSafe k) true (ns k 490)
    (fun j:Fin 3=>ns k (#[868,909,950][j.val]!)) := by
  run_tac select `PhysicalCallerClosure.TableReadRows "code_490" "definition"
private abbrev rd_code_975 : ∀ k : Nat,TableReadRows (M:=callerMachine k) (Safe:=NativeSafe k) false (ns k 975)
    (fun j:Fin 3=>ns k (#[1345,1385,1425][j.val]!)) := by
  run_tac select `PhysicalCallerClosure.TableReadRows "code_975" "definition"
private def gammaControl (k : Nat) (a : Bool) : Fin (callerMachine k).stateCount:=if a then ns k 488 else ns k 9
private def readControl (k : Nat) (a : Bool) : Fin (callerMachine k).stateCount:=if a then ns k 490 else ns k 11
private def startControl (k : Nat) (mode : Fin 3) : Fin (callerMachine k).stateCount:=ns k (#[7,964,973][mode.val]!)
private def inputEntry (k : Nat) (b : Bool) : Fin (callerMachine k).stateCount:=if b then ns k 962 else ns k 5
private def anchorMode {S} (source : Fin S → Bool) (M : Nat) : Fin 3:=
  if M < S then SerializedBody.sourceMode source (M-1) else ⟨2,by decide⟩
private def initialTape (T : Nat → Option Bool) (S M : Nat) : Nat → Option Bool:=
  if M < S then put T M none else T
private def sourceHoles (T : Nat → Option Bool) (S M A : Nat) : Nat → Option Bool:=
  put (if M < S then put T (M-1) none else T) A none
private theorem physical_code (k : Nat) (b : Bool) :
    Nonempty (InitialRows (M:=callerMachine k) (Safe:=NativeSafe k) b (inputEntry k b) (gammaControl k)) := by
  cases b
  · exact ⟨ini_code_0 k⟩
  · exact ⟨ini_code_1 k⟩
private theorem gamma_code (k : Nat) (a : Bool) :
    GammaStopRows (M:=callerMachine k) (Safe:=NativeSafe k) (gammaControl k a) (readControl k a) := by
  cases a
  · exact ini_stop_9 k
  · exact ini_stop_488 k
private theorem gamma_safe (k : Nat) (a : Bool) : NativeSafe k (gammaControl k a) := by
  cases a <;> exact ns_safe k _ (by decide) (by decide)
private theorem gamma_loop (k : Nat) (a : Bool) : ∀ b,
    (callerMachine k).step (gammaControl k a) (some b)=(gammaControl k a,some b,.left) := by
  cases a
  · exact ini_loop_9 k
  · exact ini_loop_488 k
private theorem read_code (k : Nat) (a : Bool) :
    Nonempty (TableReadRows (M:=callerMachine k) (Safe:=NativeSafe k) true (readControl k a)
      (fun tag=>writerEntry k (boolTag a) tag)) := by
  cases a
  · have eq:(fun tag=>writerEntry k (boolTag false) tag)=(fun j:Fin 3=>ns k (#[399,440,481][j.val]!)):=by
      funext j;fin_cases j <;> rfl
    rw [eq];exact ⟨rd_code_11 k⟩
  · have eq:(fun tag=>writerEntry k (boolTag true) tag)=(fun j:Fin 3=>ns k (#[868,909,950][j.val]!)):=by
      funext j;fin_cases j <;> rfl
    rw [eq];exact ⟨rd_code_490 k⟩
private theorem virtual_code (k : Nat) :
    Nonempty (TableReadRows (M:=callerMachine k) (Safe:=NativeSafe k) false (ns k 975)
      (fun tag=>writerEntry k ⟨2,by decide⟩ tag)) := by
  have eq:(fun tag=>writerEntry k ⟨2,by decide⟩ tag)=(fun j:Fin 3=>ns k (#[1345,1385,1425][j.val]!)):=by
    funext j;fin_cases j <;> rfl
  rw [eq];exact ⟨rd_code_975 k⟩
private theorem tag_from_source {S p} (source : Fin S → Bool) (T : Nat → Option Bool) (tag : Fin 3)
    (ps:p ≤ S) (_eof:T S=none) (cell:∀ hp:p < S,T p=some (source ⟨p,hp⟩))
    (v:tag.val=2 ↔ p=S) (bit:tag.val=1 ↔ T p=some true) : tag=SerializedBody.sourceMode source p := by
  have bound:=tag.isLt
  by_cases hp:p < S
  · have n2:tag.val≠2:=by intro eq;have h:=v.mp eq;omega
    rw [cell hp] at bit
    cases hb:source ⟨p,hp⟩
    · have n1:tag.val≠1:=by simpa only [hb,Bool.false_eq_true,Option.some.injEq,iff_false] using bit
      have zero:tag.val=0:=by omega
      apply Fin.ext
      simpa only [SerializedBody.sourceMode,dif_pos hp,hb,Bool.false_eq_true,ite_false] using zero
    · have one:tag.val=1:=by simpa only [hb,iff_true] using bit
      apply Fin.ext
      simpa only [SerializedBody.sourceMode,dif_pos hp,hb,ite_true] using one
  · have eq:p=S:=by omega
    have two:tag.val=2:=v.mpr eq
    apply Fin.ext
    simpa only [SerializedBody.sourceMode,dif_neg hp] using two
private theorem initial_source (k : Nat) (S L H M A P : Nat) (T : Nat → Option Bool) (source : Fin S → Bool)
    (a2:2 ≤ A) (margin:A+2 ≤ M) (as:A ≤ S) (sl:S < L) (lh:L < H) (room:H ≤ P)
    (gamma:T (A-2)=none) (marker:T (A-1)=some true)
    (src:∀ i,A ≤ i → ∀ hi:i < S,T i=some (source ⟨i,hi⟩))
    (ts:T S=none) (tl:T L=none) (th:T H=none)
    (reg:∀ i,S < i → i < L → ∃ b,T i=some b) (beta:∀ i,L < i → i < H → ∃ b,T i=some b) :
    Path (callerMachine k) (NativeSafe k) P (2*(H-A)+11)
      (node (startControl k (SerializedBody.sourceMode source M)) H (initialTape T S M))
      (node (writerEntry k (anchorMode source M) (SerializedBody.sourceMode source A)) H (sourceHoles T S M A)) := by
  by_cases physical:M < S
  · let b:=source ⟨M,physical⟩
    have am:M-1 < S:=by omega
    let a:=source ⟨M-1,am⟩
    let I:=put T M none
    have high (i) (hi:M < i) : I i=T i:=by simp only [I,put,if_neg (show i≠M by omega)]
    have mode:SerializedBody.sourceMode source M=boolTag b:=by
      simp only [SerializedBody.sourceMode,dif_pos physical,boolTag,b]
    have ac:anchorMode source M=boolTag a:=by
      simp only [anchorMode,if_pos physical,SerializedBody.sourceMode,dif_pos am,boolTag,a]
    have startRow:∀ v,(callerMachine k).step (startControl k (boolTag b)) v=(inputEntry k b,v,.stay):=by
      cases hb:b
      · exact ini_start_0 k
      · exact ini_start_1 k
    have safe:NativeSafe k (startControl k (boolTag b)):=by cases b <;> exact ns_safe k _ (by decide) (by decide)
    have first:=keep (startControl k (boolTag b)) (inputEntry k b) H H I .stay (P:=P) room room safe (startRow _) rfl
    obtain ⟨code⟩:=physical_code k b
    have lift:=initial_lift (Mpos:=M) (T:=I) (a:=a) (by omega) physical sl lh room
      (by simp only [I,put,if_true]) (by simp only [I,put,if_neg (show M-1≠M by omega)];exact src (M-1) (by omega) am)
      (by rw [high S physical];exact ts) (by rw [high L (by omega)];exact tl) (by rw [high H (by omega)];exact th)
      (by intro i lo hi;rw [high i lo];exact ⟨_,src i (by omega) hi⟩)
      (by intro i lo hi;rw [high i (by omega)];exact reg i lo hi)
      (by intro i lo hi;rw [high i (by omega)];exact beta i lo hi) code
    let U:=put T (M-1) none
    have restored:put (put I M (some b)) (M-1) none=U:=by
      have tm:T M=some b:=src M (by omega) physical
      have eq:put I M (some b)=T:=by
        funext i;by_cases h:i=M <;> simp [I,put,h,tm]
      rw [eq]
    rw [restored] at lift
    have low (i) (hi:i < M-1) : U i=T i:=by simp only [U,put,if_neg (show i≠M-1 by omega)]
    have ug:U (A-2)=none:=by rw [low (A-2) (by omega)];exact gamma
    have um:U (A-2+1)=some true:=by rw [show A-2+1=A-1 by omega,low (A-1) (by omega)];exact marker
    have gp:=gamma_scan (P:=P) (hi:=M-2) (low:=A-2) (T:=U) (by omega) (by omega) ug um (by
      intro i lo hi
      rw [low i (by omega)]
      by_cases eq:i=A-1
      · exact ⟨true,by rw [eq];exact marker⟩
      · exact ⟨_,src i (by omega) (by omega)⟩) (gamma_safe k a) (gamma_loop k a) (gamma_code k a)
    rw [show A-2+2=A by omega] at gp
    obtain ⟨rc⟩:=read_code k a
    have unchanged (i) (hi:i≠M-1) : U i=T i:=by simp only [U,put,if_neg hi]
    have us:U S=none:=by rw [unchanged S (by omega)];exact ts
    obtain ⟨tag,te,tv,read⟩:=read_table (anchored:=true) (p:=A) (anchor:=M-1) (T:=U) as sl lh room us
      (by rw [unchanged L (by omega)];exact tl) (by rw [unchanged H (by omega)];exact th)
      (by intro i lo hi ne;rcases ne with bad|ne
          · contradiction
          · rw [unchanged i ne];exact ⟨_,src i (by omega) hi⟩)
      (by intro phy;rw [low A (by omega)];exact ⟨_,src A le_rfl phy⟩)
      (by intro _ _;exact ⟨by omega,by omega,by simp only [U,put,if_true]⟩)
      (by intro i lo hi;rw [unchanged i (by omega)];exact reg i lo hi)
      (by intro i lo hi;rw [unchanged i (by omega)];exact beta i lo hi) rc
    have tagEq:tag=SerializedBody.sourceMode source A:=tag_from_source source U tag as us (by
      intro phy;rw [low A (by omega)];exact src A le_rfl phy) te tv
    rw [tagEq] at read
    have whole:=first.append (lift.append (gp.append read))
    rw [mode,ac]
    simp only [initialTape,sourceHoles,if_pos physical]
    change Path (callerMachine k) (NativeSafe k) P (2*(H-A)+11)
      (node (startControl k (boolTag b)) H I)
      (node (writerEntry k (boolTag a) (SerializedBody.sourceMode source A)) H (put U A none))
    convert whole using 1
    omega
  · have mode:SerializedBody.sourceMode source M=⟨2,by decide⟩:=by simp only [SerializedBody.sourceMode,dif_neg physical]
    have am:anchorMode source M=⟨2,by decide⟩:=by simp only [anchorMode,if_neg physical]
    have first:=keep (ns k 973) (ns k 971) H H T .stay (P:=P) room room (ns_safe k 973 (by decide) (by decide)) (ini_start_2 k _) rfl
    have seek:=plain_seek (p:=A-2) (T:=T) (by omega) sl lh room gamma ts tl th (by
      intro i lo hi
      by_cases eq:i=A-1
      · exact ⟨true,by rw [eq];exact marker⟩
      · exact ⟨_,src i (by omega) hi⟩) reg beta (ini_virtual_seek k)
    have stop:=gamma_stop (P:=P) (low:=A-2) (T:=T) (by omega) gamma (by rw [show A-2+1=A-1 by omega];exact marker) (ini_stop_968 k)
    rw [show A-2+2=A by omega] at stop
    obtain ⟨code⟩:=virtual_code k
    obtain ⟨tag,te,tv,read⟩:=read_table (anchored:=false) (p:=A) (T:=T) (anchor:=0) as sl lh room ts tl th (by
      intro i lo hi _;exact ⟨_,src i (by omega) hi⟩) (by intro phy;exact ⟨_,src A le_rfl phy⟩)
      (by intro _ bad;contradiction) reg beta code
    have tagEq:tag=SerializedBody.sourceMode source A:=tag_from_source source T tag as ts (by intro phy;exact src A le_rfl phy) te tv
    rw [tagEq] at read
    have whole:=first.append (seek.append (stop.append read))
    rw [mode,am]
    simp only [initialTape,sourceHoles,if_neg physical]
    change Path (callerMachine k) (NativeSafe k) P (2*(H-A)+11)
      (node (ns k 973) H T) (node (writerEntry k ⟨2,by decide⟩ (SerializedBody.sourceMode source A)) H (put T A none))
    convert whole using 1
    omega
end PhysicalCallerClosure
