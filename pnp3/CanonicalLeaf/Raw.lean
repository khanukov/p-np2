import CanonicalLeaf.Counter
namespace CanonicalLeaf
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
run_cmd do
  for (mod,ns,s,localName) in [("CanonicalLeaf.Rows","CanonicalLeaf","base_end","base_end"),
      ("CanonicalLeaf.Rows","CanonicalLeaf","transport","transport"),
      ("VirtualLeaf.Raw","VirtualLeaf","image_before","image_before"),("VirtualLeaf.Raw","VirtualLeaf","width","width"),
      ("VirtualLeaf.Body","VirtualLeaf","extra_ne","extra_ne"),("VirtualLeaf.Transport","VirtualLeaf","entry_ne","entry_ne"),
      ("VirtualLeaf.Transport","VirtualLeaf","transport","old_transport"),("VirtualLeaf.Transport","VirtualLeaf","entry_val","entry_val")] do
    let found:=(← getEnv).constants.toList.map Prod.fst |>.filter fun n =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++s)
    unless found.length==1 do throwError "Ambiguous private term {mod}/{s}: {found}"
    logInfo m!"private-term|{found.head!}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str Name.anonymous localName) found.head! :: st.openDecls}
private theorem five_price (n s bound : Nat) (h : s+(2*n+5) ≤ bound) : s+5 ≤ bound := by omega
private theorem below_result (k : Nat) (s : Fin (machine k).stateCount)
    (low : s.val < (IngressRepair.machine k).stateCount) (b : Bool) : s ≠ result k b := by
  intro bad; have e:=congrArg Fin.val bad
  cases b with
  | false => change s.val=(IngressRepair.machine k).stateCount+6 at e; omega
  | true => change s.val=(IngressRepair.machine k).stateCount+7 at e; omega
private theorem cursor_live (k i : Nat) (hi : i < Cursor.stateCount k) (different : i ≠ 40) :
    IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k i) ≠ (IngressRepair.machine k).reject := by
  intro bad; have e:=congrArg Fin.val bad
  change 288+i%Cursor.stateCount k=328 at e
  rw [Nat.mod_eq_of_lt hi] at e; omega
/-- Same original accepted raw source; three virtual families consumed, normal prefix preserved. -/
theorem accepted_leaf (k : Nat) : Target.Raw k := by
  intro a m x w accepted
  obtain ⟨pr,parsed,z,hH,gamma,eof,physical⟩:=VirtualLeaf.accepted_leaf k x w accepted
  let S:=a+m; let R:=pairLength a m; let B:=FixedRawLengthFence.allocation R
  let n:=pr.2.n; let L:=S+z+2; let F:=FixedRawLengthFence.fencePos R
  let p:=min (9+2*z+2^n) S; let r:=S-p
  let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
  let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
  let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
  let Y:=RuntimeBitLength.Target.fullImage X L n F r
  let Z:=AllArityBitLength.Target.seedImage Y F r n
  let c:=initialConfig (machine k) B (encodePair x w)
  let base:=initialConfig (VirtualLeaf.machine k) B (encodePair x w)
  let old:=initialConfig (IngressRepair.machine k) B (encodePair x w)
  let H : Fin (tapeLength R B):=⟨S+z+n+3,hH⟩
  let deliver (T : Nat → Option Bool) : Prop :=
    ∃ positive : 0 < n, S ≤ Cursor.Target.M k n z ∧
    (∀ j : Fin (Cursor.Target.W k n), padRead (Fin.append x w) (Cursor.Target.M k n z+j.val)=false) ∧
    (treeCircuitWitnessCodec (thresholdPoly k)).decode n (fun _ => false)=some (Pnp3.Models.Circuit.input ⟨0,positive⟩) ∧
    ∃ t s, s ≤ t ∧ t ≤ 2147483648*(k+1)*(R+1)^5 ∧
    (IngressRepair.machine k).run t old=⟨VirtualLeaf.entry k,H,fun i => T i.val⟩ ∧
    (IngressRepair.machine k).run s old=⟨VirtualLeaf.entry k,H,fun i => T i.val⟩ ∧
    (∀ u, u < s → ((IngressRepair.machine k).run u old).state ≠ VirtualLeaf.entry k) ∧
    (machine k).run s c=⟨entry k,H,fun i => T i.val⟩ ∧
    s+5 ≤ 4294967296*(k+1)*(R+1)^5 ∧
    (machine k).run (s+5) c=⟨result k false,H,Function.update (fun i => T i.val) H (some false)⟩ ∧
    (∀ u, u ≤ s+5 → ((machine k).run u c).state ≠ (machine k).accept ∧ ((machine k).run u c).state ≠ (machine k).reject) ∧
    (∀ u, u < s+5 → ∀ b, ((machine k).run u c).state ≠ result k b)
  have wn : n ≤ S:=width x w accepted parsed
  have Hv : L+n+1=S+z+n+3 := by dsimp only [L]; omega
  fromDonor "VirtualReady.Raw" "VirtualReady" "actual_base" =>
    obtain ⟨frame,_fresh⟩:=OLD (n:=n) x w gamma
      (AcceptedBody.strict_capacity x w gamma wn) (Stream.accepted_rows_fit k x w accepted parsed gamma)
  fromDonor "VirtualReady.Raw" "VirtualReady" "Base.arena" => have arena:=OLD frame
  fromDonor "VirtualReady.Raw" "VirtualReady" "Base.sep" => have sep:=OLD frame
  fromDonor "VirtualReady.Raw" "VirtualReady" "Base.right" => have last:=OLD frame
  change S+z+n+3+2^n < F at arena
  change V L=none at sep
  change V (S+z+n+3)=none at last
  have room : S+z+n+3 < F := (Nat.le_add_right _ _).trans_lt arena
  have assn (i : Nat) (lo : L < i) (hi : i < L+n+1) : V i=some false := by
    dsimp only [V,Stream.Target.image]
    rw [if_pos ⟨lo,hi⟩,CappedWorkspace.overflow_bits]
    simp [List.getElem!_eq_getElem?_getD,List.getElem?_replicate]; split_ifs <;> rfl
  have close (T : Nat → Option Bool) (shape : T=V ∨ T=Cursor.Target.image V k S n z F)
      (positive : 0 < n) (logical : S ≤ Cursor.Target.M k n z)
      (zeros : ∀ j : Fin (Cursor.Target.W k n), padRead (Fin.append x w) (Cursor.Target.M k n z+j.val)=false)
      (decoded : (treeCircuitWitnessCodec (thresholdPoly k)).decode n (fun _ => false)=some (Pnp3.Models.Circuit.input ⟨0,positive⟩))
      (t s : Nat) (hs : s ≤ t) (ht : t ≤ 2147483648*(k+1)*(R+1)^5)
      (oldT : (IngressRepair.machine k).run t old=⟨VirtualLeaf.entry k,H,fun i => T i.val⟩)
      (oldS : (IngressRepair.machine k).run s old=⟨VirtualLeaf.entry k,H,fun i => T i.val⟩)
      (first : ∀ u, u < s → ((IngressRepair.machine k).run u old).state ≠ VirtualLeaf.entry k)
      (preOld : (VirtualLeaf.machine k).run s base=⟨entry k,H,fun i => T i.val⟩)
      (price : s+(2*n+5) ≤ 4294967296*(k+1)*(R+1)^5) : deliver T := by
    have point (i : Nat) (hi : i ≤ S+z+n+3) : T i=V i := by
      rcases shape with eq | eq
      · rw [eq]
      · rw [eq]; exact image_before V k S n z F i (hi.trans (Nat.le_of_lt room)) logical
    have tf : T L=none := (point L (by dsimp [L]; omega)).trans sep
    have th : T (S+z+n+3)=none := (point _ le_rfl).trans last
    have digits (j : Fin n) : T ((L+n+1)-1-j.val)=some false := by
      rw [point _ (by dsimp only [L]; omega)]
      exact assn _ (by omega) (by omega)
    have low:=base_end base ⟨VirtualLeaf.entry k,H,fun i => T i.val⟩ preOld (entry_ne k).2
    have tx (u : Nat) (hu : u ≤ s) : (machine k).run u c=(VirtualLeaf.machine k).run u base :=
      transport base (fun v hv => low v (by omega)) u hu
    have pre : (machine k).run s c=⟨entry k,H,fun i => T i.val⟩ := by rw [tx s le_rfl,preOld]
    obtain ⟨body,_footprint,_safe,early,_tape,_semantic,_cover,_tail⟩:=prepared k L n (fun _ => false)
      (fun i : Fin (tapeLength R B) => T i.val) (by rw [Hv]; exact hH) tf (by simpa only [Hv] using th) digits
    have done : (machine k).run (s+5) c=⟨result k false,H,Function.update (fun i => T i.val) H (some false)⟩ := by
      rw [UniformTM.run_add,pre]
      simpa only [Hv,if_neg (show n ≠ 0 by omega),dif_pos positive] using body
    have safe:= (machine k).no_terminal_of_le c
      (by rw [done]; exact (extra_ne k ⟨6,by decide⟩).1)
      (by rw [done]; exact (extra_ne k ⟨6,by decide⟩).2)
    refine ⟨positive,logical,zeros,decoded,t,s,hs,ht,oldT,oldS,first,pre,five_price n s _ price,done,safe,?_⟩
    intro u hu b
    by_cases before : u < s
    · rw [tx u (by omega)]; exact below_result k _ (low u (by omega)) b
    · have eq : u=s+(u-s) := by omega
      rw [eq,UniformTM.run_add,pre]
      simpa only [Hv] using early (u-s) (by omega) b
  refine ⟨pr,parsed,z,hH,gamma,?_,?_⟩
  · intro atEOF
    obtain ⟨pos,logical,zeros,decoded,t,s,hs,ht,oldT,oldS,first,pre,price,_done,_safe⟩:=eof atEOF
    exact close V (Or.inl rfl) pos logical zeros decoded t s hs ht oldT oldS first pre price
  · intro phys
    obtain ⟨fit,outcome⟩:=physical phys
    refine ⟨fit,?_⟩
    rcases outcome with ⟨over,logical,leaf⟩ | ⟨fits,tail⟩
    · obtain ⟨pos,logical',zeros,decoded,t,s,hs,ht,oldT,oldS,first,pre,price,_done,_safe⟩:=leaf
      exact Or.inl ⟨over,logical,close _ (Or.inr rfl) pos logical' zeros decoded t s hs ht oldT oldS first pre price⟩
    · refine Or.inr ⟨fits,?_⟩
      rcases tail with ⟨wr,t,d,ht,hd,total,firstRun,first,normal⟩ | ⟨v2,v3,v4,v5,dd,cap,logical,leaf⟩
      · have low:=base_end base _ normal (cursor_live k (613+93*k) (by unfold Cursor.stateCount; omega) (by omega))
        have tx (u : Nat) (hu : u ≤ t+d) : (machine k).run u c=(VirtualLeaf.machine k).run u base :=
          transport base (fun v hv => low v (by omega)) u hu
        exact Or.inl ⟨wr,t,d,ht,hd,total,(tx t (by omega)).trans firstRun,
          (by intro u hu bad; rw [tx u (by omega)] at bad; exact first u hu bad),(tx (t+d) le_rfl).trans normal⟩
      · obtain ⟨pos,logical',zeros,decoded,t,s,hs,ht,oldT,oldS,first,pre,price,_done,_safe⟩:=leaf
        exact Or.inr ⟨v2,v3,v4,v5,dd,cap,logical,close _ (Or.inr rfl) pos logical' zeros decoded t s hs ht oldT oldS first pre price⟩
/-- Same universal repaired missing-FIRST-payload reject domain, no malformed-final claim. -/
theorem missing_payload (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m) (z : Nat)
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (pos : 0 < z) (short : a+m=9+z) :
    ∃ t, t ≤ 128*(pairLength a m+1)^2 ∧
      ((machine k).run t (initialConfig (machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=(machine k).reject ∧
      PartAEndpoint.thresholdContentWitnessRelation k a m x w=false := by
  obtain ⟨t,ht,done,prior,_safe,negative⟩:=IngressRepair.absent_first_payload k x w z tag gamma pos short
  let old:=initialConfig (IngressRepair.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
  have first (u : Nat) (hu : u < t) : ((IngressRepair.machine k).run u old).state ≠ VirtualLeaf.entry k := by
    intro bad; have bound:=prior u hu; have e:=congrArg Fin.val bad
    rw [entry_val] at e
    change ((IngressRepair.machine k).run u old).state.val < 139 at bound
    omega
  have oldTx:=old_transport old first
  have tx:=transport (VirtualLeaf.config k old) (t:=t) (by
    intro u hu; rw [oldTx u (by omega)]
    have bound:=prior u hu
    change ((IngressRepair.machine k).run u old).state.val < (IngressRepair.machine k).stateCount
    have room : 139 ≤ (IngressRepair.machine k).stateCount := by change 139 ≤ 288+Cursor.stateCount k; omega
    omega) t le_rfl
  refine ⟨t,ht,?_,negative⟩
  have eq:=congrArg Config.state (tx.trans (oldTx t le_rfl))
  exact eq.trans (congrArg (VirtualLeaf.embed k) done)
end CanonicalLeaf
