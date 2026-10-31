import VirtualLeaf.Body
import Complexity.PrivateInterfaceLookupResolvedLeaf
namespace VirtualLeaf
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
run_cmd do
  let rows := [("Transport","first_ready"),("Transport","transport"),("Transport","avoids"),
      ("Transport","entry_val"),("Body","extra_ne"),("Source","virtual_source")]
  let validated ← ofExcept (PartAPrivateLeaf.batch (← getEnv) (rows.map fun (m,s) => (PartAPrivateLeaf.key ("VirtualLeaf."++m), PartAPrivateLeaf.key ("VirtualLeaf."++s))))
  for ((m,s),target) in rows.zip validated do
    let _ := m
    let ns := [target]
    logInfo m!"private-term|{ns.head!}"
    modifyScope fun st => {st with openDecls:=.explicit ((s.splitOn ".").foldl Name.str Name.anonymous) ns.head! :: st.openDecls}
private theorem width {k a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true) {pr : AcceptedBody.Parsed k}
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr) : pr.2.n ≤ a+m := by
  obtain ⟨pr',hp,table,_rest⟩:=AllArityWorkspace.accepted_raw k x w accepted
  have same : pr'=pr := Option.some.inj (hp.symm.trans parsed)
  cases same
  have lt:=Nat.lt_two_pow_self (n:=pr.2.n); change 2^pr.2.n ≤ a+m at table; omega
private theorem price (R k n t s : Nat) (hn : n ≤ R) (hs : s ≤ t)
    (ht : t ≤ 2147483648*(k+1)*(R+1)^5) : s+(2*n+5) ≤ 4294967296*(k+1)*(R+1)^5 := by
  have p : R+1 ≤ (R+1)^5 := by nlinarith only [Nat.zero_le R,Nat.zero_le (R^2),Nat.zero_le (R^3),Nat.zero_le (R^4),Nat.zero_le (R^5)]
  have q:=Nat.mul_le_mul_left ((R+1)^5) (show 1 ≤ k+1 by omega)
  nlinarith only [p,q,hn,hs,ht,Nat.zero_le ((k+1)*(R+1)^5)]
private theorem widen (R k t : Nat) (h : t ≤ 2147483648*(k+1)*(R+1)^5) : t ≤ 4294967296*(k+1)*(R+1)^5 := by
  nlinarith only [h,Nat.zero_le ((k+1)*(R+1)^5)]
private theorem distinct (k i : Nat) (hi : i < Cursor.stateCount k) (different : i ≠ 936+93*k) :
    IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k i) ≠ entry k := by
  intro bad; have e:=congrArg Fin.val bad
  change 288+i%Cursor.stateCount k=(entry k).val at e
  rw [entry_val,Nat.mod_eq_of_lt hi] at e; omega
private theorem image_before (V : Nat → Option Bool) (k S n z F i : Nat)
    (before : i ≤ F) (logical : S ≤ Cursor.Target.M k n z) : Cursor.Target.image V k S n z F i=V i := by
  dsimp only [Cursor.Target.image]
  rw [if_neg (by omega)]
  split_ifs
  · dsimp only [Cursor.Target.scratch]; rw [if_neg (by omega)]
  · rfl
/-- All accepted virtual families execute one real leaf; normal first-W/q613 is preserved. -/
theorem accepted_leaf (k : Nat) : Target.Raw k := by
  intro a m x w accepted
  obtain ⟨pr,parsed,z,hH,gamma,eof,physical⟩:=RawPrelude.accepted_prelude k x w accepted
  let S:=a+m; let R:=pairLength a m; let B:=FixedRawLengthFence.allocation R
  let n:=pr.2.n; let L:=S+z+2; let F:=FixedRawLengthFence.fencePos R
  let p:=min (9+2*z+2^n) S; let r:=S-p
  let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
  let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
  let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
  let Y:=RuntimeBitLength.Target.fullImage X L n F r
  let Z:=AllArityBitLength.Target.seedImage Y F r n
  let c:=initialConfig (machine k) B (encodePair x w)
  let old:=initialConfig (IngressRepair.machine k) B (encodePair x w)
  let H : Fin (tapeLength R B):=⟨S+z+n+3,hH⟩
  let deliver (T : Nat → Option Bool) : Prop :=
    ∃ positive : 0 < n, S ≤ Cursor.Target.M k n z ∧
    (∀ j : Fin (Cursor.Target.W k n), padRead (Fin.append x w) (Cursor.Target.M k n z+j.val)=false) ∧
    (treeCircuitWitnessCodec (thresholdPoly k)).decode n (fun _ => false)=some (Pnp3.Models.Circuit.input ⟨0,positive⟩) ∧
    ∃ t s, s ≤ t ∧ t ≤ 2147483648*(k+1)*(R+1)^5 ∧
    (IngressRepair.machine k).run t old=⟨entry k,H,fun i => T i.val⟩ ∧
    (IngressRepair.machine k).run s old=⟨entry k,H,fun i => T i.val⟩ ∧
    (∀ u, u < s → ((IngressRepair.machine k).run u old).state ≠ entry k) ∧
    (machine k).run s c=⟨embed k (entry k),H,fun i => T i.val⟩ ∧
    s+(2*n+5) ≤ 4294967296*(k+1)*(R+1)^5 ∧
    (machine k).run (s+(2*n+5)) c=⟨result k false,H,Function.update (fun i => T i.val) H (some false)⟩ ∧
    (∀ u, u ≤ s+(2*n+5) → ((machine k).run u c).state ≠ (machine k).accept ∧ ((machine k).run u c).state ≠ (machine k).reject)
  have wn : n ≤ S:=width x w accepted parsed
  have sr : S ≤ R:=by dsimp only [S,R,pairLength]; omega
  have nr : n ≤ R:=wn.trans sr
  have Hv : L+n+1=S+z+n+3 := by dsimp only [L]; omega
  fromDonor "VirtualReady.Raw" "VirtualReady" "actual_base" =>
    obtain ⟨base,_fresh⟩:=OLD (n:=n) x w gamma
      (AcceptedBody.strict_capacity x w gamma wn) (Stream.accepted_rows_fit k x w accepted parsed gamma)
  fromDonor "VirtualReady.Raw" "VirtualReady" "Base.arena" => have arena:=OLD base
  fromDonor "VirtualReady.Raw" "VirtualReady" "Base.sep" => have sep:=OLD base
  fromDonor "VirtualReady.Raw" "VirtualReady" "Base.right" => have last:=OLD base
  change S+z+n+3+2^n < F at arena
  change V L=none at sep
  change V (S+z+n+3)=none at last
  have room : S+z+n+3 < F := (Nat.le_add_right _ _).trans_lt arena
  have assn (i : Nat) (lo : L < i) (hi : i < L+n+1) : V i=some false := by
    dsimp only [V,Stream.Target.image]
    rw [if_pos ⟨lo,hi⟩,CappedWorkspace.overflow_bits]
    simp [List.getElem!_eq_getElem?_getD,List.getElem?_replicate]; split_ifs <;> rfl
  have close (T : Nat → Option Bool) (logical : S ≤ Cursor.Target.M k n z)
      (shape : T=V ∨ T=Cursor.Target.image V k S n z F) (t : Nat)
      (ht : t ≤ 2147483648*(k+1)*(R+1)^5)
      (run : (IngressRepair.machine k).run t old=⟨entry k,H,fun i => T i.val⟩) : deliver T := by
    obtain ⟨positive,zeros⟩:=virtual_source x w accepted parsed z gamma logical
    have point (i : Nat) (hi : i ≤ S+z+n+3) : T i=V i := by
      rcases shape with eq | eq
      · rw [eq]
      · rw [eq]; exact image_before V k S n z F i (hi.trans (Nat.le_of_lt room)) logical
    have tf : T L=none := (point L (by dsimp [L]; omega)).trans sep
    have th : T (S+z+n+3)=none := (point _ le_rfl).trans last
    have td (j : Fin n) : T (L+j.val+1)=some false := by rw [point _ (by dsimp [L]; omega)]; exact assn _ (by omega) (by omega)
    obtain ⟨s,hs,same,first⟩:=first_ready old (congrArg Config.state run)
    have start : (IngressRepair.machine k).run s old=⟨entry k,H,fun i => T i.val⟩:=same.trans run
    have pre : (machine k).run s c=⟨embed k (entry k),H,fun i => T i.val⟩ := by
      have eq:=transport old first s le_rfl
      rw [start] at eq; exact eq
    obtain ⟨body,_footprint,_safe,_semantic⟩:=prepared k L n (fun _ => false) (fun i : Fin (tapeLength R B) => T i.val)
      (by rw [Hv]; exact hH) tf (by simpa only [Hv] using th) td
    have done : (machine k).run (s+(2*n+5)) c=⟨result k false,H,Function.update (fun i => T i.val) H (some false)⟩ := by
      rw [UniformTM.run_add,pre]
      simpa [Hv,positive,show n ≠ 0 by omega] using body
    have safe:= (machine k).no_terminal_of_le c
      (by rw [done]; exact (extra_ne k ⟨6,by decide⟩).1)
      (by rw [done]; exact (extra_ne k ⟨6,by decide⟩).2)
    exact ⟨positive,logical,zeros,((decode_leaf k n (fun _ => false)).2.2 positive).1,t,s,hs,ht,run,start,first,pre,
      price R k n t s nr hs ht,done,safe⟩
  have repaired (t : Nat) := IngressRepair.accepted_transport k x w accepted t
  refine ⟨pr,parsed,z,hH,gamma,?_,?_⟩
  · intro atEOF
    obtain ⟨t,ht,logical,run,_safe⟩:=eof atEOF
    exact close V logical (Or.inl rfl) t ht (by rw [repaired]; exact run)
  · intro phys
    obtain ⟨fit,outcome⟩:=physical phys
    change F+5*r+n+7 < tapeLength R B at fit
    refine ⟨fit,?_⟩
    rcases outcome with ⟨over,logical,t,_ht,_entry,ht,run,_safe⟩ | ⟨fits,tail⟩
    · exact Or.inl ⟨over,logical,close _ (Nat.le_of_lt logical) (Or.inr rfl) _ ht (by rw [repaired]; exact run)⟩
    · refine Or.inr ⟨fits,?_⟩
      rcases tail with ⟨wr,t,d,ht,hd,firstRun,first,total,normal,_safe⟩ |
        ⟨v2,v3,v4,v5,dd,cap,logical,t,_ht,_entry,_first,total,run,_safe⟩
      · have endRun : (IngressRepair.machine k).run (t+d) old=IngressRepair.producer.seqEmbedRight (Cursor.machine k)
            ⟨Cursor.q k (613+93*k),⟨F+1,lt_of_le_of_lt (by omega : F+1 ≤ F+5*r+n+7) fit⟩,
              fun i => CappedWeight.Target.image Z L n F r (bitLength (Cursor.Target.W k n)) 0 0 (Cursor.Target.W k n) 0 i.val⟩ := by rw [repaired]; exact normal
        have noReady := avoids old (by rw [endRun]; exact distinct k (613+93*k) (by unfold Cursor.stateCount; omega) (by omega))
        have tx (u : Nat) (hu : u ≤ t+d) : (machine k).run u c=config k ((IngressRepair.machine k).run u old) :=
          transport old (t:=t+d) (fun u hu => noReady u (by omega)) u hu
        refine Or.inl ⟨wr,t,d,ht,hd,widen R k _ total,?_,?_,?_⟩
        · rw [tx t (by omega),repaired]; exact congrArg (config k) firstRun
        · intro u hu bad
          rw [tx u (by omega)] at bad
          change embed k ((IngressRepair.machine k).run u old).state=embed k _ at bad
          have eq:=(table_delta k).1 bad
          rw [repaired] at eq
          exact first u hu eq
        · rw [tx (t+d) le_rfl,endRun]
      · exact Or.inr ⟨v2,v3,v4,v5,dd,cap,logical,
          close _ (Nat.le_of_lt logical) (Or.inr rfl) _ total (by rw [repaired]; exact run)⟩
/-- Reviewed repaired rejection domain survives the extension, on the same raw tape. -/
theorem missing_payload (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m) (z : Nat)
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (pos : 0 < z) (short : a+m=9+z) :
    ∃ t, t ≤ 128*(pairLength a m+1)^2 ∧
      ((machine k).run t (initialConfig (machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=(machine k).reject ∧
      PartAEndpoint.thresholdContentWitnessRelation k a m x w=false := by
  obtain ⟨t,ht,done,prior,_safe,negative⟩:=IngressRepair.absent_first_payload k x w z tag gamma pos short
  let old:=initialConfig (IngressRepair.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
  have safe (u : Nat) (hu : u < t) : ((IngressRepair.machine k).run u old).state ≠ entry k := by
    intro bad
    have bound:=prior u hu
    have eq:=congrArg Fin.val bad
    rw [entry_val] at eq
    change ((IngressRepair.machine k).run u old).state.val < 139 at bound
    omega
  have tx:=transport old safe t le_rfl
  refine ⟨t,ht,?_,negative⟩
  have states:=congrArg Config.state tx
  exact states.trans (congrArg (embed k) done)
end VirtualLeaf
