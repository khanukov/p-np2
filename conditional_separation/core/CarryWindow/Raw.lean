import CarryWindow.Body
import CanonicalLeaf.Fixtures
import Complexity.PrivateInterfaceLookupResolvedCarryWindow
namespace CarryWindow
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
run_cmd do
  let rows := [("CarryWindow.Body","CarryWindow","carry","carry"),
      ("CarryWindow.Geometry","CarryWindow","Banks","Banks"),
      ("CarryWindow.Geometry","CarryWindow","Banks.mk","BanksMk"),
      ("CarryWindow.Geometry","CarryWindow","A","A"),("CarryWindow.Geometry","CarryWindow","D","D"),
      ("CarryWindow.Body","CarryWindow","code0","code0"),
      ("CarryWindow.Body","CarryWindow","deadBase","deadBase"),
      ("CarryWindow.Body","CarryWindow","actual_row","actual_row"),
      ("CarryWindow.Body","CarryWindow","base_dead","base_dead"),
      ("CarryWindow.Body","CarryWindow","shift_dest","shift_dest"),
      ("CarryWindow.Body","CarryWindow","action","action"),

      ("VirtualLeaf.Body","VirtualLeaf","Trace.run","trRun"),
      ("VirtualLeaf.Body","VirtualLeaf","Trace.bound","trBound"),
      ("VirtualLeaf.Transport","VirtualLeaf","entry_val","entry_val"),
      ("CarryWindow.Transport","CarryWindow","transport","newTransport")]
  let validated ← ofExcept (PartAPrivateCarryWindow.batch (← getEnv) (rows.map fun (o,ns,key,_) => (PartAPrivateCarryWindow.key o, PartAPrivateCarryWindow.key (ns++"."++key))))
  for ((mod,ns,key,localName),target) in rows.zip validated do
    let _ := (mod,ns,key)
    let names := [target]
    logInfo m!"private-term|{names.head!}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str Name.anonymous localName) names.head! :: st.openDecls}
private def cq (k i : Nat) := VirtualLeaf.embed k (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k i))
private theorem cqval (k i : Nat) (hi : i < Cursor.stateCount k) : (cq k i).val=288+i := by
  change 288+i%Cursor.stateCount k=288+i
  rw [Nat.mod_eq_of_lt hi]
private def Closed (k : Nat) (s : Fin (CanonicalLeaf.machine k).stateCount) : Prop :=
  s=(CanonicalLeaf.machine k).reject ∨ (IngressRepair.machine k).stateCount ≤ s.val ∨
    ∃ i, deadBase i=true ∧ s=cq k (i+93*k)
private theorem dead_limits (i : Nat) (h : deadBase i=true) : 330 ≤ i ∧ i<937 ∧ i≠430 ∧ i≠613 := by
  dsimp only [deadBase] at h; have h:=of_decide_eq_true h; omega
private theorem closed_ne (k : Nat) (s : Fin (CanonicalLeaf.machine k).stateCount) (h : Closed k s) :
    s≠cq k (430+93*k) ∧ s≠cq k (613+93*k) := by
  rcases h with h | h | ⟨i,di,eq⟩
  · subst s; constructor
    all_goals intro bad; have e:=congrArg Fin.val bad
    all_goals rw [cqval k _ (by unfold Cursor.stateCount; omega)] at e
    all_goals change 328=_ at e; omega
  · constructor
    all_goals intro bad; rw [bad,cqval k _ (by unfold Cursor.stateCount; omega)] at h
    all_goals change 288+Cursor.stateCount k≤_ at h; unfold Cursor.stateCount at h; omega
  · rw [eq]; have lim:=dead_limits i di
    constructor
    all_goals intro bad; have e:=congrArg Fin.val bad
    all_goals rw [cqval k _ (by unfold Cursor.stateCount; omega),cqval k _ (by unfold Cursor.stateCount; omega)] at e
    all_goals omega
private theorem closed_step (k : Nat) (s : Fin (CanonicalLeaf.machine k).stateCount) (b : Option Bool)
    (h : Closed k s) : Closed k ((CanonicalLeaf.machine k).step s b).1 := by
  rcases h with eq | high | ⟨i,di,eq⟩
  · rw [eq,UniformTM.step_reject]; exact Or.inl rfl
  · rw [CanonicalLeaf.table_delta]
    cases b with
    | none =>
      fromDonor "CanonicalLeaf.Rows" "CanonicalLeaf" "region_step" =>
        rcases OLD k s none (Or.inl high) with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
    | some b =>
      dsimp only
      by_cases e : s=VirtualLeaf.extra k ⟨2,by decide⟩
      · rw [if_pos e]; exact Or.inr (Or.inl (by cases b <;> change _ ≤ (IngressRepair.machine k).stateCount+_ <;> omega))
      · rw [if_neg e]
        fromDonor "CanonicalLeaf.Rows" "CanonicalLeaf" "region_step" =>
          rcases OLD k s (some b) (Or.inl high) with h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
  · rw [eq]; dsimp only [cq]; rw [CanonicalLeaf.repaired_rows]
    have lim:=dead_limits i di
    by_cases entry : i=936
    · subst i
      cases b with
      | none => rw [if_pos (by exact ⟨Fin.ext (by rw [entry_val]; change 288+(936+93*k)%Cursor.stateCount k=1224+93*k; rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)]; omega),rfl⟩)]; exact Or.inr (Or.inl (by change _≤(IngressRepair.machine k).stateCount+0; omega))
      | some b =>
        rw [if_neg (by intro h; cases h.2)]
        change Closed k (VirtualLeaf.embed k ((IngressRepair.producer.seq (Cursor.machine k)).step _ _).1)
        rw [UniformTM.seq_step_right,actual_row k 936 (some b) (by omega) (by omega)]
        have dest : code0 936 (some b)/9=936 := by cases b <;> decide
        dsimp only [action]; rw [shift_dest,dest,if_neg (by decide)]
        exact Or.inr (Or.inr ⟨936,by decide,rfl⟩)
    · rw [if_neg (by intro h; have e:=congrArg Fin.val h.1; rw [entry_val] at e; change 288+(i+93*k)%Cursor.stateCount k=1224+93*k at e; rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)] at e; omega)]
      change Closed k (VirtualLeaf.embed k ((IngressRepair.producer.seq (Cursor.machine k)).step _ _).1)
      rw [UniformTM.seq_step_right,actual_row k i b lim.1 lim.2.1]
      dsimp only [action]; rw [shift_dest]
      rcases base_dead i b lim.1 lim.2.1 di with reject | dead
      · rw [if_pos reject]; exact Or.inl rfl
      · have dst:=dead_limits (code0 i b/9) dead
        rw [if_neg (by omega)]
        exact Or.inr (Or.inr ⟨_,dead,rfl⟩)
private theorem closed_run {k N B : Nat} (c : Config (CanonicalLeaf.machine k).stateCount N B)
    (h : Closed k c.state) (t : Nat) : Closed k ((CanonicalLeaf.machine k).run t c).state := by
  induction t with
  | zero => rw [UniformTM.run]; exact h
  | succ t ih => rw [UniformTM.run]; exact closed_step k _ _ ih
private theorem after613 (k : Nat) (b : Option Bool) :
    Closed k ((CanonicalLeaf.machine k).step (cq k (613+93*k)) b).1 := by
  dsimp only [cq]
  rw [CanonicalLeaf.repaired_rows,if_neg (by intro h; have e:=congrArg Fin.val h.1; rw [entry_val] at e; change 288+(613+93*k)%Cursor.stateCount k=1224+93*k at e; rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)] at e; omega)]
  change Closed k (VirtualLeaf.embed k ((IngressRepair.producer.seq (Cursor.machine k)).step _ _).1)
  rw [UniformTM.seq_step_right,actual_row k 613 b (by omega) (by omega)]
  have dst : code0 613 b/9=614 := by cases b with | none => decide | some b => cases b <;> decide
  dsimp only [action]; rw [shift_dest,dst,if_neg (by decide)]
  exact Or.inr (Or.inr ⟨614,by decide,rfl⟩)
private theorem prefix430 {k N B t : Nat} (c : Config (CanonicalLeaf.machine k).stateCount N B)
    (last : ((CanonicalLeaf.machine k).run t c).state=cq k (430+93*k))
    (first : ∀ u, u<t → ((CanonicalLeaf.machine k).run u c).state≠cq k (430+93*k)) :
    ∀ u, u<t → ((CanonicalLeaf.machine k).run u c).state≠cq k (430+93*k) ∧
      ((CanonicalLeaf.machine k).run u c).state≠cq k (613+93*k) := by
  intro u hu; refine ⟨first u hu,?_⟩
  intro bad
  have start : Closed k ((CanonicalLeaf.machine k).run (u+1) c).state := by
    rw [UniformTM.run]; change Closed k ((CanonicalLeaf.machine k).step _ _).1; rw [bad]; exact after613 k _
  have endState:=closed_run ((CanonicalLeaf.machine k).run (u+1) c) start (t-(u+1))
  rw [← UniformTM.run_add,show u+1+(t-(u+1))=t by omega] at endState
  exact (closed_ne k _ endState).1 last
private theorem carry_price (R n r g : Nat) (hn : n≤R) (hr : r≤R) (hg : g≤r) :
    g*(2*g+4*r+2*n+11)+4*r+2*n+10≤1048576*(R+1)^3 := by
  have m:=Nat.mul_le_mul hg (show 2*g+4*r+2*n+11≤8*R+11 by omega)
  have m':=Nat.mul_le_mul_right (8*R+11) hr
  nlinarith only [m,m',hn,hr,Nat.zero_le (R^3),Nat.zero_le (R^2),Nat.zero_le R]
private theorem normalFrame (V : Nat → Option Bool) (L n F r g W : Nat)
    (room : L+n+1<F) (rp : 0<r)
    (fresh : ∀ i, F < i → i ≤ F+5*r+n+7 → V i=none) :
    let Z:=AllArityBitLength.Target.seedImage (RuntimeBitLength.Target.fullImage
      (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r) F r n
    let T:=CappedWeight.Target.image Z L n F r 0 g W 0 0
    Banks T F r n ∧ T=A T F r n W r g := by
  intro Z T
  have blank (j : Nat) (hj : j≤6) : Z (D F r n j)=none := by
    fromDonor "PostWeight.Raw" "PostWeight" "seed_blank" => exact OLD V L n F r room rp fresh j hj
  have fr : Banks T F r n := by
    apply BanksMk
    · intro j hj
      have old:=blank j hj
      interval_cases j
      all_goals dsimp only [T,CappedWeight.Target.image,D] at old ⊢
      all_goals repeat' rw [if_neg (by omega)]
      all_goals exact old
    · intro i lo hi
      have old : T i=Z i := by
        dsimp only [D] at lo hi
        dsimp only [T,CappedWeight.Target.image]
        repeat' rw [if_neg (by omega)]
      rw [old]
      fromDonor "PostWeight.Raw" "PostWeight" "seed_occupied" => exact OLD V L n F r i (Or.inr ⟨lo,hi⟩)
  have shape : T=A T F r n W r g := by
    funext i
    by_cases bank0 : (F+1 < i ∧ i < F+r+2)
    · have b0 : Z i=some true := by
        dsimp only [Z,AllArityBitLength.Target.seedImage,RuntimeBitLength.Target.fullImage,CappedWorkspace.Target.image,SuffixCap.Target.image]
        rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),
          if_neg (by omega),if_neg (by omega),if_pos (by omega)]
      dsimp only [A,Target.image,D]
      rw [if_pos bank0,decide_eq_true (by omega)]
      dsimp only [T,CappedWeight.Target.image]
      repeat' rw [if_neg (by omega)]
      exact b0
    · dsimp only [A,Target.image,T,CappedWeight.Target.image]
      rw [if_neg bank0]
      split_ifs <;> first | rfl | (exfalso; omega)
  exact ⟨fr,shape⟩
private theorem lift430 {k N B t : Nat} (c : Config (CanonicalLeaf.machine k).stateCount N B)
    (last : ((CanonicalLeaf.machine k).run t c).state=cq k (430+93*k))
    (first : ∀ u, u<t → ((CanonicalLeaf.machine k).run u c).state≠cq k (430+93*k)) :
    (∀ u, u≤t → (machine k).run u (config k c)=config k ((CanonicalLeaf.machine k).run u c)) ∧
    (∀ u, u<t → ((machine k).run u (config k c)).state≠embed k (cq k (430+93*k))) := by
  have tx:=newTransport c (prefix430 c last first)
  refine ⟨tx,?_⟩
  intro u hu bad
  have st:=congrArg Config.state (tx u (by omega))
  change ((machine k).run u (config k c)).state=embed k ((CanonicalLeaf.machine k).run u c).state at st
  exact first u hu ((controls k).2.2.2.2 (st.symm.trans bad))
private theorem work_safe {k N B t : Nat} (c : Config (machine k).stateCount N B)
    (last : ((machine k).run t c).state=extra k ⟨23,by decide⟩) :
    ∀ u, u≤t → ((machine k).run u c).state≠(machine k).accept ∧
      ((machine k).run u c).state≠(machine k).reject := by
  have count : (CanonicalLeaf.machine k).stateCount=1233+93*k := by
    change 288+Cursor.stateCount k+8=1233+93*k
    unfold Cursor.stateCount; omega
  apply (machine k).no_terminal_of_le c
  all_goals intro bad; rw [last] at bad; have e:=congrArg Fin.val bad
  all_goals change (CanonicalLeaf.machine k).stateCount+23=_ at e
  all_goals first | change _=327 at e | change _=328 at e
  all_goals rw [count] at e; omega
/-- Executed carry component, arbitrary exterior/assignment; this ends before native bitLength(W). -/
theorem prepared_carry (k N B F r n g W : Nat) (T : Nat → Option Bool) (gr : g≤r)
    (blanks : ∀ j, j≤6 → T (match j with
      | 0 => F+1 | 1 => F+r+2 | 2 => F+r+n+3 | 3 => F+2*r+n+4
      | 4 => F+3*r+n+5 | 5 => F+4*r+n+6 | _ => F+5*r+n+7)=none)
    (bank1 : ∀ i, F+r+2 < i → i < F+r+n+3 → ∃ b, T i=some b)
    (fit : F+5*r+n+7<tapeLength N B) :
    let d:=g*(2*g+4*r+2*n+11)+4*r+2*n+10
    let c : Config (machine k).stateCount N B :=
      ⟨embed k (VirtualLeaf.embed k (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k (430+93*k)))),
        ⟨F+r+n+3,by omega⟩,fun i => Target.image T F r n r 0 g W 0 i.val⟩
    (machine k).run d c=⟨extra k ⟨23,by decide⟩,⟨F+r+n+3,by omega⟩,
      fun i => Target.image T F r n g 0 0 W 0 i.val⟩ ∧
    (∀ u, u≤d → F+1≤((machine k).run u c).head.val ∧ ((machine k).run u c).head.val≤F+5*r+n+7) ∧
    (∀ u, u≤d → ((machine k).run u c).state≠(machine k).accept ∧ ((machine k).run u c).state≠(machine k).reject) := by
  have fr : Banks T F r n := BanksMk blanks bank1
  have path:=carry (k:=k) (N:=N) (B:=B) fr W g gr fit
  exact ⟨trRun path,trBound path,work_safe _ (congrArg Config.state (trRun path))⟩
/-- Partial connected milestone; not CarryReady, not the frozen Body/Raw target. -/
theorem raw_carry (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true) :
    ∃ pr : (Sigma fun q : Nat => PrefixInput
      (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
      (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) q)),
    contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr ∧
    ∃ (z : Nat) (hH : a+m+z+pr.2.n+3 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
    FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
    let S:=a+m; let R:=pairLength a m; let B:=FixedRawLengthFence.allocation R
    let n:=pr.2.n; let L:=S+z+2; let F:=FixedRawLengthFence.fencePos R
    let p:=min (9+2*z+2^n) S; let r:=S-p
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
    let Y:=RuntimeBitLength.Target.fullImage X L n F r
    let Z:=AllArityBitLength.Target.seedImage Y F r n
    let T:=CappedWeight.Target.image Z L n F r 0 (n^k+k) (Cursor.Target.W k n) 0 0
    let c:=initialConfig (machine k) B (encodePair x w)
    p<S → bitLength n≤r → Cursor.Target.W k n≤r →
    ∃ (fit : F+5*r+n+7 < tapeLength R B) (t : Nat),
      t≤268435456*(k+1)*(R+1)^4 ∧
      let g:=n^k+k; let W:=Cursor.Target.W k n
      let d:=g*(2*g+4*r+2*n+11)+4*r+2*n+10
      d≤1048576*(R+1)^3 ∧
      (machine k).run t c=config k (VirtualLeaf.config k (IngressRepair.producer.seqEmbedRight (Cursor.machine k)
        ⟨Cursor.q k (430+93*k),⟨F+r+n+3,lt_of_le_of_lt (by omega : F+r+n+3≤F+5*r+n+7) fit⟩,fun i => T i.val⟩)) ∧
      (∀ u, u<t → ((machine k).run u c).state≠embed k (VirtualLeaf.embed k
        (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k (430+93*k))))) ∧
      (machine k).run (t+d) c=⟨extra k ⟨23,by decide⟩,⟨F+r+n+3,lt_of_le_of_lt (by omega : F+r+n+3≤F+5*r+n+7) fit⟩,
        fun i => Target.image T F r n g 0 0 W 0 i.val⟩ ∧
      (∀ u, u≤t+d → ((machine k).run u c).state≠(machine k).accept ∧
        ((machine k).run u c).state≠(machine k).reject)
    := by
  obtain ⟨pr,parsed,z,hH,gamma,_eof,physical⟩:=CanonicalLeaf.accepted_leaf k x w accepted
  let S:=a+m; let R:=pairLength a m; let B:=FixedRawLengthFence.allocation R
  let n:=pr.2.n; let L:=S+z+2; let F:=FixedRawLengthFence.fencePos R
  let p:=min (9+2*z+2^n) S; let r:=S-p
  let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
  let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
  let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
  let Y:=RuntimeBitLength.Target.fullImage X L n F r
  let Z:=AllArityBitLength.Target.seedImage Y F r n
  let T:=CappedWeight.Target.image Z L n F r 0 (n^k+k) (Cursor.Target.W k n) 0 0
  let base:=initialConfig (CanonicalLeaf.machine k) B (encodePair x w)
  let c:=initialConfig (machine k) B (encodePair x w)
  refine ⟨pr,parsed,z,hH,gamma,?_⟩
  change p<S → bitLength n≤r → Cursor.Target.W k n≤r → _
  intro phys fits wr
  obtain ⟨fit,outcome⟩:=physical phys
  change F+5*r+n+7<tapeLength R B at fit
  obtain ⟨_fits,tail⟩:=outcome.resolve_left (by rintro ⟨over,_⟩; exact (not_lt_of_ge fits) over)
  obtain ⟨_wr,t,_oldD,ht,_hd,_total,atW,first,_oldEnd⟩:=tail.resolve_right (by
    rintro ⟨v2,v3,v4,v5,d,cap,_⟩
    fromDonor "FullWeight.Raw" "FullWeight" "cap_weight" => have small:=OLD k n r v2 v3 v4 v5 d cap
    exact (not_lt_of_ge wr) small)
  obtain ⟨tx,firstNew⟩:=lift430 base (congrArg Config.state atW) first
  have reached : (machine k).run t c=config k (VirtualLeaf.config k (IngressRepair.producer.seqEmbedRight (Cursor.machine k)
      ⟨Cursor.q k (430+93*k),⟨F+r+n+3,lt_of_le_of_lt (by omega : F+r+n+3≤F+5*r+n+7) fit⟩,fun i => T i.val⟩)) :=
    (tx t le_rfl).trans (congrArg (config k) atW)
  fromDonor "VirtualLeaf.Raw" "VirtualLeaf" "width" => have width:=OLD x w accepted parsed
  have cap:=AcceptedBody.strict_capacity x w gamma width
  have paid:=Stream.accepted_rows_fit k x w accepted parsed gamma
  fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "actual_cells" => obtain ⟨cells,_short,fresh⟩:=OLD x w gamma cap paid
  fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "Cells.arena" => have arena:=OLD cells
  change S+z+n+3+2^n<F at arena
  have Heq : L+n+1=S+z+n+3 := by dsimp only [L]; omega
  have room : L+n+1<F := by rw [Heq]; exact (Nat.le_add_right _ _).trans_lt arena
  have rp : 0<r := Nat.sub_pos_of_lt phys
  have gr : n^k+k≤r := by
    have pos : 1≤bitLength n+4 := by omega
    have mul:=Nat.mul_le_mul_right (n^k+k) pos
    dsimp only [Cursor.Target.W] at wr
    omega
  obtain ⟨fr,shape⟩:=normalFrame V L n F r (n^k+k) (Cursor.Target.W k n) room rp
    (by intro i lo hi; exact fresh ⟨i,lt_of_le_of_lt hi fit⟩ lo)
  have path:=carry (k:=k) (N:=R) (B:=B) fr (Cursor.Target.W k n) (n^k+k) gr fit
  have run:=trRun path
  rw [← shape] at run
  have done : (machine k).run (t+((n^k+k)*(2*(n^k+k)+4*r+2*n+11)+4*r+2*n+10)) c=
      ⟨extra k ⟨23,by decide⟩,⟨F+r+n+3,lt_of_le_of_lt (by omega : F+r+n+3≤F+5*r+n+7) fit⟩,fun i => Target.image T F r n (n^k+k) 0 0 (Cursor.Target.W k n) 0 i.val⟩ := by
    rw [UniformTM.run_add,reached]
    exact run
  have nr : n≤R := by dsimp only [R,pairLength]; change n≤S at width; omega
  have rr : r≤R := by have bound:=Nat.sub_le S p; dsimp only [R,pairLength]; omega
  refine ⟨fit,t,ht,carry_price R n r (n^k+k) nr rr gr,reached,?_,?_,?_⟩
  · exact firstNew
  · exact done
  · exact work_safe c (congrArg Config.state done)
/-- A separately named normal accepted projection: zero-extension of the sealed source fixture. -/
theorem projection_normal_accepted :
    let x : Bitstring 13:=fun i => i.val==0 || i.val==2 || i.val==3 || i.val==6 || i.val==9 || i.val==12
    let w : Bitstring 14:=fun _ => false
    PartAEndpoint.thresholdContentWitnessRelation 0 13 14 x w=true := by
  dsimp only
  let x : Bitstring 13:=fun i => i.val==0 || i.val==2 || i.val==3 || i.val==6 || i.val==9 || i.val==12
  let w : Bitstring 14:=fun _ => false
  let ox : Bitstring 7:=fun i => i.val==0 || i.val==2 || i.val==3 || i.val==6
  let ow : Bitstring 8:=fun i => i.val==2 || i.val==5
  let codec:=treeCircuitWitnessCodec (thresholdPoly 0)
  have base : PartAEndpoint.thresholdContentWitnessRelation 0 7 8 ox ow=true := CanonicalLeaf.tiny_accepted
  have oldSemantic : contentSemanticAccepts codec (Fin.append ox ow)=true := by
    unfold PartAEndpoint.thresholdContentWitnessRelation PartAEndpoint.contentWitnessRelation at base
    split at base
    · rename_i shape; cases shape; simpa only [AcceptedBody.concat_eq_append] using base
    · contradiction
  have padding : Fin.append x w=padWord (Fin.append ox ow) 27 := by
    funext ⟨i,hi⟩
    have bound : i<27 := hi
    interval_cases i
    all_goals norm_num [padWord,padRead,Fin.append,Fin.addCases,x,w,ox,ow]
    all_goals rfl
  have semantic : contentSemanticAccepts codec (Fin.append x w)=true := by
    rw [padding,contentSemanticAccepts_padWord_of_le codec (Fin.append ox ow) (by decide)]
    exact oldSemantic
  unfold PartAEndpoint.thresholdContentWitnessRelation PartAEndpoint.contentWitnessRelation
  split
  · simpa only [AcceptedBody.concat_eq_append] using semantic
  · rename_i guard; exact (guard (by norm_num [Pnp3.ComplexityInterfaces.certificateLength])).elim
/-- The literal repaired bad word, uniformly in k. -/
theorem stall_reject (k : Nat) :
    let x : Bitstring 11:=fun i => i.val==0 || i.val==2 || i.val==3 || i.val==6 || i.val==10
    let w : Bitstring 0:=Fin.elim0
    ∃ t, t≤128*(pairLength 11 0+1)^2 ∧
      ((machine k).run t (initialConfig (machine k) 9216 (encodePair x w))).state=(machine k).reject ∧
      PartAEndpoint.thresholdContentWitnessRelation k 11 0 x w=false := by
  dsimp only
  apply missing_payload k _ _ 2 (by decide) (by decide) (by decide) (by decide)
/-- Kernel same-word nonvacuity at the connected Resume430 boundary, not CarryReady. -/
theorem projection_raw_carry :
    let x : Bitstring 13:=fun i => i.val==0 || i.val==2 || i.val==3 || i.val==6 || i.val==9 || i.val==12
    let w : Bitstring 14:=fun _ => false
    ∃ t, ((machine 0).run t (initialConfig (machine 0) 28224 (encodePair x w))).state=extra 0 ⟨23,by decide⟩ := by
  dsimp only
  let x : Bitstring 13:=fun i => i.val==0 || i.val==2 || i.val==3 || i.val==6 || i.val==9 || i.val==12
  let w : Bitstring 14:=fun _ => false
  obtain ⟨pr,parsed,z,_hH,gamma,physical⟩:=raw_carry 0 x w projection_normal_accepted
  have g : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some 1 := by decide
  have z1 : z=1:=Option.some.inj (gamma.symm.trans g)
  obtain ⟨_consumed,header,target⟩:=contentInput?_target_eq_contentHeader _ _ parsed
  have h : contentHeader? (Fin.append x w)=some (1,3) := by decide
  have n1 : pr.2.n=1:=target.trans (congrArg Prod.fst (Option.some.inj (header.symm.trans h)))
  obtain ⟨_fit,t,_ht,_price,_entry,_first,last,_safe⟩:=physical
    (by rw [z1,n1]; decide) (by rw [z1,n1]; norm_num [bitLength,Nat.log2]) (by rw [z1,n1]; norm_num [Cursor.Target.W,bitLength,Nat.log2])
  exact ⟨_,congrArg Config.state last⟩
end CarryWindow
