import RepairedFrontier.Runtime
namespace RepairedFrontier
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Tactic
set_option maxRecDepth 4000
attribute [local irreducible] UniformTM.run
private theorem stream_bound {N B S z n A F : Nat} (T : Nat → Option Bool)
    (hp : 2 ≤ A) (full : A ≤ S) (room : S+z+n+3 < F) (fit : F < tapeLength N B)
    (source : ∀ i, A ≤ i → i < S → ∃ b, T i=some b) (eof : T S=none)
    (reg : ∀ i, S < i → i < S+z+2 → T i=some false) (sep : T (S+z+2)=none)
    (marks : ∀ i, S+z+2 < i → i < S+z+n+3 → T i=some true)
    (right : T (S+z+n+3)=none) (scratch : ∀ i, S+z+n+3 < i → i < F → T i=none)
    (fence : T F=some false) (hole : T (A-2)=none) (marker : T (A-1)=some true)
    (hL : S+z+2 < tapeLength N B) :
    ∃ tb, tb ≤ n+2+InputRead.readClock n z (S-A)+64*(F+1)^2 ∧
      let c : Config Stream.machine.stateCount N B := ⟨Stream.machine.start,⟨S+z+2,hL⟩,fun i => T i.val⟩
      (Stream.machine.run tb c).state=Stream.machine.reject ∨
      (Stream.machine.run tb c).state=Stream.q 57 ∨ (Stream.machine.run tb c).state=Stream.q 58 := by
  run_tac do
    let env ← getEnv
    let mut mapping := []
    for key in ["Frame","Frame.mk","install_read"] do
      let ns := env.constants.toList.map Prod.fst |>.filter fun n =>
        n.toString.startsWith "_private.SmallOrbit.Runtime." && n.toString.endsWith (".SmallOrbit."++key)
      unless ns.length==1 do throwError "Ambiguous body API {key}: {ns}"
      mapping := mapping++[("OLD_"++key.replace "." "_",ns.head!)]
    let ast ← ofExcept (Parser.runParserCategory env `tactic "(
      let frame : OLD_Frame T S z n A F := @OLD_Frame_mk T S z n A F ⟨hp,full⟩ room source eof reg sep marks right scratch fence hole marker
      let U := Body.clear T (S+z+3) n
      have low (i : Nat) (hi : i ≤ S+z+2) : U i=T i := by
        unfold U Body.clear; rw [if_neg (by omega)]
      have high (i : Nat) (hi : S+z+n+3 ≤ i) : U i=T i := by
        unfold U Body.clear; rw [if_neg (by omega)]
      have hH : S+z+n+3 < tapeLength N B := room.trans fit
      obtain ⟨tb,price,_paid,finish⟩ := Stream.kernel N B S z n A F U hp full room fit
        (by intro i lo hi; rw [low i (by omega)]; exact source i lo hi)
        (by rw [low S (by omega)]; exact eof)
        (by intro i lo hi; rw [low i (by omega)]; exact reg i lo hi)
        (by rw [low _ le_rfl]; exact sep)
        (by rw [high _ le_rfl]; exact right)
        (by intro i lo hi; rw [high i (by omega)]; exact scratch i lo hi)
        (by rw [high F (by omega)]; exact fence) hH
      have pre := OLD_install_read T frame fit hL
      refine ⟨n+2+InputRead.readClock n z (S-A)+tb,by omega,?_⟩
      dsimp only
      rw [Stream.machine.run_add,pre]
      by_cases fits : 2^n ≤ F-(S+z+n+3)-1
      · rw [if_pos fits] at finish
        obtain ⟨_hr,done⟩ := finish
        rw [done]
        by_cases last : Stream.Target.cursor A S (2^n)=S
        · right; left; simp only [if_pos last]
        · right; right; simp only [if_neg last]
      · rw [if_neg fits] at finish
        obtain ⟨_hf,done⟩ := finish
        rw [done]
        left; rfl)")
    evalTactic (ast.rewriteBottomUp fun stx =>
      if stx.isIdent then
        match mapping.find? (fun p => p.1==stx.getId.toString) with
        | some (_,n) => mkIdent n
        | none => stx
      else stx)
private theorem phase_price (R n z d t b : Nat) (nn : n ≤ 3*R) (zz : z ≤ R) (dd : d ≤ R)
    (tt : t ≤ 128*(R+1)^2) (bb : b ≤ n+2+InputRead.readClock n z d+64*(3*R+3)^2) :
    t+b ≤ 4096*(R+1)^2 := by
  unfold InputRead.readClock at bb
  nlinarith [Nat.zero_le (R^2)]
private theorem wide_orbit {a m z n : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (wide : 2 ≤ z) (physical : 9+z < a+m) (cap : n < FixedRawLengthFence.capacity a m z)
    (T : Nat) (price : T ≤ 128*(pairLength a m+1)^2)
    (e : Config SmallIngress.producer.stateCount (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)))
    (success : SmallIngress.producer.run T (initialConfig SmallIngress.producer
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))=e)
    (accept : e.state=SmallIngress.producer.accept) (head : e.head.val=a+m+z+2)
    (tape : e.tape=FixedRawLengthFence.countdownTape (FixedRawLengthFence.allocation (pairLength a m)) x w z 0 n) :
    ∃ t, t ≤ 4096*(pairLength a m+1)^2 ∧
      ((SmallIngress.machine.run t (initialConfig SmallIngress.machine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state.val=328 ∨
       (SmallIngress.machine.run t (initialConfig SmallIngress.machine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state.val=345 ∨
       (SmallIngress.machine.run t (initialConfig SmallIngress.machine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state.val=346) := by
  let R := pairLength a m
  let B := FixedRawLengthFence.allocation R
  let S := a+m
  let H := S+z+n+3
  let F := FixedRawLengthFence.fencePos R
  let A := 8+z+FixedGammaTargetPayloadExhaustion.termWalk S z+1
  let U := Body.extend (FixedRawLengthFence.countdownTape B x w z 0 n)
  have resource := (FixedRawLengthFence.resource_bounds R).1
  have cells := FixedRawLengthFence.countdown_success_cells x w gamma resource (Nat.le_of_lt cap)
  obtain ⟨room,scratch,hF,fence⟩ := Stream.raw_budget_cells x w gamma cap
  change H < F at room
  change F < tapeLength R B at hF
  have room' : S+z+n+3 < F := room
  have hF' : F < tapeLength (pairLength a m) B := hF
  have hS : 9+z < S := physical
  have walk : 1 ≤ FixedGammaTargetPayloadExhaustion.termWalk S z := by
    unfold FixedGammaTargetPayloadExhaustion.termWalk FixedGammaTargetPayloadLoopFoundation.walk
    omega
  have aS : A ≤ S := by
    dsimp [A]
    unfold FixedGammaTargetPayloadExhaustion.termWalk FixedGammaTargetPayloadLoopFoundation.walk
    omega
  have hL : S+z+2 < tapeLength R B := by omega
  have read (i : Nat) (hi : i < tapeLength R B) : U i=FixedRawLengthFence.countdownTape B x w z 0 n ⟨i,hi⟩ := by
    have hi' : i < tapeLength (pairLength a m) B := hi
    simp only [U,Body.extend,dif_pos hi']
  have low (i : Nat) (hi : i < S) : U i=FixedGammaTargetPayloadExhaustion.finishTape B x w z ⟨i,by omega⟩ := by
    rw [read i (by omega)]
    exact cells.1 _ hi
  have src (i : Nat) (lo : A ≤ i) (hi : i < S) : ∃ b, U i=some b := by
    have afterHeader : 9+2*z ≤ i := by
      dsimp [A] at lo
      unfold FixedGammaTargetPayloadExhaustion.termWalk FixedGammaTargetPayloadLoopFoundation.walk at lo
      omega
    rw [read i (by omega)]
    exact ⟨_,Body.raw_source_after_header x w gamma resource (Nat.le_of_lt cap) ⟨i,by change i < tapeLength (pairLength a m) B; omega⟩ (by change 8+2*z+1 ≤ i; omega) hi⟩
  have eof : U S=none := by
    rw [read S (by omega)]
    unfold FixedRawLengthFence.countdownTape
    rw [if_neg (by omega : S≠F)]
    simp [FixedGammaTargetUnaryCountdown.loopTape,S]
  have reg (i : Nat) (lo : S < i) (hi : i < S+z+2) : U i=some false := by
    rw [read i (by omega)]
    exact cells.2.1 (i-S-1) (by omega) _ (by dsimp [S]; omega)
  have sep : U (S+z+2)=none := by
    rw [read _ hL]
    exact cells.2.2.1 _ (by dsimp [S]; omega)
  have marks (i : Nat) (lo : S+z+2 < i) (hi : i < H) : U i=some true := by
    rw [read i (by omega)]
    exact cells.2.2.2.1 ⟨i,by change i < tapeLength (pairLength a m) B; omega⟩ (by change a+m+3+z ≤ i; dsimp [S] at lo; omega) (by change i < a+m+3+z+n; dsimp [H,S] at hi; omega)
  have right : U H=none := by rw [read H (room.trans hF)]; exact cells.2.2.2.2.1 _ (by dsimp [H,S]; omega) room
  have fresh (i : Nat) (lo : H < i) (hi : i < F) : U i=none := by
    rw [read i (hi.trans hF)]
    exact cells.2.2.2.2.1 _ (by dsimp [H,S] at lo ⊢; omega) hi
  have last : U F=some false := by rw [read F hF]; exact cells.2.2.2.2.2 _ rfl
  have hole : U (A-2)=none := by
    rw [low _ (by omega)]
    unfold FixedGammaTargetPayloadExhaustion.finishTape
    have hh : 8+z ≤ A-2 ∧ A-2 < 8+z+FixedGammaTargetPayloadExhaustion.termWalk S z := by dsimp [A]; omega
    rw [if_pos hh]
  have marker : U (A-1)=some true := by
    rw [low _ (by omega)]
    unfold FixedGammaTargetPayloadExhaustion.finishTape
    have he : A-1=8+z+FixedGammaTargetPayloadExhaustion.termWalk S z := by dsimp [A]
    rw [if_neg (by change ¬(8+z ≤ A-1 ∧ A-1 < 8+z+FixedGammaTargetPayloadExhaustion.termWalk S z); omega),if_pos he]
  obtain ⟨tb,bprice,body⟩ := stream_bound U (by dsimp [A]; omega) aS room hF src eof reg sep marks right fresh last hole marker hL
  obtain ⟨tp,tpT,first,arrived⟩ := Body.first_accept_whole SmallIngress.producer
    (initialConfig SmallIngress.producer B (encodePair x w)) T e success accept
  have entry : (⟨Stream.machine.start,e.head,e.tape⟩ : Config Stream.machine.stateCount R B)=
      ⟨Stream.machine.start,⟨S+z+2,hL⟩,fun i => U i.val⟩ := by
    refine Config.ext_parts rfl (Fin.ext head) ?_
    funext i
    rw [tape]
    exact (Body.extend_read _ i).symm
  have hand := SmallIngress.producer.seq_handoff Stream.machine
    (initialConfig SmallIngress.producer B (encodePair x w)) first (by rw [arrived]; exact accept) tb
  rw [arrived] at hand
  change SmallIngress.machine.run (tp+tb) (initialConfig SmallIngress.machine B (encodePair x w))=
    SmallIngress.producer.seqEmbedRight Stream.machine (Stream.machine.run tb ⟨Stream.machine.start,e.head,e.tape⟩) at hand
  rw [entry] at hand
  have nR : n ≤ 3*R := by
    dsimp [FixedRawLengthFence.capacity,FixedRawLengthFence.fencePos] at cap
    change n < (3*R+2)-(a+m+3+z) at cap
    omega
  have sR : S ≤ R := by dsimp [S,R,pairLength]; omega
  have zR : z ≤ R := by omega
  have bprice' : tb ≤ n+2+InputRead.readClock n z (S-A)+64*(3*R+3)^2 := by
    simpa only [F,FixedRawLengthFence.fencePos,Nat.add_assoc] using bprice
  have total := phase_price R n z (S-A) tp tb nR zR ((Nat.sub_le _ _).trans sR) (tpT.trans price) bprice'
  dsimp only at body
  refine ⟨tp+tb,total,?_⟩
  rw [hand]
  rcases body with rejected | at57 | at58
  · left; change 288+(Stream.machine.run tb _).state.val=328; rw [rejected]; rfl
  · right; left; change 288+(Stream.machine.run tb _).state.val=345; rw [at57]; rfl
  · right; right; change 288+(Stream.machine.run tb _).state.val=346; rw [at58]; rfl
private theorem installer_rows :
    Stream.machine.step (Stream.q 1) (some true)=(Stream.q 1,some false,.right) ∧
    Stream.machine.step (Stream.q 1) (some false)=(Stream.machine.reject,some false,.stay) ∧
    Stream.machine.step Stream.machine.start none=(Stream.q 1,none,.right) := by decide
private theorem seed_scan {N B : Nat} (T : Nat → Option Bool) (h n : Nat)
    (fit : h+n < tapeLength N B) (marks : ∀ i, h ≤ i → i < h+n → T i=some true) :
    Stream.machine.run n (⟨Stream.q 1,⟨h,by omega⟩,fun i => T i.val⟩ : Config 64 N B)=
      ⟨Stream.q 1,⟨h+n,fit⟩,fun i => Body.clear T h n i.val⟩ := by
  induction n generalizing T h with
  | zero =>
    simp only [UniformTM.run,Nat.add_zero]
    refine Config.ext_parts rfl rfl ?_
    funext i
    simp only [Body.clear,if_neg (by omega : ¬(h ≤ i.val ∧ i.val < h+0))]
  | succ n ih =>
    have hb := marks h le_rfl (by omega)
    let V := Body.put T h (some false)
    have one : Stream.machine.stepConfig (⟨Stream.q 1,⟨h,by omega⟩,fun i => T i.val⟩ : Config 64 N B)=
        ⟨Stream.q 1,⟨h+1,by omega⟩,fun i => V i.val⟩ := by
      refine Config.ext_parts ?_ ?_ ?_
      · change (Stream.machine.step (Stream.q 1) (T h)).1=Stream.q 1
        rw [hb]; exact congrArg Prod.fst installer_rows.1
      · apply Fin.ext
        change (moveHead ⟨h,by omega⟩ (Stream.machine.step (Stream.q 1) (T h)).2.2).val=h+1
        rw [hb,installer_rows.1]; simp only [moveHead,show h+1 < tapeLength N B by omega,↓reduceDIte]
      · funext i
        change (if i=⟨h,by omega⟩ then (Stream.machine.step (Stream.q 1) (T h)).2.1 else T i.val)=V i.val
        rw [hb,installer_rows.1]
        simp only [V,Body.put,Fin.ext_iff]
    have peel : Stream.machine.run (n+1) (⟨Stream.q 1,⟨h,by omega⟩,fun i => T i.val⟩ : Config 64 N B)=
        Stream.machine.run n (Stream.machine.stepConfig ⟨Stream.q 1,⟨h,by omega⟩,fun i => T i.val⟩) := by
      rw [show n+1=1+n by omega,Stream.machine.run_add]
      simp only [UniformTM.run]
    rw [peel,one]
    have rest := ih V (h+1) (by omega) (by
      intro i lo hi
      unfold V Body.put
      rw [if_neg (by omega)]
      exact marks i (by omega) (by omega))
    simpa only [V,Body.clear_step,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using rest
private theorem install_reject {N B L n : Nat} (T : Nat → Option Bool)
    (fit : L+n+1 < tapeLength N B) (blank : T L=none)
    (marks : ∀ i, L < i → i < L+n+1 → T i=some true) (fence : T (L+n+1)=some false) :
    (Stream.machine.run (n+2) (⟨Stream.machine.start,⟨L,by omega⟩,fun i => T i.val⟩ : Config 64 N B)).state=Stream.machine.reject := by
  have one : Stream.machine.stepConfig (⟨Stream.machine.start,⟨L,by omega⟩,fun i => T i.val⟩ : Config 64 N B)=
      ⟨Stream.q 1,⟨L+1,by omega⟩,fun i => T i.val⟩ := by
    refine Config.ext_parts ?_ ?_ ?_
    · change (Stream.machine.step Stream.machine.start (T L)).1=Stream.q 1
      rw [blank]; exact congrArg Prod.fst installer_rows.2.2
    · apply Fin.ext
      change (moveHead ⟨L,by omega⟩ (Stream.machine.step Stream.machine.start (T L)).2.2).val=L+1
      rw [blank,installer_rows.2.2]; simp only [moveHead,show L+1 < tapeLength N B by omega,↓reduceDIte]
    · funext i
      change (if i=⟨L,by omega⟩ then (Stream.machine.step Stream.machine.start (T L)).2.1 else T i.val)=T i.val
      rw [blank,installer_rows.2.2]
      split_ifs with eq
      · subst i; exact blank.symm
      · rfl
  have mid := seed_scan T (L+1) n (by omega : L+1+n < tapeLength N B)
    (by intro i lo hi; exact marks i (by omega) (by omega))
  have runmid : Stream.machine.run (n+1) (⟨Stream.machine.start,⟨L,by omega⟩,fun i => T i.val⟩ : Config 64 N B)=
      ⟨Stream.q 1,⟨L+1+n,by omega⟩,fun i => Body.clear T (L+1) n i.val⟩ := by
    rw [show n+1=1+n by omega,Stream.machine.run_add]
    simp only [UniformTM.run]
    rw [one]
    exact mid
  rw [show n+2=(n+1)+1 by omega,UniformTM.run,runmid]
  change (Stream.machine.step (Stream.q 1) (Body.clear T (L+1) n (L+1+n))).1=Stream.machine.reject
  have cell : Body.clear T (L+1) n (L+1+n)=some false := by
    unfold Body.clear
    rw [if_neg (by omega)]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using fence
  rw [cell,installer_rows.2.1]
private theorem small_orbit {a m : Nat} (x : Bitstring a) (w : Bitstring m) (n : Fin 3)
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some (if n.val=0 then 0 else 1))
    (full : (if n.val=0 then 9 else 11) ≤ a+m)
    (h8 : FixedContentTagGate.physicalSymbol (Fin.append x w) 8=some (n.val==0))
    (h9 : n.val≠0 → FixedContentTagGate.physicalSymbol (Fin.append x w) 9=some true)
    (h10 : n.val≠0 → FixedContentTagGate.physicalSymbol (Fin.append x w) 10=some (n.val==2)) :
    ∃ t, t ≤ 4096*(pairLength a m+1)^2 ∧
      ((SmallIngress.machine.run t (initialConfig SmallIngress.machine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state.val=345 ∨
       (SmallIngress.machine.run t (initialConfig SmallIngress.machine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state.val=346) := by
  run_tac do
    let env ← getEnv
    let mut mapping := []
    for key in ["small_tape_eq","raw_orbit"] do
      let ns := env.constants.toList.map Prod.fst |>.filter fun nm =>
        nm.toString.startsWith "_private.SmallOrbit.Runtime." && nm.toString.endsWith (".SmallOrbit."++key)
      unless ns.length==1 do throwError "Ambiguous small body API {key}: {ns}"
      mapping := mapping++[("OLD_"++key,ns.head!)]
    let ast ← ofExcept (Parser.runParserCategory env `tactic "(
      obtain ⟨tp,hL,price,hand⟩ := SmallIngress.raw_small_physical x w n tag full h8 h9 h10
      have te := OLD_small_tape_eq (B := FixedRawLengthFence.allocation (pairLength a m)) x w n full h8
      rw [te] at hand
      have nn : n.val ≤ 2 := by omega
      have zz : (if n.val=0 then 0 else 1) ≤ 1 := by split_ifs <;> omega
      have ss : 9 ≤ a+m := by split_ifs at full <;> omega
      have cap : n.val < FixedRawLengthFence.capacity a m (if n.val=0 then 0 else 1) := by
        unfold FixedRawLengthFence.capacity FixedRawLengthFence.fencePos pairLength
        omega
      have power : 2^n.val ≤ 4 := by fin_cases n <;> decide
      have rows : 2^n.val ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+(if n.val=0 then 0 else 1)+n.val+3)-1 := by
        unfold FixedRawLengthFence.fencePos pairLength
        omega
      obtain ⟨t,_hH,price',_paid,hp,done⟩ := OLD_raw_orbit x w gamma cap (by split_ifs at full ⊢ <;> omega)
        (by intro h; split_ifs at h <;> omega) rows
        ⟨tp,hL,price.trans (Nat.mul_le_mul_right _ (by decide : 64 ≤ 144)),hand⟩
      refine ⟨t,price',?_⟩
      rw [done]
      by_cases last : Stream.Target.cursor (9+2*(if n.val=0 then 0 else 1)) (a+m) (2^n.val)=a+m
      · simp only [if_pos last]; left; rfl
      · simp only [if_neg last]; right; rfl)")
    evalTactic (ast.rewriteBottomUp fun stx =>
      if stx.isIdent then
        match mapping.find? (fun p => p.1==stx.getId.toString) with
        | some (_,nm) => mkIdent nm
        | none => stx
      else stx)
private theorem live_hit (k : Nat) {N B : Nat} (y : Bitstring N) (T : Nat)
    (hit : (SmallIngress.machine.run T (initialConfig SmallIngress.machine B y)).state.val=328 ∨
      (SmallIngress.machine.run T (initialConfig SmallIngress.machine B y)).state.val=345 ∨
      (SmallIngress.machine.run T (initialConfig SmallIngress.machine B y)).state.val=346) :
    ∃ t, t≤T ∧ (((IngressRepair.machine k).run t (initialConfig (IngressRepair.machine k) B y)).state.val=328 ∨
      ((IngressRepair.machine k).run t (initialConfig (IngressRepair.machine k) B y)).state.val=345 ∨
      ((IngressRepair.machine k).run t (initialConfig (IngressRepair.machine k) B y)).state.val=346) := by
  run_tac do
    let env ← getEnv
    let mut mapping := []
    for key in ["er","exits","old_inert","raw_row","er_initial","map_er"] do
      let ns := env.constants.toList.map Prod.fst |>.filter fun n =>
        n.toString.startsWith "_private.AllArityCursor.Runtime." && n.toString.endsWith (".AllArityCursor."++key)
      unless ns.length==1 do throwError "Ambiguous literal transport API {key}: {ns}"
      mapping := mapping++[("OLD_"++key,ns.head!)]
    let ns := env.constants.toList.map Prod.fst |>.filter fun n =>
      n.toString.startsWith "_private.IngressRepair.Transport." && n.toString.endsWith ".IngressRepair.refinement"
    unless ns.length==1 do throwError "Ambiguous repair refinement API: {ns}"
    mapping := mapping++[("REPAIR",ns.head!)]
    let ast ← ofExcept (Parser.runParserCategory env `tactic "(
      let c := initialConfig SmallIngress.machine B y
      rcases hit with reject | work
      · have old := Cursor.Transport.avoid_changed_rows SmallIngress.machine (AllArityCursor.machine k)
          (OLD_er k) OLD_exits (fun c hc => OLD_old_inert c hc) (OLD_raw_row k) c T
          (by change ¬(_=345 ∨ _=346); rw [reject]; omega)
        rw [OLD_er_initial,OLD_map_er] at old
        have oldReject : ((AllArityCursor.machine k).run T (initialConfig (AllArityCursor.machine k) B y)).state=
            (AllArityCursor.machine k).reject := by
          apply Fin.ext
          rw [old]
          change (SmallIngress.machine.run T c).state.val=328
          exact reject
        have done := IngressRepair.reject_preserved k (initialConfig (IngressRepair.machine k) B y) T oldReject
        refine ⟨T,le_rfl,Or.inl ?_⟩
        have v := congrArg Fin.val done
        exact v
      · have work' : OLD_exits (SmallIngress.machine.run T c).state := work
        obtain ⟨t,ht,_first,_eq,old,_prefix⟩ := Cursor.Transport.first_changed_rows SmallIngress.machine (AllArityCursor.machine k)
          (OLD_er k) OLD_exits (fun c hc => OLD_old_inert c hc) (OLD_raw_row k) c T work'
        rw [OLD_er_initial,OLD_map_er] at old
        refine ⟨t,ht,?_⟩
        rcases REPAIR k (initialConfig (IngressRepair.machine k) B y) t with rejected | same
        · left; exact congrArg Fin.val rejected
        · have same' : (IngressRepair.machine k).run t (initialConfig (IngressRepair.machine k) B y)=
              (AllArityCursor.machine k).run t (initialConfig (AllArityCursor.machine k) B y) := same
          rw [same',old]
          change (SmallIngress.machine.run T c).state.val=328 ∨
            (SmallIngress.machine.run T c).state.val=345 ∨ (SmallIngress.machine.run T c).state.val=346
          exact Or.inr work)")
    evalTactic (ast.rewriteBottomUp fun stx =>
      if stx.isIdent then
        match mapping.find? (fun p => p.1==stx.getId.toString) with
        | some (_,n) => mkIdent n
        | none => stx
      else stx)
private theorem equality_orbit {a m z n : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (cap : n=FixedRawLengthFence.capacity a m z)
    (T : Nat) (price : T ≤ 128*(pairLength a m+1)^2)
    (e : Config SmallIngress.producer.stateCount (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)))
    (success : SmallIngress.producer.run T (initialConfig SmallIngress.producer
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))=e)
    (accept : e.state=SmallIngress.producer.accept) (head : e.head.val=a+m+z+2)
    (tape : e.tape=FixedRawLengthFence.countdownTape (FixedRawLengthFence.allocation (pairLength a m)) x w z 0 n) :
    ∃ t, t ≤ 4096*(pairLength a m+1)^2 ∧
      (SmallIngress.machine.run t (initialConfig SmallIngress.machine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state.val=328 := by
  let R := pairLength a m
  let B := FixedRawLengthFence.allocation R
  let L := a+m+z+2
  let U := Body.extend (FixedRawLengthFence.countdownTape B x w z 0 n)
  have resource := (FixedRawLengthFence.resource_bounds R).1
  have cells := FixedRawLengthFence.countdown_success_cells x w gamma resource (Nat.le_of_eq cap)
  have eqF : L+n+1=FixedRawLengthFence.fencePos R := by
    have support := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z gamma).1
    dsimp [L,FixedRawLengthFence.capacity,FixedRawLengthFence.fencePos,R,pairLength] at *
    omega
  have fit : L+n+1 < tapeLength R B := by
    rw [eqF]
    dsimp [FixedRawLengthFence.fencePos,tapeLength]
    omega
  have read (i : Nat) (hi : i < tapeLength (pairLength a m) B) : U i=FixedRawLengthFence.countdownTape B x w z 0 n ⟨i,hi⟩ := by simp only [U,Body.extend,dif_pos hi]
  have hL : L < tapeLength R B := by omega
  have blank : U L=none := by rw [read L hL]; exact cells.2.2.1 _ (by dsimp [L]; omega)
  have marks (i : Nat) (lo : L < i) (hi : i < L+n+1) : U i=some true := by
    rw [read i (by change i < tapeLength R B; omega)]
    exact cells.2.2.2.1 ⟨i,by change i < tapeLength R B; omega⟩
      (by change a+m+3+z ≤ i; dsimp [L] at lo; omega) (by change i < a+m+3+z+n; dsimp [L] at hi; omega)
  have fence : U (L+n+1)=some false := by rw [read _ fit]; exact cells.2.2.2.2.2 _ eqF
  have body := install_reject U fit blank marks fence
  obtain ⟨tp,tpT,first,arrived⟩ := Body.first_accept_whole SmallIngress.producer
    (initialConfig SmallIngress.producer B (encodePair x w)) T e success accept
  have entry : (⟨Stream.machine.start,e.head,e.tape⟩ : Config Stream.machine.stateCount R B)=
      ⟨Stream.machine.start,⟨L,hL⟩,fun i => U i.val⟩ := by
    refine Config.ext_parts rfl (Fin.ext head) ?_
    funext i; rw [tape]; exact (Body.extend_read _ i).symm
  have hand := SmallIngress.producer.seq_handoff Stream.machine
    (initialConfig SmallIngress.producer B (encodePair x w)) first (by rw [arrived]; exact accept) (n+2)
  rw [arrived] at hand
  change SmallIngress.machine.run (tp+(n+2)) (initialConfig SmallIngress.machine B (encodePair x w))=
    SmallIngress.producer.seqEmbedRight Stream.machine (Stream.machine.run (n+2) ⟨Stream.machine.start,e.head,e.tape⟩) at hand
  rw [entry] at hand
  have nR : n ≤ 3*R := by
    dsimp [FixedRawLengthFence.capacity,FixedRawLengthFence.fencePos] at cap
    change n=(3*R+2)-(a+m+3+z) at cap
    have support := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z gamma).1
    omega
  have total := phase_price R n 0 0 tp (n+2) nR (Nat.zero_le _) (Nat.zero_le _) (tpT.trans price)
    (by unfold InputRead.readClock; omega)
  refine ⟨tp+(n+2),total,?_⟩
  rw [hand]
  change 288+(Stream.machine.run (n+2) _).state.val=328
  rw [body]; rfl
end RepairedFrontier
