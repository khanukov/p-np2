import CanonicalLeaf.Raw
import VirtualLeaf.Fixtures
namespace CanonicalLeaf
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
/-- Complete control ABI: no extra states, no start/verdict/entry/result relabeling. -/
theorem controls (k : Nat) :
    (machine k).stateCount=(VirtualLeaf.machine k).stateCount ∧
    (machine k).start=(VirtualLeaf.machine k).start ∧
    (machine k).accept=(VirtualLeaf.machine k).accept ∧
    (machine k).reject=(VirtualLeaf.machine k).reject ∧
    entry k=VirtualLeaf.embed k (VirtualLeaf.entry k) ∧
    ∀ b, result k b=VirtualLeaf.result k b := by exact ⟨rfl,rfl,rfl,rfl,rfl,fun _ => rfl⟩
theorem normal_work (k : Nat) {N B : Nat} (c : Config (machine k).stateCount N B)
    (t : Nat) (h : Fin (tapeLength N B)) (T : Fin (tapeLength N B) → Option Bool)
    (done : (machine k).run t c=VirtualLeaf.config k (IngressRepair.producer.seqEmbedRight (Cursor.machine k)
      ⟨Cursor.q k (613+93*k),h,T⟩)) :
    ∀ u, u≤t → ((machine k).run u c).state≠(machine k).accept ∧
      ((machine k).run u c).state≠(machine k).reject := by
  have value : ((machine k).run t c).state.val=901+93*k := by
    rw [done]
    change 288+(613+93*k)%Cursor.stateCount k=901+93*k
    rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)]; omega
  have a : (machine k).accept.val=327 := (AllArityCursor.control_values k).2.2.1
  have r : (machine k).reject.val=328 := (AllArityCursor.control_values k).2.2.2
  apply (machine k).no_terminal_of_le c
  · intro bad; have eq:=congrArg Fin.val bad; rw [value,a] at eq; omega
  · intro bad; have eq:=congrArg Fin.val bad; rw [value,r] at eq; omega
/-- Original accepted projection witness, reusing the sealed kernel proof. -/
theorem tiny_accepted :
    let x : Bitstring 7:=fun i => i.val==0 || i.val==2 || i.val==3 || i.val==6
    let w : Bitstring 8:=fun i => i.val==2 || i.val==5
    PartAEndpoint.thresholdContentWitnessRelation 0 7 8 x w=true := by exact VirtualLeaf.tiny_accepted
/-- The reviewed missing-FIRST-payload bad word remains a literal reject, all k. -/
theorem stall_reject (k : Nat) :
    let x : Bitstring 11:=fun i => i.val==0 || i.val==2 || i.val==3 || i.val==6 || i.val==10
    let w : Bitstring 0:=Fin.elim0
    ∃ t, t≤128*(pairLength 11 0+1)^2 ∧
      ((machine k).run t (initialConfig (machine k) 9216 (encodePair x w))).state=(machine k).reject ∧
      PartAEndpoint.thresholdContentWitnessRelation k 11 0 x w=false := by
  dsimp only
  apply missing_payload k _ _ 2 (by decide) (by decide) (by decide) (by decide)
/-- A genuine accepted raw virtual fixture, not an accepted host-trace assumption. -/
theorem tiny_raw :
    let x : Bitstring 7:=fun i => i.val==0 || i.val==2 || i.val==3 || i.val==6
    let w : Bitstring 8:=fun i => i.val==2 || i.val==5
    ∃ t, t≤4294967296*(pairLength 7 8+1)^5 ∧
      ((machine 0).run t (initialConfig (machine 0) 9216 (encodePair x w))).state=result 0 false ∧
      ((machine 0).run t (initialConfig (machine 0) 9216 (encodePair x w))).head.val=20 := by
  dsimp only
  let x : Bitstring 7:=fun i => i.val==0 || i.val==2 || i.val==3 || i.val==6
  let w : Bitstring 8:=fun i => i.val==2 || i.val==5
  obtain ⟨pr,parsed,z,_hH,gamma,_eof,physical⟩:=accepted_leaf 0 x w tiny_accepted
  have g : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some 1 := by decide
  have z1 : z=1:=Option.some.inj (gamma.symm.trans g)
  obtain ⟨consumed,header,target⟩:=contentInput?_target_eq_contentHeader _ _ parsed
  have h : contentHeader? (Fin.append x w)=some (1,3) := by decide
  have n1 : pr.2.n=1:=target.trans (congrArg Prod.fst (Option.some.inj (header.symm.trans h)))
  have phys : min (9+2*z+2^pr.2.n) (7+8) < 7+8 := by rw [z1,n1]; decide
  obtain ⟨_fit,outcome⟩:=physical phys
  rcases outcome with ⟨over,_⟩ | ⟨_fits,tail⟩
  · have bad : ¬(7+8-min (9+2*1+2^1) (7+8) < bitLength 1) := by norm_num [bitLength,Nat.log2]
    exact False.elim (bad (by simpa only [z1,n1] using over))
  · rcases tail with ⟨wr,_⟩ | ⟨_v2,_v3,_v4,_v5,_d,_cap,_logical,leaf⟩
    · have bad : ¬(Cursor.Target.W 0 1 ≤ 7+8-min (9+2*1+2^1) (7+8)) := by norm_num [Cursor.Target.W,bitLength,Nat.log2]
      exact False.elim (bad (by simpa only [z1,n1] using wr))
    · obtain ⟨_positive,_logical,_zeros,_decoded,t,s,_hs,_ht,_old,_firstCfg,_first,_prefix,price,run,_safe,_firstResult⟩:=leaf
      refine ⟨_,price,congrArg Config.state run,?_⟩
      have eq:=congrArg (fun c => c.head.val) run
      simpa only [z1,n1] using eq
/-- Prepared row1/n2: canonical beta0=true; valid old forward frame returns its leftmost=false. -/
theorem discriminator (k : Nat) :
    let T : Fin (tapeLength 0 16) → Option Bool:=fun i => if i.val=0 ∨ i.val=3 then none else some (i.val==2)
    let H : Fin (tapeLength 0 16):=⟨3,by decide⟩
    let c : Config (machine k).stateCount 0 16:=⟨entry k,H,T⟩
    (machine k).run 5 c=⟨result k true,H,Function.update T H (some true)⟩ ∧
    (VirtualLeaf.machine k).run 9 c=⟨VirtualLeaf.result k false,H,Function.update T H (some false)⟩ ∧
    ∀ j : Fin 2, T ⟨3-1-j.val,by change 3-1-j.val < 17; omega⟩=some (Pnp3.Core.vecOfNat 2 1 j) := by
  dsimp only
  let T : Fin (tapeLength 0 16) → Option Bool:=fun i => if i.val=0 ∨ i.val=3 then none else some (i.val==2)
  have digits : ∀ j : Fin 2, T ⟨3-1-j.val,by change 3-1-j.val < 17; omega⟩=some (Pnp3.Core.vecOfNat 2 1 j) := by
    intro j; fin_cases j <;> decide
  have native:=prepared k 0 2 (Pnp3.Core.vecOfNat 2 1) T (by decide) (by decide) (by decide) digits
  have forward:=VirtualLeaf.prepared k 0 2 (fun j : Fin 2 => j.val==1) T (by decide) (by decide) (by decide)
    (by intro j; fin_cases j <;> decide)
  exact ⟨native.1,forward.1,digits⟩
end CanonicalLeaf
