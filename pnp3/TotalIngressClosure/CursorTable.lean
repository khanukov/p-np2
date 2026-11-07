import TotalIngressClosure.RawTable
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("TotalIngressClosure.RawTable","TotalIngressClosure","table_prefix","tablePrefix"),
      ("AllArityCursor.Runtime","AllArityCursor","first_raw","firstRaw"),
      ("AllArityCursor.Runtime","AllArityCursor","map_right","mapRight")] do
    let found:=env.constants.toList.filter fun (n,_)=>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,.thmInfo ci)]=>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun s=>{s with openDecls:=.explicit (Name.str .anonymous aliasName) n::s.openDecls}
    | _=>throwError "Nonunique first live table cursor {mod}/{key}: {found.map Prod.fst}"
set_option maxRecDepth 4000 in
/-- Recovered FIRST arrival at the live Cursor row, retaining the same complete
physical image and every-prefix head bounds on arbitrary supported source data. -/
private theorem table_first (k : Nat) {a m n consumed z : Nat} (x : Bitstring a) (w : Bitstring m)
    (header:contentHeader? (Fin.append x w)=some (n,consumed))
    (tag:FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (physical:z=0 ∨ 9+z < a+m) (cap:n < FixedRawLengthFence.capacity a m z)
    (rows:2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1) :
    let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
    let S:=a+m;let p:=min (9+2*z+2^n) S
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) (S+z+2) n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let c:=initialConfig (AllArityCursor.machine k) B (encodePair x w)
    ∃ (t : Nat) (_hH:S+z+n+3 < tapeLength R B) (hp:p < tapeLength R B),t ≤ 4096*(R+1)^2 ∧
      (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
        ⟨Cursor.q k (if p=S then 57 else 58),⟨p,hp⟩,fun i=>V i.val⟩ ∧
      (∀ u,u < t → ((AllArityCursor.machine k).run u c).state.val ≠ 345 ∧
        ((AllArityCursor.machine k).run u c).state.val ≠ 346) ∧
      (∀ u,u ≤ t → ((AllArityCursor.machine k).run u c).state.val < 352) ∧
      (∀ u,u ≤ t → ((AllArityCursor.machine k).run u c).head.val ≤ 12*(R+1)^2) := by
  intro R B S p U V c
  obtain ⟨T,hH,price,heads,finished⟩:=tablePrefix x w header tag gamma physical cap
  rw [if_pos rows] at finished
  obtain ⟨hp,done⟩:=finished
  let s:=Stream.q (if p=S then 57 else 58)
  have choice:s.val=57 ∨ s.val=58:=by dsimp only [s,Stream.q];split_ifs <;> simp
  obtain ⟨t,ht,oldDone,tx,first⟩:=firstRaw k (encodePair x w) T s choice ⟨p,hp⟩ (fun i=>V i.val) done
  refine ⟨t,hH,hp,ht.trans price,?_,?_,?_,?_⟩
  · rw [tx t le_rfl,oldDone,mapRight]
    change SmallIngress.producer.seqEmbedRight (Cursor.machine k)
      ⟨Cursor.q k s.val,⟨p,hp⟩,fun i=>V i.val⟩=_
    have eq:s.val=(if p=S then 57 else 58):=by dsimp only [s,Stream.q];split_ifs <;> decide
    rw [eq]
  · intro u hu
    exact ⟨(first u hu).2.2.1,(first u hu).2.2.2⟩
  · intro u hu
    rw [tx u hu]
    exact (SmallIngress.machine.run u (initialConfig SmallIngress.machine B (encodePair x w))).state.isLt
  · intro u hu
    rw [tx u hu]
    exact heads u (hu.trans ht)
end TotalIngressClosure
