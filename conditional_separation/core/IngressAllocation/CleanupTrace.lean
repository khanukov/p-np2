import IngressAllocation.ArithmeticPaths
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("VirtualReady.Kernel","VirtualReady","Frame","CleanupFrame"),
      ("VirtualReady.Kernel","VirtualReady","embed","cleanupEmbed"),
      ("VirtualReady.Kernel","VirtualReady","Frame.room","cleanRoom"),
      ("VirtualReady.Kernel","VirtualReady","cleanup_path","cleanupPath"),
      ("VirtualReady.Kernel","VirtualReady","route_path","routePath"),
      ("VirtualReady.Kernel","VirtualReady","Path.append","pathAppend"),
      ("VirtualReady.Kernel","VirtualReady","Path.execute","pathRun"),
      ("IngressAllocation.ArithmeticPaths","IngressAllocation.CleanupStage","every_head","pathHeads")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique real dirty cleanup path {mod}/{key}: {found.map Prod.fst}"
private theorem ready_q (k : Nat) : Cursor.q k (889+93*k+47)=Cursor.mReady k ⟨2,by decide⟩:=by
  change Cursor.q k (889+93*k+47)=Cursor.q k (64+265+82*k+1+11*k+604+2)
  congr 1
  omega
private theorem cleanup_d0_heads (k N B L n Q F r : Nat) (T : Nat → Option Bool)
    (fr : CleanupFrame T L n Q F r) (fit : F+5*r+n+7 < tapeLength N B) :
    let c : Config (Cursor.machine k).stateCount N B:=
      ⟨Cursor.q k (798+93*k),⟨F+1,by omega⟩,fun i=>T i.val⟩
    let d:=F-(L+n+1)+18*r+6*n+44
    ((Cursor.machine k).run d c).state=Cursor.mReady k ⟨2,by decide⟩ ∧
      ((Cursor.machine k).run d c).head.val=L+n+1 ∧
      (∀ u,u ≤ d → ((Cursor.machine k).run u c).head.val ≤ F+5*r+n+7) := by
  let path:=cleanupPath k (F+5*r+n+7) L n Q F r T fr (by change F+5*r+n+7 ≤ F+5*r+n+7;exact le_rfl)
  have run:=pathRun (N:=N) (B:=B) path fit
  dsimp only [cleanupEmbed] at run
  have heads:=pathHeads path fit (by change F+1 < tapeLength N B;omega)
  refine ⟨?_,?_,heads⟩
  · change ((Cursor.machine k).run _ _).state=_
    rw [run]
    exact ready_q k
  · change ((Cursor.machine k).run _ _).head.val=_
    rw [run]
private theorem cleanup_d2_heads (k N B L n Q F r : Nat) (T : Nat → Option Bool)
    (fr : CleanupFrame T L n Q F r) (fit : F+5*r+n+7 < tapeLength N B) (odd : Bool) :
    let c : Config (Cursor.machine k).stateCount N B:=
      ⟨Cursor.q k (if odd then 250 else 304),⟨F+r+n+3,by omega⟩,fun i=>T i.val⟩
    let d:=(n+r+4)+(F-(L+n+1)+18*r+6*n+44)
    ((Cursor.machine k).run d c).state=Cursor.mReady k ⟨2,by decide⟩ ∧
      ((Cursor.machine k).run d c).head.val=L+n+1 ∧
      (∀ u,u ≤ d → ((Cursor.machine k).run u c).head.val ≤ F+5*r+n+7) := by
  have route:=routePath k (F+5*r+n+7) L n Q F r T fr le_rfl odd
  have clean:=cleanupPath k (F+5*r+n+7) L n Q F r T fr le_rfl
  have path:=pathAppend route clean
  have run:=pathRun (N:=N) (B:=B) path fit
  dsimp only [cleanupEmbed] at run
  have heads:=pathHeads path fit (by change F+r+n+3 < tapeLength N B;omega)
  refine ⟨?_,?_,heads⟩
  · change ((Cursor.machine k).run _ _).state=_
    rw [run]
    exact ready_q k
  · change ((Cursor.machine k).run _ _).head.val=_
    rw [run]
end IngressAllocation
