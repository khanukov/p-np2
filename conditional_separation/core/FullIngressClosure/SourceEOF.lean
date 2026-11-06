import Complexity.PrivateInterfaceLookupResolvedSourceScan
import FullIngressClosure.SourceScan
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let checked ← PartAPrivateSourceScan.bindings `FullIngressClosure.SourceEOF
  let env ← getEnv
  for (n,aliasName) in checked do
    let some ci := env.find? n | throwError "validated source-scan identity disappeared"
    logInfo m!"private-term|{n}|type={ci.type}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
private structure EOFCode (k : Nat) (entry out : Fin (BodyIngress.machine k).stateCount) where
  register : Fin (BodyIngress.machine k).stateCount
  safeEntry : Safe k entry
  enter : (BodyIngress.machine k).step entry none=(register,none,.right)
  rest : RegReturnCode k 0 register out
private theorem eof_return {k lo P D T S L H F Q entry out}
    (code : EOFCode k entry out) (grid : Grid D T) (corridor : Corridor T S L H)
    (arena : Arena T H F Q) (d0 : D 0=F+1) (lower : lo ≤ S) (upper : D 12 ≤ P) :
    ∃ t,t ≤ 8*(P+16) ∧ PPath k lo P t (pNode entry S T) (pNode out (D 0) T) := by
  have order:=corridorOrder corridor
  have gap:=arenaGap arena
  have high0:=(gridMono grid 0 12 (by decide) le_rfl).trans upper
  have first:=pKeep (k:=k) (lo:=lo) (hi:=P) entry code.register S (S+1) T .right
    ⟨code.safeEntry.1,code.safeEntry.2.1⟩ code.safeEntry.2.2 ⟨lower,by omega⟩ ⟨by omega,by omega⟩
    (by rw [corridorEof corridor]; exact code.enter) rfl
  obtain ⟨t,price,path⟩:=fromRegister (k:=k) (lo:=lo) (P:=P) code.rest grid corridor arena (by decide) d0 lower upper
  exact ⟨_,by omega,pAppend first path⟩
end FullIngressClosure
