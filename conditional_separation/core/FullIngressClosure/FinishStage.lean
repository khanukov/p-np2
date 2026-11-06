import Complexity.PrivateInterfaceLookupResolvedFinish
import FullIngressClosure.SourceImage
import FullIngressClosure.HalvingStage
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let checked ← PartAPrivateFinish.bindings `FullIngressClosure.FinishStage
  let env ← getEnv
  for (n,aliasName) in checked do
    let some ci := env.find? n | throwError "validated finish-frame identity disappeared"
    logInfo m!"private-term|{n}|type={ci.type}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
private structure FinishStageCode (k : Nat) (mode : Fin 3) (entry : Fin (BodyIngress.machine k).stateCount) where
  at9 : Fin (BodyIngress.machine k).stateCount
  after9 : Fin (BodyIngress.machine k).stateCount
  at11 : Fin (BodyIngress.machine k).stateCount
  after11 : Fin (BodyIngress.machine k).stateCount
  at10 : Fin (BodyIngress.machine k).stateCount
  after10 : Fin (BodyIngress.machine k).stateCount
  atH : Fin (BodyIngress.machine k).stateCount
  route9 : Travel k 0 9 entry at9
  clear9 : PaintCode k at9 after9 false
  route11 : Travel k 9 11 after9 at11
  clear11 : PaintCode k at11 after11 false
  route10 : Travel k 11 10 after11 at10
  fill10 : PaintCode k at10 after10 true
  returnH : ToHCode k 10 after10 atH
  safeH : Safe k atH
  enter : (BodyIngress.machine k).step atH none=(BodyIngress.body k (SerializedBody.entry mode),none,.stay)
private theorem finish_stage {k lo P D T H F Q mode entry} (code : FinishStageCode k mode entry)
    (grid : Grid D T) (arena : Arena T H F Q) (d0 : D 0=F+1)
    (w9 w11 w10 : Nat) (len9 : D 10=D 9+w9+1) (len11 : D 12=D 11+w11+1) (len10 : D 11=D 10+w10+1)
    (lower : lo ≤ H) (upper : D 12 ≤ P) :
    ∃ t,t ≤ 32*(P+16) ∧ PPath k lo P t (pNode entry (D 0) T)
      (pNode (BodyIngress.body k (SerializedBody.entry mode)) H
        (setBank (setBank (setBank T D 9 0) D 11 0) D 10 w10)) := by
  have gap:=arenaGap arena
  have low0 : lo ≤ D 0:=by omega
  have fit9 : D 9+w9+1 ≤ P:=by rw [← len9]; exact (gridMono grid 10 12 (by decide) le_rfl).trans upper
  have fit11 : D 11+w11+1 ≤ P:=by rw [← len11]; exact upper
  have fit10 : D 10+w10+1 ≤ P:=by rw [← len10]; exact (gridMono grid 11 12 (by decide) le_rfl).trans upper
  obtain ⟨t0,h0,go9⟩:=travel (k:=k) (lo:=lo) (P:=P) code.route9 grid (by decide) (by decide) low0 upper
  have clear9:=paint (k:=k) (lo:=lo) (P:=P) code.clear9 T (D 9) w9
    (low0.trans (gridMono grid 0 9 (by decide) (by decide))) fit9
    (gridBlank grid 9 (by decide)) (by rw [← len9]; exact gridBlank grid 10 (by decide))
    (by intro i il iu; exact gridCells grid 9 i (by decide) il (by rwa [len9]))
  rw [paintedBank T D 9 w9 false len9] at clear9
  have grid1:=bankGrid grid 9 0 (by decide)
  have arena1:=bankArena grid arena (by decide : 9<12) d0 (v:=0)
  obtain ⟨t1,h1,go11⟩:=travel (k:=k) (lo:=lo) (P:=P) code.route11 grid1 (by decide) (by decide) low0 upper
  have clear11:=paint (k:=k) (lo:=lo) (P:=P) code.clear11 (setBank T D 9 0) (D 11) w11
    (low0.trans (gridMono grid 0 11 (by decide) (by decide))) fit11
    (gridBlank grid1 11 (by decide)) (by rw [← len11]; exact gridBlank grid1 12 le_rfl)
    (by intro i il iu; exact gridCells grid1 11 i (by decide) il (by rwa [len11]))
  rw [paintedBank _ D 11 w11 false len11] at clear11
  have grid2:=bankGrid grid1 11 0 (by decide)
  have arena2:=bankArena grid1 arena1 (by decide : 11<12) d0 (v:=0)
  obtain ⟨t2,h2,go10⟩:=travel (k:=k) (lo:=lo) (P:=P) code.route10 grid2 (by decide) (by decide) low0 upper
  have fill10:=paint (k:=k) (lo:=lo) (P:=P) code.fill10 (setBank (setBank T D 9 0) D 11 0) (D 10) w10
    (low0.trans (gridMono grid 0 10 (by decide) (by decide))) fit10
    (gridBlank grid2 10 (by decide)) (by rw [← len10]; exact gridBlank grid2 11 (by decide))
    (by intro i il iu; exact gridCells grid2 10 i (by decide) il (by rwa [len10]))
  rw [paintedBank _ D 10 w10 true len10] at fill10
  have grid3:=bankGrid grid2 10 w10 (by decide)
  have arena3:=bankArena grid2 arena2 (by decide : 10<12) d0 (v:=w10)
  obtain ⟨t3,h3,returnH⟩:=toH (k:=k) (lo:=lo) (P:=P) code.returnH grid3 arena3 (by decide) d0 lower upper
  have highH : H ≤ P:=by have h:=(gridMono grid 0 12 (by decide) le_rfl).trans upper; omega
  have enter:=pKeep (k:=k) (lo:=lo) (hi:=P) code.atH (BodyIngress.body k (SerializedBody.entry mode)) H H
    (setBank (setBank (setBank T D 9 0) D 11 0) D 10 w10) .stay
    ⟨code.safeH.1,code.safeH.2.1⟩ code.safeH.2.2 ⟨lower,highH⟩ ⟨lower,highH⟩
    (by rw [arenaBlank arena3]; exact code.enter) rfl
  refine ⟨_,?_,pAppend go9 (pAppend clear9 (pAppend go11 (pAppend clear11 (pAppend go10 (pAppend fill10 (pAppend returnH enter))))))⟩
  nlinarith only [h0,h1,h2,h3,fit9,fit10,fit11,Nat.zero_le (D 9),Nat.zero_le (D 10),Nat.zero_le (D 11)]
end FullIngressClosure
