import FullIngressClosure.HalvingStage
import FullIngressClosure.ArithmeticCertificates
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("BodyIngress.Native","BodyIngress","Node.mk","pNode"),
      ("BodyIngress.Native","BodyIngress","Path","PPath"),
      ("BodyIngress.Native","BodyIngress","Path.append","pAppend"),
      ("BodyIngress.Native","BodyIngress","keep","pKeep"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid","Grid"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid.mono","gridMono"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid.blank","gridBlank"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid.cells","gridCells"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Unary","BankUnary"),
      ("FullIngressClosure.Workspace","FullIngressClosure","setBank","setBank"),
      ("FullIngressClosure.Workspace","FullIngressClosure","bank_grid","bankGrid"),
      ("FullIngressClosure.Workspace","FullIngressClosure","bank_other","bankOther"),
      ("FullIngressClosure.Workspace","FullIngressClosure","bank_unary","bankUnary"),
      ("FullIngressClosure.Move","FullIngressClosure","Travel","Travel"),
      ("FullIngressClosure.Move","FullIngressClosure","travel","travel"),
      ("FullIngressClosure.Move","FullIngressClosure","copy_value","copyValue"),
      ("FullIngressClosure.Move","FullIngressClosure","Travel.right","trRight"),
      ("FullIngressClosure.Move","FullIngressClosure","Travel.left","trLeft"),
      ("FullIngressClosure.Move","FullIngressClosure","Travel.stay","trStay"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteR.nil","rrNil"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteR.next","rrNext"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteL.nil","rlNil"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteL.next","rlNext"),
      ("FullIngressClosure.Paint","FullIngressClosure","paint","paint"),
      ("FullIngressClosure.PaintCertificates","FullIngressClosure","paint1323","paint1323"),
      ("FullIngressClosure.HalvingStage","FullIngressClosure","painted_bank","paintedBank"),
      ("FullIngressClosure.ArithmeticCertificates","FullIngressClosure","copy3","copy3"),
      ("FullIngressClosure.Rows","FullIngressClosure","native_row","nativeRow"),
      ("FullIngressClosure.Certificates","FullIngressClosure","st","st"),
      ("FullIngressClosure.Certificates","FullIngressClosure","st_small","stSmall"),
      ("FullIngressClosure.Certificates","FullIngressClosure","safeNative","safeNative") ] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Nonunique physical anchor setup proof {mod}/{key}: {found.map Prod.fst}"
private def toAnchor (k : Nat) : Travel k 1 7 (st k 1311) (st k 1323) :=
  (trRight (rrNext (safeNative k 1311 (by decide)) (safeNative k 1312 (by decide))
      (by rw [stSmall k 1311 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1312 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1312 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1313 (by decide)) (safeNative k 1314 (by decide))
      (by rw [stSmall k 1313 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1314 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1314 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1315 (by decide)) (safeNative k 1316 (by decide))
      (by rw [stSmall k 1315 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1316 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1316 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1317 (by decide)) (safeNative k 1318 (by decide))
      (by rw [stSmall k 1317 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1318 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1318 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1319 (by decide)) (safeNative k 1320 (by decide))
      (by rw [stSmall k 1319 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1320 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1320 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1321 (by decide)) (safeNative k 1322 (by decide))
      (by rw [stSmall k 1321 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1322 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1322 (by decide),nativeRow]; rfl) (rrNil 7 (st k 1323)))))))))
private def toBack (k : Nat) : Travel k 7 10 (st k 1382) (st k 1388) :=
  (trRight (rrNext (safeNative k 1382 (by decide)) (safeNative k 1383 (by decide))
      (by rw [stSmall k 1382 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1383 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1383 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1384 (by decide)) (safeNative k 1385 (by decide))
      (by rw [stSmall k 1384 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1385 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1385 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1386 (by decide)) (safeNative k 1387 (by decide))
      (by rw [stSmall k 1386 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1387 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1387 (by decide),nativeRow]; rfl) (rrNil 10 (st k 1388))))))
private theorem anchor_setup {k lo P D} (r : Nat) (T : Nat → Option Bool) (grid : Grid D T)
    (lenA : D 8=D 7+r+1) (lenB : D 11=D 10+(3*r+3)+1) (lenC : D 6=D 5+r+1)
    (lower : lo ≤ D 0) (upper : D 12 ≤ P)
    (emptyB : BankUnary D T 10 0) (emptyC : BankUnary D T 5 0) :
    ∃ t,t ≤ 256*(r+1)*(P+16) ∧ PPath k lo P t
      (pNode (st k 1311) (D 1) T)
      (pNode (st k 1461) (D 10) (setBank (setBank (setBank T D 7 r) D 10 r) D 5 0)) := by
  obtain ⟨t0,h0,first⟩:=travel (toAnchor k) grid (by decide) (by decide) lower upper
  have low:=lower.trans (gridMono grid 0 7 (by decide) (by decide))
  have high : D 7+r+1 ≤ P:=by rw [← lenA]; exact (gridMono grid 8 12 (by decide) le_rfl).trans upper
  have painting:=paint (k:=k) (lo:=lo) (P:=P) (paint1323 k) T (D 7) r low high
    (gridBlank grid 7 (by decide)) (by rw [← lenA]; exact gridBlank grid 8 (by decide))
    (by intro i il iu; exact gridCells grid 7 i (by decide) il (by rwa [lenA]))
  rw [paintedBank T D 7 r true lenA] at painting
  have grid1:=bankGrid grid 7 r (by decide)
  have emptyB' : BankUnary D (setBank T D 7 r) 10 0:=
    bankOther grid 10 7 0 r (by decide) (by decide) (by decide) emptyB
  have emptyC' : BankUnary D (setBank T D 7 r) 5 0:=
    bankOther grid 5 7 0 r (by decide) (by decide) (by decide) emptyC
  obtain ⟨t1,h1,copyPath⟩:=copyValue (copy3 k) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) r (3*r+3) r lenA lenB lenC lower upper
    r le_rfl (by omega) le_rfl _ grid1 (bankUnary T D 7 r) emptyB' emptyC'
  have grid2:=bankGrid (bankGrid grid1 10 r (by decide)) 5 0 (by decide)
  obtain ⟨t2,h2,last⟩:=travel (toBack k) grid2 (by decide) (by decide) lower upper
  have safe:=safeNative k 1388 (by decide)
  have jump:=pKeep (k:=k) (lo:=lo) (hi:=P) (st k 1388) (st k 1461) (D 10) (D 10)
    (setBank (setBank (setBank T D 7 r) D 10 r) D 5 0) .stay
    ⟨safe.1,safe.2.1⟩ safe.2.2
    ⟨lower.trans (gridMono grid 0 10 (by decide) (by decide)),(gridMono grid 10 12 (by decide) le_rfl).trans upper⟩
    ⟨lower.trans (gridMono grid 0 10 (by decide) (by decide)),(gridMono grid 10 12 (by decide) le_rfl).trans upper⟩
    (by rw [gridBlank grid2 10 (by decide),stSmall k 1388 (by decide),nativeRow]; rfl) rfl
  refine ⟨_,?_,pAppend first (pAppend painting (pAppend copyPath (pAppend last jump)))⟩
  nlinarith only [h0,h1,h2,high,Nat.zero_le (D 7)]
end FullIngressClosure
