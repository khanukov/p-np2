import FullIngressClosure.InitializationPath
import FullIngressClosure.Padding
import FullIngressClosure.Registers
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("BodyIngress.Native","BodyIngress","Node.mk","pNode"),
      ("BodyIngress.Native","BodyIngress","Path","PPath"),
      ("BodyIngress.Native","BodyIngress","Path.append","pAppend"),
      ("FullIngressClosure.Initialization","FullIngressClosure","Six","Six"),
      ("FullIngressClosure.Initialization","FullIngressClosure","Six.fresh","frameFresh"),
      ("FullIngressClosure.Initialization","FullIngressClosure","Before","Before"),
      ("FullIngressClosure.Initialization","FullIngressClosure","stageTape","stageTape"),
      ("FullIngressClosure.Initialization","FullIngressClosure","width","width"),
      ("FullIngressClosure.Initialization","FullIngressClosure","partial_initial","partialInitial"),
      ("FullIngressClosure.Initialization","FullIngressClosure","partial_complete","partialComplete"),
      ("FullIngressClosure.Initialization","FullIngressClosure","fill_partial","fillPartial"),
      ("FullIngressClosure.Initialization","FullIngressClosure","partial_blank","partialBlank"),
      ("FullIngressClosure.Initialization","FullIngressClosure","partial_cells","partialCells"),
      ("FullIngressClosure.Initialization","FullIngressClosure","delimiter_mono","delimiterMono"),
      ("FullIngressClosure.Initialization","FullIngressClosure","delimiter_rise","delimiterRise"),
      ("FullIngressClosure.Initialization","FullIngressClosure","copy_frame","copyFrame"),
      ("FullIngressClosure.InitializationPath","FullIngressClosure","partial_travel","partialTravel"),
      ("FullIngressClosure.CloneStage","FullIngressClosure","clone_stage","cloneStage"),
      ("FullIngressClosure.Certificates","FullIngressClosure","st","st"),
      ("FullIngressClosure.Padding","FullIngressClosure","stack_padding","stackPadding"),
      ("FullIngressClosure.Padding","FullIngressClosure","prefixFalse","prefixFalse"),
      ("FullIngressClosure.Initialization","FullIngressClosure","partial_old","partialOld"),
      ("FullIngressClosure.Registers","FullIngressClosure","Registers","Registers"),
      ("FullIngressClosure.Registers","FullIngressClosure","Registers.mk","registersMk"),
      ("FullIngressClosure.InitializationPath","FullIngressClosure","join0","join0"),
      ("FullIngressClosure.InitializationPath","FullIngressClosure","join1","join1"),
      ("FullIngressClosure.InitializationPath","FullIngressClosure","join2","join2"),
      ("FullIngressClosure.InitializationPath","FullIngressClosure","join3","join3"),
      ("FullIngressClosure.InitializationPath","FullIngressClosure","join4","join4"),
      ("FullIngressClosure.InitializationPath","FullIngressClosure","join5","join5"),
      ("FullIngressClosure.InitializationPath","FullIngressClosure","join6","join6"),
      ("FullIngressClosure.InitializationPath","FullIngressClosure","toPad","toPad"),
      ("FullIngressClosure.InitializationPath","FullIngressClosure","fromPad","fromPad"),
      ("FullIngressClosure.InitializationPath","FullIngressClosure","join8","join8"),
      ("FullIngressClosure.CloneCertificates","FullIngressClosure","clone0","clone0"),
      ("FullIngressClosure.CloneCertificates","FullIngressClosure","clone1","clone1"),
      ("FullIngressClosure.CloneCertificates","FullIngressClosure","clone2","clone2"),
      ("FullIngressClosure.CloneCertificates","FullIngressClosure","clone3","clone3"),
      ("FullIngressClosure.CloneCertificates","FullIngressClosure","clone4","clone4"),
      ("FullIngressClosure.CloneCertificates","FullIngressClosure","clone5","clone5"),
      ("FullIngressClosure.CloneCertificates","FullIngressClosure","clone6","clone6"),
      ("FullIngressClosure.CloneCertificates","FullIngressClosure","clone7","clone7"),
      ("FullIngressClosure.CloneCertificates","FullIngressClosure","clone8","clone8"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid","Grid"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid.mk","gridMk"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Unary","BankUnary") ] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Nonunique workspace setup term {mod}/{key}: {found.map Prod.fst}"
private theorem workspace_grid {T F r n} (frame : Six T F r n) :
    Grid (SerializedBody.delimiter F r n) (stageTape T F r n 12 0) := by
  refine gridMk ?_ ?_ ?_ ?_
  · intro j hj; exact delimiterRise F r n j hj
  · intro a b ab hb; exact delimiterMono F r n a b ab hb
  · intro j hj; exact partialBlank frame 12 0 j (by decide) le_rfl hj
  · intro j i hj il iu; exact partialCells frame 12 0 j i (by decide) le_rfl hj il iu
private theorem workspace_setup {k lo P F r n} (T : Nat → Option Bool) (frame : Six T F r n)
    (lower : lo ≤ SerializedBody.delimiter F r n 0) (upper : SerializedBody.delimiter F r n 12 ≤ P) :
    ∃ t,t ≤ 256*(n+r+1)*(P+16) ∧ PPath k lo P t
      (pNode (st k 0) (SerializedBody.delimiter F r n 0) T)
      (pNode (st k 770) (SerializedBody.delimiter F r n 0) (stageTape T F r n 12 0)) := by
  let D:=SerializedBody.delimiter F r n
  change D 12 ≤ P at upper
  have finish (b) (six : 6 ≤ b) (bound : b < 12) := partialComplete T F r n b six bound
  obtain ⟨t0,h0,c0⟩:=cloneStage (clone0 k) (stageTape T F r n 6 (0)) D
    (copyFrame frame lo P 0 6 (0) (by decide) (by decide) (by decide)
      (by dsimp only [width]; omega) lower upper)
  rw [fillPartial] at c0
  rw [show (0)+width r n 0=width r n 6 by dsimp only [width]; omega,finish 6 (by decide) (by decide)] at c0
  obtain ⟨s0,p0,j0⟩:=partialTravel (join0 k) T frame (b:=7) (f:=0) (by decide) (by decide) (by decide) (by decide) lower upper
  obtain ⟨t1,h1,c1⟩:=cloneStage (clone1 k) (stageTape T F r n 7 (0)) D
    (copyFrame frame lo P 0 7 (0) (by decide) (by decide) (by decide)
      (by dsimp only [width]; omega) lower upper)
  rw [fillPartial] at c1
  rw [show (0)+width r n 0=width r n 7 by dsimp only [width]; omega,finish 7 (by decide) (by decide)] at c1
  obtain ⟨s1,p1,j1⟩:=partialTravel (join1 k) T frame (b:=8) (f:=0) (by decide) (by decide) (by decide) (by decide) lower upper
  obtain ⟨t2,h2,c2⟩:=cloneStage (clone2 k) (stageTape T F r n 8 (0)) D
    (copyFrame frame lo P 1 8 (0) (by decide) (by decide) (by decide)
      (by dsimp only [width]; omega) lower upper)
  rw [fillPartial] at c2
  rw [show (0)+width r n 1=width r n 8 by dsimp only [width]; omega,finish 8 (by decide) (by decide)] at c2
  obtain ⟨s2,p2,j2⟩:=partialTravel (join2 k) T frame (b:=9) (f:=0) (by decide) (by decide) (by decide) (by decide) lower upper
  obtain ⟨t3,h3,c3⟩:=cloneStage (clone3 k) (stageTape T F r n 9 (0)) D
    (copyFrame frame lo P 0 9 (0) (by decide) (by decide) (by decide)
      (by dsimp only [width]; omega) lower upper)
  rw [fillPartial] at c3
  have norm3 : (0)+width r n 0=r := by dsimp only [width]; omega
  rw [norm3] at c3
  obtain ⟨s3,p3,j3⟩:=partialTravel (join3 k) T frame (b:=9) (f:=r) (by decide) (by decide) (by decide) (by decide) lower upper
  obtain ⟨t4,h4,c4⟩:=cloneStage (clone4 k) (stageTape T F r n 9 (r)) D
    (copyFrame frame lo P 0 9 (r) (by decide) (by decide) (by decide)
      (by dsimp only [width]; omega) lower upper)
  rw [fillPartial] at c4
  rw [show (r)+width r n 0=width r n 9 by dsimp only [width]; omega,finish 9 (by decide) (by decide)] at c4
  obtain ⟨s4,p4,j4⟩:=partialTravel (join4 k) T frame (b:=10) (f:=0) (by decide) (by decide) (by decide) (by decide) lower upper
  obtain ⟨t5,h5,c5⟩:=cloneStage (clone5 k) (stageTape T F r n 10 (0)) D
    (copyFrame frame lo P 0 10 (0) (by decide) (by decide) (by decide)
      (by dsimp only [width]; omega) lower upper)
  rw [fillPartial] at c5
  have norm5 : (0)+width r n 0=r := by dsimp only [width]; omega
  rw [norm5] at c5
  obtain ⟨s5,p5,j5⟩:=partialTravel (join5 k) T frame (b:=10) (f:=r) (by decide) (by decide) (by decide) (by decide) lower upper
  obtain ⟨t6,h6,c6⟩:=cloneStage (clone6 k) (stageTape T F r n 10 (r)) D
    (copyFrame frame lo P 0 10 (r) (by decide) (by decide) (by decide)
      (by dsimp only [width]; omega) lower upper)
  rw [fillPartial] at c6
  have norm6 : (r)+width r n 0=2*r := by dsimp only [width]; omega
  rw [norm6] at c6
  obtain ⟨s6,p6,j6⟩:=partialTravel (join6 k) T frame (b:=10) (f:=2*r) (by decide) (by decide) (by decide) (by decide) lower upper
  obtain ⟨t7,h7,c7⟩:=cloneStage (clone7 k) (stageTape T F r n 10 (2*r)) D
    (copyFrame frame lo P 0 10 (2*r) (by decide) (by decide) (by decide)
      (by dsimp only [width]; omega) lower upper)
  rw [fillPartial] at c7
  have norm7 : (2*r)+width r n 0=3*r := by dsimp only [width]; omega
  rw [norm7] at c7
  obtain ⟨tp,hp,padGo⟩:=partialTravel (toPad k) T frame (b:=10) (f:=3*r) (by decide) (by decide) (by decide) (by decide) lower upper
  have pad:=stackPadding k lo P (D 10) (3*r) (stageTape T F r n 10 (3*r))
    (lower.trans (delimiterMono F r n 0 10 (by decide) (by decide)))
    (by have h:=delimiterMono F r n 11 12 (by decide) le_rfl; change D 11 ≤ D 12 at h
        have eq : D 11=D 10+3*r+4:=by dsimp only [D,SerializedBody.delimiter]; omega
        omega)
    (partialBlank frame 10 (3*r) 10 (by decide) (by decide) le_rfl)
    (by intro i il iu; dsimp only [stageTape]; rw [if_pos ⟨il,iu⟩])
    (by
      intro j jl ju
      have db6:=delimiterMono F r n 6 10 (by decide) (by decide)
      change D 6 ≤ D 10 at db6
      have old : stageTape T F r n 10 (3*r) (D 10+3*r+j)=T (D 10+3*r+j) := by
        dsimp only [D,stageTape]
        rw [if_neg (by omega),if_neg (by
          rintro ⟨u,_u6,ub,il,iu⟩
          have h:=delimiterMono F r n (u.val+1) 10 (by omega) (by decide)
          change SerializedBody.delimiter F r n (u.val+1) ≤ SerializedBody.delimiter F r n 10 at h
          omega)]
      rw [old]
      apply frameFresh frame
      · change D 6 < D 10+3*r+j
        omega
      · change D 10+3*r+j ≤ D 12
        have h:=delimiterMono F r n 11 12 (by decide) le_rfl
        change D 11 ≤ D 12 at h
        have eq : D 11=D 10+3*r+4:=by dsimp only [D,SerializedBody.delimiter]; omega
        omega)
  have padEq : prefixFalse (stageTape T F r n 10 (3*r)) (D 10) (3*r+3)=stageTape T F r n 11 0 := by
    have full : 3*r+3=width r n 10:=rfl
    rw [full,← finish 10 (by decide) (by decide)]
    funext i
    dsimp only [D,prefixFalse,stageTape]
    split_ifs <;> first | rfl | (exfalso; omega)
  rw [padEq] at pad
  obtain ⟨tf,hf,padBack⟩:=partialTravel (fromPad k) T frame (b:=11) (f:=0) (by decide) (by decide) (by decide) (by decide) lower upper
  obtain ⟨tj,hj,padJoin⟩:=partialTravel (join8 k) T frame (b:=11) (f:=0) (by decide) (by decide) (by decide) (by decide) lower upper
  obtain ⟨t8,h8,c8⟩:=cloneStage (clone8 k) (stageTape T F r n 11 (0)) D
    (copyFrame frame lo P 0 11 (0) (by decide) (by decide) (by decide)
      (by dsimp only [width]; omega) lower upper)
  rw [fillPartial] at c8
  rw [show (0)+width r n 0=width r n 11 by dsimp only [width]; omega,finish 11 (by decide) (by decide)] at c8
  rw [partialInitial] at c0
  have path:=pAppend c0 (pAppend j0 (pAppend c1 (pAppend j1 (pAppend c2 (pAppend j2
    (pAppend c3 (pAppend j3 (pAppend c4 (pAppend j4 (pAppend c5 (pAppend j5
      (pAppend c6 (pAppend j6 (pAppend c7 (pAppend padGo (pAppend pad (pAppend padBack (pAppend padJoin c8))))))))))))))))))
  refine ⟨_,?_,path⟩
  dsimp only [width] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  nlinarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,p0,p1,p2,p3,p4,p5,p6,hp,hf,hj,Nat.zero_le P,Nat.zero_le n,Nat.zero_le r]
private theorem registers_after_setup {T F r n} (frame : Six T F r n) (values : Nat → Nat)
    (old : ∀ j,j < 6 → BankUnary (SerializedBody.delimiter F r n) T j (values j)) :
    Registers (SerializedBody.delimiter F r n) (stageTape T F r n 12 0)
      (fun j=>if j < 6 then values j else 0) := by
  refine registersMk (workspace_grid frame) ?_
  intro j hj i il iu
  by_cases oldBank : j < 6
  · dsimp only
    rw [if_pos oldBank]
    rw [partialOld (b:=12) (f:=0) (by decide) le_rfl (by
      have h:=delimiterMono F r n (j+1) 6 (by omega) (by decide)
      omega)]
    exact old j oldBank i il iu
  · have inside : ∃ u : Fin 12,6 ≤ u.val ∧ u.val < 12 ∧
        SerializedBody.delimiter F r n u.val < i ∧ i < SerializedBody.delimiter F r n (u.val+1) :=
      ⟨⟨j,hj⟩,by dsimp; omega,hj,il,iu⟩
    change Before F r n 12 i at inside
    dsimp only [stageTape]
    rw [if_neg (by omega),if_pos inside,if_neg oldBank,decide_eq_false (by omega)]
end FullIngressClosure
