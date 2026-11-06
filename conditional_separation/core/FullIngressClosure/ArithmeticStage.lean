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
      ("FullIngressClosure.Registers","FullIngressClosure","Registers","Registers"),
      ("FullIngressClosure.Registers","FullIngressClosure","Registers.grid","registerGrid"),
      ("FullIngressClosure.Registers","FullIngressClosure","transfer_registers","transferRegisters"),
      ("FullIngressClosure.Registers","FullIngressClosure","copy_registers","copyRegisters"),
      ("FullIngressClosure.Workspace","FullIngressClosure","setBank","setBank"),
      ("FullIngressClosure.Move","FullIngressClosure","Travel","Travel"),
      ("FullIngressClosure.Move","FullIngressClosure","travel","travel"),
      ("FullIngressClosure.Move","FullIngressClosure","Travel.right","trRight"),
      ("FullIngressClosure.Move","FullIngressClosure","Travel.left","trLeft"),
      ("FullIngressClosure.Move","FullIngressClosure","Travel.stay","trStay"),
      ("FullIngressClosure.Rows","FullIngressClosure","native_row","nativeRow"),
      ("FullIngressClosure.Certificates","FullIngressClosure","st","st"),
      ("FullIngressClosure.Certificates","FullIngressClosure","st_small","stSmall"),
      ("FullIngressClosure.Certificates","FullIngressClosure","safeNative","safeNative"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteR.nil","rrNil"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteR.next","rrNext"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteL.nil","rlNil"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteL.next","rlNext"),
      ("FullIngressClosure.ArithmeticCertificates","FullIngressClosure","copy0","copy0"),
      ("FullIngressClosure.ArithmeticCertificates","FullIngressClosure","copy1","copy1"),
      ("FullIngressClosure.ArithmeticCertificates","FullIngressClosure","copy2","copy2"),
      ("FullIngressClosure.ArithmeticCertificates","FullIngressClosure","move1","move1"),
      ("FullIngressClosure.ArithmeticCertificates","FullIngressClosure","move2","move2") ] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Nonunique literal arithmetic assembly term {mod}/{key}: {found.map Prod.fst}"
private def toEll (k : Nat) : Travel k 0 2 (st k 922) (st k 926) :=
  (trRight (rrNext (safeNative k 922 (by decide)) (safeNative k 923 (by decide))
      (by rw [stSmall k 922 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 923 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 923 (by decide),nativeRow]; rfl) (rrNext (safeNative k 924 (by decide)) (safeNative k 925 (by decide))
      (by rw [stSmall k 924 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 925 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 925 (by decide),nativeRow]; rfl) (rrNil 2 (st k 926)))))
private def toW (k : Nat) : Travel k 2 5 (st k 962) (st k 968) :=
  (trRight (rrNext (safeNative k 962 (by decide)) (safeNative k 963 (by decide))
      (by rw [stSmall k 962 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 963 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 963 (by decide),nativeRow]; rfl) (rrNext (safeNative k 964 (by decide)) (safeNative k 965 (by decide))
      (by rw [stSmall k 964 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 965 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 965 (by decide),nativeRow]; rfl) (rrNext (safeNative k 966 (by decide)) (safeNative k 967 (by decide))
      (by rw [stSmall k 966 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 967 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 967 (by decide),nativeRow]; rfl) (rrNil 5 (st k 968))))))
private def toCopy (k : Nat) : Travel k 5 3 (st k 984) (st k 988) :=
  (trLeft (rlNext (safeNative k 984 (by decide)) (safeNative k 985 (by decide))
      (by rw [stSmall k 984 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 985 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 985 (by decide),nativeRow]; rfl) (rlNext (safeNative k 986 (by decide)) (safeNative k 987 (by decide))
      (by rw [stSmall k 986 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 987 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 987 (by decide),nativeRow]; rfl) (rlNil 3 (st k 988)))))
private def toN (k : Nat) : Travel k 3 1 (st k 1172) (st k 1176) :=
  (trLeft (rlNext (safeNative k 1172 (by decide)) (safeNative k 1173 (by decide))
      (by rw [stSmall k 1172 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1173 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1173 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1174 (by decide)) (safeNative k 1175 (by decide))
      (by rw [stSmall k 1174 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1175 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1175 (by decide),nativeRow]; rfl) (rlNil 1 (st k 1176)))))
private def initialValues (g ell W j : Nat) : Nat :=
  if j=0 then g else if j=2 then ell else if j=5 then W else 0
private def arithmeticTape (T : Nat → Option Bool) (D : Nat → Nat) (g ell W : Nat) : Nat → Option Bool :=
  let T1:=setBank (setBank T D 6 g) D 11 0
  let T2:=setBank (setBank T1 D 2 0) D 9 ell
  let T3:=setBank (setBank T2 D 5 0) D 3 W
  let T4:=setBank (setBank T3 D 4 W) D 11 0
  setBank (setBank T4 D 11 W) D 5 0
private def finalValues (g ell W j : Nat) : Nat :=
  if j=0 ∨ j=6 then g else if j=9 then ell else if j=3 ∨ j=4 ∨ j=11 then W else 0
private theorem arithmetic_prepare {k lo P F r n} (T : Nat → Option Bool) (g ell W : Nat)
    (frame : Registers (SerializedBody.delimiter F r n) T (initialValues g ell W))
    (gfit : g ≤ r) (ellfit : ell ≤ r) (Wfit : W ≤ r)
    (lower : lo ≤ SerializedBody.delimiter F r n 0) (upper : SerializedBody.delimiter F r n 12 ≤ P) :
    ∃ t,t ≤ 1024*(g+ell+W+1)*(P+16) ∧ PPath k lo P t
      (pNode (st k 770) (SerializedBody.delimiter F r n 0) T)
      (pNode (st k 1176) (SerializedBody.delimiter F r n 1)
        (arithmeticTape T (SerializedBody.delimiter F r n) g ell W)) ∧
      Registers (SerializedBody.delimiter F r n) (arithmeticTape T (SerializedBody.delimiter F r n) g ell W)
        (finalValues g ell W) := by
  let D:=SerializedBody.delimiter F r n
  have length0 : D 1=D 0+r+1:=by dsimp only [D,SerializedBody.delimiter]; omega
  have length2 : D 3=D 2+r+1:=by dsimp only [D,SerializedBody.delimiter]; omega
  have length3 : D 4=D 3+r+1:=by dsimp only [D,SerializedBody.delimiter]; omega
  have length4 : D 5=D 4+r+1:=by dsimp only [D,SerializedBody.delimiter]; omega
  have length5 : D 6=D 5+r+1:=by dsimp only [D,SerializedBody.delimiter]; omega
  have length6 : D 7=D 6+r+1:=by dsimp only [D,SerializedBody.delimiter]; omega
  have length9 : D 10=D 9+2*r+1:=by dsimp only [D,SerializedBody.delimiter]; omega
  have length11 : D 12=D 11+r+1:=by dsimp only [D,SerializedBody.delimiter]; omega
  obtain ⟨t0,h0,c0,f0⟩:=copyRegisters (copy0 k) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) r r r length0 length6 length11 lower upper T
    (initialValues g ell W) frame gfit gfit gfit rfl rfl
  simp [initialValues] at c0 h0 f0
  obtain ⟨s0,q0,j0⟩:=travel (toEll k) (registerGrid f0) (by decide) (by decide) lower upper
  obtain ⟨t1,h1,c1,f1⟩:=transferRegisters (move1 k) (by decide) (by decide) (by decide)
    r (2*r) length2 length9 lower upper _ _ f0
    (by simpa [initialValues,Function.update_apply] using ellfit)
    (by simp [initialValues]; omega)
  simp [initialValues] at c1 h1 f1
  obtain ⟨s1,q1,j1⟩:=travel (toW k) (registerGrid f1) (by decide) (by decide) lower upper
  obtain ⟨t2,h2,c2,f2⟩:=transferRegisters (move2 k) (by decide) (by decide) (by decide)
    r r length5 length3 lower upper _ _ f1
    (by simpa [initialValues,Function.update_apply] using Wfit)
    (by simpa [initialValues,Function.update_apply,Nat.zero_add] using Wfit)
  simp [initialValues] at c2 h2 f2
  obtain ⟨s2,q2,j2⟩:=travel (toCopy k) (registerGrid f2) (by decide) (by decide) lower upper
  obtain ⟨t3,h3,c3,f3⟩:=copyRegisters (copy1 k) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) r r r length3 length4 length11 lower upper _ _ f2
    (by simpa [initialValues,Function.update_apply,Nat.zero_add] using Wfit)
    (by simpa [initialValues,Function.update_apply,Nat.zero_add] using Wfit)
    (by simpa [initialValues,Function.update_apply,Nat.zero_add] using Wfit)
    (by simp [initialValues]) (by simp)
  obtain ⟨t4,h4,c4,f4⟩:=copyRegisters (copy2 k) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) r r r length3 length11 length5 lower upper _ _ f3
    (by simpa [initialValues,Function.update_apply,Nat.zero_add] using Wfit)
    (by simpa [initialValues,Function.update_apply,Nat.zero_add] using Wfit)
    (by simpa [initialValues,Function.update_apply,Nat.zero_add] using Wfit)
    (by simp) (by simp)
  obtain ⟨s3,q3,j3⟩:=travel (toN k) (registerGrid f4) (by decide) (by decide) lower upper
  have resultValues : Function.update (Function.update
      (Function.update (Function.update
        (Function.update (Function.update
          (Function.update (Function.update
            (Function.update (Function.update (initialValues g ell W) 6 g) 11 0) 2 0) 9 ell) 5 0) 3 W) 4 W) 11 0) 11 W) 5 0=
      finalValues g ell W := by
    funext j
    by_cases h0 : j=0 <;> by_cases h2 : j=2 <;> by_cases h3 : j=3 <;> by_cases h4 : j=4 <;>
      by_cases h5 : j=5 <;> by_cases h6 : j=6 <;> by_cases h9 : j=9 <;> by_cases h11 : j=11 <;>
      simp [Function.update_apply,initialValues,finalValues,h0,h2,h3,h4,h5,h6,h9,h11]
  change t0 ≤ 128*(g+1)*(P+16) at h0
  change t1 ≤ 32*(ell+1)*(P+16) at h1
  change t2 ≤ 32*(W+1)*(P+16) at h2
  change t3 ≤ 128*(W+1)*(P+16) at h3
  change t4 ≤ 128*(W+1)*(P+16) at h4
  have path:=pAppend c0 (pAppend j0 (pAppend c1 (pAppend j1 (pAppend c2 (pAppend j2 (pAppend c3 (pAppend c4 j3)))))))
  refine ⟨_,?_,path,?_⟩
  · nlinarith only [h0,h1,h2,h3,h4,q0,q1,q2,q3,Nat.zero_le g,Nat.zero_le ell,Nat.zero_le W,Nat.zero_le P]
  · change Registers D _ _ at f4 ⊢
    rw [← resultValues]
    exact f4
end FullIngressClosure
