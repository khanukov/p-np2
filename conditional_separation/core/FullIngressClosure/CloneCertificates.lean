import FullIngressClosure.CloneStage
import FullIngressClosure.Certificates
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  for (mod,key,aliasName) in [
      ("Rows","native_row","nativeRow"),("Certificates","st","st"),
      ("Certificates","st_small","stSmall"),("Certificates","safeNative","safeNative"),
      ("Clone","CopyBranch","CopyBranch"),("Clone","CopyBranch.mk","branchMk"),
      ("Clone","CopyRows","CopyRows"),("Clone","CopyRows.mk","copyMk"),
      ("Paths","RouteR.nil","rrNil"),("Paths","RouteR.next","rrNext"),
      ("Paths","RouteL.nil","rlNil"),("Paths","RouteL.next","rlNext")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private.FullIngressClosure."++mod++".") && n.toString.endsWith (".FullIngressClosure."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Nonunique literal clone certificate term {mod}/{key}: {found.map Prod.fst}"
private def clone0_false (k : Nat) : CopyBranch k 0 6 (st k 1) false := by
  refine branchMk (st k 2) (st k 3) (st k 13) (st k 14) (st k 15) (st k 16) (st k 17) (st k 27) (st k 28)
    (safeNative k 2 (by decide)) (safeNative k 13 (by decide)) (safeNative k 14 (by decide)) (safeNative k 15 (by decide)) (safeNative k 16 (by decide)) (safeNative k 27 (by decide)) (safeNative k 28 (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 1 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 2 (by decide),nativeRow]; rfl)
  · rw [stSmall k 2 (by decide),nativeRow]; rfl
  · exact (rrNext (safeNative k 3 (by decide)) (safeNative k 4 (by decide))
      (by rw [stSmall k 3 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 4 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 4 (by decide),nativeRow]; rfl) (rrNext (safeNative k 5 (by decide)) (safeNative k 6 (by decide))
      (by rw [stSmall k 5 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 6 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 6 (by decide),nativeRow]; rfl) (rrNext (safeNative k 7 (by decide)) (safeNative k 8 (by decide))
      (by rw [stSmall k 7 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 8 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 8 (by decide),nativeRow]; rfl) (rrNext (safeNative k 9 (by decide)) (safeNative k 10 (by decide))
      (by rw [stSmall k 9 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 10 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 10 (by decide),nativeRow]; rfl) (rrNext (safeNative k 11 (by decide)) (safeNative k 12 (by decide))
      (by rw [stSmall k 11 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 12 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 12 (by decide),nativeRow]; rfl) (rrNil 6 (st k 13)))))))
  · rw [stSmall k 13 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 14 (by decide),nativeRow]; rfl)
  · rw [stSmall k 14 (by decide),nativeRow]; rfl
  · rw [stSmall k 15 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 16 (by decide),nativeRow]; rfl)
  · rw [stSmall k 16 (by decide),nativeRow]; rfl
  · exact (rlNext (safeNative k 17 (by decide)) (safeNative k 18 (by decide))
      (by rw [stSmall k 17 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 18 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 18 (by decide),nativeRow]; rfl) (rlNext (safeNative k 19 (by decide)) (safeNative k 20 (by decide))
      (by rw [stSmall k 19 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 20 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 20 (by decide),nativeRow]; rfl) (rlNext (safeNative k 21 (by decide)) (safeNative k 22 (by decide))
      (by rw [stSmall k 21 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 22 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 22 (by decide),nativeRow]; rfl) (rlNext (safeNative k 23 (by decide)) (safeNative k 24 (by decide))
      (by rw [stSmall k 23 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 24 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 24 (by decide),nativeRow]; rfl) (rlNext (safeNative k 25 (by decide)) (safeNative k 26 (by decide))
      (by rw [stSmall k 25 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 26 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 26 (by decide),nativeRow]; rfl) (rlNil 1 (st k 27)))))))
  · rw [stSmall k 27 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 28 (by decide),nativeRow]; rfl)
  · rw [stSmall k 28 (by decide),nativeRow]; rfl
private def clone0_true (k : Nat) : CopyBranch k 0 6 (st k 1) true := by
  refine branchMk (st k 29) (st k 30) (st k 40) (st k 41) (st k 42) (st k 43) (st k 44) (st k 54) (st k 55)
    (safeNative k 29 (by decide)) (safeNative k 40 (by decide)) (safeNative k 41 (by decide)) (safeNative k 42 (by decide)) (safeNative k 43 (by decide)) (safeNative k 54 (by decide)) (safeNative k 55 (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 1 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 29 (by decide),nativeRow]; rfl)
  · rw [stSmall k 29 (by decide),nativeRow]; rfl
  · exact (rrNext (safeNative k 30 (by decide)) (safeNative k 31 (by decide))
      (by rw [stSmall k 30 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 31 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 31 (by decide),nativeRow]; rfl) (rrNext (safeNative k 32 (by decide)) (safeNative k 33 (by decide))
      (by rw [stSmall k 32 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 33 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 33 (by decide),nativeRow]; rfl) (rrNext (safeNative k 34 (by decide)) (safeNative k 35 (by decide))
      (by rw [stSmall k 34 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 35 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 35 (by decide),nativeRow]; rfl) (rrNext (safeNative k 36 (by decide)) (safeNative k 37 (by decide))
      (by rw [stSmall k 36 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 37 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 37 (by decide),nativeRow]; rfl) (rrNext (safeNative k 38 (by decide)) (safeNative k 39 (by decide))
      (by rw [stSmall k 38 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 39 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 39 (by decide),nativeRow]; rfl) (rrNil 6 (st k 40)))))))
  · rw [stSmall k 40 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 41 (by decide),nativeRow]; rfl)
  · rw [stSmall k 41 (by decide),nativeRow]; rfl
  · rw [stSmall k 42 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 43 (by decide),nativeRow]; rfl)
  · rw [stSmall k 43 (by decide),nativeRow]; rfl
  · exact (rlNext (safeNative k 44 (by decide)) (safeNative k 45 (by decide))
      (by rw [stSmall k 44 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 45 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 45 (by decide),nativeRow]; rfl) (rlNext (safeNative k 46 (by decide)) (safeNative k 47 (by decide))
      (by rw [stSmall k 46 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 47 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 47 (by decide),nativeRow]; rfl) (rlNext (safeNative k 48 (by decide)) (safeNative k 49 (by decide))
      (by rw [stSmall k 48 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 49 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 49 (by decide),nativeRow]; rfl) (rlNext (safeNative k 50 (by decide)) (safeNative k 51 (by decide))
      (by rw [stSmall k 50 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 51 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 51 (by decide),nativeRow]; rfl) (rlNext (safeNative k 52 (by decide)) (safeNative k 53 (by decide))
      (by rw [stSmall k 52 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 53 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 53 (by decide),nativeRow]; rfl) (rlNil 1 (st k 54)))))))
  · rw [stSmall k 54 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 55 (by decide),nativeRow]; rfl)
  · rw [stSmall k 55 (by decide),nativeRow]; rfl
private def clone0 (k : Nat) : CopyRows k 0 6 (st k 0) (st k 1) (st k 56) (st k 57) := by
  refine copyMk (safeNative k 0 (by decide)) (safeNative k 1 (by decide))
    (safeNative k 56 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 0 (by decide),nativeRow]; rfl
  · intro bit; cases bit
    · exact clone0_false k
    · exact clone0_true k
  · rw [stSmall k 1 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 56 (by decide),nativeRow]; rfl)
  · rw [stSmall k 56 (by decide),nativeRow]; rfl
private def clone1_false (k : Nat) : CopyBranch k 0 7 (st k 59) false := by
  refine branchMk (st k 60) (st k 61) (st k 73) (st k 74) (st k 75) (st k 76) (st k 77) (st k 89) (st k 90)
    (safeNative k 60 (by decide)) (safeNative k 73 (by decide)) (safeNative k 74 (by decide)) (safeNative k 75 (by decide)) (safeNative k 76 (by decide)) (safeNative k 89 (by decide)) (safeNative k 90 (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 59 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 60 (by decide),nativeRow]; rfl)
  · rw [stSmall k 60 (by decide),nativeRow]; rfl
  · exact (rrNext (safeNative k 61 (by decide)) (safeNative k 62 (by decide))
      (by rw [stSmall k 61 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 62 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 62 (by decide),nativeRow]; rfl) (rrNext (safeNative k 63 (by decide)) (safeNative k 64 (by decide))
      (by rw [stSmall k 63 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 64 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 64 (by decide),nativeRow]; rfl) (rrNext (safeNative k 65 (by decide)) (safeNative k 66 (by decide))
      (by rw [stSmall k 65 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 66 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 66 (by decide),nativeRow]; rfl) (rrNext (safeNative k 67 (by decide)) (safeNative k 68 (by decide))
      (by rw [stSmall k 67 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 68 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 68 (by decide),nativeRow]; rfl) (rrNext (safeNative k 69 (by decide)) (safeNative k 70 (by decide))
      (by rw [stSmall k 69 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 70 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 70 (by decide),nativeRow]; rfl) (rrNext (safeNative k 71 (by decide)) (safeNative k 72 (by decide))
      (by rw [stSmall k 71 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 72 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 72 (by decide),nativeRow]; rfl) (rrNil 7 (st k 73))))))))
  · rw [stSmall k 73 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 74 (by decide),nativeRow]; rfl)
  · rw [stSmall k 74 (by decide),nativeRow]; rfl
  · rw [stSmall k 75 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 76 (by decide),nativeRow]; rfl)
  · rw [stSmall k 76 (by decide),nativeRow]; rfl
  · exact (rlNext (safeNative k 77 (by decide)) (safeNative k 78 (by decide))
      (by rw [stSmall k 77 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 78 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 78 (by decide),nativeRow]; rfl) (rlNext (safeNative k 79 (by decide)) (safeNative k 80 (by decide))
      (by rw [stSmall k 79 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 80 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 80 (by decide),nativeRow]; rfl) (rlNext (safeNative k 81 (by decide)) (safeNative k 82 (by decide))
      (by rw [stSmall k 81 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 82 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 82 (by decide),nativeRow]; rfl) (rlNext (safeNative k 83 (by decide)) (safeNative k 84 (by decide))
      (by rw [stSmall k 83 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 84 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 84 (by decide),nativeRow]; rfl) (rlNext (safeNative k 85 (by decide)) (safeNative k 86 (by decide))
      (by rw [stSmall k 85 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 86 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 86 (by decide),nativeRow]; rfl) (rlNext (safeNative k 87 (by decide)) (safeNative k 88 (by decide))
      (by rw [stSmall k 87 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 88 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 88 (by decide),nativeRow]; rfl) (rlNil 1 (st k 89))))))))
  · rw [stSmall k 89 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 90 (by decide),nativeRow]; rfl)
  · rw [stSmall k 90 (by decide),nativeRow]; rfl
private def clone1_true (k : Nat) : CopyBranch k 0 7 (st k 59) true := by
  refine branchMk (st k 91) (st k 92) (st k 104) (st k 105) (st k 106) (st k 107) (st k 108) (st k 120) (st k 121)
    (safeNative k 91 (by decide)) (safeNative k 104 (by decide)) (safeNative k 105 (by decide)) (safeNative k 106 (by decide)) (safeNative k 107 (by decide)) (safeNative k 120 (by decide)) (safeNative k 121 (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 59 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 91 (by decide),nativeRow]; rfl)
  · rw [stSmall k 91 (by decide),nativeRow]; rfl
  · exact (rrNext (safeNative k 92 (by decide)) (safeNative k 93 (by decide))
      (by rw [stSmall k 92 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 93 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 93 (by decide),nativeRow]; rfl) (rrNext (safeNative k 94 (by decide)) (safeNative k 95 (by decide))
      (by rw [stSmall k 94 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 95 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 95 (by decide),nativeRow]; rfl) (rrNext (safeNative k 96 (by decide)) (safeNative k 97 (by decide))
      (by rw [stSmall k 96 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 97 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 97 (by decide),nativeRow]; rfl) (rrNext (safeNative k 98 (by decide)) (safeNative k 99 (by decide))
      (by rw [stSmall k 98 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 99 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 99 (by decide),nativeRow]; rfl) (rrNext (safeNative k 100 (by decide)) (safeNative k 101 (by decide))
      (by rw [stSmall k 100 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 101 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 101 (by decide),nativeRow]; rfl) (rrNext (safeNative k 102 (by decide)) (safeNative k 103 (by decide))
      (by rw [stSmall k 102 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 103 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 103 (by decide),nativeRow]; rfl) (rrNil 7 (st k 104))))))))
  · rw [stSmall k 104 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 105 (by decide),nativeRow]; rfl)
  · rw [stSmall k 105 (by decide),nativeRow]; rfl
  · rw [stSmall k 106 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 107 (by decide),nativeRow]; rfl)
  · rw [stSmall k 107 (by decide),nativeRow]; rfl
  · exact (rlNext (safeNative k 108 (by decide)) (safeNative k 109 (by decide))
      (by rw [stSmall k 108 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 109 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 109 (by decide),nativeRow]; rfl) (rlNext (safeNative k 110 (by decide)) (safeNative k 111 (by decide))
      (by rw [stSmall k 110 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 111 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 111 (by decide),nativeRow]; rfl) (rlNext (safeNative k 112 (by decide)) (safeNative k 113 (by decide))
      (by rw [stSmall k 112 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 113 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 113 (by decide),nativeRow]; rfl) (rlNext (safeNative k 114 (by decide)) (safeNative k 115 (by decide))
      (by rw [stSmall k 114 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 115 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 115 (by decide),nativeRow]; rfl) (rlNext (safeNative k 116 (by decide)) (safeNative k 117 (by decide))
      (by rw [stSmall k 116 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 117 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 117 (by decide),nativeRow]; rfl) (rlNext (safeNative k 118 (by decide)) (safeNative k 119 (by decide))
      (by rw [stSmall k 118 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 119 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 119 (by decide),nativeRow]; rfl) (rlNil 1 (st k 120))))))))
  · rw [stSmall k 120 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 121 (by decide),nativeRow]; rfl)
  · rw [stSmall k 121 (by decide),nativeRow]; rfl
private def clone1 (k : Nat) : CopyRows k 0 7 (st k 58) (st k 59) (st k 122) (st k 123) := by
  refine copyMk (safeNative k 58 (by decide)) (safeNative k 59 (by decide))
    (safeNative k 122 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 58 (by decide),nativeRow]; rfl
  · intro bit; cases bit
    · exact clone1_false k
    · exact clone1_true k
  · rw [stSmall k 59 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 122 (by decide),nativeRow]; rfl)
  · rw [stSmall k 122 (by decide),nativeRow]; rfl
private def clone2_false (k : Nat) : CopyBranch k 1 8 (st k 126) false := by
  refine branchMk (st k 127) (st k 128) (st k 140) (st k 141) (st k 142) (st k 143) (st k 144) (st k 156) (st k 157)
    (safeNative k 127 (by decide)) (safeNative k 140 (by decide)) (safeNative k 141 (by decide)) (safeNative k 142 (by decide)) (safeNative k 143 (by decide)) (safeNative k 156 (by decide)) (safeNative k 157 (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 126 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 127 (by decide),nativeRow]; rfl)
  · rw [stSmall k 127 (by decide),nativeRow]; rfl
  · exact (rrNext (safeNative k 128 (by decide)) (safeNative k 129 (by decide))
      (by rw [stSmall k 128 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 129 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 129 (by decide),nativeRow]; rfl) (rrNext (safeNative k 130 (by decide)) (safeNative k 131 (by decide))
      (by rw [stSmall k 130 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 131 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 131 (by decide),nativeRow]; rfl) (rrNext (safeNative k 132 (by decide)) (safeNative k 133 (by decide))
      (by rw [stSmall k 132 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 133 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 133 (by decide),nativeRow]; rfl) (rrNext (safeNative k 134 (by decide)) (safeNative k 135 (by decide))
      (by rw [stSmall k 134 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 135 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 135 (by decide),nativeRow]; rfl) (rrNext (safeNative k 136 (by decide)) (safeNative k 137 (by decide))
      (by rw [stSmall k 136 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 137 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 137 (by decide),nativeRow]; rfl) (rrNext (safeNative k 138 (by decide)) (safeNative k 139 (by decide))
      (by rw [stSmall k 138 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 139 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 139 (by decide),nativeRow]; rfl) (rrNil 8 (st k 140))))))))
  · rw [stSmall k 140 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 141 (by decide),nativeRow]; rfl)
  · rw [stSmall k 141 (by decide),nativeRow]; rfl
  · rw [stSmall k 142 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 143 (by decide),nativeRow]; rfl)
  · rw [stSmall k 143 (by decide),nativeRow]; rfl
  · exact (rlNext (safeNative k 144 (by decide)) (safeNative k 145 (by decide))
      (by rw [stSmall k 144 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 145 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 145 (by decide),nativeRow]; rfl) (rlNext (safeNative k 146 (by decide)) (safeNative k 147 (by decide))
      (by rw [stSmall k 146 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 147 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 147 (by decide),nativeRow]; rfl) (rlNext (safeNative k 148 (by decide)) (safeNative k 149 (by decide))
      (by rw [stSmall k 148 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 149 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 149 (by decide),nativeRow]; rfl) (rlNext (safeNative k 150 (by decide)) (safeNative k 151 (by decide))
      (by rw [stSmall k 150 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 151 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 151 (by decide),nativeRow]; rfl) (rlNext (safeNative k 152 (by decide)) (safeNative k 153 (by decide))
      (by rw [stSmall k 152 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 153 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 153 (by decide),nativeRow]; rfl) (rlNext (safeNative k 154 (by decide)) (safeNative k 155 (by decide))
      (by rw [stSmall k 154 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 155 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 155 (by decide),nativeRow]; rfl) (rlNil 2 (st k 156))))))))
  · rw [stSmall k 156 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 157 (by decide),nativeRow]; rfl)
  · rw [stSmall k 157 (by decide),nativeRow]; rfl
private def clone2_true (k : Nat) : CopyBranch k 1 8 (st k 126) true := by
  refine branchMk (st k 158) (st k 159) (st k 171) (st k 172) (st k 173) (st k 174) (st k 175) (st k 187) (st k 188)
    (safeNative k 158 (by decide)) (safeNative k 171 (by decide)) (safeNative k 172 (by decide)) (safeNative k 173 (by decide)) (safeNative k 174 (by decide)) (safeNative k 187 (by decide)) (safeNative k 188 (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 126 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 158 (by decide),nativeRow]; rfl)
  · rw [stSmall k 158 (by decide),nativeRow]; rfl
  · exact (rrNext (safeNative k 159 (by decide)) (safeNative k 160 (by decide))
      (by rw [stSmall k 159 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 160 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 160 (by decide),nativeRow]; rfl) (rrNext (safeNative k 161 (by decide)) (safeNative k 162 (by decide))
      (by rw [stSmall k 161 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 162 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 162 (by decide),nativeRow]; rfl) (rrNext (safeNative k 163 (by decide)) (safeNative k 164 (by decide))
      (by rw [stSmall k 163 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 164 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 164 (by decide),nativeRow]; rfl) (rrNext (safeNative k 165 (by decide)) (safeNative k 166 (by decide))
      (by rw [stSmall k 165 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 166 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 166 (by decide),nativeRow]; rfl) (rrNext (safeNative k 167 (by decide)) (safeNative k 168 (by decide))
      (by rw [stSmall k 167 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 168 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 168 (by decide),nativeRow]; rfl) (rrNext (safeNative k 169 (by decide)) (safeNative k 170 (by decide))
      (by rw [stSmall k 169 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 170 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 170 (by decide),nativeRow]; rfl) (rrNil 8 (st k 171))))))))
  · rw [stSmall k 171 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 172 (by decide),nativeRow]; rfl)
  · rw [stSmall k 172 (by decide),nativeRow]; rfl
  · rw [stSmall k 173 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 174 (by decide),nativeRow]; rfl)
  · rw [stSmall k 174 (by decide),nativeRow]; rfl
  · exact (rlNext (safeNative k 175 (by decide)) (safeNative k 176 (by decide))
      (by rw [stSmall k 175 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 176 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 176 (by decide),nativeRow]; rfl) (rlNext (safeNative k 177 (by decide)) (safeNative k 178 (by decide))
      (by rw [stSmall k 177 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 178 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 178 (by decide),nativeRow]; rfl) (rlNext (safeNative k 179 (by decide)) (safeNative k 180 (by decide))
      (by rw [stSmall k 179 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 180 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 180 (by decide),nativeRow]; rfl) (rlNext (safeNative k 181 (by decide)) (safeNative k 182 (by decide))
      (by rw [stSmall k 181 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 182 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 182 (by decide),nativeRow]; rfl) (rlNext (safeNative k 183 (by decide)) (safeNative k 184 (by decide))
      (by rw [stSmall k 183 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 184 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 184 (by decide),nativeRow]; rfl) (rlNext (safeNative k 185 (by decide)) (safeNative k 186 (by decide))
      (by rw [stSmall k 185 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 186 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 186 (by decide),nativeRow]; rfl) (rlNil 2 (st k 187))))))))
  · rw [stSmall k 187 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 188 (by decide),nativeRow]; rfl)
  · rw [stSmall k 188 (by decide),nativeRow]; rfl
private def clone2 (k : Nat) : CopyRows k 1 8 (st k 125) (st k 126) (st k 189) (st k 190) := by
  refine copyMk (safeNative k 125 (by decide)) (safeNative k 126 (by decide))
    (safeNative k 189 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 125 (by decide),nativeRow]; rfl
  · intro bit; cases bit
    · exact clone2_false k
    · exact clone2_true k
  · rw [stSmall k 126 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 189 (by decide),nativeRow]; rfl)
  · rw [stSmall k 189 (by decide),nativeRow]; rfl
private def clone3_false (k : Nat) : CopyBranch k 0 9 (st k 193) false := by
  refine branchMk (st k 194) (st k 195) (st k 211) (st k 212) (st k 213) (st k 214) (st k 215) (st k 231) (st k 232)
    (safeNative k 194 (by decide)) (safeNative k 211 (by decide)) (safeNative k 212 (by decide)) (safeNative k 213 (by decide)) (safeNative k 214 (by decide)) (safeNative k 231 (by decide)) (safeNative k 232 (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 193 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 194 (by decide),nativeRow]; rfl)
  · rw [stSmall k 194 (by decide),nativeRow]; rfl
  · exact (rrNext (safeNative k 195 (by decide)) (safeNative k 196 (by decide))
      (by rw [stSmall k 195 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 196 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 196 (by decide),nativeRow]; rfl) (rrNext (safeNative k 197 (by decide)) (safeNative k 198 (by decide))
      (by rw [stSmall k 197 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 198 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 198 (by decide),nativeRow]; rfl) (rrNext (safeNative k 199 (by decide)) (safeNative k 200 (by decide))
      (by rw [stSmall k 199 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 200 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 200 (by decide),nativeRow]; rfl) (rrNext (safeNative k 201 (by decide)) (safeNative k 202 (by decide))
      (by rw [stSmall k 201 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 202 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 202 (by decide),nativeRow]; rfl) (rrNext (safeNative k 203 (by decide)) (safeNative k 204 (by decide))
      (by rw [stSmall k 203 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 204 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 204 (by decide),nativeRow]; rfl) (rrNext (safeNative k 205 (by decide)) (safeNative k 206 (by decide))
      (by rw [stSmall k 205 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 206 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 206 (by decide),nativeRow]; rfl) (rrNext (safeNative k 207 (by decide)) (safeNative k 208 (by decide))
      (by rw [stSmall k 207 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 208 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 208 (by decide),nativeRow]; rfl) (rrNext (safeNative k 209 (by decide)) (safeNative k 210 (by decide))
      (by rw [stSmall k 209 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 210 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 210 (by decide),nativeRow]; rfl) (rrNil 9 (st k 211))))))))))
  · rw [stSmall k 211 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 212 (by decide),nativeRow]; rfl)
  · rw [stSmall k 212 (by decide),nativeRow]; rfl
  · rw [stSmall k 213 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 214 (by decide),nativeRow]; rfl)
  · rw [stSmall k 214 (by decide),nativeRow]; rfl
  · exact (rlNext (safeNative k 215 (by decide)) (safeNative k 216 (by decide))
      (by rw [stSmall k 215 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 216 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 216 (by decide),nativeRow]; rfl) (rlNext (safeNative k 217 (by decide)) (safeNative k 218 (by decide))
      (by rw [stSmall k 217 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 218 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 218 (by decide),nativeRow]; rfl) (rlNext (safeNative k 219 (by decide)) (safeNative k 220 (by decide))
      (by rw [stSmall k 219 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 220 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 220 (by decide),nativeRow]; rfl) (rlNext (safeNative k 221 (by decide)) (safeNative k 222 (by decide))
      (by rw [stSmall k 221 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 222 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 222 (by decide),nativeRow]; rfl) (rlNext (safeNative k 223 (by decide)) (safeNative k 224 (by decide))
      (by rw [stSmall k 223 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 224 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 224 (by decide),nativeRow]; rfl) (rlNext (safeNative k 225 (by decide)) (safeNative k 226 (by decide))
      (by rw [stSmall k 225 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 226 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 226 (by decide),nativeRow]; rfl) (rlNext (safeNative k 227 (by decide)) (safeNative k 228 (by decide))
      (by rw [stSmall k 227 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 228 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 228 (by decide),nativeRow]; rfl) (rlNext (safeNative k 229 (by decide)) (safeNative k 230 (by decide))
      (by rw [stSmall k 229 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 230 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 230 (by decide),nativeRow]; rfl) (rlNil 1 (st k 231))))))))))
  · rw [stSmall k 231 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 232 (by decide),nativeRow]; rfl)
  · rw [stSmall k 232 (by decide),nativeRow]; rfl
private def clone3_true (k : Nat) : CopyBranch k 0 9 (st k 193) true := by
  refine branchMk (st k 233) (st k 234) (st k 250) (st k 251) (st k 252) (st k 253) (st k 254) (st k 270) (st k 271)
    (safeNative k 233 (by decide)) (safeNative k 250 (by decide)) (safeNative k 251 (by decide)) (safeNative k 252 (by decide)) (safeNative k 253 (by decide)) (safeNative k 270 (by decide)) (safeNative k 271 (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 193 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 233 (by decide),nativeRow]; rfl)
  · rw [stSmall k 233 (by decide),nativeRow]; rfl
  · exact (rrNext (safeNative k 234 (by decide)) (safeNative k 235 (by decide))
      (by rw [stSmall k 234 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 235 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 235 (by decide),nativeRow]; rfl) (rrNext (safeNative k 236 (by decide)) (safeNative k 237 (by decide))
      (by rw [stSmall k 236 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 237 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 237 (by decide),nativeRow]; rfl) (rrNext (safeNative k 238 (by decide)) (safeNative k 239 (by decide))
      (by rw [stSmall k 238 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 239 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 239 (by decide),nativeRow]; rfl) (rrNext (safeNative k 240 (by decide)) (safeNative k 241 (by decide))
      (by rw [stSmall k 240 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 241 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 241 (by decide),nativeRow]; rfl) (rrNext (safeNative k 242 (by decide)) (safeNative k 243 (by decide))
      (by rw [stSmall k 242 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 243 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 243 (by decide),nativeRow]; rfl) (rrNext (safeNative k 244 (by decide)) (safeNative k 245 (by decide))
      (by rw [stSmall k 244 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 245 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 245 (by decide),nativeRow]; rfl) (rrNext (safeNative k 246 (by decide)) (safeNative k 247 (by decide))
      (by rw [stSmall k 246 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 247 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 247 (by decide),nativeRow]; rfl) (rrNext (safeNative k 248 (by decide)) (safeNative k 249 (by decide))
      (by rw [stSmall k 248 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 249 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 249 (by decide),nativeRow]; rfl) (rrNil 9 (st k 250))))))))))
  · rw [stSmall k 250 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 251 (by decide),nativeRow]; rfl)
  · rw [stSmall k 251 (by decide),nativeRow]; rfl
  · rw [stSmall k 252 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 253 (by decide),nativeRow]; rfl)
  · rw [stSmall k 253 (by decide),nativeRow]; rfl
  · exact (rlNext (safeNative k 254 (by decide)) (safeNative k 255 (by decide))
      (by rw [stSmall k 254 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 255 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 255 (by decide),nativeRow]; rfl) (rlNext (safeNative k 256 (by decide)) (safeNative k 257 (by decide))
      (by rw [stSmall k 256 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 257 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 257 (by decide),nativeRow]; rfl) (rlNext (safeNative k 258 (by decide)) (safeNative k 259 (by decide))
      (by rw [stSmall k 258 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 259 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 259 (by decide),nativeRow]; rfl) (rlNext (safeNative k 260 (by decide)) (safeNative k 261 (by decide))
      (by rw [stSmall k 260 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 261 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 261 (by decide),nativeRow]; rfl) (rlNext (safeNative k 262 (by decide)) (safeNative k 263 (by decide))
      (by rw [stSmall k 262 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 263 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 263 (by decide),nativeRow]; rfl) (rlNext (safeNative k 264 (by decide)) (safeNative k 265 (by decide))
      (by rw [stSmall k 264 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 265 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 265 (by decide),nativeRow]; rfl) (rlNext (safeNative k 266 (by decide)) (safeNative k 267 (by decide))
      (by rw [stSmall k 266 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 267 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 267 (by decide),nativeRow]; rfl) (rlNext (safeNative k 268 (by decide)) (safeNative k 269 (by decide))
      (by rw [stSmall k 268 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 269 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 269 (by decide),nativeRow]; rfl) (rlNil 1 (st k 270))))))))))
  · rw [stSmall k 270 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 271 (by decide),nativeRow]; rfl)
  · rw [stSmall k 271 (by decide),nativeRow]; rfl
private def clone3 (k : Nat) : CopyRows k 0 9 (st k 192) (st k 193) (st k 272) (st k 273) := by
  refine copyMk (safeNative k 192 (by decide)) (safeNative k 193 (by decide))
    (safeNative k 272 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 192 (by decide),nativeRow]; rfl
  · intro bit; cases bit
    · exact clone3_false k
    · exact clone3_true k
  · rw [stSmall k 193 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 272 (by decide),nativeRow]; rfl)
  · rw [stSmall k 272 (by decide),nativeRow]; rfl
private def clone4_false (k : Nat) : CopyBranch k 0 9 (st k 275) false := by
  refine branchMk (st k 276) (st k 277) (st k 293) (st k 294) (st k 295) (st k 296) (st k 297) (st k 313) (st k 314)
    (safeNative k 276 (by decide)) (safeNative k 293 (by decide)) (safeNative k 294 (by decide)) (safeNative k 295 (by decide)) (safeNative k 296 (by decide)) (safeNative k 313 (by decide)) (safeNative k 314 (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 275 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 276 (by decide),nativeRow]; rfl)
  · rw [stSmall k 276 (by decide),nativeRow]; rfl
  · exact (rrNext (safeNative k 277 (by decide)) (safeNative k 278 (by decide))
      (by rw [stSmall k 277 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 278 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 278 (by decide),nativeRow]; rfl) (rrNext (safeNative k 279 (by decide)) (safeNative k 280 (by decide))
      (by rw [stSmall k 279 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 280 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 280 (by decide),nativeRow]; rfl) (rrNext (safeNative k 281 (by decide)) (safeNative k 282 (by decide))
      (by rw [stSmall k 281 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 282 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 282 (by decide),nativeRow]; rfl) (rrNext (safeNative k 283 (by decide)) (safeNative k 284 (by decide))
      (by rw [stSmall k 283 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 284 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 284 (by decide),nativeRow]; rfl) (rrNext (safeNative k 285 (by decide)) (safeNative k 286 (by decide))
      (by rw [stSmall k 285 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 286 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 286 (by decide),nativeRow]; rfl) (rrNext (safeNative k 287 (by decide)) (safeNative k 288 (by decide))
      (by rw [stSmall k 287 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 288 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 288 (by decide),nativeRow]; rfl) (rrNext (safeNative k 289 (by decide)) (safeNative k 290 (by decide))
      (by rw [stSmall k 289 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 290 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 290 (by decide),nativeRow]; rfl) (rrNext (safeNative k 291 (by decide)) (safeNative k 292 (by decide))
      (by rw [stSmall k 291 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 292 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 292 (by decide),nativeRow]; rfl) (rrNil 9 (st k 293))))))))))
  · rw [stSmall k 293 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 294 (by decide),nativeRow]; rfl)
  · rw [stSmall k 294 (by decide),nativeRow]; rfl
  · rw [stSmall k 295 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 296 (by decide),nativeRow]; rfl)
  · rw [stSmall k 296 (by decide),nativeRow]; rfl
  · exact (rlNext (safeNative k 297 (by decide)) (safeNative k 298 (by decide))
      (by rw [stSmall k 297 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 298 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 298 (by decide),nativeRow]; rfl) (rlNext (safeNative k 299 (by decide)) (safeNative k 300 (by decide))
      (by rw [stSmall k 299 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 300 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 300 (by decide),nativeRow]; rfl) (rlNext (safeNative k 301 (by decide)) (safeNative k 302 (by decide))
      (by rw [stSmall k 301 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 302 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 302 (by decide),nativeRow]; rfl) (rlNext (safeNative k 303 (by decide)) (safeNative k 304 (by decide))
      (by rw [stSmall k 303 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 304 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 304 (by decide),nativeRow]; rfl) (rlNext (safeNative k 305 (by decide)) (safeNative k 306 (by decide))
      (by rw [stSmall k 305 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 306 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 306 (by decide),nativeRow]; rfl) (rlNext (safeNative k 307 (by decide)) (safeNative k 308 (by decide))
      (by rw [stSmall k 307 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 308 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 308 (by decide),nativeRow]; rfl) (rlNext (safeNative k 309 (by decide)) (safeNative k 310 (by decide))
      (by rw [stSmall k 309 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 310 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 310 (by decide),nativeRow]; rfl) (rlNext (safeNative k 311 (by decide)) (safeNative k 312 (by decide))
      (by rw [stSmall k 311 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 312 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 312 (by decide),nativeRow]; rfl) (rlNil 1 (st k 313))))))))))
  · rw [stSmall k 313 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 314 (by decide),nativeRow]; rfl)
  · rw [stSmall k 314 (by decide),nativeRow]; rfl
private def clone4_true (k : Nat) : CopyBranch k 0 9 (st k 275) true := by
  refine branchMk (st k 315) (st k 316) (st k 332) (st k 333) (st k 334) (st k 335) (st k 336) (st k 352) (st k 353)
    (safeNative k 315 (by decide)) (safeNative k 332 (by decide)) (safeNative k 333 (by decide)) (safeNative k 334 (by decide)) (safeNative k 335 (by decide)) (safeNative k 352 (by decide)) (safeNative k 353 (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 275 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 315 (by decide),nativeRow]; rfl)
  · rw [stSmall k 315 (by decide),nativeRow]; rfl
  · exact (rrNext (safeNative k 316 (by decide)) (safeNative k 317 (by decide))
      (by rw [stSmall k 316 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 317 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 317 (by decide),nativeRow]; rfl) (rrNext (safeNative k 318 (by decide)) (safeNative k 319 (by decide))
      (by rw [stSmall k 318 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 319 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 319 (by decide),nativeRow]; rfl) (rrNext (safeNative k 320 (by decide)) (safeNative k 321 (by decide))
      (by rw [stSmall k 320 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 321 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 321 (by decide),nativeRow]; rfl) (rrNext (safeNative k 322 (by decide)) (safeNative k 323 (by decide))
      (by rw [stSmall k 322 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 323 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 323 (by decide),nativeRow]; rfl) (rrNext (safeNative k 324 (by decide)) (safeNative k 325 (by decide))
      (by rw [stSmall k 324 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 325 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 325 (by decide),nativeRow]; rfl) (rrNext (safeNative k 326 (by decide)) (safeNative k 327 (by decide))
      (by rw [stSmall k 326 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 327 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 327 (by decide),nativeRow]; rfl) (rrNext (safeNative k 328 (by decide)) (safeNative k 329 (by decide))
      (by rw [stSmall k 328 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 329 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 329 (by decide),nativeRow]; rfl) (rrNext (safeNative k 330 (by decide)) (safeNative k 331 (by decide))
      (by rw [stSmall k 330 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 331 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 331 (by decide),nativeRow]; rfl) (rrNil 9 (st k 332))))))))))
  · rw [stSmall k 332 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 333 (by decide),nativeRow]; rfl)
  · rw [stSmall k 333 (by decide),nativeRow]; rfl
  · rw [stSmall k 334 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 335 (by decide),nativeRow]; rfl)
  · rw [stSmall k 335 (by decide),nativeRow]; rfl
  · exact (rlNext (safeNative k 336 (by decide)) (safeNative k 337 (by decide))
      (by rw [stSmall k 336 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 337 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 337 (by decide),nativeRow]; rfl) (rlNext (safeNative k 338 (by decide)) (safeNative k 339 (by decide))
      (by rw [stSmall k 338 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 339 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 339 (by decide),nativeRow]; rfl) (rlNext (safeNative k 340 (by decide)) (safeNative k 341 (by decide))
      (by rw [stSmall k 340 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 341 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 341 (by decide),nativeRow]; rfl) (rlNext (safeNative k 342 (by decide)) (safeNative k 343 (by decide))
      (by rw [stSmall k 342 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 343 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 343 (by decide),nativeRow]; rfl) (rlNext (safeNative k 344 (by decide)) (safeNative k 345 (by decide))
      (by rw [stSmall k 344 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 345 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 345 (by decide),nativeRow]; rfl) (rlNext (safeNative k 346 (by decide)) (safeNative k 347 (by decide))
      (by rw [stSmall k 346 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 347 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 347 (by decide),nativeRow]; rfl) (rlNext (safeNative k 348 (by decide)) (safeNative k 349 (by decide))
      (by rw [stSmall k 348 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 349 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 349 (by decide),nativeRow]; rfl) (rlNext (safeNative k 350 (by decide)) (safeNative k 351 (by decide))
      (by rw [stSmall k 350 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 351 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 351 (by decide),nativeRow]; rfl) (rlNil 1 (st k 352))))))))))
  · rw [stSmall k 352 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 353 (by decide),nativeRow]; rfl)
  · rw [stSmall k 353 (by decide),nativeRow]; rfl
private def clone4 (k : Nat) : CopyRows k 0 9 (st k 274) (st k 275) (st k 354) (st k 355) := by
  refine copyMk (safeNative k 274 (by decide)) (safeNative k 275 (by decide))
    (safeNative k 354 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 274 (by decide),nativeRow]; rfl
  · intro bit; cases bit
    · exact clone4_false k
    · exact clone4_true k
  · rw [stSmall k 275 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 354 (by decide),nativeRow]; rfl)
  · rw [stSmall k 354 (by decide),nativeRow]; rfl
private def clone5_false (k : Nat) : CopyBranch k 0 10 (st k 357) false := by
  refine branchMk (st k 358) (st k 359) (st k 377) (st k 378) (st k 379) (st k 380) (st k 381) (st k 399) (st k 400)
    (safeNative k 358 (by decide)) (safeNative k 377 (by decide)) (safeNative k 378 (by decide)) (safeNative k 379 (by decide)) (safeNative k 380 (by decide)) (safeNative k 399 (by decide)) (safeNative k 400 (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 357 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 358 (by decide),nativeRow]; rfl)
  · rw [stSmall k 358 (by decide),nativeRow]; rfl
  · exact (rrNext (safeNative k 359 (by decide)) (safeNative k 360 (by decide))
      (by rw [stSmall k 359 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 360 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 360 (by decide),nativeRow]; rfl) (rrNext (safeNative k 361 (by decide)) (safeNative k 362 (by decide))
      (by rw [stSmall k 361 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 362 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 362 (by decide),nativeRow]; rfl) (rrNext (safeNative k 363 (by decide)) (safeNative k 364 (by decide))
      (by rw [stSmall k 363 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 364 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 364 (by decide),nativeRow]; rfl) (rrNext (safeNative k 365 (by decide)) (safeNative k 366 (by decide))
      (by rw [stSmall k 365 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 366 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 366 (by decide),nativeRow]; rfl) (rrNext (safeNative k 367 (by decide)) (safeNative k 368 (by decide))
      (by rw [stSmall k 367 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 368 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 368 (by decide),nativeRow]; rfl) (rrNext (safeNative k 369 (by decide)) (safeNative k 370 (by decide))
      (by rw [stSmall k 369 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 370 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 370 (by decide),nativeRow]; rfl) (rrNext (safeNative k 371 (by decide)) (safeNative k 372 (by decide))
      (by rw [stSmall k 371 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 372 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 372 (by decide),nativeRow]; rfl) (rrNext (safeNative k 373 (by decide)) (safeNative k 374 (by decide))
      (by rw [stSmall k 373 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 374 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 374 (by decide),nativeRow]; rfl) (rrNext (safeNative k 375 (by decide)) (safeNative k 376 (by decide))
      (by rw [stSmall k 375 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 376 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 376 (by decide),nativeRow]; rfl) (rrNil 10 (st k 377)))))))))))
  · rw [stSmall k 377 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 378 (by decide),nativeRow]; rfl)
  · rw [stSmall k 378 (by decide),nativeRow]; rfl
  · rw [stSmall k 379 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 380 (by decide),nativeRow]; rfl)
  · rw [stSmall k 380 (by decide),nativeRow]; rfl
  · exact (rlNext (safeNative k 381 (by decide)) (safeNative k 382 (by decide))
      (by rw [stSmall k 381 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 382 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 382 (by decide),nativeRow]; rfl) (rlNext (safeNative k 383 (by decide)) (safeNative k 384 (by decide))
      (by rw [stSmall k 383 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 384 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 384 (by decide),nativeRow]; rfl) (rlNext (safeNative k 385 (by decide)) (safeNative k 386 (by decide))
      (by rw [stSmall k 385 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 386 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 386 (by decide),nativeRow]; rfl) (rlNext (safeNative k 387 (by decide)) (safeNative k 388 (by decide))
      (by rw [stSmall k 387 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 388 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 388 (by decide),nativeRow]; rfl) (rlNext (safeNative k 389 (by decide)) (safeNative k 390 (by decide))
      (by rw [stSmall k 389 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 390 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 390 (by decide),nativeRow]; rfl) (rlNext (safeNative k 391 (by decide)) (safeNative k 392 (by decide))
      (by rw [stSmall k 391 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 392 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 392 (by decide),nativeRow]; rfl) (rlNext (safeNative k 393 (by decide)) (safeNative k 394 (by decide))
      (by rw [stSmall k 393 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 394 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 394 (by decide),nativeRow]; rfl) (rlNext (safeNative k 395 (by decide)) (safeNative k 396 (by decide))
      (by rw [stSmall k 395 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 396 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 396 (by decide),nativeRow]; rfl) (rlNext (safeNative k 397 (by decide)) (safeNative k 398 (by decide))
      (by rw [stSmall k 397 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 398 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 398 (by decide),nativeRow]; rfl) (rlNil 1 (st k 399)))))))))))
  · rw [stSmall k 399 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 400 (by decide),nativeRow]; rfl)
  · rw [stSmall k 400 (by decide),nativeRow]; rfl
private def clone5_true (k : Nat) : CopyBranch k 0 10 (st k 357) true := by
  refine branchMk (st k 401) (st k 402) (st k 420) (st k 421) (st k 422) (st k 423) (st k 424) (st k 442) (st k 443)
    (safeNative k 401 (by decide)) (safeNative k 420 (by decide)) (safeNative k 421 (by decide)) (safeNative k 422 (by decide)) (safeNative k 423 (by decide)) (safeNative k 442 (by decide)) (safeNative k 443 (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 357 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 401 (by decide),nativeRow]; rfl)
  · rw [stSmall k 401 (by decide),nativeRow]; rfl
  · exact (rrNext (safeNative k 402 (by decide)) (safeNative k 403 (by decide))
      (by rw [stSmall k 402 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 403 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 403 (by decide),nativeRow]; rfl) (rrNext (safeNative k 404 (by decide)) (safeNative k 405 (by decide))
      (by rw [stSmall k 404 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 405 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 405 (by decide),nativeRow]; rfl) (rrNext (safeNative k 406 (by decide)) (safeNative k 407 (by decide))
      (by rw [stSmall k 406 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 407 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 407 (by decide),nativeRow]; rfl) (rrNext (safeNative k 408 (by decide)) (safeNative k 409 (by decide))
      (by rw [stSmall k 408 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 409 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 409 (by decide),nativeRow]; rfl) (rrNext (safeNative k 410 (by decide)) (safeNative k 411 (by decide))
      (by rw [stSmall k 410 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 411 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 411 (by decide),nativeRow]; rfl) (rrNext (safeNative k 412 (by decide)) (safeNative k 413 (by decide))
      (by rw [stSmall k 412 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 413 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 413 (by decide),nativeRow]; rfl) (rrNext (safeNative k 414 (by decide)) (safeNative k 415 (by decide))
      (by rw [stSmall k 414 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 415 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 415 (by decide),nativeRow]; rfl) (rrNext (safeNative k 416 (by decide)) (safeNative k 417 (by decide))
      (by rw [stSmall k 416 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 417 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 417 (by decide),nativeRow]; rfl) (rrNext (safeNative k 418 (by decide)) (safeNative k 419 (by decide))
      (by rw [stSmall k 418 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 419 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 419 (by decide),nativeRow]; rfl) (rrNil 10 (st k 420)))))))))))
  · rw [stSmall k 420 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 421 (by decide),nativeRow]; rfl)
  · rw [stSmall k 421 (by decide),nativeRow]; rfl
  · rw [stSmall k 422 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 423 (by decide),nativeRow]; rfl)
  · rw [stSmall k 423 (by decide),nativeRow]; rfl
  · exact (rlNext (safeNative k 424 (by decide)) (safeNative k 425 (by decide))
      (by rw [stSmall k 424 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 425 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 425 (by decide),nativeRow]; rfl) (rlNext (safeNative k 426 (by decide)) (safeNative k 427 (by decide))
      (by rw [stSmall k 426 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 427 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 427 (by decide),nativeRow]; rfl) (rlNext (safeNative k 428 (by decide)) (safeNative k 429 (by decide))
      (by rw [stSmall k 428 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 429 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 429 (by decide),nativeRow]; rfl) (rlNext (safeNative k 430 (by decide)) (safeNative k 431 (by decide))
      (by rw [stSmall k 430 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 431 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 431 (by decide),nativeRow]; rfl) (rlNext (safeNative k 432 (by decide)) (safeNative k 433 (by decide))
      (by rw [stSmall k 432 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 433 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 433 (by decide),nativeRow]; rfl) (rlNext (safeNative k 434 (by decide)) (safeNative k 435 (by decide))
      (by rw [stSmall k 434 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 435 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 435 (by decide),nativeRow]; rfl) (rlNext (safeNative k 436 (by decide)) (safeNative k 437 (by decide))
      (by rw [stSmall k 436 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 437 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 437 (by decide),nativeRow]; rfl) (rlNext (safeNative k 438 (by decide)) (safeNative k 439 (by decide))
      (by rw [stSmall k 438 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 439 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 439 (by decide),nativeRow]; rfl) (rlNext (safeNative k 440 (by decide)) (safeNative k 441 (by decide))
      (by rw [stSmall k 440 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 441 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 441 (by decide),nativeRow]; rfl) (rlNil 1 (st k 442)))))))))))
  · rw [stSmall k 442 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 443 (by decide),nativeRow]; rfl)
  · rw [stSmall k 443 (by decide),nativeRow]; rfl
private def clone5 (k : Nat) : CopyRows k 0 10 (st k 356) (st k 357) (st k 444) (st k 445) := by
  refine copyMk (safeNative k 356 (by decide)) (safeNative k 357 (by decide))
    (safeNative k 444 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 356 (by decide),nativeRow]; rfl
  · intro bit; cases bit
    · exact clone5_false k
    · exact clone5_true k
  · rw [stSmall k 357 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 444 (by decide),nativeRow]; rfl)
  · rw [stSmall k 444 (by decide),nativeRow]; rfl
private def clone6_false (k : Nat) : CopyBranch k 0 10 (st k 447) false := by
  refine branchMk (st k 448) (st k 449) (st k 467) (st k 468) (st k 469) (st k 470) (st k 471) (st k 489) (st k 490)
    (safeNative k 448 (by decide)) (safeNative k 467 (by decide)) (safeNative k 468 (by decide)) (safeNative k 469 (by decide)) (safeNative k 470 (by decide)) (safeNative k 489 (by decide)) (safeNative k 490 (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 447 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 448 (by decide),nativeRow]; rfl)
  · rw [stSmall k 448 (by decide),nativeRow]; rfl
  · exact (rrNext (safeNative k 449 (by decide)) (safeNative k 450 (by decide))
      (by rw [stSmall k 449 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 450 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 450 (by decide),nativeRow]; rfl) (rrNext (safeNative k 451 (by decide)) (safeNative k 452 (by decide))
      (by rw [stSmall k 451 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 452 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 452 (by decide),nativeRow]; rfl) (rrNext (safeNative k 453 (by decide)) (safeNative k 454 (by decide))
      (by rw [stSmall k 453 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 454 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 454 (by decide),nativeRow]; rfl) (rrNext (safeNative k 455 (by decide)) (safeNative k 456 (by decide))
      (by rw [stSmall k 455 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 456 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 456 (by decide),nativeRow]; rfl) (rrNext (safeNative k 457 (by decide)) (safeNative k 458 (by decide))
      (by rw [stSmall k 457 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 458 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 458 (by decide),nativeRow]; rfl) (rrNext (safeNative k 459 (by decide)) (safeNative k 460 (by decide))
      (by rw [stSmall k 459 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 460 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 460 (by decide),nativeRow]; rfl) (rrNext (safeNative k 461 (by decide)) (safeNative k 462 (by decide))
      (by rw [stSmall k 461 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 462 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 462 (by decide),nativeRow]; rfl) (rrNext (safeNative k 463 (by decide)) (safeNative k 464 (by decide))
      (by rw [stSmall k 463 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 464 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 464 (by decide),nativeRow]; rfl) (rrNext (safeNative k 465 (by decide)) (safeNative k 466 (by decide))
      (by rw [stSmall k 465 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 466 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 466 (by decide),nativeRow]; rfl) (rrNil 10 (st k 467)))))))))))
  · rw [stSmall k 467 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 468 (by decide),nativeRow]; rfl)
  · rw [stSmall k 468 (by decide),nativeRow]; rfl
  · rw [stSmall k 469 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 470 (by decide),nativeRow]; rfl)
  · rw [stSmall k 470 (by decide),nativeRow]; rfl
  · exact (rlNext (safeNative k 471 (by decide)) (safeNative k 472 (by decide))
      (by rw [stSmall k 471 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 472 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 472 (by decide),nativeRow]; rfl) (rlNext (safeNative k 473 (by decide)) (safeNative k 474 (by decide))
      (by rw [stSmall k 473 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 474 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 474 (by decide),nativeRow]; rfl) (rlNext (safeNative k 475 (by decide)) (safeNative k 476 (by decide))
      (by rw [stSmall k 475 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 476 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 476 (by decide),nativeRow]; rfl) (rlNext (safeNative k 477 (by decide)) (safeNative k 478 (by decide))
      (by rw [stSmall k 477 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 478 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 478 (by decide),nativeRow]; rfl) (rlNext (safeNative k 479 (by decide)) (safeNative k 480 (by decide))
      (by rw [stSmall k 479 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 480 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 480 (by decide),nativeRow]; rfl) (rlNext (safeNative k 481 (by decide)) (safeNative k 482 (by decide))
      (by rw [stSmall k 481 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 482 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 482 (by decide),nativeRow]; rfl) (rlNext (safeNative k 483 (by decide)) (safeNative k 484 (by decide))
      (by rw [stSmall k 483 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 484 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 484 (by decide),nativeRow]; rfl) (rlNext (safeNative k 485 (by decide)) (safeNative k 486 (by decide))
      (by rw [stSmall k 485 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 486 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 486 (by decide),nativeRow]; rfl) (rlNext (safeNative k 487 (by decide)) (safeNative k 488 (by decide))
      (by rw [stSmall k 487 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 488 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 488 (by decide),nativeRow]; rfl) (rlNil 1 (st k 489)))))))))))
  · rw [stSmall k 489 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 490 (by decide),nativeRow]; rfl)
  · rw [stSmall k 490 (by decide),nativeRow]; rfl
private def clone6_true (k : Nat) : CopyBranch k 0 10 (st k 447) true := by
  refine branchMk (st k 491) (st k 492) (st k 510) (st k 511) (st k 512) (st k 513) (st k 514) (st k 532) (st k 533)
    (safeNative k 491 (by decide)) (safeNative k 510 (by decide)) (safeNative k 511 (by decide)) (safeNative k 512 (by decide)) (safeNative k 513 (by decide)) (safeNative k 532 (by decide)) (safeNative k 533 (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 447 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 491 (by decide),nativeRow]; rfl)
  · rw [stSmall k 491 (by decide),nativeRow]; rfl
  · exact (rrNext (safeNative k 492 (by decide)) (safeNative k 493 (by decide))
      (by rw [stSmall k 492 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 493 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 493 (by decide),nativeRow]; rfl) (rrNext (safeNative k 494 (by decide)) (safeNative k 495 (by decide))
      (by rw [stSmall k 494 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 495 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 495 (by decide),nativeRow]; rfl) (rrNext (safeNative k 496 (by decide)) (safeNative k 497 (by decide))
      (by rw [stSmall k 496 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 497 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 497 (by decide),nativeRow]; rfl) (rrNext (safeNative k 498 (by decide)) (safeNative k 499 (by decide))
      (by rw [stSmall k 498 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 499 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 499 (by decide),nativeRow]; rfl) (rrNext (safeNative k 500 (by decide)) (safeNative k 501 (by decide))
      (by rw [stSmall k 500 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 501 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 501 (by decide),nativeRow]; rfl) (rrNext (safeNative k 502 (by decide)) (safeNative k 503 (by decide))
      (by rw [stSmall k 502 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 503 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 503 (by decide),nativeRow]; rfl) (rrNext (safeNative k 504 (by decide)) (safeNative k 505 (by decide))
      (by rw [stSmall k 504 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 505 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 505 (by decide),nativeRow]; rfl) (rrNext (safeNative k 506 (by decide)) (safeNative k 507 (by decide))
      (by rw [stSmall k 506 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 507 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 507 (by decide),nativeRow]; rfl) (rrNext (safeNative k 508 (by decide)) (safeNative k 509 (by decide))
      (by rw [stSmall k 508 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 509 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 509 (by decide),nativeRow]; rfl) (rrNil 10 (st k 510)))))))))))
  · rw [stSmall k 510 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 511 (by decide),nativeRow]; rfl)
  · rw [stSmall k 511 (by decide),nativeRow]; rfl
  · rw [stSmall k 512 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 513 (by decide),nativeRow]; rfl)
  · rw [stSmall k 513 (by decide),nativeRow]; rfl
  · exact (rlNext (safeNative k 514 (by decide)) (safeNative k 515 (by decide))
      (by rw [stSmall k 514 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 515 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 515 (by decide),nativeRow]; rfl) (rlNext (safeNative k 516 (by decide)) (safeNative k 517 (by decide))
      (by rw [stSmall k 516 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 517 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 517 (by decide),nativeRow]; rfl) (rlNext (safeNative k 518 (by decide)) (safeNative k 519 (by decide))
      (by rw [stSmall k 518 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 519 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 519 (by decide),nativeRow]; rfl) (rlNext (safeNative k 520 (by decide)) (safeNative k 521 (by decide))
      (by rw [stSmall k 520 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 521 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 521 (by decide),nativeRow]; rfl) (rlNext (safeNative k 522 (by decide)) (safeNative k 523 (by decide))
      (by rw [stSmall k 522 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 523 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 523 (by decide),nativeRow]; rfl) (rlNext (safeNative k 524 (by decide)) (safeNative k 525 (by decide))
      (by rw [stSmall k 524 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 525 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 525 (by decide),nativeRow]; rfl) (rlNext (safeNative k 526 (by decide)) (safeNative k 527 (by decide))
      (by rw [stSmall k 526 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 527 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 527 (by decide),nativeRow]; rfl) (rlNext (safeNative k 528 (by decide)) (safeNative k 529 (by decide))
      (by rw [stSmall k 528 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 529 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 529 (by decide),nativeRow]; rfl) (rlNext (safeNative k 530 (by decide)) (safeNative k 531 (by decide))
      (by rw [stSmall k 530 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 531 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 531 (by decide),nativeRow]; rfl) (rlNil 1 (st k 532)))))))))))
  · rw [stSmall k 532 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 533 (by decide),nativeRow]; rfl)
  · rw [stSmall k 533 (by decide),nativeRow]; rfl
private def clone6 (k : Nat) : CopyRows k 0 10 (st k 446) (st k 447) (st k 534) (st k 535) := by
  refine copyMk (safeNative k 446 (by decide)) (safeNative k 447 (by decide))
    (safeNative k 534 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 446 (by decide),nativeRow]; rfl
  · intro bit; cases bit
    · exact clone6_false k
    · exact clone6_true k
  · rw [stSmall k 447 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 534 (by decide),nativeRow]; rfl)
  · rw [stSmall k 534 (by decide),nativeRow]; rfl
private def clone7_false (k : Nat) : CopyBranch k 0 10 (st k 537) false := by
  refine branchMk (st k 538) (st k 539) (st k 557) (st k 558) (st k 559) (st k 560) (st k 561) (st k 579) (st k 580)
    (safeNative k 538 (by decide)) (safeNative k 557 (by decide)) (safeNative k 558 (by decide)) (safeNative k 559 (by decide)) (safeNative k 560 (by decide)) (safeNative k 579 (by decide)) (safeNative k 580 (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 537 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 538 (by decide),nativeRow]; rfl)
  · rw [stSmall k 538 (by decide),nativeRow]; rfl
  · exact (rrNext (safeNative k 539 (by decide)) (safeNative k 540 (by decide))
      (by rw [stSmall k 539 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 540 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 540 (by decide),nativeRow]; rfl) (rrNext (safeNative k 541 (by decide)) (safeNative k 542 (by decide))
      (by rw [stSmall k 541 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 542 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 542 (by decide),nativeRow]; rfl) (rrNext (safeNative k 543 (by decide)) (safeNative k 544 (by decide))
      (by rw [stSmall k 543 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 544 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 544 (by decide),nativeRow]; rfl) (rrNext (safeNative k 545 (by decide)) (safeNative k 546 (by decide))
      (by rw [stSmall k 545 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 546 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 546 (by decide),nativeRow]; rfl) (rrNext (safeNative k 547 (by decide)) (safeNative k 548 (by decide))
      (by rw [stSmall k 547 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 548 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 548 (by decide),nativeRow]; rfl) (rrNext (safeNative k 549 (by decide)) (safeNative k 550 (by decide))
      (by rw [stSmall k 549 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 550 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 550 (by decide),nativeRow]; rfl) (rrNext (safeNative k 551 (by decide)) (safeNative k 552 (by decide))
      (by rw [stSmall k 551 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 552 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 552 (by decide),nativeRow]; rfl) (rrNext (safeNative k 553 (by decide)) (safeNative k 554 (by decide))
      (by rw [stSmall k 553 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 554 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 554 (by decide),nativeRow]; rfl) (rrNext (safeNative k 555 (by decide)) (safeNative k 556 (by decide))
      (by rw [stSmall k 555 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 556 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 556 (by decide),nativeRow]; rfl) (rrNil 10 (st k 557)))))))))))
  · rw [stSmall k 557 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 558 (by decide),nativeRow]; rfl)
  · rw [stSmall k 558 (by decide),nativeRow]; rfl
  · rw [stSmall k 559 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 560 (by decide),nativeRow]; rfl)
  · rw [stSmall k 560 (by decide),nativeRow]; rfl
  · exact (rlNext (safeNative k 561 (by decide)) (safeNative k 562 (by decide))
      (by rw [stSmall k 561 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 562 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 562 (by decide),nativeRow]; rfl) (rlNext (safeNative k 563 (by decide)) (safeNative k 564 (by decide))
      (by rw [stSmall k 563 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 564 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 564 (by decide),nativeRow]; rfl) (rlNext (safeNative k 565 (by decide)) (safeNative k 566 (by decide))
      (by rw [stSmall k 565 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 566 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 566 (by decide),nativeRow]; rfl) (rlNext (safeNative k 567 (by decide)) (safeNative k 568 (by decide))
      (by rw [stSmall k 567 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 568 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 568 (by decide),nativeRow]; rfl) (rlNext (safeNative k 569 (by decide)) (safeNative k 570 (by decide))
      (by rw [stSmall k 569 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 570 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 570 (by decide),nativeRow]; rfl) (rlNext (safeNative k 571 (by decide)) (safeNative k 572 (by decide))
      (by rw [stSmall k 571 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 572 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 572 (by decide),nativeRow]; rfl) (rlNext (safeNative k 573 (by decide)) (safeNative k 574 (by decide))
      (by rw [stSmall k 573 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 574 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 574 (by decide),nativeRow]; rfl) (rlNext (safeNative k 575 (by decide)) (safeNative k 576 (by decide))
      (by rw [stSmall k 575 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 576 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 576 (by decide),nativeRow]; rfl) (rlNext (safeNative k 577 (by decide)) (safeNative k 578 (by decide))
      (by rw [stSmall k 577 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 578 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 578 (by decide),nativeRow]; rfl) (rlNil 1 (st k 579)))))))))))
  · rw [stSmall k 579 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 580 (by decide),nativeRow]; rfl)
  · rw [stSmall k 580 (by decide),nativeRow]; rfl
private def clone7_true (k : Nat) : CopyBranch k 0 10 (st k 537) true := by
  refine branchMk (st k 581) (st k 582) (st k 600) (st k 601) (st k 602) (st k 603) (st k 604) (st k 622) (st k 623)
    (safeNative k 581 (by decide)) (safeNative k 600 (by decide)) (safeNative k 601 (by decide)) (safeNative k 602 (by decide)) (safeNative k 603 (by decide)) (safeNative k 622 (by decide)) (safeNative k 623 (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 537 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 581 (by decide),nativeRow]; rfl)
  · rw [stSmall k 581 (by decide),nativeRow]; rfl
  · exact (rrNext (safeNative k 582 (by decide)) (safeNative k 583 (by decide))
      (by rw [stSmall k 582 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 583 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 583 (by decide),nativeRow]; rfl) (rrNext (safeNative k 584 (by decide)) (safeNative k 585 (by decide))
      (by rw [stSmall k 584 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 585 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 585 (by decide),nativeRow]; rfl) (rrNext (safeNative k 586 (by decide)) (safeNative k 587 (by decide))
      (by rw [stSmall k 586 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 587 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 587 (by decide),nativeRow]; rfl) (rrNext (safeNative k 588 (by decide)) (safeNative k 589 (by decide))
      (by rw [stSmall k 588 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 589 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 589 (by decide),nativeRow]; rfl) (rrNext (safeNative k 590 (by decide)) (safeNative k 591 (by decide))
      (by rw [stSmall k 590 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 591 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 591 (by decide),nativeRow]; rfl) (rrNext (safeNative k 592 (by decide)) (safeNative k 593 (by decide))
      (by rw [stSmall k 592 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 593 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 593 (by decide),nativeRow]; rfl) (rrNext (safeNative k 594 (by decide)) (safeNative k 595 (by decide))
      (by rw [stSmall k 594 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 595 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 595 (by decide),nativeRow]; rfl) (rrNext (safeNative k 596 (by decide)) (safeNative k 597 (by decide))
      (by rw [stSmall k 596 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 597 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 597 (by decide),nativeRow]; rfl) (rrNext (safeNative k 598 (by decide)) (safeNative k 599 (by decide))
      (by rw [stSmall k 598 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 599 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 599 (by decide),nativeRow]; rfl) (rrNil 10 (st k 600)))))))))))
  · rw [stSmall k 600 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 601 (by decide),nativeRow]; rfl)
  · rw [stSmall k 601 (by decide),nativeRow]; rfl
  · rw [stSmall k 602 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 603 (by decide),nativeRow]; rfl)
  · rw [stSmall k 603 (by decide),nativeRow]; rfl
  · exact (rlNext (safeNative k 604 (by decide)) (safeNative k 605 (by decide))
      (by rw [stSmall k 604 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 605 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 605 (by decide),nativeRow]; rfl) (rlNext (safeNative k 606 (by decide)) (safeNative k 607 (by decide))
      (by rw [stSmall k 606 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 607 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 607 (by decide),nativeRow]; rfl) (rlNext (safeNative k 608 (by decide)) (safeNative k 609 (by decide))
      (by rw [stSmall k 608 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 609 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 609 (by decide),nativeRow]; rfl) (rlNext (safeNative k 610 (by decide)) (safeNative k 611 (by decide))
      (by rw [stSmall k 610 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 611 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 611 (by decide),nativeRow]; rfl) (rlNext (safeNative k 612 (by decide)) (safeNative k 613 (by decide))
      (by rw [stSmall k 612 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 613 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 613 (by decide),nativeRow]; rfl) (rlNext (safeNative k 614 (by decide)) (safeNative k 615 (by decide))
      (by rw [stSmall k 614 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 615 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 615 (by decide),nativeRow]; rfl) (rlNext (safeNative k 616 (by decide)) (safeNative k 617 (by decide))
      (by rw [stSmall k 616 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 617 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 617 (by decide),nativeRow]; rfl) (rlNext (safeNative k 618 (by decide)) (safeNative k 619 (by decide))
      (by rw [stSmall k 618 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 619 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 619 (by decide),nativeRow]; rfl) (rlNext (safeNative k 620 (by decide)) (safeNative k 621 (by decide))
      (by rw [stSmall k 620 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 621 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 621 (by decide),nativeRow]; rfl) (rlNil 1 (st k 622)))))))))))
  · rw [stSmall k 622 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 623 (by decide),nativeRow]; rfl)
  · rw [stSmall k 623 (by decide),nativeRow]; rfl
private def clone7 (k : Nat) : CopyRows k 0 10 (st k 536) (st k 537) (st k 624) (st k 625) := by
  refine copyMk (safeNative k 536 (by decide)) (safeNative k 537 (by decide))
    (safeNative k 624 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 536 (by decide),nativeRow]; rfl
  · intro bit; cases bit
    · exact clone7_false k
    · exact clone7_true k
  · rw [stSmall k 537 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 624 (by decide),nativeRow]; rfl)
  · rw [stSmall k 624 (by decide),nativeRow]; rfl
private def clone8_false (k : Nat) : CopyBranch k 0 11 (st k 674) false := by
  refine branchMk (st k 675) (st k 676) (st k 696) (st k 697) (st k 698) (st k 699) (st k 700) (st k 720) (st k 721)
    (safeNative k 675 (by decide)) (safeNative k 696 (by decide)) (safeNative k 697 (by decide)) (safeNative k 698 (by decide)) (safeNative k 699 (by decide)) (safeNative k 720 (by decide)) (safeNative k 721 (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 674 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 675 (by decide),nativeRow]; rfl)
  · rw [stSmall k 675 (by decide),nativeRow]; rfl
  · exact (rrNext (safeNative k 676 (by decide)) (safeNative k 677 (by decide))
      (by rw [stSmall k 676 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 677 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 677 (by decide),nativeRow]; rfl) (rrNext (safeNative k 678 (by decide)) (safeNative k 679 (by decide))
      (by rw [stSmall k 678 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 679 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 679 (by decide),nativeRow]; rfl) (rrNext (safeNative k 680 (by decide)) (safeNative k 681 (by decide))
      (by rw [stSmall k 680 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 681 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 681 (by decide),nativeRow]; rfl) (rrNext (safeNative k 682 (by decide)) (safeNative k 683 (by decide))
      (by rw [stSmall k 682 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 683 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 683 (by decide),nativeRow]; rfl) (rrNext (safeNative k 684 (by decide)) (safeNative k 685 (by decide))
      (by rw [stSmall k 684 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 685 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 685 (by decide),nativeRow]; rfl) (rrNext (safeNative k 686 (by decide)) (safeNative k 687 (by decide))
      (by rw [stSmall k 686 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 687 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 687 (by decide),nativeRow]; rfl) (rrNext (safeNative k 688 (by decide)) (safeNative k 689 (by decide))
      (by rw [stSmall k 688 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 689 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 689 (by decide),nativeRow]; rfl) (rrNext (safeNative k 690 (by decide)) (safeNative k 691 (by decide))
      (by rw [stSmall k 690 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 691 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 691 (by decide),nativeRow]; rfl) (rrNext (safeNative k 692 (by decide)) (safeNative k 693 (by decide))
      (by rw [stSmall k 692 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 693 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 693 (by decide),nativeRow]; rfl) (rrNext (safeNative k 694 (by decide)) (safeNative k 695 (by decide))
      (by rw [stSmall k 694 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 695 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 695 (by decide),nativeRow]; rfl) (rrNil 11 (st k 696))))))))))))
  · rw [stSmall k 696 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 697 (by decide),nativeRow]; rfl)
  · rw [stSmall k 697 (by decide),nativeRow]; rfl
  · rw [stSmall k 698 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 699 (by decide),nativeRow]; rfl)
  · rw [stSmall k 699 (by decide),nativeRow]; rfl
  · exact (rlNext (safeNative k 700 (by decide)) (safeNative k 701 (by decide))
      (by rw [stSmall k 700 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 701 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 701 (by decide),nativeRow]; rfl) (rlNext (safeNative k 702 (by decide)) (safeNative k 703 (by decide))
      (by rw [stSmall k 702 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 703 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 703 (by decide),nativeRow]; rfl) (rlNext (safeNative k 704 (by decide)) (safeNative k 705 (by decide))
      (by rw [stSmall k 704 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 705 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 705 (by decide),nativeRow]; rfl) (rlNext (safeNative k 706 (by decide)) (safeNative k 707 (by decide))
      (by rw [stSmall k 706 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 707 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 707 (by decide),nativeRow]; rfl) (rlNext (safeNative k 708 (by decide)) (safeNative k 709 (by decide))
      (by rw [stSmall k 708 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 709 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 709 (by decide),nativeRow]; rfl) (rlNext (safeNative k 710 (by decide)) (safeNative k 711 (by decide))
      (by rw [stSmall k 710 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 711 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 711 (by decide),nativeRow]; rfl) (rlNext (safeNative k 712 (by decide)) (safeNative k 713 (by decide))
      (by rw [stSmall k 712 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 713 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 713 (by decide),nativeRow]; rfl) (rlNext (safeNative k 714 (by decide)) (safeNative k 715 (by decide))
      (by rw [stSmall k 714 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 715 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 715 (by decide),nativeRow]; rfl) (rlNext (safeNative k 716 (by decide)) (safeNative k 717 (by decide))
      (by rw [stSmall k 716 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 717 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 717 (by decide),nativeRow]; rfl) (rlNext (safeNative k 718 (by decide)) (safeNative k 719 (by decide))
      (by rw [stSmall k 718 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 719 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 719 (by decide),nativeRow]; rfl) (rlNil 1 (st k 720))))))))))))
  · rw [stSmall k 720 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 721 (by decide),nativeRow]; rfl)
  · rw [stSmall k 721 (by decide),nativeRow]; rfl
private def clone8_true (k : Nat) : CopyBranch k 0 11 (st k 674) true := by
  refine branchMk (st k 722) (st k 723) (st k 743) (st k 744) (st k 745) (st k 746) (st k 747) (st k 767) (st k 768)
    (safeNative k 722 (by decide)) (safeNative k 743 (by decide)) (safeNative k 744 (by decide)) (safeNative k 745 (by decide)) (safeNative k 746 (by decide)) (safeNative k 767 (by decide)) (safeNative k 768 (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 674 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 722 (by decide),nativeRow]; rfl)
  · rw [stSmall k 722 (by decide),nativeRow]; rfl
  · exact (rrNext (safeNative k 723 (by decide)) (safeNative k 724 (by decide))
      (by rw [stSmall k 723 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 724 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 724 (by decide),nativeRow]; rfl) (rrNext (safeNative k 725 (by decide)) (safeNative k 726 (by decide))
      (by rw [stSmall k 725 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 726 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 726 (by decide),nativeRow]; rfl) (rrNext (safeNative k 727 (by decide)) (safeNative k 728 (by decide))
      (by rw [stSmall k 727 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 728 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 728 (by decide),nativeRow]; rfl) (rrNext (safeNative k 729 (by decide)) (safeNative k 730 (by decide))
      (by rw [stSmall k 729 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 730 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 730 (by decide),nativeRow]; rfl) (rrNext (safeNative k 731 (by decide)) (safeNative k 732 (by decide))
      (by rw [stSmall k 731 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 732 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 732 (by decide),nativeRow]; rfl) (rrNext (safeNative k 733 (by decide)) (safeNative k 734 (by decide))
      (by rw [stSmall k 733 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 734 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 734 (by decide),nativeRow]; rfl) (rrNext (safeNative k 735 (by decide)) (safeNative k 736 (by decide))
      (by rw [stSmall k 735 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 736 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 736 (by decide),nativeRow]; rfl) (rrNext (safeNative k 737 (by decide)) (safeNative k 738 (by decide))
      (by rw [stSmall k 737 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 738 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 738 (by decide),nativeRow]; rfl) (rrNext (safeNative k 739 (by decide)) (safeNative k 740 (by decide))
      (by rw [stSmall k 739 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 740 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 740 (by decide),nativeRow]; rfl) (rrNext (safeNative k 741 (by decide)) (safeNative k 742 (by decide))
      (by rw [stSmall k 741 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 742 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 742 (by decide),nativeRow]; rfl) (rrNil 11 (st k 743))))))))))))
  · rw [stSmall k 743 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 744 (by decide),nativeRow]; rfl)
  · rw [stSmall k 744 (by decide),nativeRow]; rfl
  · rw [stSmall k 745 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 746 (by decide),nativeRow]; rfl)
  · rw [stSmall k 746 (by decide),nativeRow]; rfl
  · exact (rlNext (safeNative k 747 (by decide)) (safeNative k 748 (by decide))
      (by rw [stSmall k 747 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 748 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 748 (by decide),nativeRow]; rfl) (rlNext (safeNative k 749 (by decide)) (safeNative k 750 (by decide))
      (by rw [stSmall k 749 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 750 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 750 (by decide),nativeRow]; rfl) (rlNext (safeNative k 751 (by decide)) (safeNative k 752 (by decide))
      (by rw [stSmall k 751 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 752 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 752 (by decide),nativeRow]; rfl) (rlNext (safeNative k 753 (by decide)) (safeNative k 754 (by decide))
      (by rw [stSmall k 753 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 754 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 754 (by decide),nativeRow]; rfl) (rlNext (safeNative k 755 (by decide)) (safeNative k 756 (by decide))
      (by rw [stSmall k 755 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 756 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 756 (by decide),nativeRow]; rfl) (rlNext (safeNative k 757 (by decide)) (safeNative k 758 (by decide))
      (by rw [stSmall k 757 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 758 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 758 (by decide),nativeRow]; rfl) (rlNext (safeNative k 759 (by decide)) (safeNative k 760 (by decide))
      (by rw [stSmall k 759 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 760 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 760 (by decide),nativeRow]; rfl) (rlNext (safeNative k 761 (by decide)) (safeNative k 762 (by decide))
      (by rw [stSmall k 761 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 762 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 762 (by decide),nativeRow]; rfl) (rlNext (safeNative k 763 (by decide)) (safeNative k 764 (by decide))
      (by rw [stSmall k 763 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 764 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 764 (by decide),nativeRow]; rfl) (rlNext (safeNative k 765 (by decide)) (safeNative k 766 (by decide))
      (by rw [stSmall k 765 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 766 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 766 (by decide),nativeRow]; rfl) (rlNil 1 (st k 767))))))))))))
  · rw [stSmall k 767 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 768 (by decide),nativeRow]; rfl)
  · rw [stSmall k 768 (by decide),nativeRow]; rfl
private def clone8 (k : Nat) : CopyRows k 0 11 (st k 673) (st k 674) (st k 769) (st k 770) := by
  refine copyMk (safeNative k 673 (by decide)) (safeNative k 674 (by decide))
    (safeNative k 769 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 673 (by decide),nativeRow]; rfl
  · intro bit; cases bit
    · exact clone8_false k
    · exact clone8_true k
  · rw [stSmall k 674 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 769 (by decide),nativeRow]; rfl)
  · rw [stSmall k 769 (by decide),nativeRow]; rfl
end FullIngressClosure
