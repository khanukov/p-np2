import IngressAllocation.ArithmeticPaths
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
namespace FirstLengthStage
run_cmd do
  let env ← getEnv
  for (key,aliasName) in [("Node","pNode"),("Node.head","pHead"),("embed","pEmbed"),("Path","PPath"),("Path.nil","pNil"),("Path.cons","pCons"),("Edge.before","pBefore"),("Path.execute","pExecute")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith "_private.RuntimeBitLength.Kernel." && n.toString.endsWith (".RuntimeBitLength."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique unchanged path interface: {key}: {found.map Prod.fst}"
private theorem prefix_path {k P t : Nat} {c d : pNode k}
    (path : PPath k P t c d) :
    ∀ u,u ≤ t → ∃ z,PPath k P u c z ∧ pHead z ≤ P := by
  induction path with
  | nil c hp =>
    intro u hu
    have zero : u=0 := by omega
    subst u
    exact ⟨c,pNil c hp,hp⟩
  | @cons t c d e edge rest ih =>
    intro u hu
    cases u with
    | zero => exact ⟨c,pNil c (pBefore edge),pBefore edge⟩
    | succ u =>
      obtain ⟨z,hz,bound⟩:=ih u (by omega)
      exact ⟨z,pCons edge hz,bound⟩
private theorem every_head {k N B P t : Nat} {c d : pNode k}
    (path : PPath k P t c d) (fit : P < tapeLength N B) (hc : pHead c < tapeLength N B) :
    ∀ u,u ≤ t → ((Cursor.machine k).run u (pEmbed c hc)).head.val ≤ P := by
  intro u hu
  obtain ⟨z,first,bound⟩:=prefix_path path u hu
  have run:=pExecute (N:=N) (B:=B) first fit
  change (Cursor.machine k).run u (pEmbed c hc)=pEmbed z (lt_of_le_of_lt bound fit) at run
  rw [run]
  exact bound
end FirstLengthStage
namespace SeedStage
run_cmd do
  let env ← getEnv
  for (key,aliasName) in [("Node","pNode"),("Node.head","pHead"),("embed","pEmbed"),("Path","PPath"),("Path.nil","pNil"),("Path.cons","pCons"),("Edge.before","pBefore"),("Path.execute","pExecute")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith "_private.AllArityBitLength.Kernel." && n.toString.endsWith (".AllArityBitLength."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique unchanged path interface: {key}: {found.map Prod.fst}"
private theorem prefix_path {k P t : Nat} {c d : pNode k}
    (path : PPath k P t c d) :
    ∀ u,u ≤ t → ∃ z,PPath k P u c z ∧ pHead z ≤ P := by
  induction path with
  | nil c hp =>
    intro u hu
    have zero : u=0 := by omega
    subst u
    exact ⟨c,pNil c hp,hp⟩
  | @cons t c d e edge rest ih =>
    intro u hu
    cases u with
    | zero => exact ⟨c,pNil c (pBefore edge),pBefore edge⟩
    | succ u =>
      obtain ⟨z,hz,bound⟩:=ih u (by omega)
      exact ⟨z,pCons edge hz,bound⟩
private theorem every_head {k N B P t : Nat} {c d : pNode k}
    (path : PPath k P t c d) (fit : P < tapeLength N B) (hc : pHead c < tapeLength N B) :
    ∀ u,u ≤ t → ((Cursor.machine k).run u (pEmbed c hc)).head.val ≤ P := by
  intro u hu
  obtain ⟨z,first,bound⟩:=prefix_path path u hu
  have run:=pExecute (N:=N) (B:=B) first fit
  change (Cursor.machine k).run u (pEmbed c hc)=pEmbed z (lt_of_le_of_lt bound fit) at run
  rw [run]
  exact bound
end SeedStage
end IngressAllocation
