import FullIngressClosure.Rows
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  for (key,aliasName) in [
      ("Node","PNode"),("Node.mk","pNode"),("Edge.mk","pEdge"),("put","put"),("dest","dest"),("Edge","PEdge"),
      ("Path","PPath"),("Path.nil","pNil"),("Path.cons","pCons"),
      ("Path.append","pAppend"),("Path.bounds","pBounds"),
      ("Path.execute","pExecute"),("Path.prefix_bounds","pPrefix"),
      ("keep","pKeep"),("sweepR","pSweepR"),("sweepL","pSweepL")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith "_private.BodyIngress.Native." &&
      n.toString.endsWith (".BodyIngress."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Expected unique ordinary path term {key}: {found.map Prod.fst}"
private def Safe (k : Nat) (s : Fin (BodyIngress.machine k).stateCount) : Prop :=
  s ≠ (BodyIngress.machine k).accept ∧ s ≠ (BodyIngress.machine k).reject ∧
  ∀ mode : Fin 3, s ≠ BodyIngress.body k (SerializedBody.entry mode)
private theorem hop {k lo hi : Nat} (s q : Fin (BodyIngress.machine k).stateCount)
    (h h' : Nat) (T : Nat → Option Bool) (w : Option Bool) (mv : Move)
    (safe : Safe k s) (hb : lo ≤ h ∧ h ≤ hi) (ha : lo ≤ h' ∧ h' ≤ hi)
    (row : (BodyIngress.machine k).step s (T h)=(q,w,mv)) (move : dest h mv=h') :
    PPath k lo hi 1 (pNode s h T) (pNode q h' (put T h w)) := by
  apply pCons (d:=(pNode q h' (put T h w)))
  · refine pEdge ⟨safe.1,safe.2.1⟩ safe.2.2 hb ha ?_ ?_ ?_
    · rw [row]
    · rw [row]; exact move
    · rw [row]
  · exact pNil _ ha
private theorem crossR {k lo hi : Nat} (e s q : Fin (BodyIngress.machine k).stateCount)
    (T : Nat → Option Bool) (a w : Nat) (lower : lo ≤ a) (upper : a+w+1 ≤ hi)
    (safeE : Safe k e) (safeS : Safe k s)
    (atA : T a=none) (atB : T (a+w+1)=none)
    (cells : ∀ i, a < i → i < a+w+1 → ∃ b, T i=some b)
    (start : (BodyIngress.machine k).step e none=(s,none,.right))
    (loop : ∀ b, (BodyIngress.machine k).step s (some b)=(s,some b,.right))
    (stop : (BodyIngress.machine k).step s none=(q,none,.stay)) :
    PPath k lo hi (w+2) (pNode e a T) (pNode q (a+w+1) T) := by
  have one:=pKeep (k:=k) (lo:=lo) (hi:=hi) e s a (a+1) T .right ⟨safeE.1,safeE.2.1⟩ safeE.2.2
    ⟨lower,by omega⟩ ⟨by omega,by omega⟩ (by rw [atA]; exact start) rfl
  have mid:=pSweepR (k:=k) (lo:=lo) (hi:=hi) s T (a+1) w (by omega) (by omega) ⟨safeS.1,safeS.2.1⟩ safeS.2.2 (by
    intro i hl hu
    obtain ⟨b,hb⟩:=cells i (by omega) (by omega)
    rw [hb]; exact loop b)
  rw [show a+1+w=a+w+1 by omega] at mid
  have last:=pKeep (k:=k) (lo:=lo) (hi:=hi) s q (a+w+1) (a+w+1) T .stay ⟨safeS.1,safeS.2.1⟩ safeS.2.2
    ⟨by omega,upper⟩ ⟨by omega,upper⟩ (by rw [atB]; exact stop) rfl
  simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using pAppend one (pAppend mid last)
private theorem crossL {k lo hi : Nat} (e s q : Fin (BodyIngress.machine k).stateCount)
    (T : Nat → Option Bool) (a w : Nat) (lower : lo ≤ a) (upper : a+w+1 ≤ hi)
    (safeE : Safe k e) (safeS : Safe k s)
    (atA : T a=none) (atB : T (a+w+1)=none)
    (cells : ∀ i, a < i → i < a+w+1 → ∃ b, T i=some b)
    (start : (BodyIngress.machine k).step e none=(s,none,.left))
    (loop : ∀ b, (BodyIngress.machine k).step s (some b)=(s,some b,.left))
    (stop : (BodyIngress.machine k).step s none=(q,none,.stay)) :
    PPath k lo hi (w+2) (pNode e (a+w+1) T) (pNode q a T) := by
  have one:=pKeep (k:=k) (lo:=lo) (hi:=hi) e s (a+w+1) (a+w) T .left ⟨safeE.1,safeE.2.1⟩ safeE.2.2
    ⟨by omega,upper⟩ ⟨by omega,by omega⟩ (by rw [atB]; exact start) (by simp [dest])
  have mid:=pSweepL (k:=k) (lo:=lo) (hi:=hi) s T a w lower (by omega) ⟨safeS.1,safeS.2.1⟩ safeS.2.2 (by
    intro i hl hu
    obtain ⟨b,hb⟩:=cells i hl (by omega)
    rw [hb]; exact loop b)
  have last:=pKeep (k:=k) (lo:=lo) (hi:=hi) s q a a T .stay ⟨safeS.1,safeS.2.1⟩ safeS.2.2
    ⟨lower,by omega⟩ ⟨lower,by omega⟩ (by rw [atA]; exact stop) rfl
  simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using pAppend one (pAppend mid last)
private inductive RouteR (k : Nat) : Nat → Nat →
    Fin (BodyIngress.machine k).stateCount → Fin (BodyIngress.machine k).stateCount → Prop
  | nil (i q) : RouteR k i i q q
  | next {i j e s q x} : Safe k e → Safe k s →
      (BodyIngress.machine k).step e none=(s,none,.right) →
      (∀ b, (BodyIngress.machine k).step s (some b)=(s,some b,.right)) →
      (BodyIngress.machine k).step s none=(q,none,.stay) →
      RouteR k (i+1) j q x → RouteR k i j e x
private inductive RouteL (k : Nat) : Nat → Nat →
    Fin (BodyIngress.machine k).stateCount → Fin (BodyIngress.machine k).stateCount → Prop
  | nil (i q) : RouteL k i i q q
  | next {i j e s q x} : Safe k e → Safe k s →
      (BodyIngress.machine k).step e none=(s,none,.left) →
      (∀ b, (BodyIngress.machine k).step s (some b)=(s,some b,.left)) →
      (BodyIngress.machine k).step s none=(q,none,.stay) →
      RouteL k i j q x → RouteL k (i+1) j e x
private theorem RouteR.span {k i j e x} (h : RouteR k i j e x) : i ≤ j := by
  induction h with | nil => exact le_rfl | next _ _ _ _ _ _ ih => omega
private theorem RouteL.span {k i j e x} (h : RouteL k i j e x) : j ≤ i := by
  induction h with | nil => exact le_rfl | next _ _ _ _ _ _ ih => omega
private theorem RouteR.execute {k i j e x lo hi} (h : RouteR k i j e x)
    (D : Nat → Nat) (T : Nat → Option Bool) (lower : lo ≤ D i) (upper : D j ≤ hi)
    (rise : ∀ u, i ≤ u → u < j → D u < D (u+1))
    (mono : ∀ a b, i ≤ a → a ≤ b → b ≤ j → D a ≤ D b)
    (blank : ∀ u, i ≤ u → u ≤ j → T (D u)=none)
    (cells : ∀ u v, i ≤ u → u < j → D u < v → v < D (u+1) → ∃ b,T v=some b) :
    PPath k lo hi (D j-D i+(j-i)) (pNode e (D i) T) (pNode x (D j) T) := by
  induction h with
  | nil i q => simpa using pNil (pNode q (D i) T) ⟨lower,upper⟩
  | @next i j e s q x se ss re rs rn rest ih =>
    have ij:=rest.span
    have di:=rise i le_rfl (by omega)
    have eqn : D i+(D (i+1)-D i-1)+1=D (i+1) := by omega
    have cross:=crossR (k:=k) (lo:=lo) (hi:=hi) e s q T (D i) (D (i+1)-D i-1) lower
      (by rw [eqn]; exact le_trans (mono _ _ (by omega) (by omega) le_rfl) upper)
      se ss (blank _ le_rfl (by omega)) (by rw [eqn]; exact blank _ (by omega) (by omega))
      (by intro v hl hu; exact cells i v le_rfl (by omega) hl (by rwa [eqn] at hu)) re rs rn
    rw [eqn] at cross
    have tail:=ih (le_trans lower (Nat.le_of_lt di)) upper
      (by intro u hl hu; exact rise u (by omega) hu)
      (by intro a b hl ab bj; exact mono a b (by omega) ab bj)
      (by intro u hl hu; exact blank u (by omega) hu)
      (by intro u v hl hu a b; exact cells u v (by omega) hu a b)
    simpa only [show D (i+1)-D i-1+2+(D j-D (i+1)+(j-(i+1)))=D j-D i+(j-i) by
      have endge:=mono _ _ (by omega) ij le_rfl
      omega] using pAppend cross tail
private theorem RouteL.execute {k i j e x lo hi} (h : RouteL k i j e x)
    (D : Nat → Nat) (T : Nat → Option Bool) (lower : lo ≤ D j) (upper : D i ≤ hi)
    (rise : ∀ u, j ≤ u → u < i → D u < D (u+1))
    (mono : ∀ a b, j ≤ a → a ≤ b → b ≤ i → D a ≤ D b)
    (blank : ∀ u, j ≤ u → u ≤ i → T (D u)=none)
    (cells : ∀ u v, j ≤ u → u < i → D u < v → v < D (u+1) → ∃ b,T v=some b) :
    PPath k lo hi (D i-D j+(i-j)) (pNode e (D i) T) (pNode x (D j) T) := by
  induction h with
  | nil i q => simpa using pNil (pNode q (D i) T) ⟨lower,upper⟩
  | @next i j e s q x se ss re rs rn rest ih =>
    have ij:=rest.span
    have di:=rise i (by omega) (by omega)
    have eqn : D i+(D (i+1)-D i-1)+1=D (i+1) := by omega
    have cross:=crossL (k:=k) (lo:=lo) (hi:=hi) e s q T (D i) (D (i+1)-D i-1)
      (le_trans lower (mono _ _ le_rfl ij (by omega))) (by rw [eqn]; exact upper)
      se ss (blank _ (by omega) (by omega)) (by rw [eqn]; exact blank _ (by omega) le_rfl)
      (by intro v hl hu; exact cells i v (by omega) (by omega) hl (by rwa [eqn] at hu)) re rs rn
    rw [eqn] at cross
    have tail:=ih lower (Nat.le_trans (Nat.le_of_lt di) upper)
      (by intro u hl hu; exact rise u hl (by omega))
      (by intro a b hl ab bj; exact mono a b hl ab (by omega))
      (by intro u hl hu; exact blank u hl (by omega))
      (by intro u v hl hu a b; exact cells u v hl (by omega) a b)
    simpa only [show D (i+1)-D i-1+2+(D i-D j+(i-j))=D (i+1)-D j+(i+1-j) by
      have startge:=mono _ _ le_rfl ij (by omega)
      omega] using pAppend cross tail
end FullIngressClosure
