import FullIngressClosure.CloneCertificates
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  for (key,aliasName) in [("CopyFrame","CopyFrame"),("CopyFrame.mk","copyFrameMk"),("fill","fill")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith "_private.FullIngressClosure.Clone." && n.toString.endsWith (".FullIngressClosure."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Nonunique installer frame term {key}: {found.map Prod.fst}"
private def width (r n j : Nat) : Nat :=
  match j with | 1 => n | 8 => n | 9 => 2*r | 10 => 3*r+3 | _ => r
private theorem next_delimiter (F r n j : Nat) (hj : j < 12) :
    SerializedBody.delimiter F r n (j+1)=SerializedBody.delimiter F r n j+width r n j+1 := by
  interval_cases j <;> dsimp only [SerializedBody.delimiter,width] <;> omega
private theorem delimiter_rise (F r n j : Nat) (hj : j < 12) :
    SerializedBody.delimiter F r n j < SerializedBody.delimiter F r n (j+1) := by
  rw [next_delimiter F r n j hj]
  omega
private theorem delimiter_mono (F r n a b : Nat) (ab : a ≤ b) (bound : b ≤ 12) :
    SerializedBody.delimiter F r n a ≤ SerializedBody.delimiter F r n b := by
  induction b with
  | zero =>
    have eq : a=0 := by omega
    subst a
    exact le_rfl
  | succ b ih =>
    by_cases same : a=b+1
    · subst a; exact le_rfl
    · exact (ih (by omega) (by omega)).trans (Nat.le_of_lt (delimiter_rise F r n b (by omega)))
private def Before (F r n b i : Nat) : Prop :=
  ∃ j : Fin 12,6 ≤ j.val ∧ j.val < b ∧ SerializedBody.delimiter F r n j.val < i ∧ i < SerializedBody.delimiter F r n (j.val+1)
private theorem before_below {F r n b i : Nat} (bound : b ≤ 12) (h : Before F r n b i) :
    i < SerializedBody.delimiter F r n b := by
  obtain ⟨j,_six,hi,lo,up⟩:=h
  exact up.trans_le (delimiter_mono F r n (j.val+1) b (by omega) bound)
private theorem before_step (F r n b i : Nat) (six : 6 ≤ b) (bound : b < 12) :
    Before F r n (b+1) i ↔ Before F r n b i ∨
      (SerializedBody.delimiter F r n b < i ∧ i < SerializedBody.delimiter F r n (b+1)) := by
  constructor
  · rintro ⟨j,j6,jb,lo,hi⟩
    by_cases old : j.val < b
    · exact Or.inl ⟨j,j6,old,lo,hi⟩
    · have eq : j.val=b := by omega
      exact Or.inr (by simpa only [eq] using And.intro lo hi)
  · rintro (old | ⟨lo,hi⟩)
    · obtain ⟨j,j6,jb,lo,hi⟩:=old
      exact ⟨j,j6,by omega,lo,hi⟩
    · exact ⟨⟨b,bound⟩,six,by dsimp; omega,lo,hi⟩
private instance (F r n b i : Nat) : Decidable (Before F r n b i) := by
  unfold Before
  infer_instance
private def stageTape (T : Nat → Option Bool) (F r n b f : Nat) : Nat → Option Bool :=
  fun i=>if SerializedBody.delimiter F r n b < i ∧ i ≤ SerializedBody.delimiter F r n b+f then some false
    else if Before F r n b i then some false else T i
private theorem partial_initial (T : Nat → Option Bool) (F r n : Nat) : stageTape T F r n 6 0=T := by
  funext i
  have empty : ¬Before F r n 6 i := by rintro ⟨j,j6,jb,_⟩; omega
  dsimp only [stageTape]
  rw [if_neg (by omega),if_neg empty]
private theorem fill_partial (T : Nat → Option Bool) (F r n b f u : Nat) :
    fill (stageTape T F r n b f) (SerializedBody.delimiter F r n b) (f+u)=stageTape T F r n b (f+u) := by
  funext i
  dsimp only [fill,stageTape]
  split_ifs <;> first | rfl | (exfalso; omega)
private theorem partial_complete (T : Nat → Option Bool) (F r n b : Nat) (six : 6 ≤ b) (bound : b < 12) :
    stageTape T F r n b (width r n b)=stageTape T F r n (b+1) 0 := by
  funext i
  have full : (SerializedBody.delimiter F r n b < i ∧ i ≤ SerializedBody.delimiter F r n b+width r n b) ↔
      (SerializedBody.delimiter F r n b < i ∧ i < SerializedBody.delimiter F r n (b+1)) := by
    rw [next_delimiter F r n b bound]
    omega
  have zeroRight : stageTape T F r n (b+1) 0 i=
      (if Before F r n (b+1) i then some false else T i) := by
    dsimp only [stageTape]
    rw [if_neg (by omega)]
  rw [zeroRight]
  dsimp only [stageTape]
  simp only [before_step F r n b i six bound,full]
  split_ifs <;> first | rfl | tauto
private structure Six (T : Nat → Option Bool) (F r n : Nat) : Prop where
  blank : ∀ j,j ≤ 6 → T (SerializedBody.delimiter F r n j)=none
  cells : ∀ j i,j < 6 → SerializedBody.delimiter F r n j < i → i < SerializedBody.delimiter F r n (j+1) → ∃ bit,T i=some bit
  fresh : ∀ i,SerializedBody.delimiter F r n 6 < i → i ≤ SerializedBody.delimiter F r n 12 → T i=none
private theorem before_not_delimiter (F r n b u : Nat) (bound : u ≤ 12) :
    ¬Before F r n b (SerializedBody.delimiter F r n u) := by
  rintro ⟨j,_six,_jb,lo,hi⟩
  have jbound:=j.isLt
  by_cases order : u ≤ j.val
  · have h:=delimiter_mono F r n u j.val order (by omega)
    omega
  · have h:=delimiter_mono F r n (j.val+1) u (by omega) bound
    omega
private theorem partial_blank {T F r n} (frame : Six T F r n) (b f u : Nat)
    (b6 : 6 ≤ b) (b12 : b ≤ 12) (ub : u ≤ b) :
    stageTape T F r n b f (SerializedBody.delimiter F r n u)=none := by
  have order:=delimiter_mono F r n u b ub b12
  dsimp only [stageTape]
  rw [if_neg (by omega),if_neg (before_not_delimiter F r n b u (by omega))]
  by_cases old : u ≤ 6
  · exact frame.blank u old
  · have strict:=delimiter_rise F r n 6 (by decide)
    change SerializedBody.delimiter F r n 6 < SerializedBody.delimiter F r n 7 at strict
    have mono:=delimiter_mono F r n 7 u (by omega) (by omega)
    exact frame.fresh _ (by omega) (delimiter_mono F r n u 12 (by omega) le_rfl)
private theorem partial_old {T F r n b f i} (six : 6 ≤ b) (bound : b ≤ 12)
    (lo : i ≤ SerializedBody.delimiter F r n 6) : stageTape T F r n b f i=T i := by
  have d:=delimiter_mono F r n 6 b six bound
  have outside : ¬Before F r n b i := by
    rintro ⟨j,j6,_jb,jlo,_hi⟩
    have low:=delimiter_mono F r n 6 j.val j6 (Nat.le_of_lt j.isLt)
    omega
  dsimp only [stageTape]
  rw [if_neg (by omega),if_neg outside]
private theorem partial_cells {T F r n} (frame : Six T F r n) (b f a i : Nat)
    (six : 6 ≤ b) (bound : b ≤ 12) (ab : a < b)
    (lo : SerializedBody.delimiter F r n a < i) (hi : i < SerializedBody.delimiter F r n (a+1)) :
    ∃ bit,stageTape T F r n b f i=some bit := by
  have upper:=delimiter_mono F r n (a+1) b (by omega) bound
  dsimp only [stageTape]
  rw [if_neg (by omega)]
  by_cases old : a < 6
  · have sixUpper:=delimiter_mono F r n (a+1) 6 (by omega) (by decide)
    have outside : ¬Before F r n b i := by
      rintro ⟨j,j6,_jb,jlo,_hi⟩
      have low:=delimiter_mono F r n 6 j.val j6 (Nat.le_of_lt j.isLt)
      omega
    rw [if_neg outside]
    exact frame.cells a i old lo hi
  · have inside : Before F r n b i:=⟨⟨a,by omega⟩,by dsimp; omega,ab,lo,hi⟩
    rw [if_pos inside]
    exact ⟨false,rfl⟩
private theorem copy_frame {T F r n} (frame : Six T F r n) (lo P a b f : Nat)
    (a6 : a < 6) (b6 : 6 ≤ b) (b12 : b < 12)
    (fits : f+width r n a ≤ width r n b)
    (lower : lo ≤ SerializedBody.delimiter F r n 0) (upper : SerializedBody.delimiter F r n 12 ≤ P) :
    CopyFrame (stageTape T F r n b f) lo P a b (width r n a) f (SerializedBody.delimiter F r n) := by
  let D:=SerializedBody.delimiter F r n
  change D 12 ≤ P at upper
  have next:=next_delimiter F r n b b12
  change D (b+1)=D b+width r n b+1 at next
  have geomEnd : D b+f+width r n a+1 ≤ D 12 := by
    calc
      D b+f+width r n a+1 ≤ D b+width r n b+1 := by omega
      _ = D (b+1) := next.symm
      _ ≤ D 12 := delimiter_mono F r n (b+1) 12 (by omega) le_rfl
  have endFit : D b+f+width r n a+1 ≤ P := geomEnd.trans upper
  refine copyFrameMk (by omega) (lower.trans (delimiter_mono F r n 0 a (Nat.zero_le a) (by omega))) endFit
    (next_delimiter F r n a (by omega)) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro u v _ uv vb
    exact delimiter_mono F r n u v uv (by omega)
  · intro u _ ub
    exact delimiter_rise F r n u (by omega)
  · intro u _ ub
    exact partial_blank frame b f u b6 (by omega) ub
  · intro u i _ ub il iu
    exact partial_cells frame b f u i b6 (by omega) ub il iu
  · intro i il iu
    apply partial_cells frame b f a i b6 (by omega) (by omega) il
    rwa [next_delimiter F r n a (by omega)]
  · intro i il iu
    dsimp only [stageTape]
    rw [if_pos ⟨il,iu⟩]
  · intro i il iu
    have db6:=delimiter_mono F r n 6 b b6 (by omega)
    have beyond : ¬Before F r n b i:=by intro h; have h':=before_below (by omega) h; omega
    dsimp only [stageTape]
    rw [if_neg (by omega),if_neg beyond]
    exact frame.fresh i
      (db6.trans_lt ((Nat.le_add_right _ f).trans_lt il))
      (iu.trans geomEnd)
end FullIngressClosure
