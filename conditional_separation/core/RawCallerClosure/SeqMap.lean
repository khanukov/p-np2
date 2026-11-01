import RawCallerClosure.Embedding
namespace RawCallerClosure
open Pnp3.Complexity.Uniform.V1
private def seqMap (L A B : UniformTM) (f : Fin A.stateCount → Fin B.stateCount)
    (s : Fin (L.seq A).stateCount) : Fin (L.seq B).stateCount :=
  if h:s.val < L.stateCount then L.seqLeft B ⟨s.val,h⟩
  else L.seqRight B (f ⟨s.val-L.stateCount,by have bound:=s.isLt;change s.val < L.stateCount+A.stateCount at bound;omega⟩)
private theorem seqMap_left (L A B : UniformTM) (f : Fin A.stateCount → Fin B.stateCount) (s : Fin L.stateCount) :
    seqMap L A B f (L.seqLeft A s)=L.seqLeft B s := by
  unfold seqMap
  rw [dif_pos (show (L.seqLeft A s).val < L.stateCount from s.isLt)]
  rfl
private theorem seqMap_right (L A B : UniformTM) (f : Fin A.stateCount → Fin B.stateCount) (s : Fin A.stateCount) :
    seqMap L A B f (L.seqRight A s)=L.seqRight B (f s) := by
  unfold seqMap
  rw [dif_neg (by change ¬L.stateCount+s.val < L.stateCount;omega)]
  congr 2
  apply Fin.ext
  change L.stateCount+s.val-L.stateCount=s.val
  omega
private theorem seqMap_route (L A B : UniformTM) (f : Fin A.stateCount → Fin B.stateCount)
    (start:f A.start=B.start) (reject:f A.reject=B.reject) (s : Fin L.stateCount) :
    seqMap L A B f (L.seqRoute A s)=L.seqRoute B s := by
  unfold UniformTM.seqRoute
  split_ifs
  · rw [seqMap_right,start]
  · rw [seqMap_right,reject]
  · exact seqMap_left L A B f s
private theorem seqMap_rows (L A B : UniformTM) (f : Fin A.stateCount → Fin B.stateCount)
    (start:f A.start=B.start) (reject:f A.reject=B.reject)
    (E : Fin A.stateCount → Prop)
    (rows:∀ s,¬E s → ∀ b,B.step (f s) b=(f (A.step s b).1,(A.step s b).2))
    (s : Fin (L.seq A).stateCount)
    (clear:∀ q,s=L.seqRight A q → ¬E q) (b : Option Bool) :
    (L.seq B).step (seqMap L A B f s) b=
      (seqMap L A B f ((L.seq A).step s b).1,((L.seq A).step s b).2) := by
  by_cases left:s.val < L.stateCount
  · let q:Fin L.stateCount:=⟨s.val,left⟩
    have eq:s=L.seqLeft A q:=Fin.ext rfl
    rw [eq,seqMap_left,UniformTM.seq_step_left,UniformTM.seq_step_left]
    rw [seqMap_route L A B f start reject]
  · let q:Fin A.stateCount:=⟨s.val-L.stateCount,by have bound:=s.isLt;change s.val < L.stateCount+A.stateCount at bound;omega⟩
    have eq:s=L.seqRight A q:=by apply Fin.ext;change s.val=L.stateCount+(s.val-L.stateCount);omega
    rw [eq,seqMap_right,UniformTM.seq_step_right,UniformTM.seq_step_right]
    rw [rows q (clear q eq) b,seqMap_right]
private theorem seqMap_val (L A B : UniformTM) (f : Fin A.stateCount → Fin B.stateCount)
    (value:∀ s,(f s).val=s.val) (s : Fin (L.seq A).stateCount) :
    (seqMap L A B f s).val=s.val := by
  unfold seqMap
  split_ifs with h
  · rfl
  · change L.stateCount+(f _).val=s.val
    rw [value]
    change L.stateCount+(s.val-L.stateCount)=s.val
    omega
end RawCallerClosure
