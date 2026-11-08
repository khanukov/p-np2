import Stream.Audit
namespace Cursor.Transport
open Pnp3.Complexity.Uniform.V1
private def mapConfig {A B : UniformTM} (f : Fin A.stateCount → Fin B.stateCount)
    {N C : Nat} (c : Config A.stateCount N C) : Config B.stateCount N C :=
  ⟨f c.state,c.head,c.tape⟩
private theorem fixed_run (A : UniformTM) {N C : Nat} (c : Config A.stateCount N C)
    (fixed : A.stepConfig c=c) (t : Nat) : A.run t c=c := by
  induction t with
  | zero => rfl
  | succ t ih => simpa only [UniformTM.run,ih] using fixed
private theorem first (A : UniformTM) (E : Fin A.stateCount → Prop) {N C : Nat}
    (c : Config A.stateCount N C) (T : Nat) :
    (∃ t, t≤T ∧ E (A.run t c).state ∧ ∀ u, u<t → ¬E (A.run u c).state) ∨
      (∀ u, u≤T → ¬E (A.run u c).state) := by
  classical
  induction T with
  | zero =>
    by_cases h : E c.state
    · exact Or.inl ⟨0,le_rfl,h,by intro u hu; omega⟩
    · exact Or.inr (by
        intro u hu
        have e : u=0 := by omega
        subst u
        exact h)
  | succ T ih =>
    rcases ih with ⟨t,ht,he,hm⟩ | no
    · exact Or.inl ⟨t,by omega,he,hm⟩
    · by_cases h : E (A.run (T+1) c).state
      · exact Or.inl ⟨T+1,le_rfl,h,by intro u hu; exact no u (by omega)⟩
      · exact Or.inr (by
          intro u hu
          by_cases e : u=T+1
          · simpa only [e] using h
          · exact no u (by omega))
private theorem step_map {A B : UniformTM} (f : Fin A.stateCount → Fin B.stateCount)
    {N C : Nat} (c : Config A.stateCount N C)
    (row : ∀ b, B.step (f c.state) b =
      (f (A.step c.state b).1,(A.step c.state b).2)) :
    B.stepConfig (mapConfig f c)=mapConfig f (A.stepConfig c) := by
  apply Config.ext_parts
  · exact congrArg Prod.fst (row (c.tape c.head))
  · change moveHead c.head _=moveHead c.head _
    dsimp only [mapConfig]
    rw [row]
  · funext i
    change (if i=c.head then (B.step (f c.state) (c.tape c.head)).2.1 else c.tape i)=_
    rw [row]
    rfl
/-- Activating formerly inert rows preserves the WHOLE first-arrival Config.
The conclusion never transports a padded old endpoint through changed rows. -/
theorem first_changed_rows (A B : UniformTM) (f : Fin A.stateCount → Fin B.stateCount)
    (E : Fin A.stateCount → Prop)
    (inert : ∀ {N C} (c : Config A.stateCount N C), E c.state → A.stepConfig c=c)
    (rows : ∀ s, ¬E s → ∀ b, B.step (f s) b=(f (A.step s b).1,(A.step s b).2))
    {N C : Nat} (c : Config A.stateCount N C) (T : Nat) (hit : E (A.run T c).state) :
    ∃ t, t≤T ∧ (∀ u, u<t → ¬E (A.run u c).state) ∧
      A.run t c=A.run T c ∧
      B.run t ⟨f c.state,c.head,c.tape⟩=
        ⟨f (A.run T c).state,(A.run T c).head,(A.run T c).tape⟩ ∧
      (∀ u, u≤t → B.run u ⟨f c.state,c.head,c.tape⟩=
        ⟨f (A.run u c).state,(A.run u c).head,(A.run u c).tape⟩) := by
  obtain ⟨t,ht,he,hm⟩ := (first A E c T).resolve_right (fun no => no T le_rfl hit)
  have eq : A.run T c=A.run t c := by
    rw [show T=t+(T-t) by omega,A.run_add]
    exact fixed_run A _ (inert _ he) _
  have path : ∀ u, u≤t → B.run u (mapConfig f c)=mapConfig f (A.run u c) := by
    intro u
    induction u with
    | zero => intro _; rfl
    | succ u ih =>
      intro hu
      rw [UniformTM.run,ih (by omega),step_map f _ (rows _ (hm u (by omega)))]
      rfl
  exact ⟨t,ht,hm,eq.symm,(by simpa only [eq] using path t le_rfl),path⟩
/-- A run ending outside the old inert set could never have entered it.
Consequently an old literal rejection keeps its exact time, head and tape. -/
theorem avoid_changed_rows (A B : UniformTM) (f : Fin A.stateCount → Fin B.stateCount)
    (E : Fin A.stateCount → Prop)
    (inert : ∀ {N C} (c : Config A.stateCount N C), E c.state → A.stepConfig c=c)
    (rows : ∀ s, ¬E s → ∀ b, B.step (f s) b=(f (A.step s b).1,(A.step s b).2))
    {N C : Nat} (c : Config A.stateCount N C) (T : Nat) (outside : ¬E (A.run T c).state) :
    B.run T ⟨f c.state,c.head,c.tape⟩=⟨f (A.run T c).state,(A.run T c).head,(A.run T c).tape⟩ := by
  have absent (u : Nat) (hu : u≤T) : ¬E (A.run u c).state := by
    intro h
    have same : A.run T c=A.run u c := by
      rw [show T=u+(T-u) by omega,A.run_add]
      exact fixed_run A _ (inert _ h) _
    exact outside (by rw [same]; exact h)
  have path : ∀ u, u≤T → B.run u (mapConfig f c)=mapConfig f (A.run u c) := by
    intro u
    induction u with
    | zero => intro _; rfl
    | succ u ih =>
      intro hu
      rw [UniformTM.run,ih (by omega),step_map f _ (rows _ (absent u (by omega)))]
      rfl
  exact path T le_rfl
end Cursor.Transport
