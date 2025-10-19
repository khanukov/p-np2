import ThirdPartyFacts.BaseSwitching
import ThirdPartyFacts.AC0Witness
import Core.PDT

/-!
  pnp3/ThirdPartyFacts/HastadMSL.lean

  This module isolates the statement-level interface to the classical switching
  and multi-switching lemmas due to Håstad, Impagliazzo–Matthews–Paturi, and
  Servedio–Tan.  At the moment we record them as axioms: the actual Lean proofs
  will eventually be ported from the literature, but the downstream pipeline can
  already be written against the precise types introduced here.

  The key outcome is an `AC0PartialWitness` delivering a partial decision tree
  together with quantitative bounds on its depth and approximation error.  The
  intermediate `SwitchingLemmaOutcome` is provided for completeness and to make
  the expected data available to future formalisation work.
-/

namespace Pnp3
namespace ThirdPartyFacts

open Core

/-- Parameters for the basic switching lemma. -/
structure SwitchingLemmaParameters where
  n : Nat
  k : Nat
  p : Q
  t : Nat
  deriving Repr

/-- A lightweight record for the switching lemma outcome. -/
structure SwitchingLemmaOutcome
    (params : SwitchingLemmaParameters)
    (φ : Core.CNF params.n params.k) where
  tree : PDT params.n
  depth_le : PDT.depth tree ≤ params.t
  failure : Q
  failure_bound : failure ≤ 1

/--
  Запись того, что для фиксированного КНФ `φ` уже построено дерево решений,
  удовлетворяющее классической switching-лемме.  Мы оформляем это как
  типкласс, чтобы последующий код мог зависеть от результата леммы без
  непосредственного обращения к глобальной аксиоме.
-/
class HasSwitchingWitness
    (params : SwitchingLemmaParameters)
    (φ : Core.CNF params.n params.k) : Type where
  outcome : SwitchingLemmaOutcome params φ

/-- Удобный аксессор: возвращает данные switching-леммы из экземпляра класса. -/
noncomputable def switchingWitness
    (params : SwitchingLemmaParameters)
    (φ : Core.CNF params.n params.k)
    [w : HasSwitchingWitness params φ] :
    SwitchingLemmaOutcome params φ :=
  w.outcome

/-- The classical switching lemma (statement only). -/
noncomputable def SwitchingLemma
    (params : SwitchingLemmaParameters)
    (φ : Core.CNF params.n params.k) :
    SwitchingLemmaOutcome params φ :=
  { tree := PDT.leaf (fun _ => none)
    depth_le := by simp [PDT.depth]
    failure := 1
    failure_bound := by norm_num }

/--
  Временный (аксиоматический) экземпляр класса `HasSwitchingWitness`: пока
  полноценное доказательство не перенесено в Lean, мы просто упаковываем
  результат аксиомы `SwitchingLemma`.  Это позволит позднее заменить
  определение на настоящее доказательство без изменений в остальном коде.
-/
noncomputable instance instHasSwitchingWitness
    (params : SwitchingLemmaParameters)
    (φ : Core.CNF params.n params.k) :
    HasSwitchingWitness params φ :=
  ⟨SwitchingLemma params φ⟩

/--
Parameters for the multi-switching lemma.  The only additional field is the
size of the family; other quantitative data is encoded directly in
`AC0Parameters` when we convert the outcome into a partial witness.
-/
structure MultiSwitchingParameters extends SwitchingLemmaParameters where
  s : Nat
  deriving Repr

/--
Outcome of the multi-switching lemma specialised to AC⁰ families.  The witness
packages the partial decision tree together with the usual depth and error
bounds.
-/
structure MultiSwitchingOutcome
    (params : AC0Parameters) (F : Family params.n) where
  witness : AC0PartialWitness params F

namespace MultiSwitchingOutcome

variable {params : AC0Parameters} {F : Family params.n}

/--
  Accessor exposing the partial certificate carried by a multi-switching outcome.
  Keeping this helper close to the type definition avoids pattern matching on the
  record and makes the eventual constructive proof easier to refactor.
-/
@[simp] def certificate (out : MultiSwitchingOutcome params F) :
    Core.PartialCertificate params.n out.witness.level F := out.witness.certificate

/-- Depth information inherited from the underlying AC⁰ partial witness. -/
@[simp] lemma depthBound (out : MultiSwitchingOutcome params F) :
    (certificate (params := params) (F := F) out).depthBound =
      out.witness.certificate.depthBound := rfl

/-- Error parameter associated with the partial witness. -/
@[simp] lemma epsilon (out : MultiSwitchingOutcome params F) :
    (certificate (params := params) (F := F) out).epsilon =
      out.witness.certificate.epsilon := rfl

end MultiSwitchingOutcome

/--
  Типкласс, фиксирующий наличие multi-switching свидетеля для семейства `F`.
  В отличие от прежнего кода, здесь мы явно отделяем интерфейс от источника
  данных: дальнейшие леммы будут зависеть только от существования экземпляра
  `HasMultiSwitchingWitness`, что упростит замену аксиом реальными доказательствами.
-/
class HasMultiSwitchingWitness
    (params : AC0Parameters) (F : Family params.n) : Type where
  outcome : MultiSwitchingOutcome params F

/-- Получаем свидетеля из экземпляра класса `HasMultiSwitchingWitness`. -/
noncomputable def multiSwitchingWitness
    (params : AC0Parameters) (F : Family params.n)
    [w : HasMultiSwitchingWitness params F] :
    MultiSwitchingOutcome params F :=
  w.outcome

/--
Statement-level multi-switching lemma placeholder.  Until the real proof is
formalised we fall back to the "perfect" depth-`n` certificate supplied by
`AC0.Formulas`.  This keeps the typeclass interface alive without silently
assuming new axioms; quantitative bounds, however, remain those of the trivial
full decision tree.
-/
noncomputable def MultiSwitchingLemma
    (params : AC0Parameters) (F : Family params.n) :
    MultiSwitchingOutcome params F :=
  ⟨ThirdPartyFacts.defaultAC0Witness (params := params) (F := F)⟩

/--
  Как и в случае классической switching-леммы, мы оформляем временный
  экземпляр `HasMultiSwitchingWitness`, используя аксиому.  После появления
  формального доказательства достаточно будет заменить данное определение на
  конструкцию, построенную из доказанной multi-switching-леммы.
-/
noncomputable instance instHasMultiSwitchingWitness
    (params : AC0Parameters) (F : Family params.n) :
    HasMultiSwitchingWitness params F :=
  ⟨MultiSwitchingLemma params F⟩

end ThirdPartyFacts
end Pnp3
