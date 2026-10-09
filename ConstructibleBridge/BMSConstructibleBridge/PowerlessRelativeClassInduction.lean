import BMSConstructibleBridge.PowerlessRelativeClassOmegaAbsolute
import BMSConstructibleBridge.PowerlessRelativeClassRelativization
import BMSConstructibleBridge.PowerlessBMSQuotientInduction

/-! # 相对类内公式的实际内部自然数归纳

先把纯类公式相对化并重排自由参数，再调用其原 Z₂ 图翻译的归纳实例。
整个内部数域都被覆盖；不把非标准长度换成宿主 Nat 或 List。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassInduction

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private def swap_m {Δ : SortContext ℒ} :
    VariableSubstitution ℒ (.set :: .set :: Δ) [] (.set :: .set :: Δ)
  | _, .here => .fvar (.there .here)
  | _, .there .here => .fvar .here
  | _, .there (.there v) => .fvar (.there (.there v))

def formula_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Formula ℒ [] (.set :: .set :: Δ) :=
  (PowerlessRelativeClassRelativization.formula_m φ).substitute
    (show Substitution ℒ [] (.set :: .set :: Δ) [] (.set :: .set :: Δ) from
      .map (fun v => nomatch v) swap_m)

theorem induction_derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m []
      (SecondOrderArithmetic.induction_m (GraphTranslation.form_m (formula_m φ))) :=
  GraphTranslation.induction_m (formula_m φ)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

def number_l (K : source_coding_l hℳ) (n : SecondOrderModel.num_l ℳ) : type_l hℳ B :=
  ⟨(numberCode_l K n).val, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase
    (PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
      (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)) (numberCode_l K n).property⟩

theorem formula_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (η : Env (structure_l hℳ B hBase) [] Δ)
    (n : SecondOrderModel.num_l ℳ) :
    (formula_m φ).satisfies
      (((PowerlessRelativeClassRelativization.env_l η).pushFree B).pushFree (numberCode_l K n).val) ↔
        φ.satisfies (η.pushFree (number_l (hBase := hBase) K n)) := by
  unfold formula_m
  rw [Formula.satisfies_substitute]
  have hEnv :
      (((PowerlessRelativeClassRelativization.env_l η).pushFree (sort := SetTheory.SetSort.set) B).pushFree
        (sort := SetTheory.SetSort.set) (numberCode_l K n).val).pullback
        (show Substitution ℒ [] (.set :: .set :: Δ) [] (.set :: .set :: Δ) from
          .map (fun v => nomatch v) swap_m) =
      (PowerlessRelativeClassRelativization.env_l
        (η.pushFree (sort := SetTheory.SetSort.set) (number_l (hBase := hBase) K n))).pushFree B := by
    apply Env.ext
    · intro _ v; nomatch v
    · intro s v
      cases s
      cases v with
      | here => rfl
      | there v => cases v <;> rfl
  rw [hEnv]
  exact PowerlessRelativeClassRelativization.formula_l K φ _

theorem induction_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (η : Env (structure_l hℳ B hBase) [] Δ)
    (hZero : φ.satisfies (η.pushFree (number_l (hBase := hBase) K (SecondOrderModel.zero_l ℳ))))
    (hStep : ∀ n : SecondOrderModel.num_l ℳ,
      φ.satisfies (η.pushFree (number_l (hBase := hBase) K n)) →
        φ.satisfies (η.pushFree (number_l (hBase := hBase) K (SecondOrderModel.succ_l n)))) :
    ∀ n : SecondOrderModel.num_l ℳ, φ.satisfies (η.pushFree (number_l (hBase := hBase) K n)) := by
  have h := PowerlessBMSQuotientInduction.induction_l K (formula_m φ)
    ((PowerlessRelativeClassRelativization.env_l η).pushFree B)
    ((formula_l K φ η _).mpr hZero)
    (fun n hn => (formula_l K φ η _).mpr (hStep n ((formula_l K φ η n).mp hn)))
  exact fun n => (formula_l K φ η n).mp (h n)

#print axioms induction_derives_m
#print axioms induction_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassInduction
