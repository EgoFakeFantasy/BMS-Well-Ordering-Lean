import BMSConstructibleBridge.SecondOrderMemberDefPacketFormula
import BMSConstructibleBridge.SecondOrderMemberDefGraphFormula
import BMSConstructibleBridge.SecondOrderFormulaArguments
import YesMetaZFC.Automation.RelationalEnvironment

/-! # 唯一原图 Def 操作的实际公式

默认成员编号、七项证书和两张中间图以异质存在块绑定。原图、根和输出
是公开参数；完整边规格与筛选条件全部保留，不添加选择公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalMemberDefFormula

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open Automation.RelationalTranslation (weakenTerm existsBlock)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

abbrev context_m : SortContext signature_m :=
  [.set, .set, .set, .set, .set, .set, .set, .set, .num, .num, .set, .set, .set]

def certificate_m : Formula signature_m [] context_m :=
  let V : Term signature_m [] context_m .set := .fvar .here
  let E : Term signature_m [] context_m .set := .fvar (.there .here)
  let D : Term signature_m [] context_m .set := .fvar (.there (.there .here))
  let Q : Term signature_m [] context_m .set := .fvar (.there (.there (.there .here)))
  let R : Term signature_m [] context_m .set := .fvar (.there (.there (.there (.there .here))))
  let T : Term signature_m [] context_m .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let F : Term signature_m [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  let A : Term signature_m [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
  let r : Term signature_m [] context_m .num := .fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
  let a : Term signature_m [] context_m .num := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
  let G : Term signature_m [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
  let P : Term signature_m [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
  let W : Term signature_m [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))
  .conj (SecondOrderFormulaArguments.formula_m SecondOrderMemberDefPacketFormula.formula_m
    (.cons V (.cons E (.cons D (.cons Q (.cons R (.cons T (.cons F (.cons A (.cons r (.cons a .nil))))))))))) <|
    .conj (SecondOrderMemberDefGraphFormula.layer_m A F r G) <|
      .conj (SecondOrderMemberDefGraphFormula.selection_m V E P) (SecondOrderMemberDefGraphFormula.graft_m G P W)

theorem certificate_pure_m : language_m certificate_m = true := by
  dsimp only [certificate_m]
  change (language_m _ && (language_m _ && (language_m _ && language_m _))) = true
  simp only [Bool.and_eq_true]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact SecondOrderFormulaArguments.pure_m _ _ SecondOrderMemberDefPacketFormula.pure_m rfl
  · apply SecondOrderRelationSpecification.pure_m _ _ _ (pure_language_m _ rfl) rfl
    intro s v
    match v with
    | .here => rfl
    | .there .here => rfl
    | .there (.there .here) => rfl
  · apply SecondOrderSetSpecification.pure_m _ _ _
      (SecondOrderSelectedSubsetCollection.pure_m _ SecondOrderLegalFormulaIndex.pure_m) rfl
    intro s v
    match v with
    | .here => rfl
    | .there .here => rfl
  · apply SecondOrderRelationSpecification.pure_m _ _ _ SecondOrderGraft.pure_m rfl
    intro s v
    match v with
    | .here => rfl
    | .there .here => rfl

def instance_m {Γ Δ : SortContext signature_m} (A : Term signature_m Γ Δ .set)
    (r a : Term signature_m Γ Δ .num) (V E D Q R T F G P W : Term signature_m Γ Δ .set) :
    Formula signature_m Γ Δ := SecondOrderFormulaArguments.formula_m certificate_m
      (.cons V (.cons E (.cons D (.cons Q (.cons R (.cons T (.cons F (.cons A (.cons r (.cons a
        (.cons G (.cons P (.cons W .nil)))))))))))))

abbrev witnesses_m : SortContext signature_m := [.num, .set, .set, .set, .set, .set, .set, .set, .set, .set]

def formula_m {Γ Δ : SortContext signature_m} (A : Term signature_m Γ Δ .set)
    (r : Term signature_m Γ Δ .num) (W : Term signature_m Γ Δ .set) : Formula signature_m Γ Δ :=
  existsBlock witnesses_m <|
    .conj (SecondOrderFormulaArguments.formula_m SecondOrderMemberDefault.formula_m
      (.cons (.bvar .here) (.cons (weakenTerm witnesses_m r) (.cons (weakenTerm witnesses_m A) .nil)))) <|
      instance_m (weakenTerm witnesses_m A) (weakenTerm witnesses_m r) (.bvar .here)
        (.bvar (.there .here)) (.bvar (.there (.there .here))) (.bvar (.there (.there (.there .here))))
        (.bvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there (.there (.there (.there .here))))))
        (.bvar (.there (.there (.there (.there (.there (.there .here)))))))
        (.bvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
        (.bvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
        (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
        (weakenTerm witnesses_m W)

theorem pure_m {Γ Δ : SortContext signature_m} (A : Term signature_m Γ Δ .set)
    (r : Term signature_m Γ Δ .num) (W : Term signature_m Γ Δ .set)
    (hA : pure_term_m A = true) (hr : pure_term_m r = true) (hW : pure_term_m W = true) :
    language_m (formula_m A r W) = true := by
  rw [formula_m, SecondOrderFormulaArguments.block_pure_m]
  change (language_m _ && language_m _) = true
  simp only [Bool.and_eq_true]
  constructor
  · apply SecondOrderFormulaArguments.pure_m _ _ SecondOrderMemberDefault.pure_m
    simp only [pure_args_m, pure_term_m, SecondOrderFormulaArguments.weaken_pure_m, hA, hr]
    rfl
  · apply SecondOrderFormulaArguments.pure_m _ _ certificate_pure_m
    simp only [pure_args_m, pure_term_m, SecondOrderFormulaArguments.weaken_pure_m, hA, hr, hW]
    rfl

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalMemberDefFormula
