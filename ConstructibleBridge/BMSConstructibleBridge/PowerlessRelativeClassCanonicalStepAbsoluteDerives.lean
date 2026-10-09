import BMSConstructibleBridge.PowerlessRelativeClassCanonicalStepAbsolute
import BMSConstructibleBridge.PowerlessRelativeClassFormulaInstances

/-! # 原规范后继双向 Class 读数的正式对象模式

纯隶属 ℒ、原 Z₂、原 num/set 推导关系。全部实际参数、原母序、
母集传递性、原 Def 和同一类内静态包的守卫逐项写入句子。正式
结论是同一 Uniform 原公式的 iff，不引入完整 Class 理论或选择原则。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalStepAbsoluteDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeClassFormulaInstances (instance_m instance_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

private abbrev context_m : SortContext ℒ :=
  [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set]

private abbrev B_m : Term ℒ [] context_m .set := .fvar .here
private abbrev ω_m : Term ℒ [] context_m .set := .fvar (.there .here)
private abbrev A_m : Term ℒ [] context_m .set := .fvar (.there (.there .here))
private abbrev P_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there .here)))
private abbrev e_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there .here))))
private abbrev t₁_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there .here)))))
private abbrev t₂_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
private abbrev t₃_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
private abbrev Pair_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
private abbrev N_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
private abbrev Valid_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
private abbrev D_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
private abbrev E_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))

private def parameters_m (v : Variable context_m .set) : Term ℒ [] context_m .set := .fvar v

private def static_m : Formula ℒ [] context_m :=
  PowerlessSatisfactionExistenceSyntax.static_m ω_m e_m t₁_m t₂_m t₃_m Pair_m N_m Valid_m

private def step_m : Formula ℒ [] context_m :=
  SecondOrderCanonicalOrderUniform.step_m ω_m A_m P_m e_m t₁_m t₂_m t₃_m Pair_m Valid_m D_m E_m

def schema_m : Formula ℒ [] context_m :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B_m) <|
    .imp (PowerlessRelativeClassFormulaInstances.members_m context_m B_m parameters_m) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω_m) <|
        .imp (instance_m static_m B_m parameters_m) <|
          .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m A_m P_m) <|
            .imp (PowerlessRelativeHierarchyDerives.transitive_m A_m) <|
              .imp (PowerlessMemberDefSyntax.global_m A_m D_m) <|
                .iff (instance_m step_m B_m parameters_m) step_m

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeClassFormulaInstances.members_l K, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    PowerlessMemberDefDerives.formula_l K]
  intro hBase hMembers hω hStatic hP hTrans hDef
  let ξ : Env (PowerlessRelativeClassStructure.structure_l hℳ (B_m.eval η) hBase) [] context_m := {
    boundVal := fun v => nomatch v
    freeVal := fun {s} v => match s with | .set => ⟨η.freeVal v, hMembers v⟩ }
  have hν : ∀ v, (parameters_m v).eval η = (ξ.freeVal v).val := fun _ => rfl
  have hStatic' : PowerlessSatisfactionExistenceSyntax.static_l
      (𝒩 := PowerlessRelativeClassStructure.structure_l hℳ (B_m.eval η) hBase)
      (ω_m.eval ξ) (e_m.eval ξ) (t₁_m.eval ξ) (t₂_m.eval ξ) (t₃_m.eval ξ)
      (Pair_m.eval ξ) (N_m.eval ξ) (Valid_m.eval ξ) := by
    exact (PowerlessSatisfactionExistenceSyntax.static_formula_l ξ _ _ _ _ _ _ _ _).mp
      ((instance_l K static_m η B_m parameters_m ξ rfl hν).mp hStatic)
  have hωEq : (ω_m.eval ξ).val = K.omega := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have hRead := PowerlessRelativeClassCanonicalStepAbsolute.iff_l
    K (ω_m.eval ξ) (A_m.eval ξ) (P_m.eval ξ) (e_m.eval ξ) (t₁_m.eval ξ)
      (t₂_m.eval ξ) (t₃_m.eval ξ) (Pair_m.eval ξ) (N_m.eval ξ) (Valid_m.eval ξ)
      (D_m.eval ξ) (E_m.eval ξ) hωEq hStatic' hP (fun x y hx hy => hTrans x hx y hy) hDef
  exact (instance_l K step_m η B_m parameters_m ξ rfl hν).trans
    ((SecondOrderCanonicalOrderUniform.step_formula_l ξ
      ω_m A_m P_m e_m t₁_m t₂_m t₃_m Pair_m Valid_m D_m E_m).trans
      (hRead.trans (SecondOrderCanonicalOrderUniform.step_formula_l η
        ω_m A_m P_m e_m t₁_m t₂_m t₃_m Pair_m Valid_m D_m E_m).symm))

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalStepAbsoluteDerives
