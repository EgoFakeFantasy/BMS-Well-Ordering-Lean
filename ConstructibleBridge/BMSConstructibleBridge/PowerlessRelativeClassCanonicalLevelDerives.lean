import BMSConstructibleBridge.PowerlessRelativeClassCanonicalLevelReading
import BMSConstructibleBridge.PowerlessRelativeClassFormulaInstances
import BMSConstructibleBridge.SecondOrderCanonicalLevelDerives

/-! # 类内无枚举规范历史的原规范层 Z₂ 推导

保留完整局部检查器包、给定层图 f 与比较图 g。正式句子从真正
Class 规格推出全部 raw 输出的原规范层读数；原参考递归图已由
原 Z₂ 实际构造并消去，不是模式的额外输入。不宣称原计数式
层次公式全局绝对，也不宣称内部可数性及 BMS 终局已完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalLevelDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeClassFormulaInstances (instance_m instance_l)
open SecondOrderCanonicalLevelDerives (guard_m guard_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) := v.weakenBound SetTheory.SetSort.set
private abbrev up₃ {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) := up (up (up v))

/-- 原层图的每个输出都有同一规范序，量词保持完整 raw 范围。 -/
def reading_m {Γ Δ : SortContext ℒ}
    (ω e t₁ t₂ t₃ Pair Valid B P₀ f g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <|
    let b : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
    let X := .bvar (.there .here)
    let P := .bvar .here
    .imp (SecondOrderObjectSyntax.value_m (up₃ f) b X) <|
      .iff (SecondOrderObjectSyntax.value_m (up₃ g) b P)
        (SecondOrderCanonicalLevelSyntax.level_m (up₃ ω) (up₃ e) (up₃ t₁) (up₃ t₂) (up₃ t₃)
          (up₃ Pair) (up₃ Valid) (up₃ B) (up₃ P₀) b X P)

theorem reading_formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} (K : source_coding_l hℳ)
    {Γ Δ : SortContext ℒ} (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ)
    (ω e t₁ t₂ t₃ Pair Valid B P₀ f g : Term ℒ Γ Δ .set) :
    (reading_m ω e t₁ t₂ t₃ Pair Valid B P₀ f g).satisfies η ↔
      ∀ b X P, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) (f.eval η) b X →
        (value_l (ℳ := SecondOrderQuotient.structure_l hℳ) (g.eval η) b P ↔
          SecondOrderCanonicalLevelSyntax.level_l (ω.eval η) (e.eval η) (t₁.eval η)
            (t₂.eval η) (t₃.eval η) (Pair.eval η) (Valid.eval η) (B.eval η) (P₀.eval η) b X P) := by
  simp only [reading_m, Formula.satisfies, value_formula_l,
    SecondOrderCanonicalLevelSyntax.level_formula_l K, up₃, up, Term.eval_weakenBound,
    Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]

private abbrev context_m : SortContext ℒ :=
  [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set]

private abbrev B_m : Term ℒ [] context_m .set := .fvar .here
private abbrev ω_m : Term ℒ [] context_m .set := .fvar (.there (.here))
private abbrev x_m : Term ℒ [] context_m .set := .fvar (.there (.there (.here)))
private abbrev a_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.here))))
private abbrev y_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.here)))))
private abbrev A_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.here))))))
private abbrev U_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.here)))))))
private abbrev D_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.here))))))))
private abbrev f_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))
private abbrev e_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))
private abbrev t₁_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))
private abbrev t₂_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))
private abbrev t₃_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))))
private abbrev t₄_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))))
private abbrev Pair_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))))))
private abbrev N_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))))))
private abbrev Valid_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))))))))
private abbrev V_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))))))))
private abbrev Q_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))))))))))
private abbrev G_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))))))))))
private abbrev P₀_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))))))))))))
private abbrev g_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))))))))))))
private abbrev R_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))))))))))))))

private def parameters_m (v : Variable context_m .set) : Term ℒ [] context_m .set := .fvar v

private def point_m : Formula ℒ [] context_m :=
  PowerlessCodedHistoryCoverageSyntax.point_m B_m ω_m x_m a_m y_m A_m U_m D_m f_m e_m t₁_m t₂_m t₃_m t₄_m Pair_m N_m Valid_m V_m Q_m G_m

private def map_m : Formula ℒ [] context_m := SecondOrderObjectSyntax.map_m g_m A_m R_m

private def equations_m : Formula ℒ [] context_m :=
  PowerlessCanonicalOrderEquations.formula_m ω_m e_m t₁_m t₂_m t₃_m Pair_m Valid_m B_m P₀_m f_m g_m

def schema_m : Formula ℒ [] context_m :=
  .imp (guard_m B_m P₀_m) <|
    .imp (PowerlessRelativeClassFormulaInstances.members_m context_m B_m parameters_m) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω_m) <|
        .imp (instance_m point_m B_m parameters_m) <|
          .imp (instance_m map_m B_m parameters_m) <|
            .imp (instance_m equations_m B_m parameters_m)
              (reading_m ω_m e_m t₁_m t₂_m t₃_m Pair_m Valid_m B_m P₀_m f_m g_m)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, guard_formula_l,
    PowerlessRelativeClassFormulaInstances.members_l K, SecondOrderOmegaSyntax.omega_l]
  intro hGuard hMembers hω hPoint hg hEq
  have hBase : ∀ z, SecondOrderQuotient.mem_l hℳ z (B_m.eval η) → ∀ t,
      SecondOrderQuotient.mem_l hℳ t z → SecondOrderQuotient.mem_l hℳ t (B_m.eval η) :=
    fun z hz t ht => hGuard.2.1 z t hz ht
  let ξ : Env (PowerlessRelativeClassStructure.structure_l hℳ (B_m.eval η) hBase) [] context_m := {
    boundVal := fun v => nomatch v
    freeVal := fun {s} v => match s with | .set => ⟨η.freeVal v, hMembers v⟩ }
  have hν : ∀ v, (parameters_m v).eval η = (ξ.freeVal v).val := fun _ => rfl
  have hPointClass := (PowerlessCodedHistoryCoverageSyntax.point_formula_l
    (PowerlessRelativeClassStructure.ext_l hℳ (B_m.eval η) hBase) ξ
    B_m ω_m x_m a_m y_m A_m U_m D_m f_m e_m t₁_m t₂_m t₃_m t₄_m Pair_m N_m Valid_m V_m Q_m G_m).mp
      ((instance_l K point_m η B_m parameters_m ξ rfl hν).mp hPoint)
  have hgClass := (map_formula_l ξ g_m A_m R_m).mp
    ((instance_l K map_m η B_m parameters_m ξ rfl hν).mp hg)
  have hEqClass := (PowerlessCanonicalOrderEquations.formula_l ξ
    ω_m e_m t₁_m t₂_m t₃_m Pair_m Valid_m B_m P₀_m f_m g_m).mp
      ((instance_l K equations_m η B_m parameters_m ξ rfl hν).mp hEq)
  apply (reading_formula_l K η ω_m e_m t₁_m t₂_m t₃_m Pair_m Valid_m B_m P₀_m f_m g_m).mpr
  exact PowerlessRelativeClassCanonicalLevelReading.reading_l
    (hBase := hBase) K (B_m.eval ξ) (ω_m.eval ξ) (x_m.eval ξ) (a_m.eval ξ) (y_m.eval ξ) (A_m.eval ξ) (U_m.eval ξ) (D_m.eval ξ) (f_m.eval ξ) (e_m.eval ξ) (t₁_m.eval ξ) (t₂_m.eval ξ) (t₃_m.eval ξ) (t₄_m.eval ξ) (Pair_m.eval ξ) (N_m.eval ξ) (Valid_m.eval ξ) (V_m.eval ξ) (Q_m.eval ξ) (G_m.eval ξ) (P₀_m.eval ξ) (g_m.eval ξ) (R_m.eval ξ)
      rfl (SecondOrderOmega.unique_l hℳ hω K.omega_spec) hPointClass
        hGuard.1 hGuard.2.2.1 hGuard.2.2.2 hgClass hEqClass

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms reading_formula_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalLevelDerives
