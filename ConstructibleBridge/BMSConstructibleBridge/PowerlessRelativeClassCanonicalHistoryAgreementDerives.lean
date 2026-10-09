import BMSConstructibleBridge.PowerlessRelativeClassCanonicalHistoryAgreement
import BMSConstructibleBridge.PowerlessRelativeClassCanonicalHistoryDerives

/-! # 同一规范历史认同的原 Z₂ 对象模式

纯隶属 ℒ、原 num/set 推导核。待验证图已有 Class 资格及真正类内
无枚举方程，参考图已有原方程及原母序证书；同域原函数规格使两图
精确相等。阶段域、raw 陪域和参考图不预称 Class，待验证图不预供
全局 raw 良序。不宣称 A/H 资格、内部可数性或最终 BMS 句已完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalHistoryAgreementDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeClassFormulaInstances (instance_m instance_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

private abbrev context_m : SortContext ℒ :=
  [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set]

private abbrev B_m : Term ℒ [] context_m .set := .fvar .here
private abbrev ω_m : Term ℒ [] context_m .set := .fvar (.there .here)
private abbrev e_m : Term ℒ [] context_m .set := .fvar (.there (.there .here))
private abbrev t₁_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there .here)))
private abbrev t₂_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there .here))))
private abbrev t₃_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there .here)))))
private abbrev Pair_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
private abbrev N_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
private abbrev Valid_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
private abbrev P₀_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
private abbrev F_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
private abbrev g_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))

private def parameters_m {Γ : SortContext ℒ} (v : Variable context_m .set) : Term ℒ Γ context_m .set := .fvar v

private def static_m : Formula ℒ [] context_m :=
  PowerlessSatisfactionExistenceSyntax.static_m ω_m e_m t₁_m t₂_m t₃_m Pair_m N_m Valid_m

private def equations_m : Formula ℒ [] context_m :=
  PowerlessCanonicalOrderEquations.formula_m ω_m e_m t₁_m t₂_m t₃_m Pair_m Valid_m B_m P₀_m F_m g_m

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
private abbrev up₅ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up (up (up t))))

private def body_m : Formula ℒ [.set, .set, .set, .set, .set] context_m :=
  let δ : Term ℒ [.set, .set, .set, .set, .set] context_m .set := .bvar (.there (.there (.there (.there .here))))
  let r := .bvar (.there (.there (.there .here)))
  let q := .bvar (.there (.there .here))
  let g₀ := .bvar (.there .here)
  let q₀ := .bvar .here
  .imp (PowerlessRelativeHierarchySyntax.ordinal_m δ) <|
    .imp (SecondOrderObjectSyntax.map_m (up₅ F_m) δ r) <|
      .imp (SecondOrderObjectSyntax.map_m (up₅ g_m) δ q) <|
        .imp (SecondOrderObjectSyntax.map_m g₀ δ q₀) <|
          .imp (instance_m equations_m (up₅ B_m) parameters_m) <|
            .imp (PowerlessCanonicalOrderEquations.formula_m (up₅ ω_m) (up₅ e_m) (up₅ t₁_m)
              (up₅ t₂_m) (up₅ t₃_m) (up₅ Pair_m) (up₅ Valid_m) (up₅ B_m) (up₅ P₀_m) (up₅ F_m) g₀) <|
              .imp (PowerlessRelativeClassCanonicalHistoryDerives.order_m (up₅ F_m) g₀)
                (.equal (up₅ g_m) g₀)

def schema_m : Formula ℒ [] context_m :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B_m) <|
    .imp (PowerlessRelativeClassFormulaInstances.members_m context_m B_m parameters_m) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω_m) <|
        .imp (instance_m static_m B_m parameters_m) <|
          .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set body_m

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeClassFormulaInstances.members_l K, SecondOrderOmegaSyntax.omega_l]
  intro hBase hMembers hω hStatic δ r q g₀ q₀
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
  let ζ := η |>.pushBound δ |>.pushBound r |>.pushBound q |>.pushBound g₀ |>.pushBound q₀
  simp only [body_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.ordinal_formula_l,
    map_formula_l, PowerlessCanonicalOrderEquations.formula_l,
    PowerlessRelativeClassCanonicalHistoryDerives.order_formula_l,
    up₅, up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro hδ hF hg hg₀ hEq hEq₀ hOrder₀
  have hEq' : equations_m.satisfies ξ :=
    (instance_l K equations_m ζ (up₅ B_m) parameters_m ξ rfl (fun _ => rfl)).mp hEq
  have hClassEq := (PowerlessCanonicalOrderEquations.formula_l ξ
    ω_m e_m t₁_m t₂_m t₃_m Pair_m Valid_m B_m P₀_m F_m g_m).mp hEq'
  exact PowerlessRelativeClassCanonicalHistoryAgreement.unique_l
    K (ω_m.eval ξ) (e_m.eval ξ) (t₁_m.eval ξ) (t₂_m.eval ξ) (t₃_m.eval ξ)
      (Pair_m.eval ξ) (N_m.eval ξ) (Valid_m.eval ξ) (B_m.eval ξ) (P₀_m.eval ξ)
      (F_m.eval ξ) (g_m.eval ξ) hωEq hStatic' hδ hF hg hg₀ hClassEq hEq₀ hOrder₀

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalHistoryAgreementDerives
