import BMSConstructibleBridge.PowerlessRelativeClassCanonicalHistoryReading
import BMSConstructibleBridge.PowerlessRelativeClassFormulaInstances

/-! # 同一无枚举规范历史的原 Z₂ 对象保持模式

语言为纯隶属 ℒ，正式出口回到原 num/set 推导核。原层历史、原规范
方程、逐值母序良序、给定图的 Class 资格以及类内实际静态包都是明确
公式守卫，不预供类内完整理论。结论只相对化无枚举递归 AST，不宣称
计数式完整层次绝对、原数字重索引资格或最终 BMS 良序推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalHistoryDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeClassFormulaInstances (instance_m instance_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

private abbrev context_m : SortContext ℒ :=
  [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set]

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
private abbrev δ_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
private abbrev F_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
private abbrev r_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))
private abbrev g_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))

private def parameters_m (v : Variable context_m .set) : Term ℒ [] context_m .set := .fvar v

private def static_m : Formula ℒ [] context_m :=
  PowerlessSatisfactionExistenceSyntax.static_m ω_m e_m t₁_m t₂_m t₃_m Pair_m N_m Valid_m

private def equations_m : Formula ℒ [] context_m :=
  PowerlessCanonicalOrderEquations.formula_m ω_m e_m t₁_m t₂_m t₃_m Pair_m Valid_m B_m P₀_m F_m g_m

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def order_m {Γ Δ : SortContext ℒ} (F g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <| .imp
    (SecondOrderObjectSyntax.value_m (up (up (up F))) (.bvar (.there (.there .here))) (.bvar (.there .here))) <|
      .imp (SecondOrderObjectSyntax.value_m (up (up (up g))) (.bvar (.there (.there .here))) (.bvar .here)) <|
        PowerlessRelativeClassEnumerationWellOrder.wellOrder_m (.bvar (.there .here)) (.bvar .here)

theorem order_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) (F g : Term ℒ Γ Δ .set) :
    (order_m F g).satisfies η ↔ ∀ a X P, value_l (ℳ := 𝒩) (F.eval η) a X →
      value_l (ℳ := 𝒩) (g.eval η) a P → wellOrder_l (ℳ := 𝒩) X P := by
  simp only [order_m, Formula.satisfies, value_formula_l,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula ℒ [] context_m :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B_m) <|
    .imp (PowerlessRelativeClassFormulaInstances.members_m context_m B_m parameters_m) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω_m) <|
        .imp (instance_m static_m B_m parameters_m) <|
          .imp (PowerlessRelativeHierarchySyntax.ordinal_m δ_m) <|
            .imp (PowerlessRelativeHierarchySyntax.history_m B_m δ_m F_m r_m) <|
              .imp equations_m <| .imp (order_m F_m g_m) (instance_m equations_m B_m parameters_m)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

/-- 只包装已有原环境值及其资格证明，不从 Prop 存在性抽取 Type 数据。 -/
private def class_env_l {Δ : SortContext ℒ} (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
      ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B)
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    (hMembers : ∀ v : Variable Δ .set, PowerlessRelativeClassCorrespondence.member_l hℳ B (η.freeVal v)) :
    Env (PowerlessRelativeClassStructure.structure_l hℳ B hBase) [] Δ where
  boundVal v := nomatch v
  freeVal {s} v := match s with | .set => ⟨η.freeVal v, hMembers v⟩

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeClassFormulaInstances.members_l K, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeHierarchySemantics.ordinal_formula_l,
    PowerlessRelativeHierarchySemantics.history_formula_l K,
    equations_m, PowerlessCanonicalOrderEquations.formula_l, order_formula_l]
  intro hBase hMembers hω hStatic hδ hF hEq hOrder
  have hMembers' : ∀ v : Variable context_m .set,
      PowerlessRelativeClassCorrespondence.member_l hℳ (B_m.eval η) (η.freeVal v) := hMembers
  let ξ := class_env_l (B_m.eval η) hBase η hMembers'
  have hν : ∀ v, (parameters_m v).eval η = (ξ.freeVal v).val := fun _ => rfl
  have hStatic' : PowerlessSatisfactionExistenceSyntax.static_l
      (𝒩 := PowerlessRelativeClassStructure.structure_l hℳ (B_m.eval η) hBase)
      (ω_m.eval ξ) (e_m.eval ξ) (t₁_m.eval ξ) (t₂_m.eval ξ) (t₃_m.eval ξ)
      (Pair_m.eval ξ) (N_m.eval ξ) (Valid_m.eval ξ) := by
    exact (PowerlessSatisfactionExistenceSyntax.static_formula_l ξ _ _ _ _ _ _ _ _).mp
      ((instance_l K static_m η B_m parameters_m ξ rfl hν).mp hStatic)
  have hωEq : (ω_m.eval ξ).val = K.omega := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  obtain ⟨he, _ht₁, _ht₂, _ht₃, _hN, _hPairMap, _hPair, _hValid⟩ :=
    PowerlessRelativeClassStaticCodingReading.reading_l K hωEq hStatic'
  have he' : (e_m.eval ξ).val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val := he
  have hRawEq : PowerlessCanonicalOrderOrdinalRestriction.equations_l K
      (t₁_m.eval η) (t₂_m.eval η) (t₃_m.eval η) (Pair_m.eval η) (Valid_m.eval η)
      (B_m.eval η) (P₀_m.eval η) (F_m.eval η) (g_m.eval η) := by
    apply (PowerlessCanonicalOrderEquations.raw_l K _ _ _ _ _ _ _ _ _).mp
    have hωRaw : ω_m.eval η = K.omega := hωEq
    have heRaw : e_m.eval η = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val := he'
    rw [hωRaw, heRaw] at hEq
    exact hEq
  have hClass := PowerlessRelativeClassCanonicalHistoryReading.reading_l
    K (ω_m.eval ξ) (e_m.eval ξ) (t₁_m.eval ξ) (t₂_m.eval ξ) (t₃_m.eval ξ)
      (Pair_m.eval ξ) (N_m.eval ξ) (Valid_m.eval ξ) (B_m.eval ξ) (P₀_m.eval ξ)
      (F_m.eval ξ) (g_m.eval ξ) rfl hωEq hStatic' hδ hF hRawEq hOrder
  apply (instance_l K equations_m η B_m parameters_m ξ rfl hν).mpr
  exact (PowerlessCanonicalOrderEquations.formula_l ξ _ _ _ _ _ _ _ _ _ _ _).mpr hClass

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalHistoryDerives
