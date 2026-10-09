import BMSConstructibleBridge.PowerlessRelativeMemberSatisfactionAbsolute
import BMSConstructibleBridge.PowerlessRelativeParameters
import BMSConstructibleBridge.PowerlessRelativeHierarchyDerives
import BMSConstructibleBridge.SecondOrderAxioms
import YesMetaZFC.Automation.ModelClosure

/-! # 共尾极限成员域中完整原 Sat 规格的原 Z₂ 推导

对象语言为纯隶属 ℒ，正式背景为 SecondOrderArithmetic.theory_m。
实际传递基底、非零极限阶段、共尾守卫及原层值均保留在对象句中。
九个原 Sat 参数实际属于 W 时，同一 ambient 完整规格推出其在成员
结构中的完整规格；结论不是有界检查器，也不预供绝对性证书。

域 W 只作相对化域参数，不要求 W∈W；不增加 N/S、完整源理论、
标准 ω 或对象选择公理。全模型语义通过已核验的原图解释及固定签名
完备性回传原 Derives，不声称最终固定高度 BMS 良序性已经完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMemberSatisfactionDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderObjectSyntax (member_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

/-- 九个自由槽依次为 ω、A、e、t₁、t₂、t₃、T、F、R。 -/
def context_m : SortContext ℒ := [.set, .set, .set, .set, .set, .set, .set, .set, .set]

def template_m : Formula ℒ [] context_m :=
  PowerlessSatisfactionSpecification.spec_m (.fvar .here) (.fvar (.there .here))
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))

def parameters_m {Γ Δ : SortContext ℒ} (ω A e t₁ t₂ t₃ T F R : Term ℒ Γ Δ .set) :
    Variable context_m SetTheory.SetSort.set → Term ℒ Γ Δ .set
  | .here => ω
  | .there .here => A
  | .there (.there .here) => e
  | .there (.there (.there .here)) => t₁
  | .there (.there (.there (.there .here))) => t₂
  | .there (.there (.there (.there (.there .here)))) => t₃
  | .there (.there (.there (.there (.there (.there .here))))) => T
  | .there (.there (.there (.there (.there (.there (.there .here)))))) => F
  | .there (.there (.there (.there (.there (.there (.there (.there .here))))))) => R

/-- 实际成员域中的原完整规格；W 不占原九参数槽。 -/
def relative_m {Γ Δ : SortContext ℒ} (W ω A e t₁ t₂ t₃ T F R : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  PowerlessRelativeParameters.instance_m template_m W (parameters_m ω A e t₁ t₂ t₃ T F R)

def schema_m {Δ : SortContext ℒ} (B β W ω A e t₁ t₂ t₃ T F R : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
      .imp (PowerlessRelativeHierarchySyntax.level_m B β W) <|
        .imp (PowerlessRelativeCofinalLimitBounds.cofinal_m β) <|
          .imp (SecondOrderOmegaSyntax.omega_m ω) <|
            .imp (.forallE .set (.neg (member_m (.bvar .here) (up e)))) <|
              .imp (SecondOrderObjectSyntax.map_m T ω ω) <|
                .imp (member_m ω W) <| .imp (member_m A W) <| .imp (member_m e W) <|
                  .imp (member_m t₁ W) <| .imp (member_m t₂ W) <| .imp (member_m t₃ W) <|
                    .imp (member_m T W) <| .imp (member_m F W) <| .imp (member_m R W) <|
                      .imp (PowerlessSatisfactionSpecification.spec_m ω A e t₁ t₂ t₃ T F R)
                        (relative_m W ω A e t₁ t₂ t₃ T F R)

def sentence_m {Δ : SortContext ℒ} (B β W ω A e t₁ t₂ t₃ T F R : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B β W ω A e t₁ t₂ t₃ T F R)

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B β W ω A e t₁ t₂ t₃ T F R : Term ℒ [] Δ .set) :
    (sentence_m B β W ω A e t₁ t₂ t₃ T F R).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hB hβ hW hCofinal hω he hT hωW hAW heW ht₁W ht₂W ht₃W hTW hFW hRW hSat
  have hB' := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η B).mp hB
  have hβ' := (PowerlessRelativeHierarchySemantics.limit_formula_l η β).mp hβ
  have hW' := (PowerlessRelativeHierarchySemantics.level_formula_l K η B β W).mp hW
  have hCofinal' := (PowerlessRelativeCofinalLimitBounds.cofinal_formula_l η β).mp hCofinal
  have hω' := (SecondOrderOmegaSyntax.omega_l hℳ η ω).mp hω
  have he' : ∀ x, ¬SecondOrderQuotient.mem_l hℳ x (e.eval η) := by
    have h := he
    simp only [Formula.satisfies, member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval] at h
    simpa only [Env.pushBound, Assignment.push, SecondOrderQuotient.structure_l] using h
  have hT' := (map_formula_l η T ω ω).mp hT
  have hSat' := (PowerlessSatisfactionSpecification.spec_formula_l η ω A e t₁ t₂ t₃ T F R).mp hSat
  let h₀ : ∃ x, SecondOrderQuotient.mem_l hℳ x (W.eval η) := ⟨ω.eval η, hωW⟩
  let ω' : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) (W.eval η) :=
    ⟨ω.eval η, hωW⟩
  let A' : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) (W.eval η) :=
    ⟨A.eval η, hAW⟩
  let e' : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) (W.eval η) :=
    ⟨e.eval η, heW⟩
  let t₁' : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) (W.eval η) :=
    ⟨t₁.eval η, ht₁W⟩
  let t₂' : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) (W.eval η) :=
    ⟨t₂.eval η, ht₂W⟩
  let t₃' : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) (W.eval η) :=
    ⟨t₃.eval η, ht₃W⟩
  let T' : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) (W.eval η) :=
    ⟨T.eval η, hTW⟩
  let F' : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) (W.eval η) :=
    ⟨F.eval η, hFW⟩
  let R' : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) (W.eval η) :=
    ⟨R.eval η, hRW⟩
  let ξ : Env (PowerlessMemberStructure.structure_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) (W.eval η) h₀) [] context_m :=
    Env.empty (M := PowerlessMemberStructure.structure_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) (W.eval η) h₀)
      |>.pushFree R' |>.pushFree F' |>.pushFree T' |>.pushFree t₃' |>.pushFree t₂'
      |>.pushFree t₁' |>.pushFree e' |>.pushFree A' |>.pushFree ω'
  have hSpec : PowerlessSatisfactionSpecification.spec_l
      (𝒩 := PowerlessMemberStructure.structure_l
        (ℳ := SecondOrderQuotient.structure_l hℳ) (W.eval η) h₀) ω' A' e' t₁' t₂' t₃' T' F' R' :=
    PowerlessRelativeMemberSatisfactionAbsolute.guarded_l hB' hβ' hW' hCofinal' hω' he' hT' hSat'
  apply (PowerlessRelativeParameters.instance_l template_m η W
    (parameters_m ω A e t₁ t₂ t₃ T F R) ξ rfl (fun v => by
      match v with
      | .here => rfl
      | .there .here => rfl
      | .there (.there .here) => rfl
      | .there (.there (.there .here)) => rfl
      | .there (.there (.there (.there .here))) => rfl
      | .there (.there (.there (.there (.there .here)))) => rfl
      | .there (.there (.there (.there (.there (.there .here))))) => rfl
      | .there (.there (.there (.there (.there (.there (.there .here)))))) => rfl
      | .there (.there (.there (.there (.there (.there (.there (.there .here))))))) => rfl)).mpr
  exact (PowerlessSatisfactionSpecification.spec_formula_l ξ (.fvar .here) (.fvar (.there .here))
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))).mpr hSpec

theorem derives_m {Δ : SortContext ℒ} (B β W ω A e t₁ t₂ t₃ T F R : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B β W ω A e t₁ t₂ t₃ T F R)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ hℳ => models_l hℳ B β W ω A e t₁ t₂ t₃ T F R)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMemberSatisfactionDerives
