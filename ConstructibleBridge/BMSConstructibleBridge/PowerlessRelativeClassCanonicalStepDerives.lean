import BMSConstructibleBridge.PowerlessRelativeClassCanonicalStepOriginal
import BMSConstructibleBridge.PowerlessRelativeClassFormulaInstances
import BMSConstructibleBridge.PowerlessRelativeClassStaticCodingReading

/-! # 同一原规范后继读入 Class 的正式对象模式

语言为纯隶属 ℒ，背景为原 Z₂。同一实际 Class 静态包的读数在证明
中取得，不以编码正确性或 Sat 存在作为新的背景公理。原母集环境
良序、传递性和 raw Def 仍是显式守卫，结论是给定原 E 的 Class
资格及原规范后继公式的 Class 真值，不是完整类层次绝对性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalStepDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeClassFormulaInstances (instance_m instance_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

private abbrev static_context_m : SortContext ℒ := [.set, .set, .set, .set, .set, .set, .set, .set]
private abbrev step_context_m : SortContext ℒ := [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set]

private def static_parameters_m {Γ Δ : SortContext ℒ}
    (ω e t₁ t₂ t₃ Pair N Valid : Term ℒ Γ Δ .set) : Variable static_context_m .set → Term ℒ Γ Δ .set
  | .here => ω
  | .there .here => e
  | .there (.there .here) => t₁
  | .there (.there (.there .here)) => t₂
  | .there (.there (.there (.there .here))) => t₃
  | .there (.there (.there (.there (.there .here)))) => Pair
  | .there (.there (.there (.there (.there (.there .here))))) => N
  | .there (.there (.there (.there (.there (.there (.there .here)))))) => Valid

private def step_parameters_m {Γ Δ : SortContext ℒ}
    (ω A P e t₁ t₂ t₃ Pair Valid D E : Term ℒ Γ Δ .set) : Variable step_context_m .set → Term ℒ Γ Δ .set
  | .here => ω
  | .there .here => A
  | .there (.there .here) => P
  | .there (.there (.there .here)) => e
  | .there (.there (.there (.there .here))) => t₁
  | .there (.there (.there (.there (.there .here)))) => t₂
  | .there (.there (.there (.there (.there (.there .here))))) => t₃
  | .there (.there (.there (.there (.there (.there (.there .here)))))) => Pair
  | .there (.there (.there (.there (.there (.there (.there (.there .here))))))) => Valid
  | .there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) => D
  | .there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) => E

private def static_m : Formula ℒ [] static_context_m :=
  PowerlessSatisfactionExistenceSyntax.static_m
    (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))

private def step_m : Formula ℒ [] step_context_m :=
  SecondOrderCanonicalOrderUniform.step_m
    (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))

def schema_m {Δ : SortContext ℒ}
    (B ω e t₁ t₂ t₃ Pair N Valid A P D E : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  let ν := static_parameters_m ω e t₁ t₂ t₃ Pair N Valid
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeClassFormulaInstances.members_m static_context_m B ν) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (instance_m static_m B ν) <|
          .imp (PowerlessRelativeHierarchySyntax.class_m B A) <|
            .imp (PowerlessRelativeHierarchySyntax.class_m B P) <|
              .imp (PowerlessRelativeHierarchySyntax.class_m B D) <|
                .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m A P) <|
                  .imp (PowerlessNaturalOrder.transitive_m A) <|
                    .imp (PowerlessMemberDefSyntax.global_m A D) <|
                      .imp (SecondOrderCanonicalOrderUniform.step_m ω A P e t₁ t₂ t₃ Pair Valid D E) <|
                        .conj (PowerlessRelativeHierarchySyntax.class_m B E)
                          (instance_m step_m B (step_parameters_m ω A P e t₁ t₂ t₃ Pair Valid D E))

def sentence_m {Δ : SortContext ℒ}
    (B ω e t₁ t₂ t₃ Pair N Valid A P D E : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B ω e t₁ t₂ t₃ Pair N Valid A P D E)

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B ω e t₁ t₂ t₃ Pair N Valid A P D E : Term ℒ [] Δ .set) :
    (sentence_m B ω e t₁ t₂ t₃ Pair N Valid A P D E).TrueIn
      (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeClassFormulaInstances.members_l K, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    PowerlessNaturalOrder.transitive_formula_l, PowerlessMemberDefDerives.formula_l K,
    SecondOrderCanonicalOrderUniform.step_formula_l]
  intro hBase hMembers hω hStatic hA hPClass hD hP hTrans hDef hE
  let M := PowerlessRelativeClassStructure.type_l hℳ (B.eval η)
  let 𝒩₀ := PowerlessRelativeClassStructure.structure_l hℳ (B.eval η) hBase
  let ω₀ : M := ⟨ω.eval η, hMembers .here⟩
  let e₀ : M := ⟨e.eval η, hMembers (.there .here)⟩
  let t₁₀ : M := ⟨t₁.eval η, hMembers (.there (.there .here))⟩
  let t₂₀ : M := ⟨t₂.eval η, hMembers (.there (.there (.there .here)))⟩
  let t₃₀ : M := ⟨t₃.eval η, hMembers (.there (.there (.there (.there .here))))⟩
  let Pair₀ : M := ⟨Pair.eval η, hMembers (.there (.there (.there (.there (.there .here)))))⟩
  let N₀ : M := ⟨N.eval η, hMembers (.there (.there (.there (.there (.there (.there .here))))))⟩
  let Valid₀ : M := ⟨Valid.eval η, hMembers (.there (.there (.there (.there (.there (.there (.there .here)))))))⟩
  let A₀ : M := ⟨A.eval η, hA⟩
  let P₀ : M := ⟨P.eval η, hPClass⟩
  let D₀ : M := ⟨D.eval η, hD⟩
  let ξ : Env 𝒩₀ [] static_context_m :=
    Env.empty |>.pushFree Valid₀ |>.pushFree N₀ |>.pushFree Pair₀ |>.pushFree t₃₀
      |>.pushFree t₂₀ |>.pushFree t₁₀ |>.pushFree e₀ |>.pushFree ω₀
  have hStaticClass : PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := 𝒩₀)
      ω₀ e₀ t₁₀ t₂₀ t₃₀ Pair₀ N₀ Valid₀ := by
    have h := (instance_l K static_m η B (static_parameters_m ω e t₁ t₂ t₃ Pair N Valid) ξ
      rfl (by intro v; cases v with
        | here => rfl
        | there v => cases v with
          | here => rfl
          | there v => cases v with
            | here => rfl
            | there v => cases v with
              | here => rfl
              | there v => cases v with
                | here => rfl
                | there v => cases v with
                  | here => rfl
                  | there v => cases v with
                    | here => rfl
                    | there v => cases v with
                      | here => rfl
                      | there v => nomatch v)).mp hStatic
    simpa only [static_m, PowerlessSatisfactionExistenceSyntax.static_formula_l,
      ξ, Term.eval, Env.pushFree_here, Env.pushFree_there] using h
  have hωEq : ω₀.val = K.omega := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  obtain ⟨he, _ht₁, _ht₂, _ht₃, _hN, hPairMap, hPair, hValid⟩ :=
    PowerlessRelativeClassStaticCodingReading.reading_l K hωEq hStaticClass
  obtain ⟨V, hV, _⟩ := SecondOrderTriangularFormulaSyntax.exists_l hℳ
  obtain ⟨E₀, hSame, hClassStep⟩ := PowerlessRelativeClassCanonicalStepOriginal.original_l
    K ω₀ A₀ P₀ e₀ t₁₀ t₂₀ t₃₀ Pair₀ Valid₀ D₀ (E.eval η) hωEq he
      hStaticClass.1 hPairMap hPair hV (hValid V hV) hP hTrans hDef hE
  refine ⟨hSame ▸ E₀.property, ?_⟩
  let ζ : Env 𝒩₀ [] step_context_m :=
    Env.empty |>.pushFree E₀ |>.pushFree D₀ |>.pushFree Valid₀ |>.pushFree Pair₀
      |>.pushFree t₃₀ |>.pushFree t₂₀ |>.pushFree t₁₀ |>.pushFree e₀
      |>.pushFree P₀ |>.pushFree A₀ |>.pushFree ω₀
  apply (instance_l K step_m η B (step_parameters_m ω A P e t₁ t₂ t₃ Pair Valid D E) ζ rfl ?_).mpr
  · simpa only [step_m, SecondOrderCanonicalOrderUniform.step_formula_l, ζ,
      Term.eval, Env.pushFree_here, Env.pushFree_there] using hClassStep
  · intro v
    cases v with
    | here => rfl
    | there v => cases v with
      | here => rfl
      | there v => cases v with
        | here => rfl
        | there v => cases v with
          | here => rfl
          | there v => cases v with
            | here => rfl
            | there v => cases v with
              | here => rfl
              | there v => cases v with
                | here => rfl
                | there v => cases v with
                  | here => rfl
                  | there v => cases v with
                    | here => rfl
                    | there v => cases v with
                      | here => rfl
                      | there v => cases v with
                        | here => exact hSame.symm
                        | there v => nomatch v

theorem derives_m {Δ : SortContext ℒ}
    (B ω e t₁ t₂ t₃ Pair N Valid A P D E : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B ω e t₁ t₂ t₃ Pair N Valid A P D E)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B ω e t₁ t₂ t₃ Pair N Valid A P D E)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalStepDerives
