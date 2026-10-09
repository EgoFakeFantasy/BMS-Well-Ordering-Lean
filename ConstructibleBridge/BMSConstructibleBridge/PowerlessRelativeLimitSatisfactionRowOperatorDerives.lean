import BMSConstructibleBridge.PowerlessRelativeLimitSatisfactionRowOperator

/-! # 全内部 Sat 行调用图的原 Z₂ 对象模式

纯隶属句子经原 GraphTranslation 回到 SecondOrderArithmetic.theory_m，
正式出口为原 Derives。结论构造 Class 函数图，保留同一个 G 的全部 raw
读值及输出 W 界。局部 Seq 资格是明确对象前提，实际共尾编码包已能提供；
这里不预供输出图，也不以此宣称低层可数性或最终 hSources 已消去。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitSatisfactionRowOperatorDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l)
open PowerlessRelativeLimitSatisfactionRowOperator

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)

def conclusion_m {Γ Δ : SortContext ℒ} (B ω W G e : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <|
    let F : Term ℒ (.set :: Γ) Δ .set := .bvar .here
    .conj (PowerlessRelativeHierarchySyntax.class_m (up B) F) <|
      .conj (SecondOrderObjectSyntax.map_m F (up W) (up W)) <|
        .forallE .set <| .forallE .set <|
          let s : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
          let Z : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar .here
          .iff (SecondOrderObjectSyntax.value_m (up₂ F) s Z) <|
            .conj (SecondOrderObjectSyntax.member_m s (up₃ W)) <|
              .conj (SecondOrderObjectSyntax.member_m Z (up₃ W))
                (total_m (up₃ ω) (up₃ W) (up₃ G) (up₃ e) s Z)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem conclusion_formula_l {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
    (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (B ω W G e : Term ℒ Γ Δ .set) :
    (conclusion_m B ω W G e).satisfies η ↔ ∃ F : SecondOrderQuotient.type_l hℳ,
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) F ∧
        map_l (ℳ := SecondOrderQuotient.structure_l hℳ) F (W.eval η) (W.eval η) ∧
          ∀ s Z : SecondOrderQuotient.type_l hℳ,
            value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F s Z ↔
              mem_l hℳ s (W.eval η) ∧ mem_l hℳ Z (W.eval η) ∧
                total_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
                  (ω.eval η) (W.eval η) (G.eval η) (e.eval η) s Z := by
  simp only [conclusion_m, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l, value_formula_l,
    total_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval,
    up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m {Δ : SortContext ℒ} (B β ω W G e : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
      .imp (PowerlessRelativeHierarchySyntax.level_m B β W) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B ω) <|
          .imp (PowerlessRelativeHierarchySyntax.class_m B G) <|
            .imp (PowerlessRelativeHierarchySyntax.class_m B e) <|
              .imp (SecondOrderObjectSyntax.member_m ω W) <|
                .imp (SecondOrderObjectSyntax.member_m e W) <|
                  .imp (SecondOrderObjectSyntax.map_m G W W) <|
                    .imp (local_m ω W G) (conclusion_m B ω W G e)

def sentence_m {Δ : SortContext ℒ} (B β ω W G e : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B β ω W G e)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (B β ω W G e : Term ℒ [] Δ .set) :
    (sentence_m B β ω W G e).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hB hLimit hW hω hGClass he hωW heW hG hLocal
  apply (conclusion_formula_l K η B ω W G e).mpr
  have hBase := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η B).mp hB
  have hLimit' := (PowerlessRelativeHierarchySemantics.limit_formula_l η β).mp hLimit
  have hW' := (PowerlessRelativeHierarchySemantics.level_formula_l K η B β W).mp hW
  let ω' : type_l hℳ (B.eval η) :=
    ⟨ω.eval η, (PowerlessRelativeHierarchySemantics.class_formula_l K η B ω).mp hω⟩
  let G' : type_l hℳ (B.eval η) :=
    ⟨G.eval η, (PowerlessRelativeHierarchySemantics.class_formula_l K η B G).mp hGClass⟩
  let e' : type_l hℳ (B.eval η) :=
    ⟨e.eval η, (PowerlessRelativeHierarchySemantics.class_formula_l K η B e).mp he⟩
  obtain ⟨F, hF, hRead⟩ := PowerlessRelativeLimitSatisfactionRowOperator.exists_l
    hBase hLimit' hW' ω' G' e' hωW heW ((map_formula_l η G W W).mp hG)
      ((local_formula_l η ω W G).mp hLocal)
  exact ⟨F.val, F.property, hF, hRead⟩

theorem derives_m {Δ : SortContext ℒ} (B β ω W G e : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m B β ω W G e)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B β ω W G e)

#print axioms conclusion_formula_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitSatisfactionRowOperatorDerives
