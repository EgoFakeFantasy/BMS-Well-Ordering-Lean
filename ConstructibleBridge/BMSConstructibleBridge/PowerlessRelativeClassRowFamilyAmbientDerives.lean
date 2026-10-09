import BMSConstructibleBridge.PowerlessRelativeClassRowFamilyAmbient
import BMSConstructibleBridge.SecondOrderAxioms

/-! # 全部原商对象上的实际 Class 行族：原 Z₂ 推导

对象语言为纯隶属 ℒ，背景为原 SecondOrderArithmetic.theory_m，正式出口
为同一原图翻译的 Derives。显式假设基集 B 传递且 I、A、Q 属于实际
Class，结论取得实际 Class 行族 Y，并对全部 raw Z 与 raw i 读取精确行。

本模式直接在原商中解释，不使用 guarded_m 缩小 Z、i 或行元素的量词。
row_m 的两个有界全称由既有通用 row_formula_l 接回全部 raw 元素规格。
不从任意 Z⊆A 推出 Class Z；实际行及其全 raw 外延识别由 Ambient 接口
完成。原 Def 与该统一行族的精确认同仍须另证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassRowFamilyAmbientDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

/-- Z 与 i 都保留为原商量词，不再加入 Class 守卫。 -/
def family_m {Γ Δ : SortContext ℒ} (I A Q Y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <|
    .iff (SecondOrderObjectSyntax.member_m (.bvar .here) (up Y)) <|
      .existsE .set <|
        .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up (up I)))
          (PowerlessRelativeClassRowFamily.row_m (up (up A)) (up (up Q))
            (.bvar .here) (.bvar (.there .here)))

theorem family_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) (I A Q Y : Term ℒ Γ Δ .set) :
    (family_m I A Q Y).satisfies η ↔
      ∀ Z, member_l 𝒩 Z (Y.eval η) ↔
        ∃ i, member_l 𝒩 i (I.eval η) ∧
          PowerlessRelativeClassRowFamily.row_l (ℳ₀ := 𝒩) (A.eval η) (Q.eval η) i Z := by
  simp only [family_m, Formula.satisfies, PowerlessRelativeClassRowFamily.row_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def conclusion_m {Γ Δ : SortContext ℒ} (B I A Q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <|
    .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here))
      (family_m (up I) (up A) (up Q) (.bvar .here))

def body_m {Γ Δ : SortContext ℒ} (B I A Q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (.conj (PowerlessRelativeHierarchySyntax.class_m B I) <|
      .conj (PowerlessRelativeHierarchySyntax.class_m B A)
        (PowerlessRelativeHierarchySyntax.class_m B Q)) (conclusion_m B I A Q)

def schema_m : Formula ℒ [] [.set, .set, .set, .set] :=
  body_m (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here))))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ

theorem conclusion_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env RawModel Γ Δ) (B I A Q : Term ℒ Γ Δ .set) :
    (conclusion_m B I A Q).satisfies η ↔
      ∃ Y : SecondOrderQuotient.type_l hℳ,
        PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) Y ∧
          ∀ Z : SecondOrderQuotient.type_l hℳ, mem_l hℳ Z Y ↔
            ∃ i : SecondOrderQuotient.type_l hℳ, mem_l hℳ i (I.eval η) ∧
              PowerlessRelativeClassRowFamily.row_l (ℳ₀ := RawModel) (A.eval η) (Q.eval η) i Z := by
  simp only [conclusion_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.class_formula_l K,
    family_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 仅把输入三个实际 Class 见证做 Subtype 封装；输出保留全 raw 行规格。 -/
theorem formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env RawModel Γ Δ) (B I A Q : Term ℒ Γ Δ .set) :
    (body_m B I A Q).satisfies η := by
  rintro hTrans ⟨hI, hA, hQ⟩
  have hBase := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η B).mp hTrans
  let I' : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) :=
    ⟨I.eval η, (PowerlessRelativeHierarchySemantics.class_formula_l K η B I).mp hI⟩
  let A' : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) :=
    ⟨A.eval η, (PowerlessRelativeHierarchySemantics.class_formula_l K η B A).mp hA⟩
  let Q' : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) :=
    ⟨Q.eval η, (PowerlessRelativeHierarchySemantics.class_formula_l K η B Q).mp hQ⟩
  obtain ⟨Y, hY⟩ := PowerlessRelativeClassRowFamilyAmbient.exists_l (hBase := hBase) I' A' Q'
  exact (conclusion_formula_l K η B I A Q).mpr ⟨Y.val, Y.property, hY⟩

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  exact formula_l K η _ _ _ _

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m sentence_m (fun _ hℳ => models_l hℳ)

#print axioms family_formula_l
#print axioms formula_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassRowFamilyAmbientDerives
