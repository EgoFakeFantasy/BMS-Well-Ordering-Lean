import BMSConstructibleBridge.PowerlessCodedHistoryCoverageSyntax
import BMSConstructibleBridge.PowerlessMemberDefImageCoverage
import BMSConstructibleBridge.SecondOrderRowFamilyBounded

/-! # 任意捕获包中的完整 Sat 与 Def 行数据

对象语言为纯隶属 ℒ，背景与正式推导关系为原 Z₂。仅从同一 U 的
传递性、操作闭包和完整有限赋值覆盖，恢复给定检查器见证的完整
Sat、Seq、全部 raw 指标及精确行族。不要求 U 是实际层或 Class，
不预供原 hCoding，也不换掉给定 G 或候选输出。原 Def／历史的
认同仍须另读静态数字与旧翻译资格；本模块不宣称最终 hSources 消去。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCodedHistoryDataReading

open Logic FirstOrder ThirdOrderSemantics
open PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₅ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  up (up (up (up (up t))))

/-- 五个实际检查器见证保持不变，数据覆盖全部原环境对象。 -/
def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e t₁ t₂ t₃ P N F Q U G z r : carrier_l 𝒩) : Prop :=
  ∃ R S I J C, member_l 𝒩 R U ∧ member_l 𝒩 S U ∧ member_l 𝒩 I U ∧
    member_l 𝒩 J U ∧ member_l 𝒩 C U ∧ value_l (ℳ := 𝒩) G z R ∧
    PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒩) ω z e t₁ t₂ t₃ P F R ∧
    PowerlessMemberDefImageCoverage.spec_l (𝒩 := 𝒩) ω e N Q z R S I J C ∧
    PowerlessRelativeClassRowOrderCanonical.family_l (ℳ₀ := 𝒩) J z C r

def formula_m {Γ Δ : SortContext ℒ}
    (ω e t₁ t₂ t₃ P N F Q U G z r : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
    let C : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
    let J := .bvar (.there .here)
    let I := .bvar (.there (.there .here))
    let S := .bvar (.there (.there (.there .here)))
    let R := .bvar (.there (.there (.there (.there .here))))
    .conj (SecondOrderObjectSyntax.member_m R (up₅ U)) <|
    .conj (SecondOrderObjectSyntax.member_m S (up₅ U)) <|
    .conj (SecondOrderObjectSyntax.member_m I (up₅ U)) <|
    .conj (SecondOrderObjectSyntax.member_m J (up₅ U)) <|
    .conj (SecondOrderObjectSyntax.member_m C (up₅ U)) <|
    .conj (SecondOrderObjectSyntax.value_m (up₅ G) (up₅ z) R) <|
    .conj (PowerlessSatisfactionSpecification.spec_m (up₅ ω) (up₅ z) (up₅ e)
      (up₅ t₁) (up₅ t₂) (up₅ t₃) (up₅ P) (up₅ F) R) <|
    .conj (PowerlessMemberDefImageCoverage.spec_m (up₅ ω) (up₅ e) (up₅ N) (up₅ Q)
      (up₅ z) R S I J C)
      (SecondOrderRowOrderCanonical.family_m J (up₅ z) C (up₅ r))

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e t₁ t₂ t₃ P N F Q U G z r : Term ℒ Γ Δ .set) :
    (formula_m ω e t₁ t₂ t₃ P N F Q U G z r).satisfies η ↔
      holds_l (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (P.eval η) (N.eval η) (F.eval η) (Q.eval η) (U.eval η) (G.eval η)
        (z.eval η) (r.eval η) := by
  simp only [formula_m, holds_l, Formula.satisfies, value_formula_l,
    PowerlessSatisfactionSpecification.spec_formula_l, PowerlessMemberDefImageCoverage.formula_l,
    SecondOrderRowOrderCanonical.family_formula_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up₅, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 实际 G 的指定输出恢复完整 Sat，不另选规范图。 -/
theorem satisfaction_l {ω e t₁ t₂ t₃ P N F U G z R : type_l hℳ}
    (hω : omega_l (ℳ := 𝒱) ω)
    (hStatic : PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := 𝒱) ω e t₁ t₂ t₃ P N F)
    (hG : PowerlessMemberSatisfactionFunctionAbsolute.spec_l (𝒩 := 𝒱)
      ω e t₁ t₂ t₃ P N F U G)
    (hFinite : PowerlessCodedHistoryCoverageSyntax.finite_l (𝒩 := 𝒱) ω U)
    (hValue : value_l (ℳ := 𝒱) G z R) :
    PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒱) ω z e t₁ t₂ t₃ P F R := by
  obtain ⟨hz, _hR, hNorm⟩ := (hG.2 z R).mp hValue
  obtain ⟨_S, _hS, _hSeq, hSat, _hClean⟩ :=
    (PowerlessSatisfactionNormalizedMatrix.spec_iff_of_coverage_l hω hStatic.1.1
      hStatic.2.2.2.1 hStatic.2.1.1 (hFinite z hz)).mp hNorm
  exact hSat

/-- 检查器自己的五个见证具有完整数据与全 raw 行族规格。 -/
theorem image_l (K : source_coding_l hℳ) {ω e t₁ t₂ t₃ P N F Q U G z r : type_l hℳ}
    (hω : ω = K.omega) (hTrans : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) U)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) U)
    (hωU : mem_l hℳ ω U) (hzU : mem_l hℳ z U)
    (hStatic : PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := 𝒱) ω e t₁ t₂ t₃ P N F)
    (hG : PowerlessMemberSatisfactionFunctionAbsolute.spec_l (𝒩 := 𝒱)
      ω e t₁ t₂ t₃ P N F U G)
    (hFinite : PowerlessCodedHistoryCoverageSyntax.finite_l (𝒩 := 𝒱) ω U)
    (h : PowerlessMemberDefImageBounded.image_l (𝒩 := 𝒱) ω e N Q U G z r) :
    holds_l (𝒩 := 𝒱) ω e t₁ t₂ t₃ P N F Q U G z r := by
  obtain ⟨R, hR, S, hS, I, hI, J, hJ, C, hC, hValue, hData, hRows⟩ := h
  exact ⟨R, S, I, J, C, hR, hS, hI, hJ, hC, hValue,
    satisfaction_l (hω.symm ▸ K.omega_spec) hStatic hG hFinite hValue,
    PowerlessMemberDefImageCoverage.reading_l K hω hTrans hClosed hωU hzU hI hData,
    (SecondOrderRowFamilyBounded.family_iff_l hℳ).mp hRows⟩

/-- 完整点资格直接提供本读数的全部母域条件。 -/
theorem point_l (K : source_coding_l hℳ)
    {B ω x a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G z r : type_l hℳ}
    (hω : ω = K.omega)
    (h : PowerlessCodedHistoryCoverageSyntax.point_l (𝒩 := 𝒱)
      B ω x a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G)
    (hValue : value_l (ℳ := 𝒱) D z r) (hz : ∃ t, mem_l hℳ t z) :
    holds_l (𝒩 := 𝒱) ω e t₁ t₂ t₃ P N F Q U G z r := by
  obtain ⟨_ha, _hf, _hx, _hB, hωU, hStatic, hG, hD, _hNumeric, _hA, _hLight,
    hFinite, hTrans, hClosed⟩ := h
  obtain ⟨hzU, _hrU, hChecker⟩ := (hD.2 z r).mp hValue
  rcases hChecker with ⟨hEmpty, _hPair⟩ | ⟨_hNonempty, hImage⟩
  · obtain ⟨t, ht⟩ := hz
    exact (hEmpty t ht).elim
  · exact image_l K hω hTrans hClosed hωU hzU hStatic hG hFinite hImage

def schema_m {Δ : SortContext ℒ}
    (ω e t₁ t₂ t₃ P N F Q U G z r : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
  .imp (PowerlessNaturalOrder.transitive_m U) <|
  .imp (PowerlessRelativeFiniteHullAssignments.closed_m U) <|
  .imp (SecondOrderObjectSyntax.member_m ω U) <|
  .imp (SecondOrderObjectSyntax.member_m z U) <|
  .imp (PowerlessSatisfactionExistenceSyntax.static_m ω e t₁ t₂ t₃ P N F) <|
  .imp (PowerlessMemberSatisfactionFunctionAbsolute.graph_m ω e t₁ t₂ t₃ P N F U G) <|
  .imp (PowerlessCodedHistoryCoverageSyntax.finite_m ω U) <|
  .imp (PowerlessMemberDefImageBounded.image_m ω e N Q U G z r)
    (formula_m ω e t₁ t₂ t₃ P N F Q U G z r)

def sentence_m {Δ : SortContext ℒ}
    (ω e t₁ t₂ t₃ P N F Q U G z r : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m ω e t₁ t₂ t₃ P N F Q U G z r)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (ω e t₁ t₂ t₃ P N F Q U G z r : Term ℒ [] Δ .set) :
    (sentence_m ω e t₁ t₂ t₃ P N F Q U G z r).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, SecondOrderOmegaSyntax.omega_l,
    PowerlessNaturalOrder.transitive_formula_l, PowerlessRelativeFiniteHullAssignments.closed_formula_l,
    PowerlessSatisfactionExistenceSyntax.static_formula_l,
    PowerlessMemberSatisfactionFunctionAbsolute.graph_formula_l,
    PowerlessCodedHistoryCoverageSyntax.finite_formula_l,
    PowerlessMemberDefImageBounded.image_formula_l, formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  intro hω hTrans hClosed hωU hzU hStatic hG hFinite hImage
  exact image_l K (SecondOrderOmega.unique_l hℳ hω K.omega_spec)
    hTrans hClosed hωU hzU hStatic hG hFinite hImage

theorem derives_m {Δ : SortContext ℒ}
    (ω e t₁ t₂ t₃ P N F Q U G z r : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m ω e t₁ t₂ t₃ P N F Q U G z r)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ hℳ => models_l hℳ ω e t₁ t₂ t₃ P N F Q U G z r)

#print axioms formula_l
#print axioms satisfaction_l
#print axioms image_l
#print axioms point_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCodedHistoryDataReading
