import BMSConstructibleBridge.PowerlessHereditaryOrdinalCountability
import BMSConstructibleBridge.PowerlessHereditaryProduct
import BMSConstructibleBridge.PowerlessRelativeClassAmbientBaseGuard

/-! # 遗传基底的实际环境初始良序

纯隶属 ℒ，背景原 Z₂。由基底的实际遗传包络取得类内单射，
逆为内部 ω 满射，再构造对全部 raw 子集有效的同一初始良序。
整张干净良序图的遗传资格由基底乘积给出，不预供任何枚举。

非空性和传递性是明确前提；公开出口为原核 Derives。
本文件不把 Class 内最小元断言当作 raw 良序，也不抽取 Type 选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryAmbientBaseGuard

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "ε" => SecondOrderQuotient.mem_l hℳ

theorem exists_l (K : source_coding_l hℳ) {B ω : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ x, ε x B → ∀ y, ε y x → ε y B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hB : PowerlessHereditaryClass.member_l hℳ B B)
    (hNonempty : ∃ d, ε d B) :
    ∃ P₀, PowerlessHereditaryClass.member_l hℳ B P₀ ∧
      SecondOrderCanonicalLevelDerives.guard_l B P₀ := by
  obtain ⟨d, hd⟩ := hNonempty
  obtain ⟨f, hf, hMap, hInjective⟩ :=
    PowerlessHereditaryOrdinalCountability.countable_of_hereditary_l (hBase := hBase) K hω hB
  let A : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨B, PowerlessHereditaryClass.contained_l hℳ hBase hB⟩
  let O : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨ω, PowerlessHereditaryClass.contained_l hℳ hBase
      (PowerlessHereditaryOmega.member_l hℳ hBase hω)⟩
  let R : PowerlessRelativeClassStructure.type_l hℳ B := ⟨f, hf⟩
  let d' : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨d, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase A.property hd⟩
  let 𝒩₀ := PowerlessRelativeClassStructure.structure_l hℳ B hBase
  have hR : map_l (ℳ := 𝒩₀) R A O :=
    (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) R A O).mpr hMap
  have hInject (x y i : PowerlessRelativeClassStructure.type_l hℳ B)
      (hx : value_l (ℳ := 𝒩₀) R x i) (hy : value_l (ℳ := 𝒩₀) R y i) : x = y :=
    Subtype.ext (hInjective x.val y.val i.val
      ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) R x i).mp hx)
      ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) R y i).mp hy))
  obtain ⟨G, hG, hOnto, _hRead⟩ :=
    PowerlessRelativeClassInjectionEnumeration.exists_l hR hInject (d := d') hd
  have hGRaw := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) G O A).mp hG
  have hOntoRaw := (PowerlessRelativeClassFunctionAbsolute.onto_l (hBase := hBase) G O A).mp hOnto
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  obtain ⟨P₀, hGuard⟩ := PowerlessRelativeClassAmbientBaseGuard.exists_l K hBase G
    (hωEq ▸ hGRaw) (hωEq ▸ hOntoRaw) ⟨d, hd⟩
  exact ⟨P₀.val, PowerlessHereditaryProduct.relation_l (hBase := hBase) hB hB
    P₀.property hGuard.2.2.2, hGuard⟩

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def conclusion_m {Γ Δ : SortContext ℒ} (B : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .conj (PowerlessHereditaryClass.formula_m (up B) (.bvar .here))
    (SecondOrderCanonicalLevelDerives.guard_m (up B) (.bvar .here))

def schema_m {Δ : SortContext ℒ} (B ω : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessHereditaryClass.formula_m B B) <|
        .imp (.existsE .set (SecondOrderObjectSyntax.member_m (.bvar .here) (up B)))
          (conclusion_m B)

theorem conclusion_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (B : Term ℒ Γ Δ .set) : (conclusion_m B).satisfies η ↔
      ∃ P₀, PowerlessHereditaryClass.member_l hℳ (B.eval η) P₀ ∧
        SecondOrderCanonicalLevelDerives.guard_l (B.eval η) P₀ := by
  simp only [conclusion_m, Formula.satisfies, PowerlessHereditaryClass.formula_l K,
    SecondOrderCanonicalLevelDerives.guard_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B ω : Term ℒ [] Δ .set) :
    (Metatheory.Formula.forall_close (schema_m B ω)).TrueIn
      (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessHereditaryClass.formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval,
    conclusion_formula_l K, up, Term.eval_weakenBound, Term.eval]
  intro η hBase hω hB hNonempty
  exact exists_l K hBase hω hB hNonempty

theorem derives_m {Δ : SortContext ℒ} (B ω : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (Metatheory.Formula.forall_close (schema_m B ω))) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 B ω)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryAmbientBaseGuard
