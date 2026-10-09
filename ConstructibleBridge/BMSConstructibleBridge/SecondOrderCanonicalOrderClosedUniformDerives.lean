import BMSConstructibleBridge.SecondOrderCanonicalOrderUniformDerives
import BMSConstructibleBridge.PowerlessRelativeClassLegacyImageDefClosure

/-! # 无类内可数性前提的封闭规范 Def 后继：原 Z₂ 对象模式

对象语言为纯隶属 ℒ，背景是原 num/set 的 SecondOrderArithmetic.theory_m，
正式出口为原推导核中 GraphTranslation 下的 Derives。给定实际 Class
母集 A 和关系 P，实际原 Def(A,D) 自动提供 D 的 Class 证书，不把 D
属于 Class 或类内可数性放在前提，也不要求实际 Class 枚举图。

同一六对象编码包先于全部 A、P、D。良序、母集传递性、原 Def、完整
Sat、规范步骤、初段保持及候选唯一性均在完整原商解释；唯一性量化
任意 raw 候选 E'，并非只量化 Class 候选。全部存在见证留在 Prop，
没有抽取模型外部选择函数。本模式不构造相容历史或共同界，不是最终
BMS 良序句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalOrderClosedUniformDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding StabilityFrame
open SecondOrderCanonicalOrderUniform (step_m step_l step_formula_l)
open PowerlessRelativeHierarchySyntax (class_m)
open PowerlessMemberDefClosureDerives (transitive_m transitive_formula_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up t))
private abbrev up₆ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₃ (up₃ t)

/-- 只有 A、P 的 Class 守卫；原 Def 的结果 D 属于 Class 是结论。 -/
def mode_m {Γ Δ : SortContext ℒ} (B ω e t₁ t₂ t₃ Pair Valid : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <|
    let A : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
    let P := .bvar (.there .here)
    let D := .bvar .here
    .imp (.conj (class_m (up₃ B) A) (class_m (up₃ B) P)) <|
      .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m A P) <|
        .imp (transitive_m A) <| .imp (PowerlessMemberDefSyntax.global_m A D) <|
          .conj (class_m (up₃ B) D) <|
            .existsE .set <|
              let E : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
              let v (t : Term ℒ Γ Δ .set) := up (up₃ t)
              .conj (class_m (v B) E) <|
                .conj (step_m (v ω) (up A) (up P) (v e) (v t₁) (v t₂) (v t₃)
                  (v Pair) (v Valid) (up D) E) <|
                  .conj (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m (up D) E) <|
                    .conj (SecondOrderWellOrderCoherentUnionDerives.extension_m (up A) (up P) (up D) E) <|
                      .forallE .set <|
                        .imp (step_m (up (v ω)) (up (up A)) (up (up P)) (up (v e)) (up (v t₁))
                          (up (v t₂)) (up (v t₃)) (up (v Pair)) (up (v Valid)) (up (up D)) (.bvar .here))
                          (.equal (.bvar .here) (up E))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem mode_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (B ω e t₁ t₂ t₃ Pair Valid : Term ℒ Γ Δ .set) :
    (mode_m B ω e t₁ t₂ t₃ Pair Valid).satisfies η ↔
      ∀ A P D : SecondOrderQuotient.type_l hℳ,
        (PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) A ∧
          PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) P) →
        wellOrder_l (ℳ := 𝒱) A P →
        (∀ x y, SecondOrderQuotient.mem_l hℳ x A → SecondOrderQuotient.mem_l hℳ y x →
          SecondOrderQuotient.mem_l hℳ y A) → SecondOrderMemberDef.spec_l hℳ A D →
        PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) D ∧
          ∃ E : SecondOrderQuotient.type_l hℳ,
            PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) E ∧
            step_l (ℳ₀ := 𝒱) (ω.eval η) A P (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
              (Pair.eval η) (Valid.eval η) D E ∧ wellOrder_l (ℳ := 𝒱) D E ∧
            SecondOrderWellOrderCoherentUnion.extension_l (ℳ₀ := 𝒱) A P D E ∧
            ∀ E', step_l (ℳ₀ := 𝒱) (ω.eval η) A P (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
              (Pair.eval η) (Valid.eval η) D E' → E' = E := by
  simp only [mode_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l, transitive_formula_l,
    SecondOrderWellOrderCoherentUnionDerives.extension_formula_l,
    PowerlessMemberDefDerives.formula_l K, step_formula_l,
    up₃, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 在任何 A、P、raw D 之前固定六对象包，再自动证明 D 的 Class 闭包。 -/
theorem class_total_l {B : SecondOrderQuotient.type_l hℳ}
    {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
      ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}
    {ω : type_l hℳ B} (hΩ : omega_l (ℳ := structure_l hℳ B hBase) ω) :
    ∃ e t₁ t₂ t₃ Pair Valid : type_l hℳ B,
      ∀ A P : type_l hℳ B, ∀ D : SecondOrderQuotient.type_l hℳ,
        wellOrder_l (ℳ := 𝒱) A.val P.val →
        (∀ x y, SecondOrderQuotient.mem_l hℳ x A.val → SecondOrderQuotient.mem_l hℳ y x →
          SecondOrderQuotient.mem_l hℳ y A.val) → SecondOrderMemberDef.spec_l hℳ A.val D →
        PowerlessRelativeClassCorrespondence.member_l hℳ B D ∧
          ∃ E : type_l hℳ B,
            step_l (ℳ₀ := 𝒱) ω.val A.val P.val e.val t₁.val t₂.val t₃.val Pair.val Valid.val D E.val ∧
            wellOrder_l (ℳ := 𝒱) D E.val ∧
            SecondOrderWellOrderCoherentUnion.extension_l (ℳ₀ := 𝒱) A.val P.val D E.val ∧
            ∀ E' : SecondOrderQuotient.type_l hℳ,
              step_l (ℳ₀ := 𝒱) ω.val A.val P.val e.val t₁.val t₂.val t₃.val Pair.val Valid.val D E' →
              E' = E.val := by
  obtain ⟨e, t₁, t₂, t₃, Pair, Valid, hAll⟩ := SecondOrderCanonicalOrderUniform.class_total_l hΩ
  refine ⟨e, t₁, t₂, t₃, Pair, Valid, ?_⟩
  intro A P D hP hTrans hDef
  have hD := PowerlessRelativeClassLegacyImageDefClosure.class_l hBase A.property hDef
  let D' : type_l hℳ B := ⟨D, hD⟩
  obtain ⟨E, hStep, hOrder, hUnique⟩ := hAll A P D' hP hTrans hDef
  exact ⟨hD, E, hStep, hOrder, SecondOrderCanonicalOrderPreservation.extension_l hStep hTrans hDef, hUnique⟩

/-- 六个存在量词在模式的三个全称域量词之前，不抽取统一 Type 函数。 -/
def total_m {Γ Δ : SortContext ℒ} (B ω : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .imp (transitive_m B) <| .imp (class_m B ω) <| .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .existsE .set <| .existsE .set <| .existsE .set <|
      .existsE .set <| .existsE .set <| .existsE .set <|
        mode_m (up₆ B) (up₆ ω) (.bvar (.there (.there (.there (.there (.there .here))))))
          (.bvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there (.there .here))))
          (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

def schema_m : Formula ℒ [] [.set, .set] := total_m (.fvar .here) (.fvar (.there .here))
def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) : sentence_m.TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, total_m, Formula.satisfies, transitive_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, omega_formula_l, mode_formula_l K,
    up₆, up₃, up, Term.eval_weakenBound, Term.eval]
  intro hBase hClass hω
  let B : SecondOrderQuotient.type_l hℳ := η.freeVal .here
  have hBase' : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
      ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B :=
    fun x hx y hy => hBase x y hx hy
  let ω : type_l hℳ B := ⟨η.freeVal (.there .here), hClass⟩
  have hΩ : omega_l (ℳ := structure_l hℳ B hBase') ω :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase') ω).mpr hω
  obtain ⟨e, t₁, t₂, t₃, Pair, Valid, hAll⟩ := class_total_l hΩ
  refine ⟨e.val, t₁.val, t₂.val, t₃.val, Pair.val, Valid.val, ?_⟩
  intro A P D hGuards hP hTrans hDef
  let A' : type_l hℳ B := ⟨A, hGuards.1⟩
  let P' : type_l hℳ B := ⟨P, hGuards.2⟩
  obtain ⟨hD, E, hStep, hOrder, hExtension, hUnique⟩ := hAll A' P' D hP hTrans hDef
  exact ⟨hD, E.val, E.property, hStep, hOrder, hExtension, hUnique⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms mode_formula_l
#print axioms class_total_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalOrderClosedUniformDerives
