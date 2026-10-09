import BMSConstructibleBridge.PowerlessHereditaryParameterEnvelope
import BMSConstructibleBridge.PowerlessHereditaryProduct
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramAlphabet

/-! # 同一原三类指令字母表的遗传资格

纯隶属 ℒ，背景原 Z₂。原 Q 及其字母表规格保持不变。先把
ω×ω、原常量种子及三个标签放进同一实际可数传递包络 D，
再检查每个原指令的两个坐标都在 D。整张 Q 的遗传证书来自
统一关系母界，不是每个指令分别遗传。公开出口是原核 Derives。

基底、原常量种子及标签的遗传性仍须给出；无需标签互异，
因为本文件仅处理码域资格，不将非法指令变为合法执行。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryProgramAlphabet

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

theorem member_l {B C ω t₀ t₁ t₂ Q : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ x, ε x B → ∀ y, ε y x → ε y B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hB : PowerlessHereditaryClass.member_l hℳ B B)
    (hC : PowerlessHereditaryClass.member_l hℳ B C)
    (h₀ : PowerlessHereditaryClass.member_l hℳ B t₀)
    (h₁ : PowerlessHereditaryClass.member_l hℳ B t₁)
    (h₂ : PowerlessHereditaryClass.member_l hℳ B t₂)
    (hQ : PowerlessRelativeClassCorrespondence.member_l hℳ B Q)
    (hAlphabet : ∀ q, ε q Q ↔ PowerlessRelativeFiniteProgramAlphabet.instruction_l C ω t₀ t₁ t₂ q) :
    PowerlessHereditaryClass.member_l hℳ B Q := by
  have hωHC := PowerlessHereditaryOmega.member_l hℳ hBase hω
  obtain ⟨X, hX⟩ := SecondOrderDefinableRelationImage.exists_l hℳ (Δ := []) .truth Env.empty ω ω
  have hXRead : ∀ p, ε p X ↔ ∃ x y, ε x ω ∧ ε y ω ∧ SecondOrderPairObjects.ordered_l hℳ x y p := by
    simpa only [Formula.satisfies, true_and] using hX
  have hXHC := PowerlessHereditaryProduct.member_l (hBase := hBase) hωHC hωHC hXRead
  let η : Env 𝒱 [] [.set, .set, .set, .set, .set] :=
    (Env.empty (M := 𝒱)).pushFree (sort := SetTheory.SetSort.set) X
      |>.pushFree (sort := SetTheory.SetSort.set) C
      |>.pushFree (sort := SetTheory.SetSort.set) t₀
      |>.pushFree (sort := SetTheory.SetSort.set) t₁
      |>.pushFree (sort := SetTheory.SetSort.set) t₂
  have hParams : ∀ s (v : Variable ([.set, .set, .set, .set, .set] : SortContext ℒ) s),
      PowerlessHereditaryClass.member_l hℳ B (η.freeVal v) := by
    intro s v
    cases s
    cases v with
    | here => exact h₂
    | there v => cases v with
      | here => exact h₁
      | there v => cases v with
        | here => exact h₀
        | there v => cases v with
          | here => exact hC
          | there v => cases v with
            | here => exact hXHC
            | there v => nomatch v
  obtain ⟨D, F, hEnvelope, hωD, hMembers⟩ := PowerlessHereditaryParameterEnvelope.exists_l
    hBase hω hB [.set, .set, .set, .set, .set] η (fun v => .fvar v) hParams
  obtain ⟨hD, hF, _hBD, hTrans, _hω, hMap, hOnto⟩ := hEnvelope
  let O : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨ω, PowerlessHereditaryClass.contained_l hℳ hBase hωHC⟩
  let T : PowerlessRelativeClassStructure.type_l hℳ B := ⟨D, hD⟩
  let J : PowerlessRelativeClassStructure.type_l hℳ B := ⟨F, hF⟩
  have hDHC : PowerlessHereditaryClass.member_l hℳ B D :=
    (PowerlessHereditaryClassInternals.correspondence_l (hBase := hBase) T).mpr
      (PowerlessHereditaryExtension.exists_l O T T J
        ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) O).mpr hω)
        ((PowerlessHereditaryClassInternals.transitive_l (hBase := hBase) T).mpr hTrans)
        (fun _ hx => hx)
        ((PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) J O T).mpr hMap)
        ((PowerlessRelativeClassFunctionAbsolute.onto_l (hBase := hBase) J O T).mpr hOnto))
  have h₀D : ε t₀ D := hMembers _ (.there (.there .here))
  have h₁D : ε t₁ D := hMembers _ (.there .here)
  have h₂D : ε t₂ D := hMembers _ .here
  have hCD : ε C D := hMembers _ (.there (.there (.there .here)))
  have hXD : ε X D := hMembers _ (.there (.there (.there (.there .here))))
  apply PowerlessHereditaryProduct.relation_l (hBase := hBase) hDHC hDHC hQ
  intro q hq
  rcases (hAlphabet q).mp hq with ⟨x, hx, hPair⟩ | ⟨k, hk, hPair⟩ |
    ⟨k, l, p, hk, hl, hkl, hPair⟩
  · exact ⟨t₀, x, h₀D, hTrans C hCD x hx, hPair⟩
  · exact ⟨t₁, k, h₁D, hTrans ω hωD k hk, hPair⟩
  · exact ⟨t₂, p, h₂D, hTrans X hXD p ((hXRead p).mpr ⟨k, l, hk, hl, hkl⟩), hPair⟩

def schema_m {Δ : SortContext ℒ} (B C ω t₀ t₁ t₂ Q : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessHereditaryClass.formula_m B B) <|
        .imp (PowerlessHereditaryClass.formula_m B C) <|
          .imp (PowerlessHereditaryClass.formula_m B t₀) <|
            .imp (PowerlessHereditaryClass.formula_m B t₁) <|
              .imp (PowerlessHereditaryClass.formula_m B t₂) <|
                .imp (PowerlessRelativeHierarchySyntax.class_m B Q) <|
                  .imp (PowerlessRelativeFiniteProgramAlphabet.alphabet_m C ω t₀ t₁ t₂ Q)
                    (PowerlessHereditaryClass.formula_m B Q)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B C ω t₀ t₁ t₂ Q : Term ℒ [] Δ .set) :
    (Metatheory.Formula.forall_close (schema_m B C ω t₀ t₁ t₂ Q)).TrueIn
      (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessHereditaryClass.formula_l K,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l]
  intro η hBase hω hB hC h₀ h₁ h₂ hQ hAlphabet
  exact member_l hBase hω hB hC h₀ h₁ h₂ hQ hAlphabet

theorem derives_m {Δ : SortContext ℒ} (B C ω t₀ t₁ t₂ Q : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (Metatheory.Formula.forall_close (schema_m B C ω t₀ t₁ t₂ Q))) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 B C ω t₀ t₁ t₂ Q)

#print axioms member_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryProgramAlphabet
