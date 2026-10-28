import BMSConstructibleBridge.PowerlessRelativeLimitRelationalGraph
import BMSConstructibleBridge.PowerlessRelativeClassLegacyTranslation

/-! # 指定极限层内的原合法性与部分翻译图

在同一个原 Z₂ 编码包 K 下，直接用已核验的 Δ₀ 有限证书在 W 中构造
两张新的实际关系图。不用仅有 value 读数的旧图相等，也不假设任意 Class
元素属于 W。输入的完整 Seq(ω,ω) 和三角图必须实际在 W；零至四的标签
由 ω∈W 与 W 传递性取得同层界。

两张图均有全部原商坐标读数，因而覆盖全部内部自然数，不限外部标准码。
这是指定层内的语义中间接口；原 Def 装配仍另需其旧 powers 实数 E。
这里没有统一超限历史、Ω 正规性、完整 Collection 或 BMS 对象推导终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitLegacySyntaxGraphs

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)
open PowerlessFormulaValidityReading (code_l)
open SecondOrderEvaluationRule (numeral_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B β W : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

include hBase in
/-- Δ₀ 矩阵自己的坐标守卫消去母积的重复守卫；图仍由原层内分离取得。 -/
private theorem graph_l
    (hLimit : limit_l hℳ β) (hW : level_l hℳ B β W)
    {ω : SecondOrderQuotient.type_l hℳ} (hωW : mem_l hℳ ω W)
    {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (η : Env 𝒱 [] Δ)
    (hParams : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) W)
    (ψ : SecondOrderQuotient.type_l hℳ → SecondOrderQuotient.type_l hℳ → Prop)
    (hRead : ∀ c l, φ.satisfies ((η.pushFree l).pushFree c) ↔ ψ c l)
    (hGuard : ∀ c l, ψ c l → mem_l hℳ c ω ∧ mem_l hℳ l ω) :
    ∃ R, mem_l hℳ R W ∧ ∀ c l,
      value_l (ℳ := 𝒱) R c l ↔ ψ c l := by
  obtain ⟨R, hRW, hR⟩ := PowerlessRelativeLimitRelationalGraph.exists_l
    hBase hLimit hW hφ η hωW hωW hParams
  refine ⟨R, hRW, fun c l => ?_⟩
  have h := (hR c l).trans (and_congr Iff.rfl (and_congr Iff.rfl (hRead c l)))
  exact h.trans ⟨And.right ∘ And.right, fun hψ => ⟨(hGuard c l hψ).1, (hGuard c l hψ).2, hψ⟩⟩

include hBase in
/-- 同一 ω 中的每个实际数字根码都在指定层中；没有外部标准性限制。 -/
private theorem code_member_l (K : source_coding_l hℳ)
    (hW : level_l hℳ B β W) {ω : type_l hℳ B}
    (hωW : mem_l hℳ ω.val W) (hωEq : ω.val = K.omega)
    (n : SecondOrderModel.num_l ℳ) : mem_l hℳ (code_l K n) W := by
  apply PowerlessRelativeLevelClosure.transitive_l hℳ hBase hW ω.val hωW
  simpa only [hωEq, code_l, member_l, SecondOrderQuotient.structure_l]
    using (numberCode_l K n).property

/-- 旧五标签合法性图直接留在 W；原旧合法性实数本身无需属于 Class。 -/
theorem exists_validity_l (K : source_coding_l hℳ)
    (hLimit : limit_l hℳ β) (hW : level_l hℳ B β W)
    {ω N : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω)
    (hωEq : ω.val = K.omega) (hωW : mem_l hℳ ω.val W)
    (hNW : mem_l hℳ N.val W)
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega N.val)
    {V : SecondOrderModel.set_l ℳ} (hV : SecondOrderInternalFormulaSyntax.spec_l V) :
    ∃ G : type_l hℳ B, mem_l hℳ G.val W ∧ ∀ c l : SecondOrderQuotient.type_l hℳ,
      value_l (ℳ := 𝒱) G.val c l ↔ PowerlessRelationalCodeValidity.valid_l K V c l := by
  let e := code_l K (numeral_l ℳ 0)
  let t₁ := code_l K (numeral_l ℳ 1)
  let t₂ := code_l K (numeral_l ℳ 2)
  let t₃ := code_l K (numeral_l ℳ 3)
  let t₄ := code_l K (numeral_l ℳ 4)
  let η : Env 𝒱 [] [.set, .set, .set, .set, .set, .set, .set] :=
    (((((((Env.empty).pushFree t₄).pushFree t₃).pushFree t₂).pushFree t₁).pushFree N.val).pushFree e).pushFree ω.val
  let w : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar .here
  let z : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let s : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let a : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let b : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  let d : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let t : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  have hParams : ∀ q (v : Variable [SetTheory.SetSort.set, .set, .set, .set, .set, .set, .set] q),
      mem_l hℳ (η.freeVal v) W := by
    intro q v
    cases v with
    | here => exact hωW
    | there v => cases v with
      | here => exact code_member_l (hBase := hBase) K hW hωW hωEq (numeral_l ℳ 0)
      | there v => cases v with
        | here => exact hNW
        | there v => cases v with
          | here => exact code_member_l (hBase := hBase) K hW hωW hωEq (numeral_l ℳ 1)
          | there v => cases v with
            | here => exact code_member_l (hBase := hBase) K hW hωW hωEq (numeral_l ℳ 2)
            | there v => cases v with
              | here => exact code_member_l (hBase := hBase) K hW hωW hωEq (numeral_l ℳ 3)
              | there v => cases v with
                | here => exact code_member_l (hBase := hBase) K hW hωW hωEq (numeral_l ℳ 4)
                | there v => nomatch v
  have hRead (c l : SecondOrderQuotient.type_l hℳ) :
      (PowerlessLegacyValidityGraph.matrix_m w z s a b d t).satisfies ((η.pushFree l).pushFree c) ↔
        PowerlessLegacyValidityBounded.certificate_holds_l («𝒩» := 𝒱)
          ω.val e N.val t₁ t₂ t₃ t₄ c l :=
    PowerlessLegacyValidityGraph.matrix_formula_l η w z s a b d t c l
  obtain ⟨g, hgW, hg⟩ := graph_l (hBase := hBase) hLimit hW hωW
    (PowerlessLegacyValidityGraph.matrix_delta_l w z s a b d t) η hParams
    (fun c l => PowerlessLegacyValidityBounded.certificate_holds_l («𝒩» := 𝒱)
      ω.val e N.val t₁ t₂ t₃ t₄ c l) hRead (fun _ _ h => ⟨h.1, h.2.1⟩)
  let G : type_l hℳ B := ⟨g, ⟨β, W, hW, hgW⟩⟩
  refine ⟨G, hgW, fun c l => ?_⟩
  exact (hg c l).trans
    (PowerlessRelativeClassLegacyValidity.certificate_iff_l K hω hωEq hN hV c l)

/-- 由层内旧合法图构造层内原部分翻译图；不比较可能带垃圾成员的旧图。 -/
theorem exists_translation_l (K : source_coding_l hℳ)
    (hLimit : limit_l hℳ β) (hW : level_l hℳ B β W)
    {ω N T G : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω)
    (hωEq : ω.val = K.omega) (hωW : mem_l hℳ ω.val W)
    (hNW : mem_l hℳ N.val W) (hTW : mem_l hℳ T.val W) (hGW : mem_l hℳ G.val W)
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega N.val)
    (hT : map_l (ℳ := 𝒱) T.val K.omega K.omega)
    (hPair : PowerlessBMSQuotientPairingBounds.spec_l K T.val)
    {V C : SecondOrderModel.set_l ℳ}
    (hG : ∀ n l, value_l (ℳ := 𝒱) G.val (code_l K n) (code_l K l) ↔
      SecondOrderPairing.relation_l V n l)
    (hV : SecondOrderInternalFormulaSyntax.spec_l V)
    (hC : SecondOrderLegacyFormulaTranslation.spec_l C) :
    ∃ F : type_l hℳ B, mem_l hℳ F.val W ∧ ∀ c s : SecondOrderQuotient.type_l hℳ,
      value_l (ℳ := 𝒱) F.val c s ↔ PowerlessRelativeClassLegacyTranslation.relation_l K C c s := by
  let e := code_l K (numeral_l ℳ 0)
  let t₁ := code_l K (numeral_l ℳ 1)
  let t₂ := code_l K (numeral_l ℳ 2)
  let t₃ := code_l K (numeral_l ℳ 3)
  let t₄ := code_l K (numeral_l ℳ 4)
  let η : Env 𝒱 [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] :=
    (((((((((Env.empty).pushFree G.val).pushFree t₄).pushFree t₃).pushFree t₂).pushFree t₁).pushFree T.val).pushFree N.val).pushFree e).pushFree ω.val
  let w : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar .here
  let z : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let seq : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let t : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let a : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  let b : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let d : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  let v : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
  let g : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
  have hParams : ∀ q (v : Variable [SetTheory.SetSort.set, .set, .set, .set, .set, .set, .set, .set, .set] q),
      mem_l hℳ (η.freeVal v) W := by
    intro q v
    cases v with
    | here => exact hωW
    | there v => cases v with
      | here => exact code_member_l (hBase := hBase) K hW hωW hωEq (numeral_l ℳ 0)
      | there v => cases v with
        | here => exact hNW
        | there v => cases v with
          | here => exact hTW
          | there v => cases v with
            | here => exact code_member_l (hBase := hBase) K hW hωW hωEq (numeral_l ℳ 1)
            | there v => cases v with
              | here => exact code_member_l (hBase := hBase) K hW hωW hωEq (numeral_l ℳ 2)
              | there v => cases v with
                | here => exact code_member_l (hBase := hBase) K hW hωW hωEq (numeral_l ℳ 3)
                | there v => cases v with
                  | here => exact code_member_l (hBase := hBase) K hW hωW hωEq (numeral_l ℳ 4)
                  | there v => cases v with
                    | here => exact hGW
                    | there v => nomatch v
  have hRead (c s : SecondOrderQuotient.type_l hℳ) :
      (PowerlessLegacyTranslationGraph.matrix_m w z seq t a b d v g).satisfies ((η.pushFree s).pushFree c) ↔
        PowerlessLegacyTranslationGraph.holds_l («𝒩» := 𝒱)
          ω.val e N.val T.val t₁ t₂ t₃ t₄ G.val c s :=
    PowerlessLegacyTranslationGraph.matrix_formula_l η w z seq t a b d v g c s
  obtain ⟨f, hfW, hf⟩ := graph_l (hBase := hBase) hLimit hW hωW
    (PowerlessLegacyTranslationGraph.matrix_delta_l w z seq t a b d v g) η hParams
    (fun c s => PowerlessLegacyTranslationGraph.holds_l («𝒩» := 𝒱)
      ω.val e N.val T.val t₁ t₂ t₃ t₄ G.val c s) hRead (fun _ _ h => ⟨h.1, h.2.1⟩)
  let F : type_l hℳ B := ⟨f, ⟨β, W, hW, hfW⟩⟩
  refine ⟨F, hfW, fun c s => ?_⟩
  exact (hf c s).trans (PowerlessRelativeClassLegacyTranslation.holds_iff_l
    K hω hωEq hN hT hPair hG hV hC c s)

/-- 两张同层图的全部原商读数和全部内部数码读数同时导出。 -/
theorem exists_l (K : source_coding_l hℳ)
    (hLimit : limit_l hℳ β) (hW : level_l hℳ B β W)
    {ω N T : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω)
    (hωEq : ω.val = K.omega) (hωW : mem_l hℳ ω.val W)
    (hNW : mem_l hℳ N.val W) (hTW : mem_l hℳ T.val W)
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega N.val)
    (hT : map_l (ℳ := 𝒱) T.val K.omega K.omega)
    (hPair : PowerlessBMSQuotientPairingBounds.spec_l K T.val)
    {V C : SecondOrderModel.set_l ℳ}
    (hV : SecondOrderInternalFormulaSyntax.spec_l V)
    (hC : SecondOrderLegacyFormulaTranslation.spec_l C) :
    ∃ G F : type_l hℳ B, mem_l hℳ G.val W ∧ mem_l hℳ F.val W ∧
      (∀ c l : SecondOrderQuotient.type_l hℳ,
        value_l (ℳ := 𝒱) G.val c l ↔ PowerlessRelationalCodeValidity.valid_l K V c l) ∧
      (∀ n l, value_l (ℳ := 𝒱) G.val (code_l K n) (code_l K l) ↔
        SecondOrderPairing.relation_l V n l) ∧
      (∀ c s : SecondOrderQuotient.type_l hℳ,
        value_l (ℳ := 𝒱) F.val c s ↔ PowerlessRelativeClassLegacyTranslation.relation_l K C c s) ∧
      (∀ n m, value_l (ℳ := 𝒱) F.val (code_l K n) (code_l K m) ↔
        SecondOrderPairing.relation_l C n m) := by
  obtain ⟨G, hGW, hG⟩ := exists_validity_l (hBase := hBase) K hLimit hW hω hωEq hωW hNW hN hV
  have hGnumeric (n l : SecondOrderModel.num_l ℳ) :
      value_l (ℳ := 𝒱) G.val (code_l K n) (code_l K l) ↔
        SecondOrderPairing.relation_l V n l := by
    refine (hG _ _).trans ?_
    change PowerlessRelativeClassLegacyTranslation.relation_l K V (code_l K n) (code_l K l) ↔ _
    exact PowerlessRelativeClassLegacyTranslation.numeric_l K V n l
  obtain ⟨F, hFW, hF⟩ := exists_translation_l (hBase := hBase) K hLimit hW hω hωEq hωW
    hNW hTW hGW hN hT hPair hGnumeric hV hC
  refine ⟨G, F, hGW, hFW, hG, hGnumeric, hF, fun n m => ?_⟩
  exact (hF _ _).trans (PowerlessRelativeClassLegacyTranslation.numeric_l K C n m)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitLegacySyntaxGraphs
