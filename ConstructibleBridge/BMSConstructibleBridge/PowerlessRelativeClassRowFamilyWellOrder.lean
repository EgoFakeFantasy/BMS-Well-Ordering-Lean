import BMSConstructibleBridge.PowerlessRelativeClassRowFamily

/-! # 内部良序指标的全部行子集良序

保留行族的精确值域、最小代表逆图及最终比较关系。重复的行子集由
最小指标识别，不选择每个子集的任意表示。对象出口使用原 Z₂ 理论。
将该关系接到完整 Sat 后才能获得定义子集族，跨层相容仍需另证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassRowFamilyWellOrder

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassEnumerationWellOrder (wellOrder_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up (up t)))

def specification_m {Γ Δ : SortContext ℒ}
    (I A Q R Y F J L : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeClassRowFamily.specification_m I A Q Y F) <|
    .conj (PowerlessRelativeClassWellOrderSection.specification_m I Y F R J)
      (PowerlessRelativeClassWellOrderPullback.specification_m Y I J R L)

def schema_m : Formula ℒ [] [.set, .set, .set, .set] :=
  let I : Term ℒ [] [.set, .set, .set, .set] .set := .fvar .here
  let A : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there .here)
  let Q : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let R : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  .imp (wellOrder_m I R) <| .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
    specification_m (up₄ I) (up₄ A) (up₄ Q) (up₄ R)
      (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here)))
      (.bvar (.there .here)) (.bvar .here)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    sentence_m.TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, specification_m, Formula.satisfies,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    PowerlessRelativeClassRowFamily.specification_formula_l,
    PowerlessRelativeClassWellOrderSection.specification_formula_l,
    PowerlessRelativeClassWellOrderPullback.specification_formula_l,
    up₄, up, Term.eval_weakenBound, Term.eval]
  intro hR
  obtain ⟨Y, F, hF, hOnto, hRead, hRange⟩ :=
    PowerlessRelativeClassRowFamily.exists_l (hBase := hBase) (η.freeVal .here)
      (η.freeVal (.there .here)) (η.freeVal (.there (.there .here)))
  obtain ⟨J, hJ, hInject, hJRead⟩ := PowerlessRelativeClassWellOrderSection.exists_l hF hR hOnto
  obtain ⟨L, hL⟩ := PowerlessRelativeClassWellOrderPullback.exists_l hJ hInject hR
  exact ⟨Y, F, J, L, ⟨hF, hOnto, hRead, hRange⟩, ⟨hJ, hInject, hJRead⟩, hL⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ h𝒩 B hBase => models_l h𝒩 B hBase)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassRowFamilyWellOrder
