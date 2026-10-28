import BMSConstructibleBridge.SecondOrderMemberDefFiniteSubsets
import BMSConstructibleBridge.PowerlessRelativeClassFiniteSequences
import BMSConstructibleBridge.PowerlessRelativeLimitClosure
import BMSConstructibleBridge.SecondOrderFunctionEnumeration
import BMSConstructibleBridge.SecondOrderOmegaTransitive

/-! # 无较早极限层前提的内部有限序列集界

在任意较早共同层连续取四个 Def 后继：前两步容纳所有坐标有序对，第三步
容纳它们的全部内部有限子集，第四步用原 Δ₀ 切片收集有限函数图。
因此指定极限层含 ω、X 就足够，不再要求它们同时进入严格较早极限层。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitFiniteSequencesDirect

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)
open PowerlessRelativeClassFiniteSequences (sequence_m sequence_delta_l sequence_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B β C ω X : type_l hℳ}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem member_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    (hω : SecondOrderOmega.omega_l hℳ ω) (hωC : mem_l hℳ ω C) (hXC : mem_l hℳ X C)
    {S : type_l hℳ} (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) ω X S) : mem_l hℳ S C := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  obtain ⟨a, c, ha, hc, hωc, hXc⟩ :=
    PowerlessRelativeLimitClosure.common_l hℳ hBase hLimit hC hωC hXC
  obtain ⟨a₁, c₁, ha₁, hc₁, hDef₁⟩ :=
    PowerlessRelativeLimitClosure.def_bound_l hℳ hBase hLimit hC ha hc
  obtain ⟨a₂, c₂, ha₂, hc₂, hDef₂⟩ :=
    PowerlessRelativeLimitClosure.def_bound_l hℳ hBase hLimit hC ha₁ hc₁
  obtain ⟨a₃, c₃, ha₃, hc₃, hDef₃⟩ :=
    PowerlessRelativeLimitClosure.def_bound_l hℳ hBase hLimit hC ha₂ hc₂
  obtain ⟨a₄, c₄, ha₄, hc₄, hDef₄⟩ :=
    PowerlessRelativeLimitClosure.def_bound_l hℳ hBase hLimit hC ha₃ hc₃
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hc
  have hTrans₁ := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hc₁
  have hTrans₂ := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hc₂
  have hTrans₃ := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hc₃
  have hKeep₁ := SecondOrderMemberDefProperties.contains_l hℳ hDef₁
    (fun x y hx hy => hTrans x hx y hy)
  have hKeep₂ := SecondOrderMemberDefProperties.contains_l hℳ hDef₂
    (fun x y hx hy => hTrans₁ x hx y hy)
  have hKeep₃ := SecondOrderMemberDefProperties.contains_l hℳ hDef₃
    (fun x y hx hy => hTrans₂ x hx y hy)
  have hPairs {x y p : type_l hℳ} (hx : mem_l hℳ x ω) (hy : mem_l hℳ y X)
      (hp : SecondOrderPairObjects.ordered_l hℳ x y p) : mem_l hℳ p c₂ := by
    obtain ⟨s, t, hs, ht, hp⟩ := hp
    have hxC := hTrans ω hωc x hx
    have hyC := hTrans X hXc y hy
    exact SecondOrderMemberDefPair.member_l hℳ hDef₂
      (SecondOrderMemberDefPair.member_l hℳ hDef₁ hxC hxC hs)
      (SecondOrderMemberDefPair.member_l hℳ hDef₁ hxC hyC ht) hp
  have hFiniteMaps {n f : type_l hℳ} (hn : mem_l hℳ n ω)
      (hf : map_l (ℳ := 𝒱) f n X) : mem_l hℳ f c₃ := by
    have hFinite := SecondOrderFunctionEnumeration.finite_l hℳ hn hf
    rw [hωEq] at hFinite
    apply SecondOrderMemberDefFiniteSubsets.member_l K hDef₃ hFinite
    intro p hp
    obtain ⟨x, y, hx, hy, hxy⟩ := hf.1 p hp
    exact hPairs (SecondOrderOmegaTransitive.member_l hℳ hω hn hx) hy hxy
  let φ : Formula ℒ [] [.set, .set, .set] :=
    sequence_m (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
  let η : Env 𝒱 [] [.set, .set] := ((Env.empty).pushFree X).pushFree ω
  have hParams : ∀ s (v : Variable [SetTheory.SetSort.set, SetTheory.SetSort.set] s),
      mem_l hℳ (η.freeVal v) c₃ := by
    intro s v
    cases v with
    | here => exact hKeep₃ ω (hKeep₂ ω (hKeep₁ ω hωc))
    | there v => cases v with
      | here => exact hKeep₃ X (hKeep₂ X (hKeep₁ X hXc))
      | there v => nomatch v
  have hSC₄ : mem_l hℳ S c₄ := SecondOrderMemberDefBoundedSlice.member_l hℳ (φ := φ)
    hDef₄ hTrans₃ (sequence_delta_l _ _ _) η hParams (by
      intro f
      change ThirdOrderSemantics.member_l 𝒱 f S ↔ _
      rw [hS f]
      have hφ := sequence_formula_l (η.pushFree f)
        (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
      constructor
      · rintro ⟨n, hn, hf⟩
        exact ⟨hFiniteMaps hn hf, hφ.mpr ⟨n, hn, hf⟩⟩
      · intro hf
        exact hφ.mp hf.2)
  exact (PowerlessRelativeLimitClosure.value_l hℳ hBase hLimit hC S).mpr ⟨a₄, c₄, ha₄, hc₄, hSC₄⟩

theorem exists_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    (hω : SecondOrderOmega.omega_l hℳ ω) (hωC : mem_l hℳ ω C) (hXC : mem_l hℳ X C) :
    ∃ S, mem_l hℳ S C ∧ PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) ω X S := by
  obtain ⟨S, hS⟩ := SecondOrderFiniteSequencesDerives.exists_l hℳ ω hω X
  exact ⟨S, member_l hBase hLimit hC hω hωC hXC hS, hS⟩

def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  let B : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar .here
  let β := .fvar (.there .here)
  let C := .fvar (.there (.there .here))
  let ω := .fvar (.there (.there (.there .here)))
  let X := .fvar (.there (.there (.there (.there .here))))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B)
    (.imp (PowerlessRelativeHierarchySyntax.limit_m β)
      (.imp (PowerlessRelativeHierarchySyntax.level_m B β C)
        (.imp (SecondOrderOmegaSyntax.omega_m ω)
          (.imp (SecondOrderObjectSyntax.member_m ω C) (.imp (SecondOrderObjectSyntax.member_m X C)
            (.existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar .here)
              (C.weakenBound SetTheory.SetSort.set)) (PowerlessFiniteSequencesSyntax.spec_m
                (ω.weakenBound SetTheory.SetSort.set) (X.weakenBound SetTheory.SetSort.set) (.bvar .here)))))))))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) : sentence_m.TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ,
    PowerlessRelativeHierarchySemantics.limit_formula_l, PowerlessRelativeHierarchySemantics.level_formula_l K,
    SecondOrderOmegaSyntax.omega_l hℳ, PowerlessFiniteSequencesSyntax.spec_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval, Term.eval_weakenBound]
  exact fun hBase hLimit hC hω hωC hXC => exists_l hBase hLimit hC hω hωC hXC

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitFiniteSequencesDirect
