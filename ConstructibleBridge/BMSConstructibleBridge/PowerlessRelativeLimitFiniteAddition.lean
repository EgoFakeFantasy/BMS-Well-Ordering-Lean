import BMSConstructibleBridge.PowerlessRelativeLimitFunctionExtension
import BMSConstructibleBridge.PowerlessRelativeClassFiniteAddition

/-! # 全部内部有限加法轨迹的共同层界

给定包含 ω 的固定非零极限层，零轨迹与每次延拓都留在该层。
对带此层成员条件的实际类公式归纳，覆盖模型内部的任意长度。
结论仍是有限轨迹的界，不自动提供整条 ω 运算图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitFiniteAddition

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
  {β : SecondOrderQuotient.type_l hℳ} {C : type_l hℳ B}

private theorem successor_unique_l {a b c : type_l hℳ B}
    (hb : PowerlessNatural.successor_l (ℳ := structure_l hℳ B hBase) a b)
    (hc : PowerlessNatural.successor_l (ℳ := structure_l hℳ B hBase) a c) : b = c :=
  Subtype.ext (PowerlessBMSQuotientRecursion.successor_unique_l (a := a.val) (b := b.val) (c := c.val)
    ((PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) a b).mp hb)
    ((PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) a c).mp hc))

theorem zero_l {ω e a : type_l hℳ B}
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hC : PowerlessRelativeHierarchySemantics.level_l hℳ B β C.val)
    (hωC : mem_l hℳ ω.val C.val) (hω : omega_l (ℳ := structure_l hℳ B hBase) ω)
    (he : ∀ x : type_l hℳ B, ¬mem_l hℳ x.val e.val)
    (ha : mem_l hℳ a.val ω.val) (heω : mem_l hℳ e.val ω.val) :
    ∃ g : type_l hℳ B, mem_l hℳ g.val C.val ∧
      PowerlessAdditionFinite.trace_l (ℳ := structure_l hℳ B hBase) ω e a e g := by
  obtain ⟨m, _, hm⟩ := ((PowerlessNatural.inductive_iff_l
    (ℳ := structure_l hℳ B hBase) ω).mp hω.1).2 e heω
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC
  have hSingle (x : SecondOrderQuotient.type_l hℳ) : mem_l hℳ x m.val ↔ x = e.val := by
    rw [(PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) e m).mp hm]
    exact ⟨fun h => h.elim
      (fun hx => ((PowerlessRelativeClassOmegaAbsolute.empty_l (hBase := hBase) e).mp he x hx).elim) id, Or.inr⟩
  obtain ⟨g, hgC, hg, hValue⟩ := PowerlessRelativeLimitFunctionExtension.singleton_l hℳ hBase hLimit hC
    (hTrans ω.val hωC e.val heω) (hTrans ω.val hωC a.val ha) ha hSingle
  let g' : type_l hℳ B := ⟨g, ⟨β, C.val, hC, hgC⟩⟩
  have hg' := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) g' m ω).mpr hg
  have h₀ := (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) g' e a).mpr
    ((hValue e.val a.val).mpr ⟨rfl, rfl⟩)
  exact ⟨g', hgC, m, hm, hg', h₀, fun k _ _ _ hk _ _ _ => (he k hk).elim⟩

theorem extend_l {ω e a n m g : type_l hℳ B}
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hC : PowerlessRelativeHierarchySemantics.level_l hℳ B β C.val)
    (hωC : mem_l hℳ ω.val C.val) (hω : omega_l (ℳ := structure_l hℳ B hBase) ω)
    (hn : mem_l hℳ n.val ω.val)
    (hm : PowerlessNatural.successor_l (ℳ := structure_l hℳ B hBase) n m)
    (hgC : mem_l hℳ g.val C.val)
    (hg : PowerlessAdditionFinite.trace_l (ℳ := structure_l hℳ B hBase) ω e a n g) :
    ∃ f : type_l hℳ B, mem_l hℳ f.val C.val ∧
      PowerlessAdditionFinite.trace_l (ℳ := structure_l hℳ B hBase) ω e a m f := by
  have hTrace := hg
  obtain ⟨S, hS, hg, _, _⟩ := hg
  have hSm : S = m := successor_unique_l hS hm
  subst S
  have hInd := (PowerlessNatural.inductive_iff_l (ℳ := structure_l hℳ B hBase) ω).mp hω.1
  obtain ⟨x, hx, _⟩ := hg.2 n ((hm n).mpr (Or.inr rfl))
  obtain ⟨y, hyω, hy⟩ := hInd.2 x hx.1
  obtain ⟨m', hm'ω, hm'⟩ := hInd.2 n hn
  have hmω : mem_l hℳ m.val ω.val := (successor_unique_l hm' hm) ▸ hm'ω
  obtain ⟨T, _, hT⟩ := hInd.2 m hmω
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC
  have hIrrefl : ¬mem_l hℳ m.val m.val := fun h => SecondOrderNaturalCases.asymmetry_l hℳ h h
  obtain ⟨f, hfC, hf, hValue⟩ := PowerlessRelativeLimitFunctionExtension.exists_l hℳ hBase hLimit hC
    hgC (hTrans ω.val hωC m.val hmω) (hTrans ω.val hωC y.val hyω)
    ((PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) g m ω).mp hg) hIrrefl hyω
    ((PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) m T).mp hT)
  let f' : type_l hℳ B := ⟨f, ⟨β, C.val, hC, hfC⟩⟩
  have hf' := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f' T ω).mpr hf
  have hValue' (k z : type_l hℳ B) : value_l (ℳ := structure_l hℳ B hBase) f' k z ↔
      value_l (ℳ := structure_l hℳ B hBase) g k z ∨ k = m ∧ z = y :=
    (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f' k z).trans
      ((hValue k.val z.val).trans (or_congr
        (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) g k z).symm
        (and_congr ⟨Subtype.ext, congrArg Subtype.val⟩ ⟨Subtype.ext, congrArg Subtype.val⟩)))
  exact ⟨f', hfC, PowerlessRelativeClassFiniteAddition.extension_trace_l hω hn hm hTrace hT hx.2 hy hf' hValue'⟩

def template_m : Formula ℒ [] [.set, .set, .set, .set, .set] := .existsE .set (.conj
  (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar (.there .here)))
  (PowerlessAdditionFiniteSyntax.trace_m (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
    (.fvar .here) (.bvar .here)))

theorem template_formula_l (ω e a n : type_l hℳ B) : template_m.satisfies
    ((((((Env.empty (M := structure_l hℳ B hBase)).pushFree a).pushFree e).pushFree ω).pushFree C).pushFree n) ↔
      ∃ g : type_l hℳ B, mem_l hℳ g.val C.val ∧
        PowerlessAdditionFinite.trace_l (ℳ := structure_l hℳ B hBase) ω e a n g := by
  simp only [template_m, Formula.satisfies, PowerlessAdditionFiniteSyntax.trace_formula_l,
    SecondOrderObjectSyntax.member_m, Term.eval, Arguments.eval]
  rfl

theorem exists_l {ω e a : type_l hℳ B}
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hC : PowerlessRelativeHierarchySemantics.level_l hℳ B β C.val)
    (hωC : mem_l hℳ ω.val C.val) (hω : omega_l (ℳ := structure_l hℳ B hBase) ω)
    (he : ∀ x : type_l hℳ B, ¬mem_l hℳ x.val e.val) (ha : mem_l hℳ a.val ω.val) :
    ∀ n : type_l hℳ B, mem_l hℳ n.val ω.val →
      ∃ g : type_l hℳ B, mem_l hℳ g.val C.val ∧
        PowerlessAdditionFinite.trace_l (ℳ := structure_l hℳ B hBase) ω e a n g := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωEq := SecondOrderOmega.unique_l hℳ
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω) K.omega_spec
  let N : SecondOrderModel.num_l ℳ → type_l hℳ B := PowerlessRelativeClassInduction.number_l (hBase := hBase) K
  have heEq : N (SecondOrderModel.zero_l ℳ) = e := Subtype.ext (SecondOrderQuotient.ext_l hℳ _ _
    (fun x => iff_of_false (PowerlessBMSQuotientSuccessor.zero_l K x)
      ((PowerlessRelativeClassOmegaAbsolute.empty_l (hBase := hBase) e).mp he x)))
  let η := (Env.empty (M := structure_l hℳ B hBase)).pushFree (sort := SetTheory.SetSort.set) a
    |>.pushFree (sort := SetTheory.SetSort.set) e |>.pushFree (sort := SetTheory.SetSort.set) ω
    |>.pushFree (sort := SetTheory.SetSort.set) C
  have h := PowerlessRelativeClassInduction.induction_l K template_m η ?_ ?_
  · intro n hn
    obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨n.val, hωEq ▸ hn⟩
    have hNumEq : (numberCode_l K i).val = n.val := congrArg Subtype.val hi
    have hEq : N i = n := Subtype.ext hNumEq
    exact hEq ▸ (template_formula_l (hBase := hBase) (C := C) ω e a (N i)).mp (h i)
  · apply (template_formula_l (hBase := hBase) (C := C) ω e a (N (SecondOrderModel.zero_l ℳ))).mpr
    rw [heEq]
    exact zero_l hLimit hC hωC hω he ha
      (heEq ▸ (hωEq.symm ▸ (numberCode_l K (SecondOrderModel.zero_l ℳ)).property))
  · intro i hi
    apply (template_formula_l (hBase := hBase) (C := C) ω e a (N (SecondOrderModel.succ_l i))).mpr
    have hnω : mem_l hℳ (N i).val ω.val := hωEq.symm ▸ (numberCode_l K i).property
    have hSucc : PowerlessNatural.successor_l (ℳ := structure_l hℳ B hBase)
        (N i) (N (SecondOrderModel.succ_l i)) :=
      (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) (N i) (N (SecondOrderModel.succ_l i))).mpr
        (PowerlessBMSQuotientSuccessor.successor_l K i)
    obtain ⟨g, hgC, hg⟩ := (template_formula_l (hBase := hBase) (C := C) ω e a (N i)).mp hi
    exact extend_l hLimit hC hωC hω hnω hSucc hgC hg

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitFiniteAddition
