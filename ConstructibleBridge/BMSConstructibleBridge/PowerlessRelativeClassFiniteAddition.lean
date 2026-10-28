import BMSConstructibleBridge.PowerlessRelativeClassFunctionExtension
import BMSConstructibleBridge.PowerlessRelativeClassInduction
import BMSConstructibleBridge.PowerlessAdditionFiniteSyntax
import BMSConstructibleBridge.SecondOrderNaturalBounds
import BMSConstructibleBridge.SecondOrderNaturalCases

/-! # 相对类内的内部有限加法轨迹

常值零轨迹与单点函数延拓逐次构造后继计算。归纳实例是实际类相对化
公式的原 Z₂ 翻译，故覆盖全部内部长度，不使用完整 Collection。
结论只保证有限轨迹在类中；整条 ω 运算图仍须另外证明类内存在。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFiniteAddition

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

private theorem successor_unique_l {a b c : type_l hℳ B}
    (hb : PowerlessNatural.successor_l (ℳ := structure_l hℳ B hBase) a b)
    (hc : PowerlessNatural.successor_l (ℳ := structure_l hℳ B hBase) a c) : b = c :=
  Subtype.ext (PowerlessBMSQuotientRecursion.successor_unique_l (a := a.val) (b := b.val) (c := c.val)
    ((PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) a b).mp hb)
    ((PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) a c).mp hc))

private theorem value_unique_l {f A D x y z : type_l hℳ B}
    (hf : map_l (ℳ := structure_l hℳ B hBase) f A D)
    (hy : value_l (ℳ := structure_l hℳ B hBase) f x y)
    (hz : value_l (ℳ := structure_l hℳ B hBase) f x z) : y = z :=
  Subtype.ext (SecondOrderFunctionProperties.value_unique_l hℳ
    ((PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f A D).mp hf)
    ((PowerlessRelativeClassFunctionAbsolute.value_l f x y).mp hy)
    ((PowerlessRelativeClassFunctionAbsolute.value_l f x z).mp hz))

theorem zero_l {ω e a : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω)
    (he : ∀ x : type_l hℳ B, ¬mem_l hℳ x.val e.val) (ha : mem_l hℳ a.val ω.val)
    (heω : mem_l hℳ e.val ω.val) :
    ∃ g : type_l hℳ B, PowerlessAdditionFinite.trace_l (ℳ := structure_l hℳ B hBase) ω e a e g := by
  obtain ⟨m, hmω, hm⟩ := ((PowerlessNatural.inductive_iff_l
    (ℳ := structure_l hℳ B hBase) ω).mp hω.1).2 e heω
  obtain ⟨g, hg, hValue⟩ := PowerlessRelativeClassFunctionExtension.constant_l m ω a ha
  exact ⟨g, m, hm, hg, (hValue e a).mpr ⟨(hm e).mpr (Or.inr rfl), rfl⟩,
    fun k _ _ _ hk _ _ _ => (he k hk).elim⟩

theorem extension_trace_l {ω e a n m T g f x y : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω) (hn : mem_l hℳ n.val ω.val)
    (hm : PowerlessNatural.successor_l (ℳ := structure_l hℳ B hBase) n m)
    (hg : PowerlessAdditionFinite.trace_l (ℳ := structure_l hℳ B hBase) ω e a n g)
    (hT : PowerlessNatural.successor_l (ℳ := structure_l hℳ B hBase) m T)
    (hx : value_l (ℳ := structure_l hℳ B hBase) g n x)
    (hy : PowerlessNatural.successor_l (ℳ := structure_l hℳ B hBase) x y)
    (hf : map_l (ℳ := structure_l hℳ B hBase) f T ω)
    (hValue : ∀ k z : type_l hℳ B, value_l (ℳ := structure_l hℳ B hBase) f k z ↔
      value_l (ℳ := structure_l hℳ B hBase) g k z ∨ k = m ∧ z = y) :
    PowerlessAdditionFinite.trace_l (ℳ := structure_l hℳ B hBase) ω e a m f := by
  obtain ⟨S, hS, hg, hZero, hStep⟩ := hg
  have hSm : S = m := successor_unique_l hS hm
  subst S
  have hIrrefl : ¬mem_l hℳ m.val m.val := fun h => SecondOrderNaturalCases.asymmetry_l hℳ h h
  have hOld (k z : type_l hℳ B) (hk : mem_l hℳ k.val m.val)
      (hz : value_l (ℳ := structure_l hℳ B hBase) f k z) :
      value_l (ℳ := structure_l hℳ B hBase) g k z := by
    rcases (hValue k z).mp hz with hz | ⟨hEq, _⟩
    · exact hz
    · exact (hIrrefl (hEq ▸ hk)).elim
  refine ⟨T, hT, hf, (hValue e a).mpr (Or.inl hZero), ?_⟩
  intro k l z w hk hl hz hw
  rcases (hm k).mp hk with hk | hk
  · obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
    have hωEq := SecondOrderOmega.unique_l hℳ
      ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω) K.omega_spec
    have hlBound := SecondOrderNaturalBounds.bound_l K (hωEq ▸ hn) k.val l.val hk
      ((PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) k l).mp hl)
    have hlm : mem_l hℳ l.val m.val := (hm l).mpr
      ((or_congr Iff.rfl ⟨Subtype.ext, congrArg Subtype.val⟩).mp hlBound)
    exact hStep k l z w hk hl (hOld k z ((hm k).mpr (Or.inl hk)) hz) (hOld l w hlm hw)
  · subst k
    have hlm : l = m := successor_unique_l hl hm
    subst l
    have hzx := value_unique_l hg (hOld n z ((hm n).mpr (Or.inr rfl)) hz) hx
    have hwy := value_unique_l hf hw ((hValue m y).mpr (Or.inr ⟨rfl, rfl⟩))
    subst z
    subst w
    exact hy

theorem extend_l {ω e a n m g : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω) (hn : mem_l hℳ n.val ω.val)
    (hm : PowerlessNatural.successor_l (ℳ := structure_l hℳ B hBase) n m)
    (hg : PowerlessAdditionFinite.trace_l (ℳ := structure_l hℳ B hBase) ω e a n g) :
    ∃ f : type_l hℳ B, PowerlessAdditionFinite.trace_l (ℳ := structure_l hℳ B hBase) ω e a m f := by
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
  have hIrrefl : ¬mem_l hℳ m.val m.val := fun h => SecondOrderNaturalCases.asymmetry_l hℳ h h
  obtain ⟨f, hf, hValue⟩ := PowerlessRelativeClassFunctionExtension.exists_l hg hIrrefl hyω hT
  exact ⟨f, extension_trace_l hω hn hm hTrace hT hx.2 hy hf hValue⟩

def template_m : Formula ℒ [] [.set, .set, .set, .set] :=
  .existsE .set (PowerlessAdditionFiniteSyntax.trace_m (.fvar (.there .here))
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here)))) (.fvar .here) (.bvar .here))

theorem template_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e a n : 𝒩.Carrier .set) : template_m.satisfies
      (((((Env.empty (M := 𝒩)).pushFree a).pushFree e).pushFree ω).pushFree n) ↔
        ∃ g, PowerlessAdditionFinite.trace_l (ℳ := 𝒩) ω e a n g := by
  simp only [template_m, Formula.satisfies, PowerlessAdditionFiniteSyntax.trace_formula_l, Term.eval]
  rfl

theorem exists_l {ω e a : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω)
    (he : ∀ x : type_l hℳ B, ¬mem_l hℳ x.val e.val) (ha : mem_l hℳ a.val ω.val) :
    ∀ n : type_l hℳ B, mem_l hℳ n.val ω.val →
      ∃ g : type_l hℳ B, PowerlessAdditionFinite.trace_l (ℳ := structure_l hℳ B hBase) ω e a n g := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωEq := SecondOrderOmega.unique_l hℳ
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω) K.omega_spec
  let N : SecondOrderModel.num_l ℳ → type_l hℳ B :=
    PowerlessRelativeClassInduction.number_l (hBase := hBase) K
  have heEq : N (SecondOrderModel.zero_l ℳ) = e := Subtype.ext (SecondOrderQuotient.ext_l hℳ _ _
    (fun x => iff_of_false (PowerlessBMSQuotientSuccessor.zero_l K x)
      ((PowerlessRelativeClassOmegaAbsolute.empty_l (hBase := hBase) e).mp he x)))
  let η := (Env.empty (M := structure_l hℳ B hBase)).pushFree (sort := SetTheory.SetSort.set) a
    |>.pushFree (sort := SetTheory.SetSort.set) e |>.pushFree (sort := SetTheory.SetSort.set) ω
  have h := PowerlessRelativeClassInduction.induction_l K template_m η ?_ ?_
  · intro n hn
    obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨n.val, hωEq ▸ hn⟩
    have hNumEq : (numberCode_l K i).val = n.val := congrArg Subtype.val hi
    have hEq : N i = n := Subtype.ext hNumEq
    have h' := (template_formula_l (𝒩 := structure_l hℳ B hBase) ω e a (N i)).mp (h i)
    exact hEq ▸ h'
  · apply (template_formula_l (𝒩 := structure_l hℳ B hBase) ω e a (N (SecondOrderModel.zero_l ℳ))).mpr
    rw [heEq]
    exact zero_l hω he ha (heEq ▸ (hωEq.symm ▸ (numberCode_l K (SecondOrderModel.zero_l ℳ)).property))
  · intro i hi
    apply (template_formula_l (𝒩 := structure_l hℳ B hBase) ω e a (N (SecondOrderModel.succ_l i))).mpr
    have hnω : mem_l hℳ (N i).val ω.val := hωEq.symm ▸ (numberCode_l K i).property
    have hSucc : PowerlessNatural.successor_l (ℳ := structure_l hℳ B hBase)
        (N i) (N (SecondOrderModel.succ_l i)) :=
      (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) (N i) (N (SecondOrderModel.succ_l i))).mpr
        (PowerlessBMSQuotientSuccessor.successor_l K i)
    obtain ⟨g, hg⟩ := (template_formula_l (𝒩 := structure_l hℳ B hBase) ω e a (N i)).mp hi
    exact extend_l (n := N i) (m := N (SecondOrderModel.succ_l i)) (g := g) hω hnω hSucc hg

def schema_m : Formula ℒ [] [.set, .set, .set] :=
  .imp (SecondOrderOmegaSyntax.omega_m (.fvar .here)) <|
    .imp (.forallE .set (.neg (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar (.there .here))))) <|
      .imp (SecondOrderObjectSyntax.member_m (.fvar (.there (.there .here))) (.fvar .here)) <|
        .forallE .set (.imp (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar .here)) <|
          .existsE .set (PowerlessAdditionFiniteSyntax.trace_m (.fvar .here) (.fvar (.there .here))
            (.fvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l : sentence_m.TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hω he ha n hn
  simp only [Formula.satisfies, PowerlessAdditionFiniteSyntax.trace_formula_l, Term.eval]
  exact exists_l ((ThirdOrderSemantics.omega_formula_l η _).mp hω)
    he ha n hn

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ _ _ _ => models_l)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFiniteAddition
