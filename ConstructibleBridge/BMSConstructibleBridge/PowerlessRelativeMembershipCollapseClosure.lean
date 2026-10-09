import BMSConstructibleBridge.PowerlessRelativeMembershipCollapse
import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseBase
import BMSConstructibleBridge.PowerlessRelativeFiniteHullClosure
import BMSConstructibleBridge.SecondOrderOmegaTransitive

/-! # 实际坍缩目标的真实闭包与全部内部有限赋值

原递归方程把对象像的成员精确识别为其 I 内成员的像。它保持真实
无序对和二元并；配合源域真实闭包、满射与环境外延性，目标 T 也对
全部真实操作封闭。I 不必传递，T 不必预先具有 Class 资格或源理论。
原内部 ω 的固定性随后给出 T 内的全部内部有限赋值，不用宿主递归。
对象出口仍为原 Z₂ 的普通 Derives；完整 Sat 与 Def 认同另待证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseClosure

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeMembershipCollapseInjectivity (recursive_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 真实无序对的所有成员都在 I 中，递归方程给出其像的真实规格。 -/
theorem pair_l {I T H a b p x y q : type_l hℳ}
    (hH : SecondOrderFunctionObjects.map_l hℳ H I T) (hRec : recursive_l hℳ I H)
    (ha : mem_l hℳ a I) (hb : mem_l hℳ b I) (hpI : mem_l hℳ p I)
    (hax : SecondOrderFunctionObjects.value_l hℳ H a x)
    (hby : SecondOrderFunctionObjects.value_l hℳ H b y)
    (hpq : SecondOrderFunctionObjects.value_l hℳ H p q)
    (hp : ThirdOrderSemantics.pair_l (ℳ := 𝒱) a b p) :
    ThirdOrderSemantics.pair_l (ℳ := 𝒱) x y q := by
  intro z
  refine (hRec p q hpI hpq z).trans ⟨?_, ?_⟩
  · rintro ⟨v, _, hvp, hvz⟩
    rcases (hp v).mp hvp with rfl | rfl
    · exact Or.inl (SecondOrderFunctionProperties.value_unique_l hℳ hH hvz hax)
    · exact Or.inr (SecondOrderFunctionProperties.value_unique_l hℳ hH hvz hby)
  · rintro (rfl | rfl)
    · exact ⟨a, ha, (hp a).mpr (Or.inl rfl), hax⟩
    · exact ⟨b, hb, (hp b).mpr (Or.inr rfl), hby⟩

/-- 即使 a/b 不包含于 I，截取 I 后的二元并仍精确对应目标二元并。 -/
theorem binary_l {I H a b c x y z : type_l hℳ}
    (hRec : recursive_l hℳ I H)
    (ha : mem_l hℳ a I) (hb : mem_l hℳ b I) (hc : mem_l hℳ c I)
    (hax : SecondOrderFunctionObjects.value_l hℳ H a x)
    (hby : SecondOrderFunctionObjects.value_l hℳ H b y)
    (hcz : SecondOrderFunctionObjects.value_l hℳ H c z)
    (h : PowerlessRelativeFiniteHullAssignments.binary_l (𝒩 := 𝒱) a b c) :
    PowerlessRelativeFiniteHullAssignments.binary_l (𝒩 := 𝒱) x y z := by
  intro u
  refine (hRec c z hc hcz u).trans ⟨?_, ?_⟩
  · rintro ⟨v, hvI, hvc, hvu⟩
    rcases (h v).mp hvc with hva | hvb
    · exact Or.inl ((hRec a x ha hax u).mpr ⟨v, hvI, hva, hvu⟩)
    · exact Or.inr ((hRec b y hb hby u).mpr ⟨v, hvI, hvb, hvu⟩)
  · rintro (hux | huy)
    · obtain ⟨v, hvI, hva, hvu⟩ := (hRec a x ha hax u).mp hux
      exact ⟨v, hvI, (h v).mpr (Or.inl hva), hvu⟩
    · obtain ⟨v, hvI, hvb, hvu⟩ := (hRec b y hb hby u).mp huy
      exact ⟨v, hvI, (h v).mpr (Or.inr hvb), hvu⟩

/-- 满射回收输入，实际 map 回收输出，外延性识别任意真实目标操作。 -/
theorem closed_l {I T H : type_l hℳ}
    (hH : PowerlessRelativeMembershipCollapse.spec_l I T H)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) I) :
    PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) T := by
  constructor
  · intro x y p hx hy hp
    obtain ⟨a, ha, hax⟩ := hH.2.2.1 x hx
    obtain ⟨b, hb, hby⟩ := hH.2.2.1 y hy
    obtain ⟨c, hc⟩ := SecondOrderPairObjects.pair_exists_l hℳ a b
    have hcI := hClosed.1 a b c ha hb hc
    obtain ⟨q, hq, _⟩ := hH.2.1.2 c hcI
    have hqPair := pair_l hH.2.1 hH.2.2.2.1 ha hb hcI hax hby hq.2 hc
    have hpEq : p = q := SecondOrderQuotient.ext_l hℳ p q
      (fun u => (hp u).trans (hqPair u).symm)
    exact hpEq.symm ▸ hq.1
  · intro x y p hx hy hp
    obtain ⟨a, ha, hax⟩ := hH.2.2.1 x hx
    obtain ⟨b, hb, hby⟩ := hH.2.2.1 y hy
    obtain ⟨c, hc⟩ := PowerlessRelativeFiniteHullClosure.binary_exists_l hℳ a b
    have hcI := hClosed.2 a b c ha hb hc
    obtain ⟨q, hq, _⟩ := hH.2.1.2 c hcI
    have hqBinary := binary_l hH.2.2.2.1 ha hb hcI hax hby hq.2 hc
    have hpEq : p = q := SecondOrderQuotient.ext_l hℳ p q
      (fun u => (hp u).trans (hqBinary u).symm)
    exact hpEq.symm ▸ hq.1

/-- 只要求实际输出在 T 中，陪域对象本身可以不属于 T。 -/
theorem assignments_l (K : source_coding_l hℳ) {I T H n A f : type_l hℳ}
    (hH : PowerlessRelativeMembershipCollapse.spec_l I T H)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) I)
    (hωI : ∀ x, mem_l hℳ x K.omega → mem_l hℳ x I)
    (hn : mem_l hℳ n K.omega) (hf : SecondOrderFunctionObjects.map_l hℳ f n A)
    (hValues : ∀ x y, SecondOrderFunctionObjects.value_l hℳ f x y → mem_l hℳ y T) :
    mem_l hℳ f T := by
  have hFixed := PowerlessRelativeMembershipCollapseBase.fixed_l hℳ K.omega I T H
    (fun _ hx _ hy => SecondOrderOmegaTransitive.member_l hℳ K.omega_spec hx hy)
    hωI hH.2.1 hH.2.2.2.1
  have hωT x (hx : mem_l hℳ x K.omega) : mem_l hℳ x T := by
    obtain ⟨y, hy, _⟩ := hH.2.1.2 x (hωI x hx)
    have hyEq := SecondOrderFunctionProperties.value_unique_l hℳ hH.2.1 hy.2 (hFixed x hx)
    exact hyEq ▸ hy.1
  exact PowerlessRelativeFiniteHullAssignments.member_l K (A := A) (f := f)
    hωT (closed_l hH hClosed) hn hf hValues

/-- 真实闭包运输的纯对象模式，源域闭包不是完整源理论假设。 -/
def schema_m {Δ : SortContext ℒ} (I T H : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeFiniteHullAssignments.closed_m I) <|
    .imp (PowerlessRelativeMembershipCollapse.spec_m I T H)
      (PowerlessRelativeFiniteHullAssignments.closed_m T)

def sentence_m {Δ : SortContext ℒ} (I T H : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m I T H)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (I T H : Term ℒ [] Δ .set) :
    (sentence_m I T H).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro ζ
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeFiniteHullAssignments.closed_formula_l,
    PowerlessRelativeMembershipCollapse.spec_formula_l]
  exact fun hClosed hH => closed_l hH hClosed

theorem derives_m {Δ : SortContext ℒ} (I T H : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m I T H)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ I T H)

#print axioms pair_l
#print axioms binary_l
#print axioms closed_l
#print axioms assignments_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseClosure
