import BMSConstructibleBridge.SecondOrderFunctionRestriction
import BMSConstructibleBridge.SecondOrderFunctionAppendDerives
import BMSConstructibleBridge.SecondOrderNaturalCases

/-! # 非传递有限壳中的全部内部有限赋值

对象语言为纯隶属 ℒ，背景与正式推导关系均为原 Z₂。域 I 不必传递，
也不要求 I 属于某个层 W。只消费实际 ω 的全部成员属于 I，以及真实
无序对和二元并的闭包；这些规格量化全部原商对象，不是 MemberI 的
局部配对或并集判定。有序对由三次无序对构造，空函数由 ω⊆I 给出。

归纳公式量化任意原商陪域及任意原商函数图，每一步先实际限制到前驱
长度，再添加末项并由函数图外延性识别原图。归纳来自同一纯公式的原
Z₂ 翻译实例，覆盖非标准内部长度；没有宿主 ω 递归或 Type 数据选择。
本工具只给有限赋值闭包，不把完整 Def(I) 误用于某个 X∈I 的完整母域。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullAssignments

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open SecondOrderObjectSyntax (member_m map_m value_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)

private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)

/-- 二元并使用全部环境对象的精确成员方程。 -/
def binary_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (A B C : carrier_l 𝒩) : Prop :=
  ∀ x, member_l 𝒩 x C ↔ member_l 𝒩 x A ∨ member_l 𝒩 x B

def binary_m {Γ Δ : SortContext ℒ} (A B C : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (member_m (.bvar .here) (up C))
    (.disj (member_m (.bvar .here) (up A)) (member_m (.bvar .here) (up B)))

theorem binary_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (A B C : Term ℒ Γ Δ .set) :
    (binary_m A B C).satisfies η ↔ binary_l (A.eval η) (B.eval η) (C.eval η) := by
  simp only [binary_m, binary_l, Formula.satisfies, member_m, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 两项实际基础操作闭包；不将传递性或未知有限图闭包加入前提。 -/
def closed_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (I : carrier_l 𝒩) : Prop :=
  (∀ a b p, member_l 𝒩 a I → member_l 𝒩 b I → pair_l a b p → member_l 𝒩 p I) ∧
    ∀ a b c, member_l 𝒩 a I → member_l 𝒩 b I → binary_l a b c → member_l 𝒩 c I

def closed_m {Γ Δ : SortContext ℒ} (I : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let pair : Formula ℒ Γ Δ := .forallE .set <| .forallE .set <| .forallE .set <|
    let a := .bvar (.there (.there .here))
    let b := .bvar (.there .here)
    let p := .bvar .here
    .imp (member_m a (up₃ I)) <| .imp (member_m b (up₃ I)) <|
      .imp (SecondOrderObjectSyntax.pair_m a b p) (member_m p (up₃ I))
  let union : Formula ℒ Γ Δ := .forallE .set <| .forallE .set <| .forallE .set <|
    let a := .bvar (.there (.there .here))
    let b := .bvar (.there .here)
    let c := .bvar .here
    .imp (member_m a (up₃ I)) <| .imp (member_m b (up₃ I)) <|
      .imp (binary_m a b c) (member_m c (up₃ I))
  .conj pair union

theorem closed_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (I : Term ℒ Γ Δ .set) :
    (closed_m I).satisfies η ↔ closed_l (I.eval η) := by
  simp only [closed_m, closed_l, Formula.satisfies, pair_formula_l, binary_formula_l,
    member_m, Arguments.eval, up₃, up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

/-- 原函数的全部实际输出属于 I；陪域对象本身不须属于或包含于 I。 -/
def values_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (I f : carrier_l 𝒩) : Prop :=
  ∀ x y, value_l f x y → member_l 𝒩 y I

def values_m {Γ Δ : SortContext ℒ} (I f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <|
    .imp (value_m (up₂ f) (.bvar (.there .here)) (.bvar .here))
      (member_m (.bvar .here) (up₂ I))

theorem values_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (I f : Term ℒ Γ Δ .set) :
    (values_m I f).satisfies η ↔ values_l (I.eval η) (f.eval η) := by
  simp only [values_m, values_l, Formula.satisfies, value_formula_l, member_m,
    Arguments.eval, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

def point_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (I n : carrier_l 𝒩) : Prop :=
  ∀ A f, map_l f n A → values_l I f → member_l 𝒩 f I

def point_m {Γ Δ : SortContext ℒ} (I n : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <|
    let A := .bvar (.there .here)
    let f := .bvar .here
    .imp (map_m f (up₂ n) A) <| .imp (values_m (up₂ I) f) (member_m f (up₂ I))

theorem point_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (I n : Term ℒ Γ Δ .set) :
    (point_m I n).satisfies η ↔ point_l (I.eval η) (n.eval η) := by
  simp only [point_m, point_l, Formula.satisfies, map_formula_l, values_formula_l,
    member_m, Arguments.eval, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 首自由槽为内部长度，第二槽保留同一实际 I。 -/
def template_m : Formula ℒ [] [.set, .set] :=
  point_m (.fvar (.there .here)) (.fvar .here)

theorem template_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (I n : carrier_l 𝒩) :
    template_m.satisfies ((Env.empty (M := 𝒩)).pushFree I |>.pushFree n) ↔ point_l I n := by
  simp only [template_m, point_formula_l, Term.eval]
  rfl

/-- 所用归纳实例就在原推导核中；不是宿主 Nat 归纳。 -/
theorem induction_derives_m : Derives SecondOrderArithmetic.theory_m []
    (SecondOrderArithmetic.induction_m (GraphTranslation.form_m template_m)) :=
  GraphTranslation.induction_m template_m

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ

/-- 已有真实 Kuratowski 对的三个无序对证书全部留在 I。 -/
theorem ordered_l {I a b p : Raw}
    (h : ∀ x y z, mem_l hℳ x I → mem_l hℳ y I →
      SecondOrderPairObjects.pair_l hℳ x y z → mem_l hℳ z I)
    (ha : mem_l hℳ a I) (hb : mem_l hℳ b I)
    (hp : SecondOrderPairObjects.ordered_l hℳ a b p) : mem_l hℳ p I := by
  obtain ⟨s, t, hs, ht, hp⟩ := hp
  exact h s t p (h a a s ha ha hs) (h a b t ha hb ht) hp

/-- 单点添加只消费单集及二元并的实际闭包。 -/
theorem adjoin_l {I A a C : Raw} (h : closed_l (𝒩 := 𝒱) I)
    (hA : mem_l hℳ A I) (ha : mem_l hℳ a I)
    (hC : ∀ x, mem_l hℳ x C ↔ mem_l hℳ x A ∨ x = a) : mem_l hℳ C I := by
  obtain ⟨s, hs⟩ := SecondOrderPairObjects.pair_exists_l hℳ a a
  have hsI := h.1 a a s ha ha hs
  apply h.2 A s C hA hsI
  intro x
  change mem_l hℳ x C ↔ mem_l hℳ x A ∨ mem_l hℳ x s
  rw [hC x, hs x]
  simp only [or_self]

/-- 所有真实内部有限函数：只限制其实际输出，不限制陪域的多余成员。 -/
theorem member_l (K : source_coding_l hℳ) {I n A f : Raw}
    (hωI : ∀ x, mem_l hℳ x K.omega → mem_l hℳ x I)
    (hI : closed_l (𝒩 := 𝒱) I) (hn : mem_l hℳ n K.omega)
    (hf : map_l (ℳ := 𝒱) f n A) (hValues : values_l (𝒩 := 𝒱) I f) : mem_l hℳ f I := by
  let η : Env 𝒱 [] [.set] := (Env.empty).pushFree I
  have h := PowerlessBMSQuotientInduction.induction_l K template_m η ?_ ?_
  · obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨n, hn⟩
    have hi' : (numberCode_l K i).val = n := congrArg Subtype.val hi
    exact (template_formula_l (𝒩 := 𝒱) I n).mp (hi' ▸ h i) A f hf hValues
  · apply (template_formula_l (𝒩 := 𝒱) I _).mpr
    intro A f hf _
    have he := PowerlessBMSQuotientSuccessor.zero_l K
    have hEq : f = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val :=
      SecondOrderQuotient.ext_l hℳ _ _ fun p => iff_of_false
        (fun hp => by obtain ⟨x, _, hx, _, _⟩ := hf.1 p hp; exact he x hx) (he p)
    have heω : mem_l hℳ (numberCode_l K (SecondOrderModel.zero_l ℳ)).val K.omega :=
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).property
    exact hEq.symm ▸ hωI (numberCode_l K (SecondOrderModel.zero_l ℳ)).val heω
  · intro i hi
    apply (template_formula_l (𝒩 := 𝒱) I _).mpr
    intro A f hf hValues
    let n := (numberCode_l K i).val
    let m := (numberCode_l K (SecondOrderModel.succ_l i)).val
    have hm : PowerlessNatural.successor_l (ℳ := 𝒱) n m :=
      PowerlessBMSQuotientSuccessor.successor_l K i
    obtain ⟨g, hg, hRead⟩ := SecondOrderFunctionRestriction.exists_l hℳ hf
      (fun x hx => (hm x).mpr (Or.inl hx))
    have hgI := (template_formula_l (𝒩 := 𝒱) I n).mp hi A g hg
      (fun x y hxy => hValues x y ((hRead x y).mp hxy).2)
    obtain ⟨d, hd, _⟩ := hf.2 n ((hm n).mpr (Or.inr rfl))
    have hdI := hValues n d hd.2
    have hnI := hωI n (numberCode_l K i).property
    obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ n d
    have hpI := ordered_l (hℳ := hℳ) hI.1 hnI hdI hp
    obtain ⟨g', hG⟩ := SecondOrderFunctionAppendDerives.adjoin_l hℳ g p
    have hg'I := adjoin_l (hℳ := hℳ) hI hgI hpI hG
    have hg' : map_l (ℳ := 𝒱) g' m A := SecondOrderFunctionAppend.map_l hℳ hg
      (fun hnn => SecondOrderNaturalCases.asymmetry_l hℳ hnn hnn) hd.1 hm hp hG
    have hValue := SecondOrderFunctionAppend.value_l hℳ hp hG
    have hEq : f = g' := PowerlessBMSQuotientRecursion.map_ext_l (hM := hℳ)
      (A := m) (B := A) (D := A) hf hg' (by
        intro x y
        change SecondOrderFunctionObjects.value_l hℳ f x y ↔
          SecondOrderFunctionObjects.value_l hℳ g' x y
        rw [hValue x y]
        constructor
        · intro hxy
          rcases (hm x).mp (SecondOrderFunctionProperties.value_mem_l hℳ hf hxy).1 with hx | hx
          · exact Or.inl ((hRead x y).mpr ⟨hx, hxy⟩)
          · subst x
            exact Or.inr ⟨rfl, SecondOrderFunctionProperties.value_unique_l hℳ hf hxy hd.2⟩
        · rintro (hxy | ⟨rfl, rfl⟩)
          · exact ((hRead x y).mp hxy).2
          · exact hd.2)
    exact hEq.symm ▸ hg'I

/-- 实际切片母域包含于 I 时，不要求该母域对象也在 I。 -/
theorem subset_member_l (K : source_coding_l hℳ) {I n A f : Raw}
    (hωI : ∀ x, mem_l hℳ x K.omega → mem_l hℳ x I)
    (hI : closed_l (𝒩 := 𝒱) I) (hn : mem_l hℳ n K.omega)
    (hf : map_l (ℳ := 𝒱) f n A) (hA : ∀ x, mem_l hℳ x A → mem_l hℳ x I) : mem_l hℳ f I :=
  member_l K hωI hI hn hf (fun _ y hxy =>
    hA y (SecondOrderFunctionProperties.value_mem_l hℳ hf hxy).2)

def finite_m {Γ Δ : SortContext ℒ} (I ω : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (member_m (.bvar .here) (up ω)) (point_m (up I) (.bvar .here))

theorem finite_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (I ω : Term ℒ Γ Δ .set) : (finite_m I ω).satisfies η ↔
      ∀ n, mem_l hℳ n (ω.eval η) → point_l (𝒩 := 𝒱) (I.eval η) n := by
  simp only [finite_m, Formula.satisfies, point_formula_l, member_m, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 自由槽依次为 I、ω；所有操作守卫均在原商环境中读取。 -/
def schema_m : Formula ℒ [] [.set, .set] :=
  let I : Term ℒ [] [.set, .set] .set := .fvar .here
  let ω := .fvar (.there .here)
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (ThirdOrderTheory.subset_m ω I) <| .imp (closed_m I) (finite_m I ω)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, SecondOrderOmegaSyntax.omega_l,
    ThirdOrderSemantics.subset_formula_l, ThirdOrderSemantics.subset_l,
    ThirdOrderSemantics.member_l, closed_formula_l, finite_formula_l,
    SecondOrderQuotient.structure_l]
  intro hω hωI hI n hn A f hf hValues
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  exact member_l K (I := η.freeVal .here) (n := n) (A := A) (f := f)
    (fun x hx => hωI x (hωEq.symm ▸ hx)) hI (hωEq ▸ hn) hf hValues

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m sentence_m (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullAssignments
