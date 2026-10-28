import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseInjectivity
import BMSConstructibleBridge.PowerlessRelativeHierarchyDerives

/-!
# 成员塌缩固定完整传递基集

对象语言是纯隶属 ℒ，背景及正式出口均为原 Z₂。对同一个实际集合函数 H
证明：若传递 B 的全部成员都在源域 I 中，则 H 逐点固定 B 的成员；另有
B∈I 时才取得 H(B)=B。B∈I 本身不代替 B⊆I。

逐点性质的纯公式由既有 WeakSetInduction 归纳，归纳对象属于任意原图商，
没有模型外部良基性或标准 ω 前提。固定基集无需源域外延性或先验单射。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseBase

open Logic FirstOrder SecondOrderObjectSyntax
open PowerlessRelativeMembershipCollapseInjectivity (recursive_l recursive_m recursive_formula_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def point_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (B H x : SecondOrderQuotient.type_l hℳ) : Prop :=
  SecondOrderQuotient.mem_l hℳ x B → ∀ u,
    SecondOrderFunctionObjects.value_l hℳ H x u → u = x

def point_m {Γ Δ : SortContext ℒ} (B H x : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .imp (member_m x B) <| .forallE .set <|
    .imp (value_m (up H) (up x) (.bvar .here)) (.equal (.bvar .here) (up x))

theorem point_formula_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ)
    (B H x : Term ℒ Γ Δ .set) :
    (point_m B H x).satisfies η ↔ point_l hℳ (B.eval η) (H.eval η) (x.eval η) := by
  simp only [point_m, Formula.satisfies, SecondOrderObjectSyntax.value_l,
    up, Term.eval_weakenBound]
  rfl

/-- 首槽为归纳对象，余下两槽保持原 B 和原 H。 -/
def induction_m : Formula ℒ [] [.set, .set, .set] :=
  point_m (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)

theorem induction_formula_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set, .set]) :
    induction_m.satisfies η ↔ point_l hℳ (η.freeVal (.there .here))
      (η.freeVal (.there (.there .here))) (η.freeVal .here) :=
  point_formula_l hℳ η _ _ _

theorem point_all_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (B I T H : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B → ∀ y,
      SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B)
    (hBI : ∀ x, SecondOrderQuotient.mem_l hℳ x B → SecondOrderQuotient.mem_l hℳ x I)
    (hH : SecondOrderFunctionObjects.map_l hℳ H I T) (hRec : recursive_l hℳ I H) :
    ∀ x, point_l hℳ B H x := by
  let η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set] :=
    (Env.empty.pushFree H).pushFree B
  have hAll : ∀ x, induction_m.satisfies (η.pushFree x) := by
    apply PowerlessWeakSetInduction.induction_l (SecondOrderWeakSetTheory.models_l hℳ)
    intro x ih
    apply (induction_formula_l hℳ (η.pushFree x)).mpr
    intro hx u hxu
    apply SecondOrderQuotient.ext_l hℳ u x
    intro z
    constructor
    · intro hzu
      obtain ⟨y, _, hyx, hyz⟩ := (hRec x u (hBI x hx) hxu z).mp hzu
      have hzy : z = y := (induction_formula_l hℳ (η.pushFree y)).mp
        (ih y hyx) (hBase x hx y hyx) z hyz
      exact hzy.symm ▸ hyx
    · intro hzx
      have hzB := hBase x hx z hzx
      obtain ⟨v, hv, _⟩ := hH.2 z (hBI z hzB)
      have hvz : v = z := (induction_formula_l hℳ (η.pushFree z)).mp
        (ih z hzx) hzB v hv.2
      exact (hRec x u (hBI x hx) hxu z).mpr ⟨z, hBI z hzB, hzx, hvz ▸ hv.2⟩
  intro x
  exact (induction_formula_l hℳ (η.pushFree x)).mp (hAll x)

/-- 全部 B 成员的实际 H 图读数，不抽取宿主函数。 -/
theorem fixed_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (B I T H : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B → ∀ y,
      SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B)
    (hBI : ∀ x, SecondOrderQuotient.mem_l hℳ x B → SecondOrderQuotient.mem_l hℳ x I)
    (hH : SecondOrderFunctionObjects.map_l hℳ H I T) (hRec : recursive_l hℳ I H) :
    ∀ x, SecondOrderQuotient.mem_l hℳ x B → SecondOrderFunctionObjects.value_l hℳ H x x := by
  intro x hx
  obtain ⟨u, hu, _⟩ := hH.2 x (hBI x hx)
  exact (point_all_l hℳ B I T H hBase hBI hH hRec x hx u hu.2) ▸ hu.2

/-- B 自身只有在实际域 I 中时才有 H(B)；成员固定加外延性识别该输出。 -/
theorem base_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (B I T H : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B → ∀ y,
      SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B)
    (hBI : ∀ x, SecondOrderQuotient.mem_l hℳ x B → SecondOrderQuotient.mem_l hℳ x I)
    (hH : SecondOrderFunctionObjects.map_l hℳ H I T) (hRec : recursive_l hℳ I H)
    (hB : SecondOrderQuotient.mem_l hℳ B I) : SecondOrderFunctionObjects.value_l hℳ H B B := by
  obtain ⟨u, hu, _⟩ := hH.2 B hB
  have huB : u = B := by
    apply SecondOrderQuotient.ext_l hℳ u B
    intro z
    constructor
    · intro hzu
      obtain ⟨y, _, hyB, hyz⟩ := (hRec B u hB hu.2 z).mp hzu
      have hzy : z = y := point_all_l hℳ B I T H hBase hBI hH hRec y hyB z hyz
      exact hzy.symm ▸ hyB
    · intro hzB
      exact (hRec B u hB hu.2 z).mpr
        ⟨z, hBI z hzB, hzB, fixed_l hℳ B I T H hBase hBI hH hRec z hzB⟩
  exact huB ▸ hu.2

def fixed_m {Γ Δ : SortContext ℒ} (B H : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (member_m (.bvar .here) (up B))
    (value_m (up H) (.bvar .here) (.bvar .here))

theorem fixed_formula_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ)
    (B H : Term ℒ Γ Δ .set) : (fixed_m B H).satisfies η ↔
      ∀ x, SecondOrderQuotient.mem_l hℳ x (B.eval η) →
        SecondOrderFunctionObjects.value_l hℳ (H.eval η) x x := by
  simp only [fixed_m, Formula.satisfies, SecondOrderObjectSyntax.value_l,
    up, Term.eval_weakenBound, member_m, Arguments.eval, Term.eval]
  rfl

/-- 自由槽依次为 B、I、T、H，完整的 B⊆I 为独立守卫。 -/
def schema_m : Formula ℒ [] [.set, .set, .set, .set] :=
  let B : Term ℒ [] [.set, .set, .set, .set] .set := .fvar .here
  let I : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there .here)
  let T : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let H : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  .imp (.conj (PowerlessRelativeHierarchyDerives.transitive_m B)
    (.conj (ThirdOrderTheory.subset_m B I) (.conj (map_m H I T) (recursive_m I H))))
    (.conj (fixed_m B H) (.imp (member_m B I) (value_m H B B)))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    ThirdOrderSemantics.subset_formula_l, ThirdOrderSemantics.subset_l,
    ThirdOrderSemantics.member_l, SecondOrderObjectSyntax.map_l, recursive_formula_l,
    fixed_formula_l, SecondOrderObjectSyntax.value_l,
    member_m, Arguments.eval, Term.eval]
  rintro ⟨hBase, hBI, hH, hRec⟩
  exact ⟨fixed_l hℳ _ _ _ _ hBase hBI hH hRec,
    base_l hℳ _ _ _ _ hBase hBI hH hRec⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m sentence_m (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseBase
