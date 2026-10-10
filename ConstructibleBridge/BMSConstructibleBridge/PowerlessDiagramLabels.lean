import BMSConstructibleBridge.PowerlessDiagramConstraint

/-!
# 同一函数图的逐值标签约束

原一元公式作用于函数的每个实际输出，而非一个与函数无关的固定参数。
定义域保持为内部集合；公式不按宿主有限列表展开下标。
与 DiagramFamily 的共同见证接线时，g 取其函数绑定槽，q 取原定义域项。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessDiagramLabels

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 标签自由槽读取内层输出见证；其余自由参数原样保留。 -/
def binding_m {Γ Δ : SortContext ℒ} :
    Substitution ℒ [] (.set :: Δ) (.set :: .set :: Γ) Δ :=
  .map (fun v => nomatch v) (fun {s} v => match s, v with
    | .set, .here => .bvar .here
    | .set, .there v => .fvar v)

def labels_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (g q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.imp
    (SecondOrderObjectSyntax.member_m (.bvar .here) (q.weakenBound SetTheory.SetSort.set))
    (.existsE .set (.conj
      (SecondOrderObjectSyntax.value_m
        ((g.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set)
        (.bvar (.there .here)) (.bvar .here))
      (φ.substitute binding_m))))

theorem binding_formula_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (η : Env ℳ Γ Δ) (i a : carrier_l ℳ) :
    (φ.substitute binding_m).satisfies ((η.pushBound i).pushBound a) ↔
      φ.satisfies ((PowerlessDiagramConstraint.parameters_l η).pushFree a) := by
  rw [Formula.satisfies_substitute]
  have h : ((η.pushBound i).pushBound a).pullback binding_m =
      (PowerlessDiagramConstraint.parameters_l η).pushFree a := by
    apply Env.ext (bound := []) (fun {_} v => nomatch v)
    · intro s v
      match s, v with
      | .set, .here => rfl
      | .set, .there v => rfl
  rw [h]

theorem labels_formula_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (η : Env ℳ Γ Δ) (g q : Term ℒ Γ Δ .set) :
    (labels_m φ g q).satisfies η ↔
      ∀ i, member_l ℳ i (q.eval η) → ∃ a, value_l (g.eval η) i a ∧
        φ.satisfies ((PowerlessDiagramConstraint.parameters_l η).pushFree a) := by
  simp only [labels_m, Formula.satisfies, SecondOrderObjectSyntax.member_m,
    Arguments.eval, value_formula_l, Term.eval_weakenBound, binding_formula_l]
  rfl

/-- 指定内部下标迹的逐值约束；迹只需包含于函数的真实定义域。 -/
theorem trace_source_l {U : carrier_l ℳ} {hU₀ : ∃ x, member_l ℳ x U}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (hUT : PowerlessNaturalOrder.transitive_l U)
    {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (η : Env (structure_l U hU₀) Γ Δ) (g D : Term ℒ Γ Δ .set)
    {q : carrier_l ℳ} {B : type_l U} (hg : map_l (g.eval η).val q B.val)
    (hD : ThirdOrderSemantics.subset_l (D.eval η).val q)
    (P : carrier_l ℳ → Prop)
    (hφ : ∀ a : type_l U,
      φ.satisfies ((PowerlessDiagramConstraint.parameters_l η).pushFree a) ↔ P a.val) :
    (labels_m φ g D).satisfies η ↔
      ∀ i, member_l ℳ i (D.eval η).val → ∀ a, value_l (g.eval η).val i a → P a := by
  rw [labels_formula_l]
  constructor
  · intro h i hi a ha
    obtain ⟨b, hb, hP⟩ := h ⟨i, hUT (D.eval η).val i (D.eval η).property hi⟩ hi
    have hba := PowerlessFunction.value_unique_l hℳ hg
      ((PowerlessSourceGraphAbsolute.value_l hUT).mp hb) ha
    exact hba ▸ (hφ b).mp hP
  · intro h i hi
    obtain ⟨a, ⟨haB, ha⟩, _⟩ := hg.2 i.val (hD i.val hi)
    let a₀ : type_l U := ⟨a, hUT B.val a B.property haB⟩
    exact ⟨a₀, (PowerlessSourceGraphAbsolute.value_l hUT).mpr ha,
      (hφ a₀).mpr (h i.val hi a ha)⟩

/-- 成员结构中的逐值约束精确控制环境中同一函数图的全部实际输出。
小结构只需传递性；原公式与目标性质的对应显式给出。 -/
theorem source_l {U : carrier_l ℳ} {hU₀ : ∃ x, member_l ℳ x U}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (hUT : PowerlessNaturalOrder.transitive_l U)
    {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (η : Env (structure_l U hU₀) Γ Δ) (g q : Term ℒ Γ Δ .set)
    {B : type_l U} (hg : map_l (g.eval η).val (q.eval η).val B.val)
    (P : carrier_l ℳ → Prop)
    (hφ : ∀ a : type_l U,
      φ.satisfies ((PowerlessDiagramConstraint.parameters_l η).pushFree a) ↔ P a.val) :
    (labels_m φ g q).satisfies η ↔
      ∀ i a, value_l (g.eval η).val i a → P a := by
  rw [trace_source_l hℳ hUT φ η g q hg (fun _ h => h) P hφ]
  exact ⟨fun h i a ha => h i (PowerlessFunction.value_mem_l hℳ hg ha).1 a ha,
    fun h i _ a ha => h i a ha⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessDiagramLabels
