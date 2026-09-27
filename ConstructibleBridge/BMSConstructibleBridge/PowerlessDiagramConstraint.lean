import BMSConstructibleBridge.PowerlessRelationDiagram
import BMSConstructibleBridge.PowerlessSourceGraphAbsolute

/-!
# 内部关系图的统一重标号约束

原公式 φ 读取一对标签。图 D 记录必须保留的索引对；新标签图 g
由两个对象存在量词与一个内部全称量词约束，不展开内部长度 q。
这里只编译单个二元关系的精确约束，不宣称全部 BMS 重标号条件已满足。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessDiagramConstraint

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 自由槽 D,f,g；选择器的首槽改读绑定索引对。 -/
def binding_m {Γ : SortContext ℒ} : Substitution ℒ [] (.set :: .set :: .set :: Γ)
    [.set] (.set :: .set :: .set :: Γ) :=
  .map (fun v => nomatch v) (fun {s} v => match s, v with
    | .set, .here => .bvar .here
    | .set, .there v => .fvar (.there v))

def preserves_m {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ)) :
    Formula ℒ [] (.set :: .set :: .set :: Γ) :=
  .forallE .set (.imp (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar .here))
    ((PowerlessRelationDiagram.selector_m φ).substitute binding_m))

def preserves_l {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : Env ℳ [] Γ) (D f g : carrier_l ℳ) : Prop :=
  ∀ p, member_l ℳ p D → PowerlessRelationDiagram.selected_l φ η f g p

theorem binding_formula_l {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : Env ℳ [] Γ) (D f g p : carrier_l ℳ) :
    ((PowerlessRelationDiagram.selector_m φ).substitute binding_m).satisfies
      ((((η.pushFree g).pushFree f).pushFree D).pushBound p) ↔
      PowerlessRelationDiagram.selected_l φ η f g p := by
  rw [Formula.satisfies_substitute]
  have h : ((((η.pushFree g).pushFree f).pushFree D).pushBound p).pullback binding_m =
      ((η.pushFree g).pushFree f).pushFree p := by
    apply Env.ext
    · intro s v
      nomatch v
    · intro s v
      match s, v with
      | .set, .here => rfl
      | .set, .there v => rfl
  rw [h]
  exact PowerlessRelationDiagram.selector_formula_l φ η f g p

theorem preserves_formula_l {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : Env ℳ [] Γ) (D f g : carrier_l ℳ) :
    (preserves_m φ).satisfies (((η.pushFree g).pushFree f).pushFree D) ↔
      preserves_l φ η D f g := by
  simp only [preserves_m, preserves_l, SecondOrderObjectSyntax.member_m, Formula.satisfies]
  exact forall_congr' (fun p => imp_congr_right (fun _ => binding_formula_l φ η D f g p))

/-- 原自由参数保持不变，图与两张标签图可以是外层绑定项；允许两张图取同一个项。 -/
def instance_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (D f g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  (preserves_m φ).substitute (.map (fun {s} (v : Variable ([] : SortContext ℒ) s) => nomatch v)
    (fun {s} (v : Variable (SetTheory.SetSort.set :: SetTheory.SetSort.set :: SetTheory.SetSort.set :: Δ) s) => match s, v with
    | .set, .here => D
    | .set, .there .here => f
    | .set, .there (.there .here) => g
    | .set, .there (.there (.there v)) => .fvar v))

def parameters_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) : Env ℳ [] Δ where
  boundVal v := nomatch v
  freeVal v := η.freeVal v

theorem instance_formula_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env ℳ Γ Δ) (D f g : Term ℒ Γ Δ .set) :
    (instance_m φ D f g).satisfies η ↔
      preserves_l φ (parameters_l η) (D.eval η) (f.eval η) (g.eval η) := by
  rw [instance_m, Formula.satisfies_substitute]
  have h : η.pullback (.map (fun {s} (v : Variable ([] : SortContext ℒ) s) => nomatch v)
    (fun {s} (v : Variable (SetTheory.SetSort.set :: SetTheory.SetSort.set :: SetTheory.SetSort.set :: Δ) s) => match s, v with
      | .set, .here => D
      | .set, .there .here => f
      | .set, .there (.there .here) => g
      | .set, .there (.there (.there v)) => .fvar v)) =
      (((parameters_l η).pushFree (g.eval η)).pushFree (f.eval η)).pushFree (D.eval η) := by
    apply Env.ext
    · intro s v
      nomatch v
    · intro s v
      match s, v with
      | .set, .here => rfl
      | .set, .there .here => rfl
      | .set, .there (.there .here) => rfl
      | .set, .there (.there (.there v)) => rfl
  rw [h]
  exact preserves_formula_l φ (parameters_l η) (D.eval η) (f.eval η) (g.eval η)

/-- 自由槽 D,f,q；g 与其值域 B 由对象存在量词给出。 -/
def candidate_binding_m {Γ : SortContext ℒ} : Substitution ℒ [] (.set :: .set :: .set :: Γ)
    [.set, .set] (.set :: .set :: .set :: Γ) :=
  .map (fun v => nomatch v) (fun {s} v => match s, v with
    | .set, .here => .fvar .here
    | .set, .there .here => .fvar (.there .here)
    | .set, .there (.there .here) => .bvar (.there .here)
    | .set, .there (.there (.there v)) => .fvar (.there (.there (.there v))))

def candidate_m {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ)) :
    Formula ℒ [] (.set :: .set :: .set :: Γ) :=
  .existsE .set (.existsE .set (.conj
    (SecondOrderObjectSyntax.map_m (.bvar (.there .here)) (.fvar (.there (.there .here))) (.bvar .here))
    ((preserves_m φ).substitute candidate_binding_m)))

theorem candidate_binding_formula_l {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : Env ℳ [] Γ) (D f q g B : carrier_l ℳ) :
    ((preserves_m φ).substitute candidate_binding_m).satisfies
      (((((η.pushFree q).pushFree f).pushFree D).pushBound g).pushBound B) ↔
      preserves_l φ η D f g := by
  rw [Formula.satisfies_substitute]
  have h : (((((η.pushFree q).pushFree f).pushFree D).pushBound g).pushBound B).pullback
      candidate_binding_m = ((η.pushFree g).pushFree f).pushFree D := by
    apply Env.ext
    · intro s v
      nomatch v
    · intro s v
      match s, v with
      | .set, .here => rfl
      | .set, .there .here => rfl
      | .set, .there (.there .here) => rfl
      | .set, .there (.there (.there v)) => rfl
  rw [h]
  exact preserves_formula_l φ η D f g

theorem candidate_formula_l {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : Env ℳ [] Γ) (D f q : carrier_l ℳ) :
    (candidate_m φ).satisfies (((η.pushFree q).pushFree f).pushFree D) ↔
      ∃ g B, map_l g q B ∧ preserves_l φ η D f g := by
  simp only [candidate_m, Formula.satisfies, map_formula_l]
  apply exists_congr
  intro g
  apply exists_congr
  intro B
  exact and_congr Iff.rfl (candidate_binding_formula_l φ η D f q g B)

/-- 小层中的候选图确实是环境中的函数图，并保留每一条指定实际关系。
这里只要求源公式对目标关系的正确解释；不要求小层满足完整集合论。 -/
theorem extract_l {A : carrier_l ℳ} {hA₀ : ∃ x, member_l ℳ x A}
    (hAT : PowerlessNaturalOrder.transitive_l A)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : Env (PowerlessMemberStructure.structure_l A hA₀) [] Γ)
    (D f q : PowerlessMemberStructure.type_l A) (r : carrier_l ℳ → carrier_l ℳ → Prop)
    (hφ : ∀ a b : PowerlessMemberStructure.type_l A,
      φ.satisfies ((η.pushFree a).pushFree b) → r a.val b.val)
    (h : (candidate_m φ).satisfies (((η.pushFree q).pushFree f).pushFree D)) :
    ∃ g B, member_l ℳ g A ∧ member_l ℳ B A ∧ map_l g q.val B ∧
      ∀ p, member_l ℳ p D.val → ∃ i j a b,
        ordered_l i j p ∧ value_l f.val i a ∧ value_l g j b ∧ r a b := by
  obtain ⟨g, B, hg, h⟩ := (candidate_formula_l φ η D f q).mp h
  refine ⟨g.val, B.val, g.property, B.property, (PowerlessSourceGraphAbsolute.map_l hAT).mp hg, ?_⟩
  intro p hp
  obtain ⟨i, j, a, b, hp₀, hf, hg, h⟩ := h ⟨p, hAT D.val p D.property hp⟩ hp
  exact ⟨i.val, j.val, a.val, b.val, (PowerlessSourceGraphAbsolute.ordered_l hAT).mp hp₀,
    (PowerlessSourceGraphAbsolute.value_l hAT).mp hf,
    (PowerlessSourceGraphAbsolute.value_l hAT).mp hg, hφ a b h⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessDiagramConstraint
