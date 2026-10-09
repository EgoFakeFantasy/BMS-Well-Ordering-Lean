import BMSConstructibleBridge.PowerlessSourceRebinding
import YesMetaZFC.Automation.TotalizedGraph

/-! # 原源矩阵的无选择总化

原源矩阵按输入、输出、参数排列。缺省参数只插在原两槽之后；
总化在同一源结构中进行，有原见证时保留全部原见证，无见证时只允许
缺省值。这里不称任意原公式为 Δ₀，也不把 Prop 存在性抽成 Type 函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceWitnessTotalization

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

private def extension_m {Δ : SortContext ℒ} :
    Substitution ℒ [] (.set :: .set :: Δ) [] (.set :: .set :: .set :: Δ) :=
  .map (fun v => nomatch v) (fun {s} v => match s with
    | .set => match v with
      | .here => .fvar .here
      | .there .here => .fvar (.there .here)
      | .there (.there v) => .fvar (.there (.there (.there v))))

private def exchange_m {Δ : SortContext ℒ} :
    Substitution ℒ [] (.set :: .set :: Δ) [] (.set :: .set :: Δ) :=
  .map (fun v => nomatch v) (fun {s} v => match s with
    | .set => match v with
      | .here => .fvar (.there .here)
      | .there .here => .fvar .here
      | .there (.there v) => .fvar (.there (.there v)))

private def transpose_m {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) := φ.substitute exchange_m

variable {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ}

private theorem extension_l {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (d x y : carrier_l 𝒱) :
    (φ.substitute extension_m).satisfies (((η.pushFree d).pushFree y).pushFree x) ↔
      φ.satisfies ((η.pushFree y).pushFree x) := by
  rw [Formula.satisfies_substitute]
  apply Iff.of_eq
  apply congrArg (fun ξ => φ.satisfies ξ)
  apply Env.ext
  · intro s v; nomatch v
  · intro s v; cases s
    cases v with
    | here => rfl
    | there v => cases v <;> rfl

private theorem transpose_l {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (x y : carrier_l 𝒱) :
    (transpose_m φ).satisfies ((η.pushFree y).pushFree x) ↔
      φ.satisfies ((η.pushFree x).pushFree y) := by
  rw [transpose_m, Formula.satisfies_substitute]
  apply Iff.of_eq
  apply congrArg (fun ξ => φ.satisfies ξ)
  apply Env.ext
  · intro s v; nomatch v
  · intro s v; cases s
    cases v with
    | here => rfl
    | there v => cases v <;> rfl

def formula_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: .set :: Δ) :=
  transpose_m <| _root_.YesMetaZFC.Automation.TotalizedGraph.formula
    (transpose_m (φ.substitute extension_m))
    (.equal (.fvar .here) (.fvar (.there (.there .here))))

theorem formula_l {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (d x y : carrier_l 𝒱) :
    (formula_m φ).satisfies (((η.pushFree d).pushFree y).pushFree x) ↔
      φ.satisfies ((η.pushFree y).pushFree x) ∨
        ((¬ ∃ z, φ.satisfies ((η.pushFree z).pushFree x)) ∧ y = d) := by
  rw [formula_m, transpose_l,
    _root_.YesMetaZFC.Automation.TotalizedGraph.satisfies]
  simp only [transpose_l, extension_l, Formula.satisfies, Term.eval,
    Env.pushFree_here, Env.pushFree_there]

theorem agrees_l {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (d x y : carrier_l 𝒱) (h : ∃ z, φ.satisfies ((η.pushFree z).pushFree x)) :
    (formula_m φ).satisfies (((η.pushFree d).pushFree y).pushFree x) ↔
      φ.satisfies ((η.pushFree y).pushFree x) := by
  rw [formula_l]
  exact ⟨fun hφ => hφ.elim id (fun hφ => False.elim (hφ.1 h)), Or.inl⟩

theorem fallback_l {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (d x y : carrier_l 𝒱) (h : ¬ ∃ z, φ.satisfies ((η.pushFree z).pushFree x)) :
    (formula_m φ).satisfies (((η.pushFree d).pushFree y).pushFree x) ↔ y = d := by
  rw [formula_l]
  exact ⟨fun hφ => hφ.elim (fun hφ => False.elim (h ⟨y, hφ⟩)) And.right,
    fun hφ => Or.inr ⟨h, hφ⟩⟩

theorem total_l {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (d x : carrier_l 𝒱) :
    ∃ y, (formula_m φ).satisfies (((η.pushFree d).pushFree y).pushFree x) := by
  classical
  by_cases h : ∃ y, φ.satisfies ((η.pushFree y).pushFree x)
  · obtain ⟨y, hy⟩ := h
    exact ⟨y, (formula_l φ η d x y).mpr (Or.inl hy)⟩
  · exact ⟨d, (formula_l φ η d x d).mpr (Or.inr ⟨h, rfl⟩)⟩

#print axioms formula_l
#print axioms agrees_l
#print axioms fallback_l
#print axioms total_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceWitnessTotalization
