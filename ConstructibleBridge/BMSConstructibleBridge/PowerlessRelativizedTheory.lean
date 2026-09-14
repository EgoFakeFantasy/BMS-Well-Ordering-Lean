import BMSConstructibleBridge.PowerlessRelativization
import YesMetaZFC.Logic.FirstOrder.Completeness.ProofTheoryCore

/-!
# 有限核心片段在原语言中的成员域判定

有限列表的每一原闭句都相对化到指定域，合取得到单个原 Formula。
此处只给精确语义，不将任意有限列表冒充完整核心。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativizedTheory

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

def fragment_m (Γ : List (Sentence ℒ)) : Formula ℒ [] [.set] :=
  Formula.conjunctionList (Γ.map PowerlessRelativization.formula_m)

private def bind {Δ Θ : SortContext ℒ} (A : Term ℒ Δ Θ .set) : Substitution ℒ [] [.set] Δ Θ :=
  .map (fun v => nomatch v) (fun v => match v with | .here => A)

def instance_m {Δ Θ : SortContext ℒ} (Γ : List (Sentence ℒ)) (A : Term ℒ Δ Θ .set) : Formula ℒ Δ Θ :=
  (fragment_m Γ).substitute (bind A)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {A : carrier_l ℳ} {hA : ∃ x, member_l ℳ x A}

theorem sentence_l (φ : Sentence ℒ) :
    (PowerlessRelativization.formula_m φ).satisfies ((Env.empty (M := ℳ)).pushFree A) ↔
      φ.TrueIn (structure_l A hA) := by
  have h := PowerlessRelativization.formula_l φ (Env.empty (M := structure_l A hA))
  have hη : PowerlessRelativization.env_l (Env.empty (M := structure_l A hA)) = Env.empty := by
    apply Env.ext <;> intro _ v <;> nomatch v
  simpa only [hη, Formula.TrueIn] using h

theorem fragment_l (Γ : List (Sentence ℒ)) :
    (fragment_m Γ).satisfies ((Env.empty (M := ℳ)).pushFree A) ↔
      Theory.Models (structure_l A hA) (Theory.ofList Γ) := by
  rw [fragment_m, Formula.satisfies_conjunctionList_iff]
  constructor
  · intro h φ hφ
    exact (sentence_l φ).mp (h _ (List.mem_map.mpr ⟨φ, hφ, rfl⟩))
  · intro h φ hφ
    obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hφ
    exact (sentence_l ψ).mpr (h ψ hψ)

theorem instance_l {Δ Θ : SortContext ℒ} (Γ : List (Sentence ℒ))
    (η : Env ℳ Δ Θ) (a : Term ℒ Δ Θ .set) (h : a.eval η = A) :
    (instance_m Γ a).satisfies η ↔ Theory.Models (structure_l A hA) (Theory.ofList Γ) := by
  rw [instance_m, Formula.satisfies_substitute]
  have hη : η.pullback (bind a) =
      (Env.empty (M := ℳ)).pushFree A := by
    apply Env.ext
    · intro _ v
      nomatch v
    · intro _ v
      match v with | .here => exact h
  rw [hη]
  exact fragment_l Γ

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativizedTheory
