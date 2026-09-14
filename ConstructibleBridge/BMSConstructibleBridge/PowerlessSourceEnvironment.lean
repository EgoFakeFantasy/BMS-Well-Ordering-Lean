import BMSConstructibleBridge.PowerlessMemberStructure

/-!
# 源变量槽与实际有限赋值的对应

ξ 是变量槽环境，η 是成员结构中的实际环境；二者使用同一上游语法。
更新只要求新槽不同于全部旧槽；旧槽有界是这一条件的充分特例。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceEnvironment

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}

def bounded_l (ξ : Env ℳ Γ Δ) (k : carrier_l ℳ) : Prop :=
  ∀ t : Term ℒ Γ Δ .set, member_l ℳ (t.eval ξ) k

def represents_l {A : carrier_l ℳ} {hA : ∃ a, member_l ℳ a A}
    (ξ : Env ℳ Γ Δ) (η : Env (structure_l A hA) Γ Δ) (f : carrier_l ℳ) : Prop :=
  ∀ t : Term ℒ Γ Δ .set, value_l f (t.eval ξ) (t.eval η).val

theorem natural_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω k : carrier_l ℳ} (hω : omega_l ω) (hk : member_l ℳ k ω)
    {ξ : Env ℳ Γ Δ} (hξ : bounded_l ξ k) (t : Term ℒ Γ Δ .set) : member_l ℳ (t.eval ξ) ω :=
  PowerlessNaturalOrder.subset_l hℳ hω k hk _ (hξ t)

theorem fresh_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {k : carrier_l ℳ} {ξ : Env ℳ Γ Δ} (hξ : bounded_l ξ k) (t : Term ℒ Γ Δ .set) : t.eval ξ ≠ k := by
  intro h
  have h₀ := h ▸ hξ t
  exact PowerlessNatural.asymmetry_l hℳ h₀ h₀

theorem push_l {k l : carrier_l ℳ} {ξ : Env ℳ Γ Δ}
    (hξ : bounded_l ξ k) (hl : PowerlessNatural.successor_l k l) : bounded_l (ξ.pushBound k) l := by
  intro t
  match t with
  | .bvar .here => exact (hl k).mpr (Or.inr rfl)
  | .bvar (.there v) => exact (hl _).mpr (Or.inl (hξ (.bvar v)))
  | .fvar v => exact (hl _).mpr (Or.inl (hξ (.fvar v)))
  | .app f _ => nomatch f

theorem update_l {A : carrier_l ℳ} {hA : ∃ a, member_l ℳ a A}
    {ξ : Env ℳ Γ Δ} {η : Env (structure_l A hA) Γ Δ} {k f g : carrier_l ℳ}
    (hξ : ∀ t : Term ℒ Γ Δ .set, t.eval ξ ≠ k) (hη : represents_l ξ η f) (a : type_l A)
    (hg : PowerlessAssignmentUpdate.update_l f k a.val g) :
    represents_l (ξ.pushBound k) (η.pushBound a) g := by
  intro t
  match t with
  | .bvar .here => exact PowerlessAssignmentUpdate.at_l hg
  | .bvar (.there v) =>
      exact (PowerlessAssignmentUpdate.away_l hg (hξ (.bvar v))).mpr (hη (.bvar v))
  | .fvar v =>
      exact (PowerlessAssignmentUpdate.away_l hg (hξ (.fvar v))).mpr (hη (.fvar v))
  | .app q _ => nomatch q

theorem empty_l {A : carrier_l ℳ} {hA : ∃ a, member_l ℳ a A} (f : carrier_l ℳ) :
    represents_l (Env.empty : Env ℳ [] []) (Env.empty : Env (structure_l A hA) [] []) f := by
  intro t
  match t with
  | .bvar v => nomatch v
  | .fvar v => nomatch v
  | .app q _ => nomatch q

theorem equal_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A m f : carrier_l ℳ} {hA : ∃ a, member_l ℳ a A} {ξ : Env ℳ Γ Δ}
    {η : Env (structure_l A hA) Γ Δ} (hf : map_l f m A) (hη : represents_l ξ η f) (s t : Term ℒ Γ Δ .set) :
    PowerlessEvaluationClause.equal_l f (s.eval ξ) (t.eval ξ) ↔ s.eval η = t.eval η :=
  (PowerlessEvaluationAtoms.equal_l hℳ hf (hη s) (hη t)).trans
    ⟨Subtype.ext, fun h => congrArg Subtype.val h⟩

theorem member_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A m f : carrier_l ℳ} {hA : ∃ a, ThirdOrderSemantics.member_l ℳ a A} {ξ : Env ℳ Γ Δ}
    {η : Env (structure_l A hA) Γ Δ} (hf : map_l f m A) (hη : represents_l ξ η f) (s t : Term ℒ Γ Δ .set) :
    PowerlessEvaluationClause.member_l f (s.eval ξ) (t.eval ξ) ↔
      Formula.satisfies η (.rel .membership (.cons s (.cons t .nil))) :=
  PowerlessEvaluationAtoms.member_l hℳ hf (hη s) (hη t)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceEnvironment
