import BMSConstructibleBridge.PowerlessSourcePack

/-!
# 外部有限元数的原公式请求编码

使用既有 Values 值列，对外部固定元数递归合并两个输入。
零输入使用给定的层内缺省码；递归不假定模型的 ω 外部标准。
编码忠实性逐次消费有序对坐标唯一性，输出见证与尾部参数不变。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceTuple

open Logic FirstOrder ThirdOrderSemantics PowerlessHierarchyStage

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def env_l {Γ : SortContext ℒ} (η : Env ℳ [] Γ) :
    (n : Nat) → Values ℳ.Carrier (List.replicate n .set) →
      Env ℳ [] (List.replicate n .set ++ Γ)
  | 0, .nil => η
  | n + 1, .cons x v => (env_l η n v).pushFree x

def bounded_l (A : carrier_l ℳ) :
    (n : Nat) → Values ℳ.Carrier (List.replicate n .set) → Prop
  | 0, .nil => True
  | n + 1, .cons x v => member_l ℳ x A ∧ bounded_l A n v

def code_l (e : carrier_l ℳ) :
    (n : Nat) → Values ℳ.Carrier (List.replicate n .set) → carrier_l ℳ → Prop
  | 0, .nil, p => p = e
  | 1, .cons x .nil, p => p = x
  | n + 2, .cons x (.cons z v), p => ∃ q, ordered_l x z q ∧ code_l e (n + 1) (.cons q v) p

def empty_binding_m {Γ : SortContext ℒ} :
    Substitution ℒ [] (.set :: Γ) [] (.set :: .set :: Γ) :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => .fvar .here
    | .there v => .fvar (.there (.there v)))

theorem empty_formula_l {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Γ))
    (η : Env ℳ [] Γ) (p y : carrier_l ℳ) :
    (φ.substitute empty_binding_m).satisfies ((η.pushFree p).pushFree y) ↔
      φ.satisfies (η.pushFree y) := by
  rw [Formula.satisfies_substitute]
  apply Iff.of_eq
  congr 1
  apply Env.ext
  · intro _ v
    nomatch v
  · intro s v
    cases v <;> rfl

def form_m {Γ : SortContext ℒ} :
    (n : Nat) → Formula ℒ [] (.set :: (List.replicate n .set ++ Γ)) →
      Formula ℒ [] (.set :: .set :: Γ)
  | 0, φ => φ.substitute empty_binding_m
  | 1, φ => φ
  | n + 2, φ => form_m (n + 1) (PowerlessSourcePack.pair_m φ)

theorem code_exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (A e : carrier_l ℳ) (he : member_l ℳ e A)
    (hA : ∀ a b p, member_l ℳ a A → member_l ℳ b A → ordered_l a b p → member_l ℳ p A)
    (n : Nat) (v : Values ℳ.Carrier (List.replicate n .set)) (hv : bounded_l A n v) :
    ∃ p, member_l ℳ p A ∧ code_l e n v p := by
  match n, v with
  | 0, .nil => exact ⟨e, he, rfl⟩
  | 1, .cons x .nil => exact ⟨x, hv.1, rfl⟩
  | n + 2, .cons x (.cons z v) =>
    obtain ⟨q, hq⟩ := PowerlessBasic.ordered_exists_l hℳ x z
    obtain ⟨p, hp, h⟩ := code_exists_l hℳ A e he hA (n + 1) (.cons q v)
      ⟨hA x z q hv.1 hv.2.1 hq, hv.2.2⟩
    exact ⟨p, hp, q, hq, h⟩

theorem formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (η : Env ℳ [] Γ) (n : Nat)
    (φ : Formula ℒ [] (.set :: (List.replicate n .set ++ Γ)))
    (v : Values ℳ.Carrier (List.replicate n .set)) {e p : carrier_l ℳ}
    (hp : code_l e n v p) (y : carrier_l ℳ) :
    (form_m n φ).satisfies ((η.pushFree p).pushFree y) ↔
      φ.satisfies ((env_l η n v).pushFree y) := by
  match n, v with
  | 0, .nil => exact empty_formula_l φ η p y
  | 1, .cons x .nil =>
    change p = x at hp
    subst p
    rfl
  | n + 2, .cons x (.cons z v) =>
    obtain ⟨q, hq, hp⟩ := hp
    exact (formula_l hℳ η (n + 1) (PowerlessSourcePack.pair_m φ) (.cons q v) hp y).trans
      (PowerlessSourcePack.pair_l hℳ φ (env_l η n v) hq y)

theorem closure_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (η : Env ℳ [] Γ) (n : Nat)
    (φ : Formula ℒ [] (.set :: (List.replicate n .set ++ Γ)))
    (P : carrier_l ℳ → Prop) (A e : carrier_l ℳ) (he : member_l ℳ e A)
    (hA : ∀ a b p, member_l ℳ a A → member_l ℳ b A → ordered_l a b p → member_l ℳ p A)
    (h : ∀ p, member_l ℳ p A →
      (∃ y, P y ∧ (form_m n φ).satisfies ((η.pushFree p).pushFree y)) →
        ∃ y, member_l ℳ y A ∧ (form_m n φ).satisfies ((η.pushFree p).pushFree y)) :
    ∀ v, bounded_l A n v →
      (∃ y, P y ∧ φ.satisfies ((env_l η n v).pushFree y)) →
        ∃ y, member_l ℳ y A ∧ φ.satisfies ((env_l η n v).pushFree y) := by
  rintro v hv ⟨y, hy, hφ⟩
  obtain ⟨p, hp, hC⟩ := code_exists_l hℳ A e he hA n v hv
  obtain ⟨z, hz, hψ⟩ := h p hp ⟨y, hy, (formula_l hℳ η n φ v hC y).mpr hφ⟩
  exact ⟨z, hz, (formula_l hℳ η n φ v hC z).mp hψ⟩

/-- 任意外部固定有限元数的层次内见证具有更高的实际闭包层。 -/
theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (n : Nat)
    (φ : Formula ℒ [] (.set :: (List.replicate n .set ++ Γ)))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (ω e T t₁ t₂ t₃ : Term ℒ [] Γ .set) (α : carrier_l ℳ)
    (hω : omega_l (ω.eval (PowerlessComprehension.env_l η)))
    (ht : PowerlessEvaluationTags.tags_l (e.eval (PowerlessComprehension.env_l η))
      (t₁.eval (PowerlessComprehension.env_l η)) (t₂.eval (PowerlessComprehension.env_l η))
      (t₃.eval (PowerlessComprehension.env_l η)))
    (hT : PowerlessTriangular.triangular_l (ω.eval (PowerlessComprehension.env_l η))
      (e.eval (PowerlessComprehension.env_l η)) (T.eval (PowerlessComprehension.env_l η)))
    (hα : PowerlessOrdinal.ordinal_l α) :
    ∃ δ U, PowerlessStagePair.limit_l δ ∧ member_l ℳ α δ ∧
      stage_l (ω.eval (PowerlessComprehension.env_l η)) (e.eval (PowerlessComprehension.env_l η))
        (T.eval (PowerlessComprehension.env_l η)) (t₁.eval (PowerlessComprehension.env_l η))
        (t₂.eval (PowerlessComprehension.env_l η)) (t₃.eval (PowerlessComprehension.env_l η)) δ U ∧
      ∀ v, bounded_l U n v →
        (∃ y, PowerlessSourceWitnessDomain.domain_l
          (ω.eval (PowerlessComprehension.env_l η)) (e.eval (PowerlessComprehension.env_l η))
          (T.eval (PowerlessComprehension.env_l η)) (t₁.eval (PowerlessComprehension.env_l η))
          (t₂.eval (PowerlessComprehension.env_l η)) (t₃.eval (PowerlessComprehension.env_l η)) y ∧
          φ.satisfies ((env_l (PowerlessComprehension.env_l η) n v).pushFree y)) →
        ∃ y, member_l ℳ y U ∧
          φ.satisfies ((env_l (PowerlessComprehension.env_l η) n v).pushFree y) := by
  let ρ := PowerlessComprehension.env_l η
  obtain ⟨δ, U, hδ, hαδ, hU, h⟩ := PowerlessSourceWitnessDomain.exists_l hℳ (form_m n φ) η
    ω e T t₁ t₂ t₃ α hω ht.1 hα
  exact ⟨δ, U, hδ, hαδ, hU, closure_l hℳ ρ n φ _ U (e.eval ρ)
    (PowerlessStageClosure.empty_l hℳ hω hU hδ ht hT ht.1)
    (fun a b p ha hb hp => PowerlessStageGraphClosure.ordered_l hℳ hω ht hT hU hδ ha hb hp) h⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceTuple
