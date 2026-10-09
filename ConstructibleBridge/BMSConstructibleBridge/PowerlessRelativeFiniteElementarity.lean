import BMSConstructibleBridge.PowerlessRelativeParameters
import BMSConstructibleBridge.PowerlessSourcePredicateRequests

/-! # 实际成员子域的有限元素性对象公式

对象语言是纯隶属 ℒ。每个原公式保留自己的外部绑定上下文，原自由参数
经指定 τ 代入；I 与 W 只作域参数，不要求它们是任一成员结构中的元素。
原量词逐个用隶属 I 守卫闭合，再对外部有限原公式族作合取。
请求闭包由实际 MemberI→MemberW 反射回接这两侧对象公式。
本模块给装配语义桥，不把闭包前提或对象 AST 的存在冒充最终 Z₂ 推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteElementarity

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

abbrev family_m (Δ : SortContext ℒ) := List (Σ Γ : SortContext ℒ, Formula ℒ Γ Δ)

private def lift_m {Γ Ε : SortContext ℒ} (t : Term ℒ [] Ε .set) : Term ℒ Γ Ε .set :=
  match t with
  | .bvar v => nomatch v
  | .fvar v => .fvar v
  | .app f _ => nomatch f

private theorem eval_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Ε : SortContext ℒ} (t : Term ℒ [] Ε .set) (ξ : Env ℳ Γ Ε) (ζ : Env ℳ [] Ε)
    (h : ∀ s (v : Variable Ε s), ξ.freeVal v = ζ.freeVal v) :
    (lift_m t).eval ξ = t.eval ζ := by
  match t with
  | .bvar v => nomatch v
  | .fvar v => exact h _ v
  | .app f _ => nomatch f

private def binding_m {Γ Δ Ε : SortContext ℒ} (A : Term ℒ [] Ε .set)
    (τ : Variable Δ .set → Term ℒ [] Ε .set) : Substitution ℒ Γ (.set :: Δ) Γ Ε :=
  .map (fun v => .bvar v) (fun {s} v => match s with
    | .set => match v with
      | .here => lift_m A
      | .there v => lift_m (τ v))

private def instance_m {Γ Δ Ε : SortContext ℒ} (φ : Formula ℒ Γ Δ)
    (A : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) : Formula ℒ Γ Ε :=
  (PowerlessRelativization.formula_m φ).substitute (binding_m A τ)

private theorem instance_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {A₀ : carrier_l ℳ} {hA : ∃ x, ThirdOrderSemantics.member_l ℳ x A₀}
    {Γ Δ Ε : SortContext ℒ} (φ : Formula ℒ Γ Δ) (ξ : Env ℳ Γ Ε)
    (A : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (η : Env (structure_l A₀ hA) Γ Δ)
    (ha : (lift_m A).eval ξ = A₀)
    (hb : ∀ v : Variable Γ .set, ξ.boundVal v = (η.boundVal v).val)
    (hτ : ∀ v, (lift_m (τ v)).eval ξ = (η.freeVal v).val) :
    (instance_m φ A τ).satisfies ξ ↔ φ.satisfies η := by
  rw [instance_m, Formula.satisfies_substitute]
  have hξ : ξ.pullback (binding_m A τ) = (PowerlessRelativization.env_l η).pushFree A₀ := by
    apply Env.ext
    · intro s v
      cases s
      exact hb v
    · intro s v
      cases s
      cases v with
      | here => exact ha
      | there v => exact hτ v
  rw [hξ]
  exact PowerlessRelativization.formula_l φ η

private def quantify_m {Ε : SortContext ℒ} (I : Term ℒ [] Ε .set) :
    {Γ : SortContext ℒ} → Formula ℒ Γ Ε → Formula ℒ [] Ε
  | List.nil, φ => φ
  | List.cons .set _, φ => quantify_m I (.forallE .set (.imp
      (SecondOrderObjectSyntax.member_m (.bvar .here) (lift_m I)) φ))

private theorem quantify_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Ε : SortContext ℒ} (I : Term ℒ [] Ε .set) (φ : Formula ℒ Γ Ε) (ζ : Env ℳ [] Ε) :
    (quantify_m I φ).satisfies ζ ↔ ∀ ξ : Env ℳ Γ Ε,
      (∀ s (v : Variable Ε s), ξ.freeVal v = ζ.freeVal v) →
      (∀ v : Variable Γ .set, ThirdOrderSemantics.member_l ℳ (ξ.boundVal v) (I.eval ζ)) →
      φ.satisfies ξ := by
  induction Γ with
  | nil =>
    rw [quantify_m]
    constructor
    · intro h ξ hξ _
      have hη : ξ = ζ := by
        apply Env.ext
        · intro s v; nomatch v
        · intro s v; exact hξ s v
      simpa only [hη] using h
    · intro h
      exact h ζ (fun _ _ => rfl) (fun v => nomatch v)
  | cons s Γ ih =>
    cases s
    rw [quantify_m, ih]
    constructor
    · intro h ξ hξ hBound
      let ξ₀ := PowerlessSourceOpening.tail_l ξ
      have h₀ := h ξ₀ hξ (fun v => hBound (.there v))
      change ∀ x, ThirdOrderSemantics.member_l ℳ x ((lift_m I).eval (ξ₀.pushBound x)) →
        φ.satisfies (ξ₀.pushBound x) at h₀
      have hx : ThirdOrderSemantics.member_l ℳ (ξ.boundVal .here)
          ((lift_m I).eval (ξ₀.pushBound (ξ.boundVal .here))) := by
        rw [eval_l I (ξ₀.pushBound (ξ.boundVal .here)) ζ (fun s v => hξ s v)]
        exact hBound .here
      have hη : ξ₀.pushBound (ξ.boundVal .here) = ξ := by
        apply Env.ext
        · intro t v; cases v <;> rfl
        · intro t v; rfl
      simpa only [hη] using h₀ (ξ.boundVal .here) hx
    · intro h ξ hξ hBound
      change ∀ x, ThirdOrderSemantics.member_l ℳ x ((lift_m I).eval (ξ.pushBound x)) →
        φ.satisfies (ξ.pushBound x)
      intro x hx
      have hxI : ThirdOrderSemantics.member_l ℳ x (I.eval ζ) := by
        rw [eval_l I (ξ.pushBound x) ζ (fun s v => hξ s v)] at hx
        exact hx
      exact h (ξ.pushBound x) hξ (fun v => by
        cases v with
        | here => exact hxI
        | there v => exact hBound v)

/-- 对每个 I 内绑定赋值断言原公式在 W 与 I 中同值。 -/
def entry_m {Γ Δ Ε : SortContext ℒ} (φ : Formula ℒ Γ Δ)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) : Formula ℒ [] Ε :=
  quantify_m I (.iff (instance_m φ W τ) (instance_m φ I τ))

def form_m {Δ Ε : SortContext ℒ} (Φ : family_m Δ)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) : Formula ℒ [] Ε :=
  match Φ with
  | [] => .truth
  | p :: Φ => .conj (entry_m p.2 I W τ) (form_m Φ I W τ)

/-- 合并原有限公式族，精确保留两侧同一域上的元素性合取。 -/
theorem append_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ Ε : SortContext ℒ} (Φ Ψ : family_m Δ) (ζ : Env 𝒩 [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) :
    (form_m (Φ ++ Ψ) I W τ).satisfies ζ ↔
      (form_m Φ I W τ).satisfies ζ ∧ (form_m Ψ I W τ).satisfies ζ := by
  induction Φ with
  | nil => simp only [List.nil_append, form_m, Formula.satisfies, true_and]
  | cons p Φ ih => simp only [List.cons_append, form_m, Formula.satisfies, ih, and_assoc]

private theorem member_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ Ε : SortContext ℒ} (p : Σ Γ : SortContext ℒ, Formula ℒ Γ Δ) (Φ : family_m Δ)
    (hp : p ∈ Φ) (ζ : Env 𝒩 [] Ε) (I W : Term ℒ [] Ε .set)
    (τ : Variable Δ .set → Term ℒ [] Ε .set) (h : (form_m Φ I W τ).satisfies ζ) :
    (entry_m p.2 I W τ).satisfies ζ := by
  induction Φ with
  | nil => simp only [List.not_mem_nil] at hp
  | cons q Φ ih =>
    change (entry_m q.2 I W τ).satisfies ζ ∧ (form_m Φ I W τ).satisfies ζ at h
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h.1
    · exact ih hp h.2

/-- 从同一共同族读取任意实际子族，不另外假设子族的元素性。 -/
theorem subfamily_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ Ε : SortContext ℒ} (Ψ Φ : family_m Δ) (hΨ : ∀ p ∈ Ψ, p ∈ Φ)
    (ζ : Env 𝒩 [] Ε) (I W : Term ℒ [] Ε .set)
    (τ : Variable Δ .set → Term ℒ [] Ε .set) (h : (form_m Φ I W τ).satisfies ζ) :
    (form_m Ψ I W τ).satisfies ζ := by
  induction Ψ with
  | nil => trivial
  | cons p Ψ ih =>
    exact ⟨member_formula_l p Φ (hΨ p (by simp)) ζ I W τ h,
      ih (fun q hq => hΨ q (List.mem_cons_of_mem _ hq))⟩


/-- 不要求成员域传递：相对化公式直接读取原环境中的同一赋值。 -/
private theorem instance_raw_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ Ε : SortContext ℒ} (φ : Formula ℒ Γ Δ) (ξ : Env ℳ Γ Ε)
    (A : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (η : Env ℳ Γ Δ) (A₀ : carrier_l ℳ)
    (ha : (lift_m A).eval ξ = A₀)
    (hb : ∀ v : Variable Γ .set, ξ.boundVal v = η.boundVal v)
    (hτ : ∀ v, (lift_m (τ v)).eval ξ = η.freeVal v) :
    (instance_m φ A τ).satisfies ξ ↔
      (PowerlessRelativization.formula_m φ).satisfies (η.pushFree A₀) := by
  rw [instance_m, Formula.satisfies_substitute]
  have hξ : ξ.pullback (binding_m A τ) = η.pushFree A₀ := by
    apply Env.ext
    · intro s v
      cases s
      exact hb v
    · intro s v
      cases s
      cases v with
      | here => exact ha
      | there v => exact hτ v
  rw [hξ]

/-- 公开读取原绑定槽的两侧相对化真值；域对象不须属于自身。 -/
theorem entry_formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ Ε : SortContext ℒ} (φ : Formula ℒ Γ Δ) (ζ : Env ℳ [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (ν : Env ℳ [] Δ) (hτ : ∀ v, (τ v).eval ζ = ν.freeVal v) :
    (entry_m φ I W τ).satisfies ζ ↔ ∀ η : Env ℳ Γ Δ,
      (∀ s (v : Variable Δ s), η.freeVal v = ν.freeVal v) →
      (∀ v : Variable Γ .set, member_l ℳ (η.boundVal v) (I.eval ζ)) →
      ((PowerlessRelativization.formula_m φ).satisfies (η.pushFree (W.eval ζ)) ↔
        (PowerlessRelativization.formula_m φ).satisfies (η.pushFree (I.eval ζ))) := by
  rw [entry_m, quantify_l]
  constructor
  · intro h η hFree hBound
    let ξ : Env ℳ Γ Ε := { boundVal := η.boundVal, freeVal := ζ.freeVal }
    have h₀ := h ξ (fun _ _ => rfl) hBound
    have hRead (A : Term ℒ [] Ε .set) := instance_raw_l φ ξ A τ η (A.eval ζ)
      (eval_l A ξ ζ (fun _ _ => rfl)) (fun _ => rfl)
      (fun v => (eval_l (τ v) ξ ζ (fun _ _ => rfl)).trans
        ((hτ v).trans (hFree _ v).symm))
    exact (hRead W).symm.trans (h₀.trans (hRead I))
  · intro h ξ hFree hBound
    let η : Env ℳ Γ Δ := { boundVal := ξ.boundVal, freeVal := ν.freeVal }
    have h₀ := h η (fun _ _ => rfl) hBound
    have hRead (A : Term ℒ [] Ε .set) := instance_raw_l φ ξ A τ η (A.eval ζ)
      (eval_l A ξ ζ hFree) (fun _ => rfl)
      (fun v => (eval_l (τ v) ξ ζ hFree).trans (hτ v))
    exact (hRead W).trans (h₀.trans (hRead I).symm)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {I₀ W₀ : carrier_l ℳ} {hI : ∃ x, ThirdOrderSemantics.member_l ℳ x I₀}
  {hW : ∃ x, ThirdOrderSemantics.member_l ℳ x W₀}

local notation "𝒩" => structure_l (ℳ := ℳ) I₀ hI
local notation "𝒲" => structure_l (ℳ := ℳ) W₀ hW

theorem entry_l {Γ Δ Ε : SortContext ℒ} (φ : Formula ℒ Γ Δ) (ζ : Env ℳ [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (η : Env 𝒩 [] Δ) (hIW : subset_l I₀ W₀)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hτ : ∀ v, (τ v).eval ζ = (η.freeVal v).val)
    (h : PowerlessSourcePredicateRequests.closed_l (PowerlessSourceRequests.requests_m .truth φ)
      (PowerlessSourceClass.free_l (PowerlessSourceInclusion.env_l (hU := hW) hIW η))
      (fun x : type_l W₀ => ThirdOrderSemantics.member_l ℳ x.val I₀)) :
    (entry_m φ I W τ).satisfies ζ := by
  apply (quantify_l I _ ζ).mpr
  intro ξ hξ hBound
  let ξ₀ : Env 𝒩 Γ Δ :=
    { boundVal := fun {s} v => match s with
        | .set => ⟨ξ.boundVal v, by rw [← hI₀]; exact hBound v⟩
      freeVal := η.freeVal }
  have hFree : PowerlessSourceClass.free_l (PowerlessSourceInclusion.env_l (hU := hW) hIW ξ₀) =
      PowerlessSourceClass.free_l (PowerlessSourceInclusion.env_l (hU := hW) hIW η) := by
    apply Env.ext
    · intro s v; nomatch v
    · intro s v; rfl
  have h₀ : PowerlessSourcePredicateRequests.closed_l
      (PowerlessSourceRequests.requests_m .truth φ)
      (PowerlessSourceClass.free_l (PowerlessSourceInclusion.env_l (hU := hW) hIW ξ₀))
      (fun x : type_l W₀ => ThirdOrderSemantics.member_l ℳ x.val I₀) := by
    simpa only [hFree] using h
  have hφ := PowerlessSourcePredicateRequests.member_l hIW φ ξ₀ h₀
  have hWφ := instance_l φ ξ W τ (PowerlessSourceInclusion.env_l (hU := hW) hIW ξ₀)
    ((eval_l W ξ ζ hξ).trans hW₀) (fun _ => rfl)
    (fun v => (eval_l (τ v) ξ ζ hξ).trans (hτ v))
  have hIφ := instance_l φ ξ I τ ξ₀ ((eval_l I ξ ζ hξ).trans hI₀) (fun _ => rfl)
    (fun v => (eval_l (τ v) ξ ζ hξ).trans (hτ v))
  exact (hWφ.trans hφ).trans hIφ.symm

/-- 同一 I 的全部原请求闭包反射外部有限原公式族。 -/
theorem formula_l {Δ Ε : SortContext ℒ} (Φ : family_m Δ) (ζ : Env ℳ [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (η : Env 𝒩 [] Δ) (hIW : subset_l I₀ W₀)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hτ : ∀ v, (τ v).eval ζ = (η.freeVal v).val)
    (h : ∀ p ∈ Φ, PowerlessSourcePredicateRequests.closed_l
      (PowerlessSourceRequests.requests_m .truth p.2)
      (PowerlessSourceClass.free_l (PowerlessSourceInclusion.env_l (hU := hW) hIW η))
      (fun x : type_l W₀ => ThirdOrderSemantics.member_l ℳ x.val I₀)) :
    (form_m Φ I W τ).satisfies ζ := by
  induction Φ with
  | nil => trivial
  | cons p Φ ih =>
    exact ⟨entry_l p.2 ζ I W τ η hIW hI₀ hW₀ hτ (h p (by simp)),
      ih (fun q hq => h q (List.mem_cons_of_mem _ hq))⟩

#print axioms entry_l
#print axioms append_formula_l
#print axioms subfamily_formula_l
#print axioms entry_formula_l
#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteElementarity
