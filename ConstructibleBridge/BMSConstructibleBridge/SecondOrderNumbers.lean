import BMSConstructibleBridge.SecondOrderModel

/-!
# 任意二阶算术模型中的加法

所有归纳都提供真实纯算术公式及其环境，不能对模型数域使用宿主自然数归纳。
这组全域运算规律用于后续有限图编码的对象总性和函数性核验。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderNumbers

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

private def succ {Γ Δ : SortContext signature_m} (s : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num := Term.app (σ := signature_m) .succ (.cons s .nil)

private def add {Γ Δ : SortContext signature_m} (s t : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num := Term.app (σ := signature_m) .add (.cons s (.cons t .nil))

private def v₀ {Δ : SortContext signature_m} : Term signature_m [] (.num :: Δ) .num :=
  .fvar .here

private def v₁ {Δ : SortContext signature_m} : Term signature_m [] (.num :: .num :: Δ) .num :=
  .fvar (.there .here)

private def v₂ {Δ : SortContext signature_m} :
    Term signature_m [] (.num :: .num :: .num :: Δ) .num := .fvar (.there (.there .here))

theorem zero_add_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (n : num_l ℳ) : add_l (zero_l ℳ) n = n :=
  (SecondOrderArithmetic.zero_add_m (Γ := []) (Δ := [.num]) v₀).sound hℳ
    ((Env.empty (M := ℳ)).pushFree n) (by intro φ h; cases h)

theorem succ_add_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (m n : num_l ℳ) :
    add_l (succ_l m) n = succ_l (add_l m n) := by
  let φ : Formula signature_m [] [.num, .num] := .equal (add (succ v₁) v₀) (succ (add v₁ v₀))
  apply induct_l hℳ φ rfl ((Env.empty (M := ℳ)).pushFree m)
    (fun n => add_l (succ_l m) n = succ_l (add_l m n)) (fun _ => Iff.rfl) ?_ ?_ n
  · rw [add_zero_l hℳ, add_zero_l hℳ]
  · intro n h
    rw [add_succ_l hℳ, add_succ_l hℳ, h]

theorem add_assoc_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (m n p : num_l ℳ) :
    add_l (add_l m n) p = add_l m (add_l n p) := by
  let φ : Formula signature_m [] [.num, .num, .num] :=
    .equal (add (add v₂ v₁) v₀) (add v₂ (add v₁ v₀))
  apply induct_l hℳ φ rfl (((Env.empty (M := ℳ)).pushFree m).pushFree n)
    (fun p => add_l (add_l m n) p = add_l m (add_l n p)) (fun _ => Iff.rfl) ?_ ?_ p
  · rw [add_zero_l hℳ, add_zero_l hℳ]
  · intro p h
    rw [add_succ_l hℳ, add_succ_l hℳ, add_succ_l hℳ, h]

theorem add_comm_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (m n : num_l ℳ) : add_l m n = add_l n m := by
  let φ : Formula signature_m [] [.num, .num] := .equal (add v₁ v₀) (add v₀ v₁)
  apply induct_l hℳ φ rfl ((Env.empty (M := ℳ)).pushFree m)
    (fun n => add_l m n = add_l n m) (fun _ => Iff.rfl) ?_ ?_ n
  · rw [add_zero_l hℳ, zero_add_l hℳ]
  · intro n h
    rw [add_succ_l hℳ, succ_add_l hℳ, h]

/-- 消去任意（可能非标准的）共同左加数。 -/
theorem add_cancel_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (m n p : num_l ℳ) :
    add_l m n = add_l m p ↔ n = p := by
  let φ : Formula signature_m [] [.num, .num, .num] :=
    .iff (.equal (add v₀ v₂) (add v₀ v₁)) (.equal v₂ v₁)
  apply induct_l hℳ φ rfl (((Env.empty (M := ℳ)).pushFree n).pushFree p)
    (fun m => add_l m n = add_l m p ↔ n = p) (fun _ => Iff.rfl) ?_ ?_ m
  · rw [zero_add_l hℳ, zero_add_l hℳ]
  · intro m h
    rw [succ_add_l hℳ, succ_add_l hℳ, (injective_l hℳ).eq_iff, h]

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderNumbers
