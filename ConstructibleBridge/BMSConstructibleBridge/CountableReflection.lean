import Mathlib.Order.WellFounded
import BMSConstructibleBridge.SecondOrderPresentation
import YesMetaZFC.BMS.ExpansionReflectionInput

/-!
# 可数有限图反射背景及 BM4 良序

额外原则只谈自然数上的二元序、分层三元关系及有限图反射，不含 BM4 数组、
展开、种子表示或下降性。以下证明从该原则构造各高度的三个标签和局部下降，
最后接到原严格良序与二阶目标句。

这不是 `Z₂` 中该原则的存在性证明。其与可数模型存在原则的强度比较在研究
文档中单独核验；不能由本文件的标准公理审计推出等一致性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.CountableReflection

open StabilityFrame

set_option autoImplicit false

/-- 自然数上的反射系统；公理只涉及关系及其有限图。 -/
structure system_l where
  F : StabilityFrame Nat
  trans : ∀ {α β γ}, F.lt α β → F.lt β γ → F.lt α γ
  mono : F.LevelMonotone
  stable_trans : ∀ {k α β γ}, F.stableLt k α β → F.stableLt k β γ → F.stableLt k α γ
  reflects : FiniteReflectionPrinciple F

/-- 可数有限图反射原则；没有将 BM4 良基性作为公理的一部分。 -/
def principle_l : Prop := ∃ S : system_l, ∀ k, ∃ α β, S.F.stableLt k α β

namespace system_l

variable (S : system_l)

include S

/-- 限制到一个标签以下；普通序及稳定关系均为原关系的限制。 -/
def below_l (σ : Nat) : StabilityFrame {α // S.F.lt α σ} where
  lt := fun α β => S.F.lt α.1 β.1
  stableLt := fun k α β => S.F.stableLt k α.1 β.1
  lt_wellFounded := InvImage.wf Subtype.val S.F.lt_wellFounded
  stableLt_lt := S.F.stableLt_lt

/-- 有限图反射在向下封闭的标签区间上保持成立。 -/
theorem reflects_below_l (σ : Nat) : FiniteReflectionPrinciple (S.below_l σ) := by
  intro n m I
  let J : FiniteReflectionInput S.F n m := {
    level := I.level
    stabilityCutoff := I.stabilityCutoff
    lowerBound := I.lowerBound.1
    upperBound := I.upperBound.1
    lower := fun i => (I.lower i).1
    upper := fun i => (I.upper i).1
    lowerBound_stableLt_upperBound := I.lowerBound_stableLt_upperBound
    lower_lt_lowerBound := I.lower_lt_lowerBound
    lowerBound_le_upper := fun i => (I.lowerBound_le_upper i).imp id (congrArg Subtype.val)
    upper_lt_upperBound := I.upper_lt_upperBound
    lower_stableLt_below_cutoff := I.lower_stableLt_below_cutoff
    upper_stableLt_below_cutoff := I.upper_stableLt_below_cutoff }
  rcases S.reflects J with ⟨p⟩
  exact ⟨{
    image := fun i => ⟨p.image i, S.trans (p.image_lt_lowerBound i) I.lowerBound.2⟩
    lower_lt_image := p.lower_lt_image
    image_lt_lowerBound := p.image_lt_lowerBound
    preserves_lower_stableLt := p.preserves_lower_stableLt
    preserves_upper_lt := p.preserves_upper_lt
    preserves_upper_stableLt := p.preserves_upper_stableLt
    reflects_to_lowerBound := p.reflects_to_lowerBound }⟩

/-- 第 `n` 层稳定下端点在给定良基序中的一个极小元。 -/
noncomputable def boundary_l {n : Nat} (h : ∃ α β, S.F.stableLt n α β) : Nat :=
  S.F.lt_wellFounded.min {α | ∃ β, S.F.stableLt n α β} h

theorem boundary_pair_l {n : Nat} (h : ∃ α β, S.F.stableLt n α β) :
    ∃ β, S.F.stableLt n (S.boundary_l h) β := S.F.lt_wellFounded.min_mem _ h

/-- 极小边界以下的真稳定层号都严格小于边界层号。 -/
theorem cutoff_l {n k α β : Nat} {p : ∃ α β, S.F.stableLt n α β}
    (h : S.F.lt α (S.boundary_l p))
    (h₀ : S.F.stableLt k α β) : k < n := by
  by_contra h₁
  have h₂ : ∃ γ, S.F.stableLt n α γ := ⟨β, S.mono (Nat.le_of_not_gt h₁) h₀⟩
  exact S.F.lt_wellFounded.not_lt_min _ h₂ h

theorem support_l {n : Nat} (h : ∃ α β, S.F.stableLt n α β) :
    (S.below_l (S.boundary_l h)).FiniteLevelSupport :=
  fun α _ => ⟨n, fun _ h => S.cutoff_l α.2 h⟩

/-- 单点反射从有限图公理直接推出，不使用可构造层或序数语义。 -/
theorem singleton_l {n k c α β : Nat} (s : Fin c → Nat)
    (h : S.F.stableLt n α β) (h₀ : ∀ i, S.F.lt (s i) α)
    (h₁ : ∀ i j, S.F.stableLt j (s i) α → j < k) :
    ∃ γ, (∀ i, S.F.lt (s i) γ) ∧ S.F.lt γ α ∧
      (∀ i j, S.F.stableLt j (s i) α → S.F.stableLt j (s i) γ) ∧
      ∀ j < n, S.F.stableLt j γ α := by
  let I : FiniteReflectionInput S.F c 1 := {
    level := n
    stabilityCutoff := k
    lowerBound := α
    upperBound := β
    lower := s
    upper := fun _ => α
    lowerBound_stableLt_upperBound := h
    lower_lt_lowerBound := h₀
    lowerBound_le_upper := fun _ => Or.inr rfl
    upper_lt_upperBound := fun _ => S.F.stableLt_lt h
    lower_stableLt_below_cutoff := fun i _ j h₂ => h₁ i j h₂
    upper_stableLt_below_cutoff := fun _ _ _ h₂ =>
      (S.F.lt_wellFounded.irrefl.irrefl α (S.F.stableLt_lt h₂)).elim }
  rcases S.reflects I with ⟨p⟩
  exact ⟨p.image 0, fun i => p.lower_lt_image i 0, p.image_lt_lowerBound 0,
    fun i j h₂ => p.preserves_lower_stableLt (lowerIndex := i) (upperIndex := 0) h₂,
    fun j h₂ => p.reflects_to_lowerBound (upperIndex := 0) h₂
      (S.mono (Nat.le_of_lt h₂) h)⟩

/-- 三次单点反射构造原高度 `h` 所需的实际三个标签。 -/
theorem seed_l (h : Nat) (p : ∃ α β, S.F.stableLt (h + 3) α β) :
    Nonempty (SeedStabilityData (S.below_l (S.boundary_l p)) h) := by
  let σ := S.boundary_l p
  obtain ⟨β, hβ⟩ := S.boundary_pair_l p
  have h₁ := S.singleton_l (k := 0) (fun i : Fin 0 => Fin.elim0 i) hβ
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  obtain ⟨α, _, hα, _, h₁⟩ := h₁
  have h₂ := S.singleton_l (k := h + 3) (fun _ : Fin 1 => α)
    (S.mono (show h + 2 ≤ h + 3 by omega) hβ) (fun _ => hα)
    (fun _ _ h₂ => S.cutoff_l hα h₂)
  obtain ⟨γ, h₂, hγ, h₃, _⟩ := h₂
  have h₄ := S.singleton_l (k := h + 3) (fun i : Fin 2 => if i.1 = 0 then α else γ)
    (S.mono (show h + 1 ≤ h + 3 by omega) hβ)
    (by intro i; split <;> assumption)
    (by intro i j h₄; apply S.cutoff_l (p := p) (β := σ) (k := j) _ h₄; split <;> assumption)
  obtain ⟨δ, h₄, hδ, _, _⟩ := h₄
  exact ⟨{
    lower := ⟨α, hα⟩
    upper := ⟨γ, hγ⟩
    bound := ⟨δ, hδ⟩
    lower_lt_upper := h₂ 0
    upper_lt_bound := h₄ 1
    lower_stableLt_upper := fun k hk => h₃ 0 k (h₁ k (by omega)) }⟩

/-- 每个种子的可达性由关系原则推出，不再是背景的字段。 -/
theorem seed_acc_l (n : Nat) (q : ∃ α β, S.F.stableLt (n + 3) α β) :
    Acc Step (validSeed n) := by
  rcases S.seed_l n q with ⟨p⟩
  have h : LocalDescent.expands_l (S.below_l (S.boundary_l q)) :=
    ExpansionReflectionState.expand_bounded (S.reflects_below_l _)
      (S.support_l _) (fun h₁ h₂ => S.trans h₁ h₂) S.stable_trans
  exact LocalDescent.acc_l h p.representation
    (p.representation_boundedBy (fun h₁ h₂ => S.trans h₁ h₂))

/-- 纯可数有限图反射系统蕴含原 BM4 生成关系良基。 -/
theorem wf_l (h : ∀ n, ∃ α β, S.F.stableLt n α β) : WellFounded GeneratedStep :=
  LocalDescent.wf_l (fun n => S.seed_acc_l n (h (n + 3)))

end system_l

/-- 在明确增加可数有限图反射原则的背景下，得到原严格良序结论。 -/
theorem wellOrder_l (h : principle_l) :
    StrictWellOrder GeneratedArray GeneratedStrictDescent := by
  rcases h with ⟨S, h⟩
  exact LocalDescent.wellOrder_of_wf_l (S.wf_l h)

/-- 同一背景也推出实际自然数集合呈现的原始无下降链句。 -/
theorem sentence_l (h : principle_l) : SecondOrderPresentation.sentence_l := by
  rcases h with ⟨S, h⟩
  exact SecondOrderPresentation.sentence_iff_l.mpr (LocalDescent.no_descent_of_wf_l (S.wf_l h))

end YesMetaZFC.BMS.ConstructibleBridge.CountableReflection
