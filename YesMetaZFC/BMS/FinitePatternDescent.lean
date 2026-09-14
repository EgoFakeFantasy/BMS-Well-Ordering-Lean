import YesMetaZFC.BMS.ExpansionReflectionInput
import YesMetaZFC.BMS.LocalDescent

/-!
# 有限行层上的实际反射输入

把稳定关系截断到给定行数后，有限支撑由定义直接成立。反射假设只处理
`ExpansionReflectionState.reflectionInput` 产生的输入，不再量化任意有限图。
表示下降仍由原有复制块证书证明，不作为新假设提供。

本模块仍使用输入框架 `StabilityFrame.lt_wellFounded` 的宿主层良基性，
也仍要求实际反射见证和种子标签存在。它没有证明这些数据能在二阶算术
中构造，也没有证明反射原则的严格证明论强度下降。
-/

namespace YesMetaZFC.BMS.StabilityFrame.FinitePatternDescent

universe u

section Frame

variable {A : Type u} {F : StabilityFrame A} {H : Nat}

/-- 仅保留低于 `H` 的稳定层；标签序及其良基性完全继承原框架。 -/
def cut_l (H : Nat) (F : StabilityFrame A) : StabilityFrame A where
  lt := F.lt
  stableLt := fun k α β => k < H ∧ F.stableLt k α β
  lt_wellFounded := F.lt_wellFounded
  stableLt_lt := fun h => F.stableLt_lt h.2

/-- 截断框架自动具有统一截断值，无需原关系的有限支撑假设。 -/
theorem support_l (H : Nat) (F : StabilityFrame A) :
    (cut_l H F).FiniteLevelSupport :=
  fun _ _ => ⟨H, fun _ h => h.1⟩

/-- 截断层内的传递性足以给出截断稳定关系的传递性。 -/
theorem stable_trans_l
    (h : ∀ {k α β γ}, k < H → F.stableLt k α β →
      F.stableLt k β γ → F.stableLt k α γ)
    {k : Nat} {α β γ : A}
    (h₁ : (cut_l H F).stableLt k α β)
    (h₂ : (cut_l H F).stableLt k β γ) :
    (cut_l H F).stableLt k α γ :=
  ⟨h₁.1, h h₁.1 h₁.2 h₂.2⟩

/-- 不超过截断高度的种子数据可直接限制稳定关系。 -/
def seed_l {n : Nat} (h : n ≤ H) (p : SeedStabilityData F n) :
    SeedStabilityData (cut_l H F) n where
  lower := p.lower
  upper := p.upper
  bound := p.bound
  lower_lt_upper := p.lower_lt_upper
  upper_lt_bound := p.upper_lt_bound
  lower_stableLt_upper := fun _ h₁ =>
    ⟨Nat.lt_of_lt_of_le h₁ h, p.lower_stableLt_upper _ h₁⟩

/-- 仅要求实际扩张状态所产生的有限输入有反射见证。 -/
def reflects_l (F : StabilityFrame A) : Prop :=
  ∀ {a : ValidArray} {C : ExpansionContext a} {i : Nat}
    {p : StableRepresentation F a} (s : ExpansionReflectionState C i p),
    Nonempty (FiniteReflectionWitness s.reflectionInput)

/-- 同一框架上的完整有限反射原则蕴含实际输入反射。 -/
theorem reflects_of_full_l (h : FiniteReflectionPrinciple F) : reflects_l F :=
  fun s => h s.reflectionInput

/--
旧模型可接入截断接口。原有限支撑只在本兼容定理中使用，以便把截断输入
提升成旧原则接受的全层输入；新的下降定理不要求这一额外假设。
-/
theorem reflects_cut_of_full_l (h : FiniteReflectionPrinciple F)
    (h₀ : F.FiniteLevelSupport) : reflects_l (cut_l H F) := by
  intro a C i p s
  let I := s.reflectionInput
  rcases exists_reflectionStabilityCutoff h₀ I.lower I.upper with ⟨k, h₁, h₂⟩
  let J : FiniteReflectionInput F (C.copyStart i) C.blockLength := {
    level := I.level
    stabilityCutoff := k
    lowerBound := I.lowerBound
    upperBound := I.upperBound
    lower := I.lower
    upper := I.upper
    lowerBound_stableLt_upperBound := I.lowerBound_stableLt_upperBound.2
    lower_lt_lowerBound := I.lower_lt_lowerBound
    lowerBound_le_upper := I.lowerBound_le_upper
    upper_lt_upperBound := I.upper_lt_upperBound
    lower_stableLt_below_cutoff := h₁
    upper_stableLt_below_cutoff := h₂ }
  rcases h J with ⟨q⟩
  refine ⟨{
    image := q.image
    lower_lt_image := q.lower_lt_image
    image_lt_lowerBound := q.image_lt_lowerBound
    preserves_upper_lt := q.preserves_upper_lt
    preserves_lower_stableLt := ?_
    preserves_upper_stableLt := ?_
    reflects_to_lowerBound := ?_ }⟩
  · intro j l m h₃
    exact ⟨h₃.1, q.preserves_lower_stableLt h₃.2⟩
  · intro j l m h₃
    exact ⟨h₃.1, q.preserves_upper_stableLt h₃.2⟩
  · intro j m h₃ h₄
    exact ⟨h₄.1, q.reflects_to_lowerBound h₃ h₄.2⟩

variable (h : reflects_l (cut_l H F))
variable (h₁ : ∀ {α β γ}, F.lt α β → F.lt β γ → F.lt α γ)
variable (h₂ : ∀ {k α β γ}, k < H → F.stableLt k α β →
  F.stableLt k β γ → F.stableLt k α γ)

include h h₁ h₂

/-- 普通自然数递归只请求当前状态的见证，不预设下降结论。 -/
noncomputable def iterated_l (h : reflects_l (cut_l H F))
    (h₁ : ∀ {α β γ}, F.lt α β → F.lt β γ → F.lt α γ)
    (h₂ : ∀ {k α β γ}, k < H → F.stableLt k α β →
      F.stableLt k β γ → F.stableLt k α γ)
    {a : ValidArray} (C : ExpansionContext a)
    (p : StableRepresentation (cut_l H F) a) :
    (i : Nat) → ExpansionReflectionState C i p
  | 0 => Classical.choice
      (ExpansionReflectionState.exists_initialState C p (support_l H F))
  | i + 1 =>
      let s := iterated_l h h₁ h₂ C p i
      let q := Classical.choice (h s)
      Classical.choice
        (s.exists_successorState q (support_l H F) h₁ (stable_trans_l h₂))

/-- 有扩张上下文时，原复制块证书把当前反射见证变为严格降界。 -/
theorem expand_context_l {a : ValidArray} (C : ExpansionContext a) (i : Nat)
    {α : A} (p : StableRepresentation (cut_l H F) a) (hα : p.BoundedBy α) :
    ∃ β, F.lt β α ∧
      ∃ q : StableRepresentation (cut_l H F) (a.expand i), q.BoundedBy β := by
  let s := iterated_l h h₁ h₂ C p i
  let q := Classical.choice (h s)
  refine ⟨s.reflectionInput.lowerBound, ?_,
    s.boundedExpansionRepresentation q h₁ (stable_trans_l h₂),
    s.boundedExpansionRepresentation_boundedBy q h₁ (stable_trans_l h₂)⟩
  have h₃ : s.current.label s.lowerBoundColumn =
      p.label (s.upperColumn ⟨0, C.blockLength_pos⟩) := by
    simpa only [ExpansionReflectionState.lowerBoundColumn,
      ExpansionReflectionState.upperColumn] using
      s.lastCopy_eq (⟨0, C.blockLength_pos⟩ : Fin C.blockLength)
  change F.lt (s.current.label s.lowerBoundColumn) α
  rw [h₃]
  exact hα _

/-- 实际有限输入反射推出完整单步表示下降，而不是将其作为字段假设。 -/
theorem expands_l : LocalDescent.expands_l (cut_l H F) := by
  intro a i α p hα h₃
  cases h₄ : a.raw.length with
  | zero =>
      exfalso
      apply h₃
      apply ValidArray.ext
      have h₅ : a.raw = [] := List.eq_nil_of_length_eq_zero h₄
      rw [ValidArray.raw_expand, h₅]
      rfl
  | succ n =>
      cases h₅ : maximalParentRow a.raw with
      | some k =>
          let C := Classical.choice (exists_expansionContext_of_maximalParentRow_eq_some h₅)
          exact expand_context_l h h₁ h₂ C i p hα
      | none =>
          refine ⟨p.label ⟨n, by rw [h₄]; omega⟩, hα _,
            ExpansionReflectionState.terminalExpansionRepresentation i n h₄ h₅ p,
            ExpansionReflectionState.terminalExpansionRepresentation_boundedBy i n h₄ h₅ p⟩

/-- 一个高度的截断种子及实际反射已足以证明该种子可达。 -/
theorem seed_acc_l {n : Nat} (p : SeedStabilityData (cut_l H F) n) :
    Acc Step (validSeed n) :=
  LocalDescent.acc_l (expands_l h h₁ h₂) p.representation
    (p.representation_boundedBy h₁)

end Frame

/-- 各高度可用不同载体与框架；这里只装配已有局部种子的可达性。 -/
theorem wellOrder_l {A : Nat → Type u} (F : ∀ n, StabilityFrame (A n))
    (h : ∀ n, reflects_l (cut_l n (F n)))
    (h₁ : ∀ n, ∀ {α β γ}, (F n).lt α β → (F n).lt β γ → (F n).lt α γ)
    (h₂ : ∀ n, ∀ {k α β γ}, k < n → (F n).stableLt k α β →
      (F n).stableLt k β γ → (F n).stableLt k α γ)
    (p : ∀ n, SeedStabilityData (cut_l n (F n)) n) :
    StrictWellOrder GeneratedArray GeneratedStrictDescent :=
  LocalDescent.wellOrder_l (fun n => seed_acc_l (h n) (h₁ n) (h₂ n) (p n))

end YesMetaZFC.BMS.StabilityFrame.FinitePatternDescent
