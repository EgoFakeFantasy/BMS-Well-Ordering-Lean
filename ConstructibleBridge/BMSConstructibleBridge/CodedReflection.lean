import BMSConstructibleBridge.CountableReflection

/-!
# 反射背景的单集合代码

将普通序与所有稳定层放入同一个自然数集合。反射条件只量化自然数和有限
自然数元组；良基条件只量化一个候选函数图集合。因此 `principle_l` 的实质
形状为 `∃ X ∀ Y θ(X,Y)`，其中有限元组可用自然数列表代码替换。
这是宿主层的精确呈现；没有声称已经完成纯二阶算术 AST 的公式编译。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.CodedReflection

open StabilityFrame

set_option autoImplicit false

/-- 零号切片编码普通严格序。 -/
def lt_l (X : Set Nat) (α β : Nat) : Prop := Nat.pair 0 (Nat.pair α β) ∈ X

/-- 后继号切片编码相应稳定关系。 -/
def stable_l (X : Set Nat) (k α β : Nat) : Prop := Nat.pair (k + 1) (Nat.pair α β) ∈ X

/-- 原可数系统的整个关系图，只需一个自然数集合。 -/
def code_l (S : CountableReflection.system_l) : Set Nat :=
  {t | match (Nat.unpair t).1 with
    | 0 => S.F.lt (Nat.unpair (Nat.unpair t).2).1 (Nat.unpair (Nat.unpair t).2).2
    | k + 1 => S.F.stableLt k (Nat.unpair (Nat.unpair t).2).1
        (Nat.unpair (Nat.unpair t).2).2}

theorem lt_code_l (S : CountableReflection.system_l) (α β : Nat) :
    lt_l (code_l S) α β ↔ S.F.lt α β := by
  simp only [lt_l, code_l, Set.mem_ofPred_eq, Nat.unpair_pair]

theorem stable_code_l (S : CountableReflection.system_l) (k α β : Nat) :
    stable_l (code_l S) k α β ↔ S.F.stableLt k α β := by
  simp only [stable_l, code_l, Set.mem_ofPred_eq, Nat.unpair_pair]

/-- 除良基性外的全部公理；没有任意自然数集合量词或 BM4 对象。 -/
structure axioms_l (X : Set Nat) : Prop where
  sub : ∀ {k α β}, stable_l X k α β → lt_l X α β
  trans : ∀ {α β γ}, lt_l X α β → lt_l X β γ → lt_l X α γ
  mono : ∀ {k n α β}, k ≤ n → stable_l X n α β → stable_l X k α β
  stable_trans : ∀ {k α β γ}, stable_l X k α β → stable_l X k β γ → stable_l X k α γ
  reflects : ∀ {n m : Nat} (k c α β : Nat) (s : Fin n → Nat) (t : Fin m → Nat),
    stable_l X k α β →
    (∀ i, lt_l X (s i) α) →
    (∀ i, lt_l X α (t i) ∨ α = t i) →
    (∀ i, lt_l X (t i) β) →
    (∀ i j r, stable_l X r (s i) (t j) → r < c) →
    (∀ i j r, stable_l X r (t i) (t j) → r < c) →
    ∃ u : Fin m → Nat,
      (∀ i j, lt_l X (s i) (u j)) ∧ (∀ i, lt_l X (u i) α) ∧
      (∀ i j r, stable_l X r (s i) (t j) → stable_l X r (s i) (u j)) ∧
      (∀ i j, lt_l X (t i) (t j) → lt_l X (u i) (u j)) ∧
      (∀ i j r, stable_l X r (t i) (t j) → stable_l X r (u i) (u j)) ∧
      ∀ i r, r < k → stable_l X r (t i) β → stable_l X r (u i) α

/-- 对所有集合编码的候选链检验普通标签序的良基性。 -/
def wf_l (X : Set Nat) : Prop :=
  ∀ Y : Set Nat, SecondOrderPresentation.function_l Y →
    ∃ n α β, Nat.pair n α ∈ Y ∧ Nat.pair (n + 1) β ∈ Y ∧ ¬ lt_l X β α

/-- 关系图背景的明确单集合存在句。 -/
def principle_l : Prop :=
  ∃ X : Set Nat, axioms_l X ∧ wf_l X ∧ ∀ k, ∃ α β, stable_l X k α β

/-- 固定高度只需要这一高度以上第三层的一个稳定对。 -/
def local_l (n : Nat) : Prop :=
  ∃ X : Set Nat, axioms_l X ∧ wf_l X ∧ ∃ α β, stable_l X (n + 3) α β

/-- 集合图无下降链恰好表达原自然数关系良基。 -/
theorem wf_iff_l (X : Set Nat) : wf_l X ↔ WellFounded (lt_l X) := by
  classical
  open SecondOrderPresentation in
    constructor
    · intro h
      apply wellFounded_iff_isEmpty_descending_chain.mpr
      refine ⟨?_⟩
      rintro ⟨f, hf⟩
      obtain ⟨n, α, β, hα, hβ, h₀⟩ := h (graph_l f) (function_graph_l f)
      rw [(mem_graph_l f n α).mp hα, (mem_graph_l f (n + 1) β).mp hβ] at h₀
      exact h₀ (hf n)
    · intro h Y hY
      obtain ⟨f, hf⟩ := (function_iff_l Y).mp hY
      have h₀ : ∃ n, ¬ lt_l X (f (n + 1)) (f n) := by
        by_contra h₀
        exact (wellFounded_iff_isEmpty_descending_chain.mp h).false
          ⟨f, by simpa only [not_exists, not_not] using h₀⟩
      obtain ⟨n, h₀⟩ := h₀
      exact ⟨n, f n, f (n + 1), (hf n _).mpr rfl, (hf (n + 1) _).mpr rfl, h₀⟩

/-- 把真实系统编码后，全部有限图公理保持不变。 -/
theorem code_axioms_l (S : CountableReflection.system_l) : axioms_l (code_l S) := by
  refine {
    sub := by
      intro k α β h
      simp only [lt_code_l, stable_code_l] at h ⊢
      exact S.F.stableLt_lt h
    trans := by
      intro α β γ h h₀
      simp only [lt_code_l] at h h₀ ⊢
      exact S.trans h h₀
    mono := by
      intro k n α β h h₀
      simp only [stable_code_l] at h₀ ⊢
      exact S.mono h h₀
    stable_trans := by
      intro k α β γ h h₀
      simp only [stable_code_l] at h h₀ ⊢
      exact S.stable_trans h h₀
    reflects := ?_ }
  intro n m k c α β s t h h₀ h₁ h₂ h₃ h₄
  simp only [lt_code_l, stable_code_l] at h h₀ h₁ h₂ h₃ h₄ ⊢
  let I : FiniteReflectionInput S.F n m := {
    level := k
    stabilityCutoff := c
    lowerBound := α
    upperBound := β
    lower := s
    upper := t
    lowerBound_stableLt_upperBound := h
    lower_lt_lowerBound := h₀
    lowerBound_le_upper := h₁
    upper_lt_upperBound := h₂
    lower_stableLt_below_cutoff := h₃
    upper_stableLt_below_cutoff := h₄ }
  obtain ⟨p⟩ := S.reflects I
  exact ⟨p.image, p.lower_lt_image, p.image_lt_lowerBound,
    fun _ _ _ h => p.preserves_lower_stableLt h,
    fun _ _ h => p.preserves_upper_lt h,
    fun _ _ _ h => p.preserves_upper_stableLt h,
    fun _ _ h h₀ => p.reflects_to_lowerBound h h₀⟩

/-- 单集合公理确实重建全套可数反射系统，不附加种子或下降前提。 -/
def system_l {X : Set Nat} (h : axioms_l X) (h₀ : wf_l X) :
    CountableReflection.system_l where
  F := {
    lt := lt_l X
    stableLt := stable_l X
    lt_wellFounded := (wf_iff_l X).mp h₀
    stableLt_lt := h.sub }
  trans := h.trans
  mono := h.mono
  stable_trans := h.stable_trans
  reflects := by
    intro n m I
    obtain ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h.reflects I.level I.stabilityCutoff
      I.lowerBound I.upperBound I.lower I.upper I.lowerBound_stableLt_upperBound
      I.lower_lt_lowerBound I.lowerBound_le_upper I.upper_lt_upperBound
      I.lower_stableLt_below_cutoff I.upper_stableLt_below_cutoff
    exact ⟨{
      image := u
      lower_lt_image := h₁
      image_lt_lowerBound := h₂
      preserves_lower_stableLt := h₃ _ _ _
      preserves_upper_lt := h₄ _ _
      preserves_upper_stableLt := h₅ _ _ _
      reflects_to_lowerBound := h₆ _ _ }⟩

/-- 结构式背景和单集合存在句精确等价。 -/
theorem principle_iff_l : principle_l ↔ CountableReflection.principle_l := by
  constructor
  · rintro ⟨X, h, h₀, h₁⟩
    exact ⟨system_l h h₀, h₁⟩
  · rintro ⟨S, h₀⟩
    refine ⟨code_l S, code_axioms_l S, (wf_iff_l _).mpr ?_, ?_⟩
    · have h : lt_l (code_l S) = S.F.lt :=
        funext fun α => funext fun β => propext (lt_code_l S α β)
      rw [h]
      exact S.F.lt_wellFounded
    · simpa only [stable_code_l] using h₀

/-- 局部集合原则推出对应种子可达性；不要求任何其他高度的稳定对。 -/
theorem seed_acc_l {n : Nat} (h : local_l n) : Acc Step (validSeed n) := by
  rcases h with ⟨X, h, h₀, h₁⟩
  exact (system_l h h₀).seed_acc_l n h₁

/-- 各高度允许使用不同集合，不需要收集为统一的反射系统。 -/
theorem wellOrder_local_l (h : ∀ n, local_l n) :
    StrictWellOrder GeneratedArray GeneratedStrictDescent :=
  LocalDescent.wellOrder_l (fun n => seed_acc_l (h n))

/-- 单一额外集合存在原则下的原 BM4 严格良序定理。 -/
theorem wellOrder_l (h : principle_l) :
    StrictWellOrder GeneratedArray GeneratedStrictDescent :=
  CountableReflection.wellOrder_l (principle_iff_l.mp h)

/-- 同一额外原则下的精确二阶 BM4 无下降链句。 -/
theorem sentence_l (h : principle_l) : SecondOrderPresentation.sentence_l :=
  CountableReflection.sentence_l (principle_iff_l.mp h)

end YesMetaZFC.BMS.ConstructibleBridge.CodedReflection
