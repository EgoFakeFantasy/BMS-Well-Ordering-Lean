import BMSConstructibleBridge.TreeChain

/-!
# 可数良基图码的成员解释

一个对象由自然数节点上的关系、指定根及该根的宿主良基证书组成。允许不同
对象使用不同关系；相等解释为跨图双模拟，成员解释为某个直接子节点的换码。
实际证明换码不变性、外延性及基础性，不把这些性质作为结构字段假定。

这是可数有根图形式的语义解释域，还不是对象 `Z₂` 中的 KL 树解释：图展开为
有限序列树、其余集合公理及 `L*` 的句法解释均须另证。`Acc` 明确属于宿主层，
不能据此声称任意 Henkin 模型中的树码在外部也良基。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.CountableGraph

set_option autoImplicit false

/-- 仅要求指定根良基，未使用的节点可以不良基。 -/
structure code_l where
  rel : Nat → Nat → Prop
  root : Nat
  wf : Acc rel root

/-- 不同图码所表示对象的相等，不要求两个实数码逐字相等。 -/
def eq_l (A B : code_l) : Prop := Bisimulation.eq_l A.rel B.rel A.root B.root

/-- 成员码可以使用另一张图，只须双模拟于某个直接子节点。 -/
def mem_l (A B : code_l) : Prop :=
  ∃ b, B.rel b B.root ∧ Bisimulation.eq_l A.rel B.rel A.root b

theorem refl_l (A : code_l) : eq_l A A := Bisimulation.refl_l A.rel A.root

theorem symm_l {A B : code_l} (h : eq_l A B) : eq_l B A :=
  Bisimulation.symm_l A.rel B.rel h

theorem trans_l {A B C : code_l} (h : eq_l A B) (h₁ : eq_l B C) : eq_l A C :=
  Bisimulation.trans_l A.rel B.rel C.rel h h₁

private theorem mem_right {A B C : code_l} (h : eq_l B C) (h₁ : mem_l A B) :
    mem_l A C := by
  obtain ⟨b, h₁, h₂⟩ := h₁
  obtain ⟨c, h₃, h₄⟩ := (Bisimulation.witness_eq_l B.rel C.rel h).1 h₁
  exact ⟨c, h₃, Bisimulation.trans_l A.rel B.rel C.rel h₂ h₄⟩

/-- 解释成员关系在两个参数换码后都不变。 -/
theorem mem_congr_l {A B C D : code_l} (h : eq_l A B) (h₁ : eq_l C D) :
    mem_l A C ↔ mem_l B D := by
  constructor
  · rintro ⟨c, h₂, h₃⟩
    exact mem_right h₁ ⟨c, h₂,
      Bisimulation.trans_l B.rel A.rel C.rel (symm_l h) h₃⟩
  · rintro ⟨d, h₂, h₃⟩
    exact mem_right (symm_l h₁) ⟨d, h₂,
      Bisimulation.trans_l A.rel B.rel D.rel h h₃⟩

/-- 每个直接子节点给出解释域中的实际对象，良基证书由根证书推出。 -/
def child_l (A : code_l) (a : Nat) (h : A.rel a A.root) : code_l :=
  ⟨A.rel, a, A.wf.inv h⟩

theorem child_mem_l (A : code_l) (a : Nat) (h : A.rel a A.root) :
    mem_l (child_l A a h) A := ⟨a, h, Bisimulation.refl_l A.rel a⟩

/-- 真正遍历整个解释域的外延性；不把原始图码相等误当对象相等。 -/
theorem ext_l (A B : code_l) : eq_l A B ↔
    ∀ C : code_l, mem_l C A ↔ mem_l C B := by
  constructor
  · intro h C
    exact mem_congr_l (refl_l C) h
  · intro h
    apply (Bisimulation.unfold_l A.rel B.rel A.root B.root).mpr
    constructor
    · intro a h₁
      exact (h (child_l A a h₁)).mp (child_mem_l A a h₁)
    · intro b h₁
      obtain ⟨a, h₂, h₃⟩ := (h (child_l B b h₁)).mpr (child_mem_l B b h₁)
      exact ⟨a, h₂, Bisimulation.symm_l B.rel A.rel h₃⟩

private theorem acc (R : Nat → Nat → Prop) {a : Nat} (h : Acc R a) :
    ∀ A : code_l, Bisimulation.eq_l R A.rel a A.root → Acc mem_l A := by
  induction h with
  | intro a _ hᵢ =>
      intro A h
      refine .intro A ?_
      rintro B ⟨b, h₁, h₂⟩
      obtain ⟨c, h₃, h₄⟩ := (Bisimulation.witness_eq_l R A.rel h).2 h₁
      exact hᵢ c h₃ B (Bisimulation.trans_l R A.rel B.rel h₄
        (Bisimulation.symm_l B.rel A.rel h₂))

/-- 实际解释成员关系的宿主良基性，由每个图的根证书逐步传输。 -/
theorem wellFounded_l : WellFounded mem_l :=
  ⟨fun A => acc A.rel A.wf A (Bisimulation.refl_l A.rel A.root)⟩

/-- 解释域上的基础公理形式，最小元实际来自已证成员良基性。 -/
theorem foundation_l (A : code_l) (h : ∃ B, mem_l B A) :
    ∃ B, mem_l B A ∧ ∀ C, mem_l C B → ¬mem_l C A := by
  obtain ⟨B, h₁, h₂⟩ := wellFounded_l.has_min {B | mem_l B A} h
  exact ⟨B, h₁, fun C h₃ h₄ => h₂ C h₄ h₃⟩

/-- 图的关系部分只占一个实数；另一个根参数是自然数。 -/
def real_l (A : code_l) : Set Nat := {n | A.rel n.unpair.1 n.unpair.2}

theorem real_iff_l (A : code_l) (a b : Nat) :
    Nat.pair a b ∈ real_l A ↔ A.rel a b := by
  simp only [real_l, Set.mem_ofPred_eq, Nat.unpair_pair]

/-- 在图的移位副本之外添加新根；根的直接子节点由数谓词选择。 -/
def graft_l (R : Nat → Nat → Prop) (P : Nat → Prop) : Nat → Nat → Prop
  | a + 1, 0 => P a
  | a + 1, b + 1 => R a b
  | 0, _ => False

private theorem graft_acc (R : Nat → Nat → Prop) (P : Nat → Prop)
    {a : Nat} (h : Acc R a) : Acc (graft_l R P) (a + 1) := by
  induction h with
  | intro a _ hᵢ =>
      refine .intro (a + 1) ?_
      intro b h
      cases b with
      | zero => exact False.elim h
      | succ b => exact hᵢ b h

/-- 旧节点与其移位副本之间有显式双模拟，不依赖新根的子节点选择。 -/
theorem graft_eq_l (R : Nat → Nat → Prop) (P : Nat → Prop) (a : Nat) :
    Bisimulation.eq_l R (graft_l R P) a (a + 1) := by
  refine ⟨fun b c => c = b + 1, ?_, rfl⟩
  rintro b c rfl
  constructor
  · intro d h
    exact ⟨d + 1, h, rfl⟩
  · intro d h
    cases d with
    | zero => exact False.elim h
    | succ d => exact ⟨d, h, rfl⟩

/-- 从同一个数关系的一族良基节点实际构造集合码，不选择一族实数见证。 -/
def collect_l (R : Nat → Nat → Prop) (P : Nat → Prop)
    (h : ∀ a, P a → Acc R a) : code_l :=
  ⟨graft_l R P, 0, .intro 0 (by
    intro a h₁
    cases a with
    | zero => exact False.elim h₁
    | succ a => exact graft_acc R P (h a h₁))⟩

/-- 新根所表示的成员恰为所选旧节点的任意双模拟码。 -/
theorem collect_mem_l (R : Nat → Nat → Prop) (P : Nat → Prop)
    (h : ∀ a, P a → Acc R a) (A : code_l) :
    mem_l A (collect_l R P h) ↔ ∃ a, P a ∧ Bisimulation.eq_l A.rel R A.root a := by
  constructor
  · rintro ⟨a, h₁, h₂⟩
    cases a with
    | zero => exact False.elim h₁
    | succ a =>
        exact ⟨a, h₁, Bisimulation.trans_l A.rel (graft_l R P) R h₂
          (Bisimulation.symm_l R (graft_l R P) (graft_eq_l R P a))⟩
  · rintro ⟨a, h₁, h₂⟩
    exact ⟨a + 1, h₁, Bisimulation.trans_l A.rel R (graft_l R P) h₂ (graft_eq_l R P a)⟩

/-- 解释域中实际的空集码。 -/
def empty_l : code_l := collect_l (fun _ _ => False) (fun _ => False)
  (fun _ h => False.elim h)

theorem empty_mem_l (A : code_l) : ¬mem_l A empty_l := by
  rw [empty_l, collect_mem_l]
  rintro ⟨_, h, _⟩
  exact h

/-- 分离构造保留原图的内部边，只筛选新根的直接子节点。 -/
def sep_l (A : code_l) (P : code_l → Prop) : code_l :=
  collect_l A.rel (fun a => ∃ h : A.rel a A.root, P (child_l A a h))
    (fun _ h => A.wf.inv h.1)

/-- 对换码不变谓词的分离成员规格。这里是宿主语义构造，不是对象理解模式的推导。 -/
theorem sep_mem_l (A : code_l) (P : code_l → Prop)
    (hP : ∀ B C, eq_l B C → (P B ↔ P C)) (B : code_l) :
    mem_l B (sep_l A P) ↔ mem_l B A ∧ P B := by
  rw [sep_l, collect_mem_l]
  constructor
  · rintro ⟨a, ⟨h, h₁⟩, h₂⟩
    exact ⟨⟨a, h, h₂⟩, (hP B (child_l A a h) h₂).mpr h₁⟩
  · rintro ⟨⟨a, h, h₁⟩, h₂⟩
    exact ⟨a, ⟨h, (hP B (child_l A a h) h₁).mp h₂⟩, h₁⟩

/-- 并集码直接收集原根的两步子节点，不枚举所有等价表示。 -/
def union_l (A : code_l) : code_l :=
  collect_l A.rel (fun a => ∃ b, A.rel b A.root ∧ A.rel a b)
    (fun _ h => by obtain ⟨b, h, h₁⟩ := h; exact (A.wf.inv h).inv h₁)

/-- 实际并集构造的成员规格。 -/
theorem union_mem_l (A B : code_l) : mem_l B (union_l A) ↔
    ∃ C, mem_l C A ∧ mem_l B C := by
  rw [union_l, collect_mem_l]
  constructor
  · rintro ⟨a, ⟨b, h, h₁⟩, h₂⟩
    exact ⟨child_l A b h, child_mem_l A b h, a, h₁, h₂⟩
  · rintro ⟨C, ⟨b, h, h₁⟩, ⟨c, h₂, h₃⟩⟩
    obtain ⟨a, h₄, h₅⟩ := (Bisimulation.witness_eq_l C.rel A.rel h₁).1 h₂
    exact ⟨a, ⟨b, h, h₄⟩, Bisimulation.trans_l B.rel C.rel A.rel h₃ h₅⟩

/-- 集合后继：在原成员外再加入原对象本身，使用新根避免循环。 -/
def succ_l (A : code_l) : code_l :=
  collect_l A.rel (fun a => A.rel a A.root ∨ a = A.root)
    (fun _ h => by rcases h with h | rfl; exact A.wf.inv h; exact A.wf)

theorem succ_mem_l (A B : code_l) : mem_l B (succ_l A) ↔ mem_l B A ∨ eq_l B A := by
  rw [succ_l, collect_mem_l]
  constructor
  · rintro ⟨a, h, h₁⟩
    rcases h with h | rfl
    · exact Or.inl ⟨a, h, h₁⟩
    · exact Or.inr h₁
  · rintro (⟨a, h, h₁⟩ | h)
    · exact ⟨a, Or.inl h, h₁⟩
    · exact ⟨A.root, Or.inr rfl, h⟩

theorem succ_congr_l {A B : code_l} (h : eq_l A B) : eq_l (succ_l A) (succ_l B) := by
  apply (ext_l _ _).mpr
  intro C
  rw [succ_mem_l, succ_mem_l]
  exact or_congr (mem_congr_l (refl_l C) h)
    ⟨fun h₁ => trans_l h₁ h, fun h₁ => trans_l h₁ (symm_l h)⟩

/-- 把已经给出的数指标图族放入互不相交的配对坐标。 -/
def slices_l (F : Nat → code_l) (a b : Nat) : Prop :=
  a.unpair.1 = b.unpair.1 ∧ (F b.unpair.1).rel a.unpair.2 b.unpair.2

/-- 每个分量与其在不交和中的副本双模拟。 -/
theorem slice_eq_l (F : Nat → code_l) (i a : Nat) :
    Bisimulation.eq_l (F i).rel (slices_l F) a (Nat.pair i a) := by
  refine ⟨fun b c => c = Nat.pair i b, ?_, rfl⟩
  rintro b c rfl
  constructor
  · intro d h
    exact ⟨Nat.pair i d, by simp [slices_l, h], rfl⟩
  · intro d h
    simp only [slices_l, Nat.unpair_pair] at h
    exact ⟨d.unpair.2, h.2, by simp only [← h.1, Nat.pair_unpair]⟩

private theorem slice_acc (F : Nat → code_l) (i : Nat) {a : Nat}
    (h : Acc (F i).rel a) : Acc (slices_l F) (Nat.pair i a) := by
  induction h with
  | intro a _ hᵢ =>
      refine .intro (Nat.pair i a) ?_
      intro b h
      simp only [slices_l, Nat.unpair_pair] at h
      have h₁ : Nat.pair i b.unpair.2 = b := by rw [← h.1, Nat.pair_unpair]
      rw [← h₁]
      exact hᵢ b.unpair.2 h.2

/-- 图族必须已作为一个函数给出；此构造不从逐项存在推导可数选择。 -/
def family_l (F : Nat → code_l) (P : Nat → Prop) : code_l :=
  collect_l (slices_l F) (fun a => ∃ i, P i ∧ a = Nat.pair i (F i).root)
    (fun _ h => by obtain ⟨i, _, rfl⟩ := h; exact slice_acc F i (F i).wf)

theorem family_mem_l (F : Nat → code_l) (P : Nat → Prop) (A : code_l) :
    mem_l A (family_l F P) ↔ ∃ i, P i ∧ eq_l A (F i) := by
  rw [family_l, collect_mem_l]
  constructor
  · rintro ⟨a, ⟨i, h, rfl⟩, h₁⟩
    exact ⟨i, h, Bisimulation.trans_l A.rel (slices_l F) (F i).rel h₁
      (Bisimulation.symm_l (F i).rel (slices_l F) (slice_eq_l F i (F i).root))⟩
  · rintro ⟨i, h, h₁⟩
    exact ⟨Nat.pair i (F i).root, ⟨i, h, rfl⟩,
      Bisimulation.trans_l A.rel (F i).rel (slices_l F) h₁ (slice_eq_l F i (F i).root)⟩

/-- 两个任意图码的无序对，使用两个确定的分量，不要求任意实数族的选择。 -/
def pair_l (A B : code_l) : code_l :=
  family_l (fun i => if i = 0 then A else B) (fun i => i = 0 ∨ i = 1)

theorem pair_mem_l (A B C : code_l) : mem_l C (pair_l A B) ↔ eq_l C A ∨ eq_l C B := by
  rw [pair_l, family_mem_l]
  constructor
  · rintro ⟨i, h, h₁⟩
    rcases h with rfl | rfl
    · exact Or.inl h₁
    · exact Or.inr h₁
  · rintro (h | h)
    · exact ⟨0, Or.inl rfl, h⟩
    · exact ⟨1, Or.inr rfl, h⟩

/-- 每个非空对象的成员有自然数枚举，满射性按解释相等而非图码字面相等。 -/
theorem enumerate_l (A : code_l) (h : ∃ B, mem_l B A) :
    ∃ f : Nat → code_l, (∀ n, mem_l (f n) A) ∧
      ∀ B, mem_l B A → ∃ n, eq_l B (f n) := by
  classical
  obtain ⟨_, a, h, _⟩ := h
  let f : Nat → code_l := fun n => if h₁ : A.rel n A.root then child_l A n h₁ else child_l A a h
  refine ⟨f, ?_, ?_⟩
  · intro n
    dsimp only [f]
    split <;> exact child_mem_l A _ _
  · rintro B ⟨b, h₁, h₂⟩
    refine ⟨b, ?_⟩
    dsimp only [f]
    rw [dif_pos h₁]
    exact h₂

/-- 跨图成员下降链提升到一个固定图，逐步只取自然数最小见证。 -/
theorem lift_l (f : Nat → code_l) (h : ∀ n, mem_l (f (n + 1)) (f n))
    (A : code_l) (h₀ : eq_l (f 0) A) :
    ∃ g : Nat → Nat, g 0 = A.root ∧
      (∀ n, Bisimulation.eq_l (f n).rel A.rel (f n).root (g n)) ∧
      ∀ n, A.rel (g (n + 1)) (g n) := by
  classical
  have h₁ : ∀ n b, Bisimulation.eq_l (f n).rel A.rel (f n).root b →
      ∃ c, A.rel c b ∧ Bisimulation.eq_l (f (n + 1)).rel A.rel (f (n + 1)).root c := by
    intro n b h₁
    obtain ⟨c, h₂, h₃⟩ := h n
    obtain ⟨d, h₄, h₅⟩ := (Bisimulation.witness_eq_l (f n).rel A.rel h₁).1 h₂
    exact ⟨d, h₄, Bisimulation.trans_l (f (n + 1)).rel (f n).rel A.rel h₃ h₅⟩
  let g : ∀ n, {b // Bisimulation.eq_l (f n).rel A.rel (f n).root b} :=
    Nat.rec ⟨A.root, h₀⟩ fun n b =>
      ⟨Nat.find (h₁ n b.1 b.2), (Nat.find_spec (h₁ n b.1 b.2)).2⟩
  exact ⟨fun n => (g n).1, rfl, fun n => (g n).2,
    fun n => (Nat.find_spec (h₁ n (g n).1 (g n).2)).1⟩

end YesMetaZFC.BMS.ConstructibleBridge.CountableGraph
