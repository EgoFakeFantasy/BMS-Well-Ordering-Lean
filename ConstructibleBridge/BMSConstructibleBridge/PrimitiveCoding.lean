import Mathlib.Computability.Primrec.List
import BMSConstructibleBridge.ArithmeticPresentation

/-!
# 完整 BM4 算法的原始递归证书

证书针对现有代码及实际 `Encodable` 实例，不以同名占位算法替换原函数。
覆盖坐标与裁剪、全部行的 parent 和祖先链、复制块、完整展开、轨迹执行、
总解码、最终一步检查器及规范码搜索。按行递归只操作有限 parent 表，不要求
对函数空间编码。`Primrec` 是宿主层对指定自然数编码的证书，仍须区别于
对象算术中的公式编译、总性推导及最终良序证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PrimitiveCoding

open Primrec

set_option autoImplicit false

/-- 与实际轨迹编码使用同一配对和列表编码。 -/
theorem encode_l : Primrec₂ ArithmeticPresentation.encode_l := Primrec.encode.to₂

/-- 实际总解码的轨迹部分是原始递归的，不包括随后执行展开的部分。 -/
theorem trace_l : Primrec (fun n : Nat =>
    (Encodable.decode (α := Nat × List Nat) n).getD (0, [])) :=
  option_getD.comp Primrec.decode (const _)

/-- 两次列表查询与 Option 绑定给出原坐标函数。 -/
theorem entry_l : Primrec (fun p : BMSArray × Nat × Nat => entry? p.1 p.2.1 p.2.2) :=
  option_bind (list_getElem?.comp fst (fst.comp snd))
    (list_getElem?.comp snd (snd.comp (snd.comp fst))).to₂

/-- 支撑高度由有限列表递归计算，而非依赖无界真值搜索。 -/
theorem support_l : Primrec supportHeight := by
  have h : Primrec₂ (fun (_ : List Nat) (p : Nat × Nat) =>
      if p.2 = 0 then (if p.1 = 0 then 0 else 1) else p.2 + 1) :=
    ((ite (Primrec.eq.comp snd (const 0))
      (ite (Primrec.eq.comp fst (const 0)) (const 0) (const 1))
      (succ.comp snd)).comp snd).to₂
  apply (list_foldr Primrec.id (const 0) h).of_eq
  intro s
  change s.foldr (fun v n => if n = 0 then (if v = 0 then 0 else 1) else n + 1) 0 =
    supportHeight s
  induction s with
  | nil => rfl
  | cons v s hᵢ => simp only [List.foldr_cons, hᵢ, supportHeight_cons_l]

/-- 当前高度是各列支撑高度的有限最大值。 -/
theorem height_l : Primrec trimHeight :=
  list_foldl Primrec.id (const 0)
    ((nat_max.comp (fst.comp snd) (support_l.comp (snd.comp snd))).to₂)

/-- 原裁剪操作只使用已证高度及列表 take。 -/
theorem trim_l : Primrec trimZeroRows :=
  list_map Primrec.id (list_take.comp (height_l.comp fst) snd).to₂

/-- 初始数组的实际两列复制构造是原始递归的。 -/
theorem seed_l : Primrec seed := by
  have h (v : Nat) : Primrec (fun n : Nat => List.replicate n v) := by
    apply (list_map list_range (const v).to₂).of_eq
    intro n
    simp
  exact list_cons.comp (h 0) (list_cons.comp (h 1) (const []))

/-- 固定原始递归谓词的有界最大值搜索，不增添无界最小化。 -/
theorem greatest_l {A : Type} [Primcodable A] {p : A → Nat → Bool}
    (h : Primrec₂ p) : Primrec₂ (fun a n => greatestBelow? n (p a)) := by
  have h₀ : Primrec₂ (fun a (q : Nat × Option Nat) =>
      if p a q.1 then some q.1 else q.2) :=
    (ite (Primrec.eq.comp (h.comp fst (fst.comp snd)) (const true))
      (option_some.comp (fst.comp snd)) (snd.comp snd)).to₂
  apply (nat_rec (const none) h₀).of_eq
  intro a n
  induction n with
  | zero => rfl
  | succ n hᵢ => simp only [hᵢ, greatestBelow?]

private theorem option_lt : Primrec₂ (fun a b : Option Nat =>
    match a, b with
    | some x, some y => decide (x < y)
    | _, _ => false) := by
  have h : Primrec (fun q : Option Nat × Option Nat =>
      (q.1.bind (fun x => q.2.map (fun y => decide (x < y)))).getD false) :=
    option_getD.comp (option_bind fst
      (option_map (snd.comp fst) (nat_lt.decide.comp (snd.comp fst) snd).to₂).to₂)
      (const false)
  apply h.to₂.of_eq
  intro a b
  cases a <;> cases b <;> rfl

/-- 原 parent 算法的零行部分；仍使用原最大候选搜索与原坐标比较。 -/
theorem parent_zero_l : Primrec₂ (fun a i => parent 0 a i) := by
  have h₀ : Primrec₂ (fun (q : BMSArray × Nat) k =>
      match entry? q.1 k 0, entry? q.1 q.2 0 with
      | some x, some y => decide (x < y)
      | _, _ => false) :=
    (option_lt.comp
      (entry_l.comp (pair (fst.comp fst) (pair snd (const 0))))
      (entry_l.comp (pair (fst.comp fst) (pair (snd.comp fst) (const 0))))).to₂
  exact (ite (nat_lt.comp snd (list_length.comp fst))
    ((greatest_l h₀).comp Primrec.id snd) (const none)).to₂

/-- 有限燃料的祖先链递归；递归参数只取自然数对，不量化函数空间编码。 -/
theorem ancestor_l {A : Type} [Primcodable A] {f : A → Nat → Option Nat}
    (h : Primrec₂ f) :
    Primrec₂ (fun a (p : Nat × Nat) => ancestorChain (f a) p.1 p.2) := by
  let l (a : A) (p : Nat × Nat) : List (Nat × Nat) :=
    if p.2 = 0 then [] else [((f a p.1).getD 0, p.2 - 1)]
  let g (a : A) (p : (Nat × Nat) × List (List Nat)) : Option (List Nat) :=
    some (if p.1.2 = 0 then [] else
      match f a p.1.1 with
      | none => []
      | some i => i :: p.2.head?.getD [])
  have h₁ : Primrec₂ l :=
    (ite (Primrec.eq.comp (snd.comp snd) (const 0)) (const [])
      (list_cons.comp
        (pair (option_getD.comp (h.comp fst (fst.comp snd)) (const 0))
          (nat_sub.comp (snd.comp snd) (const 1))) (const []))).to₂
  have h₂ : Primrec₂ g := by
    apply
    (option_some.comp (ite (Primrec.eq.comp (snd.comp (fst.comp snd)) (const 0))
      (const []) (option_casesOn (h.comp fst (fst.comp (fst.comp snd))) (const [])
        (list_cons.comp snd (option_getD.comp
          (list_head?.comp (snd.comp (snd.comp fst))) (const []))).to₂))).to₂.of_eq
    intro a p
    dsimp [g]
    split
    · rfl
    · cases f a p.1.1 <;> rfl
  apply nat_omega_rec _ (snd.comp snd).to₂ h₁ h₂
  · intro a p q hq
    simp only [l] at hq
    split at hq
    · simp at hq
    · simp only [List.mem_singleton] at hq
      subst q
      dsimp
      omega
  · intro a p
    rcases p with ⟨i, n⟩
    cases n with
    | zero => simp [g, l, ancestorChain]
    | succ n => cases hᵢ : f a i <;> simp [g, l, ancestorChain, hᵢ]

private theorem table_get (a : BMSArray) (r i : Nat) :
    (((List.range a.length).map (parent r a))[i]?).getD none = parent r a i := by
  by_cases h : i < a.length
  · simp [h]
  · have h₀ : parent r a i = none := by cases r <;> simp [parent, h]
    simp [h, h₀]

/-- 所有列的 parent 表按行作普通自然数递归，避免将函数作为递归值。 -/
theorem table_l : Primrec₂ (fun a r => (List.range a.length).map (parent r a)) := by
  let g (a : BMSArray) (p : Nat × List (Option Nat)) : List (Option Nat) :=
    (List.range a.length).map fun i =>
      if i < a.length then
        greatestBelow? i (fun k =>
          (ancestorChain (fun j => p.2[j]?.getD none) i i).contains k &&
            match entry? a k (p.1 + 1), entry? a i (p.1 + 1) with
            | some x, some y => decide (x < y)
            | _, _ => false)
      else none
  have h₀ : Primrec (fun a => (List.range a.length).map (parent 0 a)) :=
    list_map (list_range.comp list_length) parent_zero_l
  have h₁ : Primrec₂ (fun (s : List (Option Nat)) j => s[j]?.getD none) :=
    (option_getD.comp (list_getElem?.comp fst snd) (const none)).to₂
  have h₂ : Primrec₂ (fun (p : (BMSArray × Nat × List (Option Nat)) × Nat) k =>
      (ancestorChain (fun j => p.1.2.2[j]?.getD none) p.2 p.2).contains k &&
        match entry? p.1.1 k (p.1.2.1 + 1), entry? p.1.1 p.2 (p.1.2.1 + 1) with
        | some x, some y => decide (x < y)
        | _, _ => false) := by
    have h₃ : Primrec (fun q : ((BMSArray × Nat × List (Option Nat)) × Nat) × Nat =>
        ancestorChain (fun j => q.1.1.2.2[j]?.getD none) q.1.2 q.1.2) :=
      (ancestor_l h₁).comp (snd.comp (snd.comp (fst.comp fst)))
      (pair (snd.comp fst) (snd.comp fst))
    have h₄ := (Primrec.list_idxOf.comp snd h₃)
    have h₅ := nat_lt.decide.comp h₄ (list_length.comp h₃)
    apply (Primrec.and.comp h₅ (option_lt.comp
      (entry_l.comp (pair (fst.comp (fst.comp fst))
        (pair snd (succ.comp (fst.comp (snd.comp (fst.comp fst)))))))
      (entry_l.comp (pair (fst.comp (fst.comp fst))
        (pair (snd.comp fst) (succ.comp (fst.comp (snd.comp (fst.comp fst))))))))).to₂.of_eq
    intro p k
    simp only [List.idxOf_lt_length_iff, List.contains_eq_mem]
  have h₃ : Primrec₂ g :=
    (list_map (list_range.comp (list_length.comp fst))
      (ite (nat_lt.comp snd (list_length.comp (fst.comp fst)))
        ((greatest_l h₂).comp Primrec.id snd) (const none)).to₂).to₂
  apply (nat_rec h₀ h₃).of_eq
  intro a r
  induction r with
  | zero => rfl
  | succ r hᵢ =>
      change g a (r, Nat.rec ((List.range a.length).map (parent 0 a))
        (fun n t => g a (n, t)) r) = _
      rw [hᵢ]
      simp only [g, table_get]
      rfl

/-- 原算法在任意行、任意列上的 parent 值均为原始递归。 -/
theorem parent_l : Primrec (fun p : BMSArray × Nat × Nat => parent p.2.1 p.1 p.2.2) :=
  (option_getD.comp
    (list_getElem?.comp (table_l.comp fst (fst.comp snd)) (snd.comp snd))
    (const none)).of_eq fun p => table_get p.1 p.2.1 p.2.2

private theorem contains : Primrec₂ (fun (s : List Nat) i => s.contains i) := by
  apply (nat_lt.decide.comp (list_idxOf.comp snd fst) (list_length.comp fst)).to₂.of_eq
  intro s i
  simp [List.idxOf_lt_length_iff]

/-- 原祖先判定包含全部行参数，不再局限于第零行。 -/
theorem ancestry_l : Primrec (fun p : BMSArray × Nat × Nat × Nat =>
    isAncestor p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have h : Primrec₂ (fun (p : BMSArray × Nat) i => parent p.2 p.1 i) :=
    (parent_l.comp (pair (fst.comp fst) (pair (snd.comp fst) snd))).to₂
  exact contains.comp ((ancestor_l h).comp (pair fst (fst.comp snd))
    (pair (snd.comp (snd.comp snd)) (snd.comp (snd.comp snd)))) (fst.comp (snd.comp snd))

/-- 搜索最后一列的最高 parent 行仅需有界搜索。 -/
theorem maximal_l : Primrec maximalParentRow := by
  have h : Primrec₂ (fun (p : BMSArray × Nat) r => (parent r p.1 p.2).isSome) :=
    (option_isSome.comp (parent_l.comp (pair (fst.comp fst) (pair snd (snd.comp fst))))).to₂
  apply (nat_casesOn list_length (const none)
    ((greatest_l h).comp Primrec.id
      (option_getD.comp (option_map (list_getElem?.comp fst snd)
        (list_length.comp snd).to₂) (const 0))).to₂).of_eq
  intro a
  cases h₀ : a.length <;> simp [maximalParentRow, h₀]

/-- 保留索引的列表映射；对元素的缺省值只在越界查询中出现。 -/
theorem indexed_l {A B C : Type} [Primcodable A] [Primcodable B] [Primcodable C]
    [Inhabited B] {f : A → List B} {g : A → Nat → B → C}
    (h : Primrec f) (h₀ : Primrec₂ (fun a (p : Nat × B) => g a p.1 p.2)) :
    Primrec (fun a => (f a).mapIdx (g a)) := by
  apply (list_map (list_range.comp (list_length.comp h))
    (h₀.comp fst (pair snd (option_getD.comp
      (list_getElem?.comp (h.comp fst) snd) (const default)))).to₂).of_eq
  intro a
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.length_mapIdx] at h₂
    simp [List.getElem?_eq_getElem h₂]

/-- 每个坐标是否上升的原布尔条件是原始递归的。 -/
theorem ascending_l : Primrec (fun p : BMSArray × Nat × Nat × Nat × Nat =>
    ascending p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) :=
  Primrec.and.comp (nat_lt.decide.comp (snd.comp (snd.comp (snd.comp snd))) (fst.comp snd))
    (Primrec.or.comp (Primrec.beq.comp (fst.comp (snd.comp (snd.comp snd))) (const 0))
      (ancestry_l.comp (pair fst
        (pair (snd.comp (snd.comp (snd.comp snd)))
          (pair (fst.comp (snd.comp snd))
            (nat_add.comp (fst.comp (snd.comp snd)) (fst.comp (snd.comp (snd.comp snd)))))))))

private theorem copy_value : Primrec (fun p : Nat × Nat × Option Nat × Option Nat =>
    match p.2.2.1, p.2.2.2 with
    | some x, some y => p.1 + p.2.1 * (y - x)
    | _, _ => p.1) := by
  apply (option_getD.comp
    (option_bind (fst.comp (snd.comp snd))
      (option_map (snd.comp (snd.comp (snd.comp fst)))
        (nat_add.comp (fst.comp (fst.comp fst))
          (nat_mul.comp (fst.comp (snd.comp (fst.comp fst)))
            (nat_sub.comp snd (snd.comp fst)))).to₂).to₂) fst).of_eq
  intro p
  rcases p with ⟨v, n, x, y⟩
  cases x <;> cases y <;> rfl

/-- 原复制块的两层带索引映射及坐标增量均使用既定算法。 -/
theorem copy_l : Primrec (fun p : BMSArray × BMSArray × Nat × Nat × Nat × List Nat =>
    copyBlock p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by
  apply indexed_l (fst.comp snd)
  change Primrec _
  apply indexed_l (snd.comp snd)
  change Primrec _
  have ha : Primrec (fun p : ((BMSArray × BMSArray × Nat × Nat × Nat × List Nat) ×
      Nat × List Nat) × Nat × Nat => p.1.1) := fst.comp fst
  have h₀ : Primrec (fun p : ((BMSArray × BMSArray × Nat × Nat × Nat × List Nat) ×
      Nat × List Nat) × Nat × Nat =>
      ascending p.1.1.1 p.1.1.2.2.1 p.1.1.2.2.2.1 p.1.2.1 p.2.1) :=
    ascending_l.comp (pair (fst.comp ha) (pair (fst.comp (snd.comp (snd.comp ha)))
      (pair (fst.comp (snd.comp (snd.comp (snd.comp ha))))
        (pair (fst.comp (snd.comp fst)) (fst.comp snd)))))
  apply (ite (Primrec.eq.comp h₀ (const true))
    (copy_value.comp (pair (snd.comp snd)
      (pair (fst.comp (snd.comp (snd.comp (snd.comp (snd.comp ha)))))
        (pair (list_getElem?.comp
          (option_getD.comp (list_head?.comp (fst.comp (snd.comp ha))) (const []))
          (fst.comp snd))
          (list_getElem?.comp (snd.comp (snd.comp (snd.comp (snd.comp (snd.comp ha)))))
            (fst.comp snd)))))) (snd.comp snd)).of_eq
  intro p
  rfl

private theorem option_elim {A B C : Type} [Primcodable A] [Primcodable B] [Primcodable C]
    {o : A → Option B} {f : A → C} {g : A → B → C}
    (h : Primrec o) (h₀ : Primrec f) (h₁ : Primrec₂ g) :
    Primrec (fun a => match o a with | none => f a | some b => g a b) := by
  apply (option_casesOn h h₀ h₁).of_eq
  intro a
  cases o a <;> rfl

/-- 包含最高行、parent 搜索和所有复制块的实际未裁剪展开。 -/
theorem raw_l : Primrec₂ expandRaw := by
  have h₀ : Primrec (fun p : BMSArray × Nat × Nat × Nat × Nat =>
      p.1.take p.2.2.2.2 ++ (List.range (p.2.1 + 1)).flatMap (fun i =>
        copyBlock p.1 (slice p.1 p.2.2.2.2 (p.2.2.1 - p.2.2.2.2))
          p.2.2.2.1 p.2.2.2.2 i (p.1[p.2.2.1]?.getD []))) := by
    have h₁ : Primrec (fun p : (BMSArray × Nat × Nat × Nat × Nat) × Nat => p.1) := fst
    have h₂ := snd.comp (snd.comp (snd.comp (snd.comp h₁)))
    have h₃ := fst.comp (snd.comp (snd.comp h₁))
    exact list_append.comp (list_take.comp (snd.comp (snd.comp (snd.comp snd))) fst)
      (list_flatMap (list_range.comp (succ.comp (fst.comp snd)))
        (copy_l.comp (pair (fst.comp h₁)
          (pair (list_take.comp (nat_sub.comp h₃ h₂)
            (list_drop.comp h₂ (fst.comp h₁)))
            (pair (fst.comp (snd.comp (snd.comp (snd.comp h₁))))
              (pair h₂ (pair snd (option_getD.comp
                (list_getElem?.comp (fst.comp h₁) h₃) (const [])))))))).to₂)
  have h₁ : Primrec (fun p : BMSArray × Nat × Nat × Nat =>
      match parent p.2.2.2 p.1 p.2.2.1 with
      | none => p.1.take p.2.2.1
      | some j => p.1.take j ++ (List.range (p.2.1 + 1)).flatMap (fun i =>
          copyBlock p.1 (slice p.1 j (p.2.2.1 - j)) p.2.2.2 j i
            (p.1[p.2.2.1]?.getD []))) := by
    apply (option_elim (parent_l.comp (pair fst
      (pair (snd.comp (snd.comp snd)) (fst.comp (snd.comp snd)))))
      (list_take.comp (fst.comp (snd.comp snd)) fst)
      (h₀.comp (pair (fst.comp fst) (pair (fst.comp (snd.comp fst))
        (pair (fst.comp (snd.comp (snd.comp fst)))
          (pair (snd.comp (snd.comp (snd.comp fst))) snd))))).to₂).of_eq
    intro p
    simp only
    cases parent p.2.2.2 p.1 p.2.2.1 <;> rfl
  have h₂ : Primrec₂ (fun (p : BMSArray × Nat) j =>
      match maximalParentRow p.1 with
      | none => p.1.take j
      | some r => match parent r p.1 j with
        | none => p.1.take j
        | some k => p.1.take k ++ (List.range (p.2 + 1)).flatMap (fun i =>
            copyBlock p.1 (slice p.1 k (j - k)) r k i (p.1[j]?.getD []))) := by
    apply (option_elim (maximal_l.comp (fst.comp fst)) (list_take.comp snd (fst.comp fst))
      (h₁.comp (pair (fst.comp (fst.comp fst))
        (pair (snd.comp (fst.comp fst)) (pair (snd.comp fst) snd)))).to₂).to₂.of_eq
    intro p j
    simp only
    cases maximalParentRow p.1 <;> rfl
  apply (nat_casesOn (list_length.comp fst) (const []) h₂).to₂.of_eq
  intro a n
  cases h : a.length with
  | zero => simp [expandRaw, h]
  | succ j =>
      simp only [h, expandRaw]
      cases maximalParentRow a with
      | none => rfl
      | some r =>
          cases parent r a j <;> rfl

/-- 完整展开，包括实际底部零行裁剪。 -/
theorem expand_l : Primrec₂ expand := trim_l.comp₂ raw_l

private theorem run_raw (a : ValidArray) (s : List Nat) :
    (ArithmeticPresentation.run_l a s).raw = s.foldl expand a.raw := by
  induction s generalizing a with
  | nil => rfl
  | cons n s hᵢ => exact hᵢ (a.expand n)

/-- 执行有限轨迹的整个原始数组结果，而非仅解码出轨迹。 -/
theorem eval_l : Primrec (fun p => (ArithmeticPresentation.eval_l p).1.raw) := by
  apply (list_foldl snd (seed_l.comp fst)
    (expand_l.comp (fst.comp snd) (snd.comp snd)).to₂).of_eq
  intro p
  exact (run_raw (validSeed p.1) p.2).symm

/-- 当前总解码器的完整执行语义是原始递归。 -/
theorem decode_l : Primrec (fun n => (ArithmeticPresentation.decode_l n).1.raw) :=
  eval_l.comp trace_l

/-- 最终一步检查器的全部三个自然数参数均有实际原始递归证书。 -/
theorem check_l : Primrec (fun p : Nat × Nat × Nat =>
    ArithmeticPresentation.check_l p.1 p.2.1 p.2.2) :=
  ((Primrec.eq.comp (decode_l.comp fst)
    (expand_l.comp (decode_l.comp (fst.comp snd)) (snd.comp snd))).and
    (Primrec.eq.comp (decode_l.comp fst) (decode_l.comp (fst.comp snd))).not).decide

/-- 最小规范码的图可由有界的更小代码检查给出。 -/
theorem norm_graph_l (n m : Nat) :
    ArithmeticPresentation.norm_l n = m ↔
      (ArithmeticPresentation.decode_l m).1.raw = (ArithmeticPresentation.decode_l n).1.raw ∧
      ∀ k < m, (ArithmeticPresentation.decode_l k).1.raw ≠
        (ArithmeticPresentation.decode_l n).1.raw := by
  open ArithmeticPresentation in
    constructor
    · intro h
      subst m
      refine ⟨congrArg (fun a => a.1.raw) (decode_norm_l n), ?_⟩
      intro k h₀ h₁
      have h₂ := code_le_l (Subtype.ext (ValidArray.ext h₁))
      change norm_l n ≤ k at h₂
      omega
    · rintro ⟨h, h₀⟩
      have h₁ := code_le_l (Subtype.ext (ValidArray.ext h))
      change norm_l n ≤ m at h₁
      have h₂ : ¬ norm_l n < m := by
        intro h₂
        exact h₀ _ h₂ (congrArg (fun a => a.1.raw) (decode_norm_l n))
      omega

/-- 规范化只需在输入代码以下搜索，故也为原始递归，而非仅一般可计算。 -/
theorem norm_l : Primrec ArithmeticPresentation.norm_l := by
  have h : PrimrecRel (fun k n => (ArithmeticPresentation.decode_l k).1.raw ≠
      (ArithmeticPresentation.decode_l n).1.raw) :=
    (Primrec.eq.comp (decode_l.comp fst) (decode_l.comp snd)).not
  apply of_graph ⟨_, Primrec.id, ArithmeticPresentation.norm_le_l⟩
  apply ((Primrec.eq.comp (decode_l.comp snd) (decode_l.comp fst)).and
    (h.forall_lt.comp snd fst)).of_eq
  intro p
  exact (norm_graph_l p.1 p.2).symm

end YesMetaZFC.BMS.ConstructibleBridge.PrimitiveCoding
