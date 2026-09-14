import BMSConstructibleBridge.SecondOrderSyntax
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Closure
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Monotonicity
import YesMetaZFC.Logic.FirstOrder.Derivation.Soundness
import YesMetaZFC.Logic.FirstOrder.Metatheory.Equality.Basic

/-!
# 二阶算术的实际对象公理

以数和集合为两个排序，采用 Peano 算术公理、集合外延、集合归纳，以及允许
任意数／集合参数和任意二阶量词的完整理解方案。沿用已核验目标的签名槽位，
但配对、起点、一步关系既不获得公理，也不准进入理解方案正文；纯片段才是
这里的二阶算术背景。不会把标准模型真值或 BM4 良基性加入对象公理。

本文件建立对象理论及标准模型核验；不声称已给出 BM4 的对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderArithmetic

open Logic FirstOrder SecondOrderSyntax

set_option autoImplicit false

/-- 纯二阶语言检查，与只准数量词的算术矩阵检查不同。 -/
def language_m {Γ Δ : SortContext signature_m} : Formula signature_m Γ Δ → Bool
  | .falsum | .truth => true
  | .rel .mem s => pure_args_m s
  | .rel .start _ | .rel .step _ => false
  | .equal s t => pure_term_m s && pure_term_m t
  | .neg φ => language_m φ
  | .conj φ ψ | .disj φ ψ | .imp φ ψ | .iff φ ψ => language_m φ && language_m ψ
  | .forallE _ φ | .existsE _ φ => language_m φ

/-- 已消去额外符号的算术矩阵属于完整二阶语言。 -/
theorem pure_language_m {Γ Δ : SortContext signature_m} (φ : Formula signature_m Γ Δ)
    (h : pure_m φ = true) : language_m φ = true := by
  induction φ with
  | falsum | truth => rfl
  | rel r s => cases r <;> exact h
  | @equal Γ Δ s t u => cases s <;> simp_all [pure_m, language_m]
  | neg φ hᵢ => exact hᵢ h
  | conj φ ψ hᵢ hⱼ | disj φ ψ hᵢ hⱼ | imp φ ψ hᵢ hⱼ | iff φ ψ hᵢ hⱼ =>
      simp_all [pure_m, language_m]
  | forallE s φ hᵢ | existsE s φ hᵢ => cases s <;> simp_all [pure_m, language_m]

private def zero {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .zero .nil

private def succ {Γ Δ : SortContext signature_m} (t : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .succ (.cons t .nil)

private def add {Γ Δ : SortContext signature_m} (s t : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .add (.cons s (.cons t .nil))

private def mul {Γ Δ : SortContext signature_m} (s t : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .mul (.cons s (.cons t .nil))

private def mem {Γ Δ : SortContext signature_m}
    (n : Term signature_m Γ Δ .num) (X : Term signature_m Γ Δ .set) :
    Formula signature_m Γ Δ :=
  Formula.rel (σ := signature_m) .mem (.cons n (.cons X .nil))

/-- 固定的算术及集合基础公理种类；不包含 BM4 专用公理。 -/
inductive base_m where
  | nonzero | injective | predecessor | add_zero | add_succ | mul_zero | mul_succ
  | extensionality | induction

/-- 每种基础公理的实际闭句。 -/
def sentence_m : base_m → Sentence signature_m
  | .nonzero => .forallE .num (.neg (.equal (succ (.bvar .here)) zero))
  | .injective => .forallE .num (.forallE .num
      (.imp (.equal (succ (.bvar (.there .here))) (succ (.bvar .here)))
        (.equal (.bvar (.there .here)) (.bvar .here))))
  | .predecessor => .forallE .num (.disj (.equal (.bvar .here) zero)
      (.existsE .num (.equal (.bvar (.there .here)) (succ (.bvar .here)))))
  | .add_zero => .forallE .num (.equal (add (.bvar .here) zero) (.bvar .here))
  | .add_succ => .forallE .num (.forallE .num
      (.equal (add (.bvar (.there .here)) (succ (.bvar .here)))
        (succ (add (.bvar (.there .here)) (.bvar .here)))))
  | .mul_zero => .forallE .num (.equal (mul (.bvar .here) zero) zero)
  | .mul_succ => .forallE .num (.forallE .num
      (.equal (mul (.bvar (.there .here)) (succ (.bvar .here)))
        (add (mul (.bvar (.there .here)) (.bvar .here)) (.bvar (.there .here)))))
  | .extensionality => .forallE .set (.forallE .set
      (.imp (.forallE .num (.iff (mem (.bvar .here) (.bvar (.there (.there .here))))
        (mem (.bvar .here) (.bvar (.there .here)))))
        (.equal (.bvar (.there .here)) (.bvar .here))))
  | .induction => .forallE .set
      (.imp (.conj (mem zero (.bvar .here))
        (.forallE .num (.imp (mem (.bvar .here) (.bvar (.there .here)))
          (mem (succ (.bvar .here)) (.bvar (.there .here))))))
        (.forallE .num (mem (.bvar .here) (.bvar (.there .here)))))

private def bind {Δ : SortContext signature_m} :
    Substitution signature_m [] (.num :: Δ) [.num, .set] Δ :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => .bvar .here
    | .there v => .fvar v)

/-- 理解方案的正文：新集合不出现在给定的谓词中，参数完整保留。 -/
def comprehension_m {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) : Formula signature_m [] Δ :=
  .existsE .set (.forallE .num (.iff (mem (.bvar .here) (.bvar (.there .here)))
    (φ.substitute bind)))

/-- 纯二阶算术的对象公理集合；理解正文允许任意二阶量词复杂度。 -/
inductive axiom_m : Sentence signature_m → Prop
  | base (k : base_m) : axiom_m (sentence_m k)
  | comprehension {Δ : SortContext signature_m} (φ : Formula signature_m [] (.num :: Δ))
      (h : language_m φ = true) :
      axiom_m (Metatheory.Formula.forall_close (comprehension_m φ))

def theory_m : Theory signature_m := axiom_m

theorem base_pure_m (k : base_m) : language_m (sentence_m k) = true := by
  cases k <;> rfl

/-- 标准自然数和全部实数满足每条基础公理。 -/
theorem base_l (k : base_m) : (sentence_m k).TrueIn structure_l := by
  cases k <;> simp only [sentence_m, Formula.TrueIn, Formula.satisfies, zero, succ,
    add, mul, mem, Term.eval, Arguments.eval]
  · exact Nat.succ_ne_zero
  · intro n m h
    exact Nat.succ.inj h
  · intro n
    cases n with
    | zero => exact Or.inl rfl
    | succ n => exact Or.inr ⟨n, rfl⟩
  · exact Nat.add_zero
  · exact Nat.add_succ
  · exact Nat.mul_zero
  · exact Nat.mul_succ
  · intro X Y h
    exact Set.ext h
  · intro X h n
    exact Nat.rec h.1 (fun n h₀ => h.2 n h₀) n

private theorem bind_l {Δ : SortContext signature_m}
    (η : Env structure_l [] Δ) (X : Set Nat) (n : Nat)
    (φ : Formula signature_m [] (.num :: Δ)) :
    Formula.satisfies ((η.pushBound X).pushBound n) (φ.substitute bind) ↔
      Formula.satisfies (η.pushFree n) φ := by
  rw [Formula.satisfies_substitute]
  have h : (((η.pushBound X).pushBound n).pullback bind) = η.pushFree n := by
    apply Env.ext
    · intro s v
      cases v
    · intro s v
      cases v <;> rfl
  rw [h]

/-- 每个实例给出的集合确为给定谓词的外延；不存在隐藏的集合参数。 -/
theorem comprehension_l {Δ : SortContext signature_m}
    (η : Env structure_l [] Δ) (φ : Formula signature_m [] (.num :: Δ)) :
    Formula.satisfies η (comprehension_m φ) := by
  change ∃ X : Set Nat, ∀ n : Nat, n ∈ X ↔
    Formula.satisfies ((η.pushBound X).pushBound n) (φ.substitute bind)
  refine ⟨{n | Formula.satisfies (η.pushFree n) φ}, ?_⟩
  intro n
  exact (bind_l η _ n φ).symm

private theorem close_l {Δ : SortContext signature_m} (φ : Formula signature_m [] Δ)
    (h : ∀ η : Env structure_l [] Δ, Formula.satisfies η φ) :
    (Metatheory.Formula.forall_close φ).TrueIn structure_l := by
  induction Δ with
  | nil => exact h Env.empty
  | cons s Δ hᵢ =>
    apply hᵢ
    intro η
    rw [Formula.satisfies_forallFreeTop]
    exact fun x => h (η.pushFree x)

/-- 该对象理论有标准模型；这不把其全部标准真句加入公理。 -/
theorem models_l : Theory.Models structure_l theory_m := by
  intro φ h
  cases h with
  | base k => exact base_l k
  | comprehension φ _ => exact close_l _ (fun η => comprehension_l η φ)

/-- 实际对象理解实例的 Hilbert 推导；仅要求正文属于规定语言。 -/
theorem comprehension_derives_m {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) (h : language_m φ = true) :
    Derives theory_m [] (comprehension_m φ) :=
  Metatheory.Derives.forall_close_open _
    (Derives.theory_axiom (axiom_m.comprehension φ h))

/-- 不含元素的集合存在这一纯闭句。 -/
def empty_m : Sentence signature_m :=
  .existsE .set (.forallE .num (.neg (mem (.bvar .here) (.bvar (.there .here)))))

/-- 从理解实例和纯逻辑推出空集存在，不把结论加入对象公理。 -/
theorem empty_derives_m : Derives theory_m [] empty_m := by
  let ψ : Formula signature_m [] [.num, .set] := mem (.fvar .here) (.fvar (.there .here))
  have h : Derives theory_m ([] : Context signature_m [.num, .set])
      (.imp (.iff ψ .falsum) (.neg ψ)) := by
    apply Derives.imp_intro
    apply Derives.neg_intro
    exact Derives.iff_elim_left (Derives.assumption (by simp))
      (Derives.assumption List.mem_cons_self)
  have h₁ := Metatheory.Derives.forall_imp_mono (σ := signature_m)
    (free := [.set]) (sort := sort_m.num) (Γ := []) h
  have h₂ := Metatheory.Derives.exists_imp_mono (σ := signature_m)
    (free := []) (sort := sort_m.set) (Γ := []) h₁
  change Derives theory_m []
    (.imp (comprehension_m (.falsum : Formula signature_m [] [.num])) empty_m) at h₂
  exact Derives.imp_elim h₂ (comprehension_derives_m .falsum rfl)

private def next {Δ : SortContext signature_m} :
    VariableSubstitution signature_m (.num :: Δ) [] (.num :: Δ) :=
  VariableSubstitution.cons (succ (.fvar .here))
    (VariableSubstitution.of_renaming (VariableRenaming.weaken sort_m.num))

/-- 任意带参数二阶公式的归纳实例；后继实例使用无捕获的统一替换。 -/
def induction_m {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) : Formula signature_m [] Δ :=
  .imp (.conj (φ.instantiateFreeTop zero)
    ((Formula.imp φ (φ.substituteFree next)).forallFreeTop sort_m.num))
    (φ.forallFreeTop sort_m.num)

private theorem inst {Δ : SortContext signature_m} {T : Theory signature_m}
    {Γ : Context signature_m Δ} {φ : Formula signature_m [] (.num :: Δ)}
    (t : Term signature_m [] Δ .num) (h : Derives T Γ (φ.forallFreeTop sort_m.num)) :
    Derives T Γ (φ.instantiateFreeTop t) := by
  simpa only [Formula.forallFreeTop, Formula.instantiateTop_abstractFreeTop] using
    Derives.forall_elim t h

private def insert {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) : Formula signature_m [] (.num :: .set :: Δ) :=
  φ.renameFree (VariableRenaming.lift (introduced := sort_m.num)
    (VariableRenaming.weaken sort_m.set))

private def extension {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) : Formula signature_m [] (.set :: Δ) :=
  (Formula.iff (mem (.fvar .here) (.fvar (.there .here))) (insert φ)).forallFreeTop sort_m.num

private theorem comprehension_eq {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) :
    comprehension_m φ = (extension φ).existsFreeTop sort_m.set := by
  unfold comprehension_m extension Formula.existsFreeTop Formula.forallFreeTop
  change Formula.existsE _ (Formula.forallE _ (.iff _ (φ.substitute bind))) =
    Formula.existsE _ (Formula.forallE _ (.iff _ _))
  congr 3
  change φ.substituteMapped _ _ =
    ((φ.renameMapped _ _).substituteMapped _ _).substituteMapped _ _
  rw [← Formula.substituteMapped_of_renaming, Formula.substituteMapped_comp,
    Formula.substituteMapped_comp]
  congr 1
  · funext s v
    cases v
  · funext s v
    cases v <;> rfl

private theorem insert_zero {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) :
    (insert φ).instantiateFreeTop zero = (φ.instantiateFreeTop zero).weakenFree sort_m.set := by
  change (φ.renameMapped _ _).substituteMapped _ _ =
    (φ.substituteMapped _ _).renameMapped _ _
  rw [← Formula.substituteMapped_of_renaming, ← Formula.substituteMapped_of_renaming,
    Formula.substituteMapped_comp, Formula.substituteMapped_comp]
  congr 1
  funext s v
  cases v <;> rfl

private theorem insert_next {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) :
    (insert φ).substituteFree next = insert (φ.substituteFree next) := by
  change (φ.renameMapped _ _).substituteMapped _ _ =
    (φ.substituteMapped _ _).renameMapped _ _
  rw [← Formula.substituteMapped_of_renaming, ← Formula.substituteMapped_of_renaming,
    Formula.substituteMapped_comp, Formula.substituteMapped_comp]
  congr 1
  funext s v
  cases v <;> rfl

private theorem insert_forall {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) :
    (insert φ).forallFreeTop sort_m.num =
      Formula.weakenFree (σ := signature_m) sort_m.set (φ.forallFreeTop sort_m.num) := by
  exact (Formula.renameMapped_forallFreeTop (VariableRenaming.weaken sort_m.set) φ).symm

private theorem insert_induction {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) :
    induction_m (insert φ) = (induction_m φ).weakenFree sort_m.set := by
  simp only [induction_m, insert_zero, insert_forall, insert_next]
  change Formula.imp _ _ = Formula.imp _ _
  congr 2
  exact insert_forall (.imp φ (φ.substituteFree next))

private theorem next_eq {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) :
    (φ.abstractFreeTop.weakenFree sort_m.num).instantiateTop (succ (.fvar .here)) =
      φ.substituteFree next := by
  change ((φ.substituteMapped _ _).renameMapped _ _).substituteMapped _ _ =
    φ.substituteMapped _ _
  rw [← Formula.substituteMapped_of_renaming, Formula.substituteMapped_comp,
    Formula.substituteMapped_comp]
  congr 1
  all_goals
    funext s v
    cases v <;> rfl

private theorem inst_next {Δ : SortContext signature_m} {T : Theory signature_m}
    {Γ : Context signature_m Δ} {φ : Formula signature_m [] (.num :: Δ)}
    (h : Derives T Γ (φ.forallFreeTop sort_m.num)) :
    Derives T (FreshVariable.extendContext sort_m.num Γ) (φ.substituteFree next) := by
  have h₁ := Derives.free_renaming (VariableRenaming.weaken sort_m.num) h
  have h₂ := Derives.forall_elim (succ (.fvar .here)) h₁
  simp only [VariableRenaming.lift_id] at h₂
  change Derives T _ ((φ.abstractFreeTop.weakenFree sort_m.num).instantiateTop _) at h₂
  rwa [next_eq] at h₂

private theorem induction_transfer {Δ : SortContext signature_m} {T : Theory signature_m}
    {Γ : Context signature_m Δ} {φ ψ : Formula signature_m [] (.num :: Δ)}
    (h : Derives T Γ ((Formula.iff φ ψ).forallFreeTop sort_m.num))
    (hᵢ : Derives T Γ (induction_m φ)) : Derives T Γ (induction_m ψ) := by
  apply Derives.imp_intro
  let θ := Formula.conj (ψ.instantiateFreeTop zero)
    ((Formula.imp ψ (ψ.substituteFree next)).forallFreeTop sort_m.num)
  have h₀ := Derives.context_weaken_cons (assumption := θ) h
  have h₁ : Derives T (θ :: Γ) (ψ.instantiateFreeTop zero) :=
    Derives.conj_elim_left (Derives.assumption List.mem_cons_self)
  have h₂ : Derives T (θ :: Γ)
      ((Formula.imp ψ (ψ.substituteFree next)).forallFreeTop sort_m.num) :=
    Derives.conj_elim_right (Derives.assumption List.mem_cons_self)
  have h₃ : Derives T (θ :: Γ) (φ.instantiateFreeTop zero) :=
    Derives.iff_elim_right (inst zero h₀) h₁
  have h₄ : Derives T (θ :: Γ)
      ((Formula.imp φ (φ.substituteFree next)).forallFreeTop sort_m.num) := by
    apply Derives.forall_intro
    apply Derives.imp_intro
    have h₅ := Derives.context_weaken_cons (assumption := φ)
      (Derives.forall_elim_newest h₀)
    have h₆ := Derives.iff_elim_left h₅ (Derives.assumption List.mem_cons_self)
    have h₇ := Derives.imp_elim
      (Derives.context_weaken_cons (Derives.forall_elim_newest h₂)) h₆
    exact Derives.iff_elim_right (Derives.context_weaken_cons (inst_next h₀)) h₇
  have h₅ := Derives.imp_elim (Derives.context_weaken_cons hᵢ)
    (Derives.conj_intro h₃ h₄)
  apply Derives.forall_intro
  exact Derives.iff_elim_left (Derives.forall_elim_newest h₀)
    (Derives.forall_elim_newest h₅)

private theorem mem_induction {Δ : SortContext signature_m}
    {Γ : Context signature_m (.set :: Δ)} : Derives theory_m Γ
      (induction_m (mem (.fvar .here) (.fvar (.there .here)))) := by
  have h : Derives theory_m Γ (Formula.fromSentence (sentence_m .induction)) :=
    Derives.theory_axiom (axiom_m.base .induction)
  exact Derives.forall_elim (.fvar .here) h

/-- 完整公式归纳由理解及集合归纳推出，允许任意二阶量词及混合参数。 -/
theorem induction_derives_m {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) (h : language_m φ = true) :
    Derives theory_m [] (induction_m φ) := by
  have h₀ := comprehension_derives_m φ h
  rw [comprehension_eq] at h₀
  apply Derives.exists_elim h₀
  rw [← insert_induction]
  exact induction_transfer (Derives.assumption List.mem_cons_self) mem_induction

/-- 直接使用公式归纳的推导规则；局部假设整体移入规范新变量上下文。 -/
theorem induction_rule_m {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
    {φ : Formula signature_m [] (.num :: Δ)} (h : language_m φ = true)
    (h₀ : Derives theory_m Γ (φ.instantiateFreeTop zero))
    (h₁ : Derives theory_m (FreshVariable.extendContext sort_m.num Γ)
      (.imp φ (φ.substituteFree next))) :
    Derives theory_m Γ (φ.forallFreeTop sort_m.num) :=
  Derives.imp_elim (Derives.of_provable (induction_derives_m φ h))
    (Derives.conj_intro h₀ (Derives.forall_intro h₁))

private theorem add_zero {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
    (t : Term signature_m [] Δ .num) : Derives theory_m Γ (.equal (add t zero) t) := by
  have h : Derives theory_m Γ
      (.forallE .num (.equal (add (.bvar .here) zero) (.bvar .here))) := by
    cases Δ <;> exact Derives.theory_axiom (axiom_m.base .add_zero)
  exact Derives.forall_elim t h

private theorem add_succ {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
    (s t : Term signature_m [] Δ .num) :
    Derives theory_m Γ (.equal (add s (succ t)) (succ (add s t))) := by
  have h : Derives theory_m Γ (.forallE .num (.forallE .num
    (.equal (add (.bvar (.there .here)) (succ (.bvar .here)))
      (succ (add (.bvar (.there .here)) (.bvar .here)))))) := by
    cases Δ <;> exact Derives.theory_axiom (axiom_m.base .add_succ)
  have h₁ := Derives.forall_elim s h
  change Derives theory_m Γ (.forallE .num
    (.equal (add (s.weakenBound sort_m.num) (succ (.bvar .here)))
      (succ (add (s.weakenBound sort_m.num) (.bvar .here))))) at h₁
  have h₂ := Derives.forall_elim t h₁
  simp only [add, succ, Formula.instantiateTop_equal, Term.instantiateTop_app,
    Arguments.instantiateTop_cons, Arguments.instantiateTop_nil,
    Term.instantiateTop_weakenBound] at h₂
  exact h₂

private theorem succ_congr {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
    {s t : Term signature_m [] Δ .num} (h : Derives theory_m Γ (.equal s t)) :
    Derives theory_m Γ (.equal (succ s) (succ t)) :=
  Metatheory.Derives.term_context_congr_of_equality (succ (.bvar .here)) h

/-- 任意两个数码的加法计算都有对象推导，不调用标准模型真值反推可证性。 -/
theorem numeral_add_m {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
    (m n : Nat) : Derives theory_m Γ
      (.equal (add (numeral_m m) (numeral_m n)) (numeral_m (m + n))) := by
  induction n with
  | zero => exact add_zero _
  | succ n hᵢ => exact Derives.eq_trans (add_succ _ _) (succ_congr hᵢ)

private theorem mul_zero {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
    (t : Term signature_m [] Δ .num) : Derives theory_m Γ (.equal (mul t zero) zero) := by
  have h : Derives theory_m Γ (.forallE .num (.equal (mul (.bvar .here) zero) zero)) := by
    cases Δ <;> exact Derives.theory_axiom (axiom_m.base .mul_zero)
  exact Derives.forall_elim t h

private theorem mul_succ {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
    (s t : Term signature_m [] Δ .num) :
    Derives theory_m Γ (.equal (mul s (succ t)) (add (mul s t) s)) := by
  have h : Derives theory_m Γ (.forallE .num (.forallE .num
      (.equal (mul (.bvar (.there .here)) (succ (.bvar .here)))
        (add (mul (.bvar (.there .here)) (.bvar .here)) (.bvar (.there .here)))))) := by
    cases Δ <;> exact Derives.theory_axiom (axiom_m.base .mul_succ)
  have h₁ := Derives.forall_elim s h
  change Derives theory_m Γ (.forallE .num
    (.equal (mul (s.weakenBound sort_m.num) (succ (.bvar .here)))
      (add (mul (s.weakenBound sort_m.num) (.bvar .here)) (s.weakenBound sort_m.num)))) at h₁
  have h₂ := Derives.forall_elim t h₁
  simp only [mul, add, succ, Formula.instantiateTop_equal, Term.instantiateTop_app,
    Arguments.instantiateTop_cons, Arguments.instantiateTop_nil,
    Term.instantiateTop_weakenBound] at h₂
  exact h₂

private theorem add_left {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
    {s t : Term signature_m [] Δ .num} (u : Term signature_m [] Δ .num)
    (h : Derives theory_m Γ (.equal s t)) :
    Derives theory_m Γ (.equal (add s u) (add t u)) := by
  have h₁ := Metatheory.Derives.term_context_congr_of_equality
    (add (.bvar .here) (u.weakenBound sort_m.num)) h
  simp only [add, Term.instantiateTop_app, Arguments.instantiateTop_cons,
    Arguments.instantiateTop_nil, Term.instantiateTop_weakenBound] at h₁
  exact h₁

/-- 任意两个数码的乘法计算由递推公理和已经核验的数码加法推出。 -/
theorem numeral_mul_m {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
    (m n : Nat) : Derives theory_m Γ
      (.equal (mul (numeral_m m) (numeral_m n)) (numeral_m (m * n))) := by
  induction n with
  | zero => exact mul_zero _
  | succ n hᵢ =>
      exact Derives.eq_trans (mul_succ _ _)
        (Derives.eq_trans (add_left _ hᵢ) (numeral_add_m _ _))

/-- 左零律由对象公式归纳推出；此处的数可以是非标准模型中的任意元素。 -/
theorem zero_add_m {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
    (t : Term signature_m [] Δ .num) : Derives theory_m Γ (.equal (add zero t) t) := by
  let φ : Formula signature_m [] (.num :: Δ) :=
    .equal (add zero (.fvar .here)) (.fvar .here)
  have h : Derives theory_m Γ (φ.forallFreeTop sort_m.num) := by
    apply induction_rule_m (φ := φ) rfl
    · exact add_zero zero
    · apply Derives.imp_intro
      exact Derives.eq_trans (add_succ zero (.fvar .here))
        (succ_congr (Derives.assumption List.mem_cons_self))
  exact inst t h

private theorem nonzero {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
    (t : Term signature_m [] Δ .num) : Derives theory_m Γ (.neg (.equal (succ t) zero)) := by
  have h : Derives theory_m Γ (.forallE .num (.neg (.equal (succ (.bvar .here)) zero))) := by
    cases Δ <;> exact Derives.theory_axiom (axiom_m.base .nonzero)
  exact Derives.forall_elim t h

private theorem injective {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
    (s t : Term signature_m [] Δ .num) :
    Derives theory_m Γ (.imp (.equal (succ s) (succ t)) (.equal s t)) := by
  have h : Derives theory_m Γ (.forallE .num (.forallE .num
    (.imp (.equal (succ (.bvar (.there .here))) (succ (.bvar .here)))
      (.equal (.bvar (.there .here)) (.bvar .here))))) := by
    cases Δ <;> exact Derives.theory_axiom (axiom_m.base .injective)
  have h₁ := Derives.forall_elim s h
  change Derives theory_m Γ (.forallE .num
    (.imp (.equal (succ (s.weakenBound sort_m.num)) (succ (.bvar .here)))
      (.equal (s.weakenBound sort_m.num) (.bvar .here)))) at h₁
  have h₂ := Derives.forall_elim t h₁
  simp only [succ, Formula.instantiateTop_imp, Formula.instantiateTop_equal,
    Term.instantiateTop_app, Arguments.instantiateTop_cons, Arguments.instantiateTop_nil,
    Term.instantiateTop_weakenBound] at h₂
  exact h₂

/-- 不同数码的不等式具有对象推导，归纳覆盖所有自然数输入。 -/
theorem numeral_ne_m {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
    (m n : Nat) (h : m ≠ n) : Derives theory_m Γ
      (.neg (.equal (numeral_m m) (numeral_m n))) := by
  induction m generalizing n with
  | zero =>
      cases n with
      | zero => exact False.elim (h rfl)
      | succ n =>
          apply Derives.neg_intro
          exact Derives.neg_elim (Derives.eq_symm
            (Derives.assumption List.mem_cons_self)) (nonzero _)
  | succ m hᵢ =>
      cases n with
      | zero => exact nonzero _
      | succ n =>
          apply Derives.neg_intro
          exact Derives.neg_elim
            (Derives.imp_elim (injective _ _) (Derives.assumption List.mem_cons_self))
            (Derives.context_weaken_cons (hᵢ n (by omega)))

private theorem add_congr {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
    {s t u v : Term signature_m [] Δ .num}
    (h : Derives theory_m Γ (.equal s t)) (h₁ : Derives theory_m Γ (.equal u v)) :
    Derives theory_m Γ (.equal (add s u) (add t v)) := by
  have h₂ := Metatheory.Derives.term_context_congr_of_equality
    (add (t.weakenBound sort_m.num) (.bvar .here)) h₁
  simp only [add, Term.instantiateTop_app, Arguments.instantiateTop_cons,
    Arguments.instantiateTop_nil, Term.instantiateTop_weakenBound] at h₂
  exact Derives.eq_trans (add_left _ h) h₂

private theorem mul_congr {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
    {s t u v : Term signature_m [] Δ .num}
    (h : Derives theory_m Γ (.equal s t)) (h₁ : Derives theory_m Γ (.equal u v)) :
    Derives theory_m Γ (.equal (mul s u) (mul t v)) := by
  have h₂ := Metatheory.Derives.term_context_congr_of_equality
    (mul (.bvar .here) (u.weakenBound sort_m.num)) h
  have h₃ := Metatheory.Derives.term_context_congr_of_equality
    (mul (t.weakenBound sort_m.num) (.bvar .here)) h₁
  simp only [mul, Term.instantiateTop_app, Arguments.instantiateTop_cons,
    Arguments.instantiateTop_nil, Term.instantiateTop_weakenBound] at h₂ h₃
  exact Derives.eq_trans h₂ h₃

/-- 纯闭算术项的实际求值可编译成对象等式推导；不包含未定义的配对符号。 -/
theorem eval_derives_m {Γ : Context signature_m []} (t : Term signature_m [] [] .num)
    (h : pure_term_m t = true) : Derives theory_m Γ
      (.equal t (numeral_m (Term.eval (Env.empty (M := structure_l)) t))) := by
  match t with
  | .bvar v => cases v
  | .fvar v => cases v
  | .app func_m.zero .nil => exact Derives.eq_refl _
  | .app func_m.succ (.cons s .nil) =>
      change (pure_term_m s && true) = true at h
      simp only [Bool.and_true] at h
      exact succ_congr (eval_derives_m s h)
  | .app func_m.add (.cons s (.cons t .nil)) =>
      change (pure_term_m s && (pure_term_m t && true)) = true at h
      simp only [Bool.and_true, Bool.and_eq_true] at h
      exact Derives.eq_trans (add_congr (eval_derives_m s h.1) (eval_derives_m t h.2))
        (numeral_add_m _ _)
  | .app func_m.mul (.cons s (.cons t .nil)) =>
      change (pure_term_m s && (pure_term_m t && true)) = true at h
      simp only [Bool.and_true, Bool.and_eq_true] at h
      exact Derives.eq_trans (mul_congr (eval_derives_m s h.1) (eval_derives_m t h.2))
        (numeral_mul_m _ _)
  | .app func_m.pair _ => contradiction
termination_by t.size
decreasing_by
  all_goals
    simp only [Term.size, Arguments.size]
    omega

/-- 在宿主元理论中由标准模型证明对象系统一致；不是 `Z₂` 内的自一致性证明。 -/
theorem consistent_m : ¬Derives theory_m [] (.falsum : Sentence signature_m) := by
  intro h
  exact h.sound models_l Env.empty (by intro φ h; cases h)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderArithmetic
