import BMSConstructibleBridge.PowerlessBMSPrefixRepresentation

/-!
# 内部副本数上的真实标签状态归纳

状态保留当前低标签前缀、固定坏块及其真实拼接，并在同一个最终数组上保存前缀表示。
长度直接取同一算术结构中的 p+d·copy 与 p+d·(copy+1)。纯公式以实际加乘后继图
绑定这些中间值；有界归纳只在该公式上应用内部 ω 归纳，不使用宿主自然数归纳。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSCopyState

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessArithmetic.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {ω e : carrier_l ℳ} {he : PowerlessNatural.zero_l e} {h₀ : member_l ℳ e ω}
  {F : PowerlessArithmetic.operations_l ω e}

local notation "𝒩" => PowerlessArithmetic.structure_l he h₀ F
local notation "add" => SecondOrderModel.add_l (ℳ := 𝒩)
local notation "mul" => SecondOrderModel.mul_l (ℳ := 𝒩)
local notation "succ" => SecondOrderModel.succ_l (ℳ := 𝒩)

/-- 低标签前缀和固定坏块的拼接，是最终数组当前已标号前缀的真实表示。 -/
def state_l (T t₁ t₂ t₃ c N : carrier_l ℳ) (H : Nat)
    (y p d : PowerlessArithmetic.num_l ω) (α β g : carrier_l ℳ)
    (copy : PowerlessArithmetic.num_l ω) : Prop :=
  ∃ f old, map_l f (add p (mul d copy)).val α ∧
    PowerlessConcatenation.graph_l ω e (add p (mul d copy)).val f g old ∧
    PowerlessBMSPrefixRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
      T t₁ t₂ t₃ c N H y (add p (mul d (succ copy))) β old

private def coordinate_l (ω e p d copy q : carrier_l ℳ) : Prop :=
  ∃ u, PowerlessMultiplication.multiplication_l ω e d copy u ∧
    PowerlessAddition.addition_l ω e p u q

private def coordinate_m {Γ Δ : SortContext ℒ}
    (ω e p d copy q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set (.conj
    (PowerlessMultiplication.multiplication_m (ω.weakenBound SetTheory.SetSort.set)
      (e.weakenBound SetTheory.SetSort.set) (d.weakenBound SetTheory.SetSort.set)
      (copy.weakenBound SetTheory.SetSort.set) (.bvar .here))
    (PowerlessAdditionSyntax.addition_m (ω.weakenBound SetTheory.SetSort.set)
      (e.weakenBound SetTheory.SetSort.set) (p.weakenBound SetTheory.SetSort.set)
      (.bvar .here) (q.weakenBound SetTheory.SetSort.set)))

private theorem coordinate_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (w z p d copy q : Term ℒ Γ Δ .set) :
    (coordinate_m w z p d copy q).satisfies η ↔
      coordinate_l (w.eval η) (z.eval η) (p.eval η) (d.eval η) (copy.eval η) (q.eval η) := by
  simp only [coordinate_m, coordinate_l, Formula.satisfies,
    PowerlessMultiplication.multiplication_formula_l, PowerlessAdditionSyntax.addition_formula_l,
    Term.eval_weakenBound]
  rfl

private theorem coordinate_value_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (hω : omega_l ω) (p d copy : PowerlessArithmetic.num_l ω) (q : carrier_l ℳ) :
    coordinate_l ω e p.val d.val copy.val q ↔ q = (add p (mul d copy)).val := by
  constructor
  · rintro ⟨u, hu, hq⟩
    have hu₀ := PowerlessMultiplication.unique_l hℳ hω he hu (F.mul_graph_l d copy)
    subst u
    exact PowerlessAddition.unique_l hℳ hω he hq (F.add_graph_l p (F.mul_l d copy))
  · intro hq
    exact ⟨(F.mul_l d copy).val, F.mul_graph_l d copy, hq.symm ▸ F.add_graph_l p (F.mul_l d copy)⟩

private def graphs_m {Γ Δ : SortContext ℒ} (H : Nat)
    (ω e T t₁ t₂ t₃ c N y p q α β g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) :=
    (t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .existsE .set (.existsE .set (.conj
    (SecondOrderObjectSyntax.map_m (.bvar (.there .here)) (w p) (w α))
    (.conj (PowerlessConcatenation.graph_m (w ω) (w e) (w p)
      (.bvar (.there .here)) (w g) (.bvar .here))
      (PowerlessBMSPrefixRepresentation.representation_m H (w ω) (w e) (w T)
        (w t₁) (w t₂) (w t₃) (w c) (w N) (w y) (w q) (w β) (.bvar .here)))))

private theorem graphs_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (hω : omega_l ω) {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (H : Nat)
    (w z T t₁ t₂ t₃ c N a b v α β g : Term ℒ Γ Δ .set)
    (y p q : PowerlessArithmetic.num_l ω)
    (hw : w.eval η = ω) (hz : z.eval η = e) (ha : a.eval η = y.val)
    (hb : b.eval η = p.val) (hv : v.eval η = q.val) :
    (graphs_m H w z T t₁ t₂ t₃ c N a b v α β g).satisfies η ↔
      ∃ f old, map_l f p.val (α.eval η) ∧
        PowerlessConcatenation.graph_l ω e p.val f (g.eval η) old ∧
        PowerlessBMSPrefixRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
          (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (c.eval η) (N.eval η)
          H y q (β.eval η) old := by
  simp only [graphs_m, Formula.satisfies, map_formula_l, PowerlessConcatenation.graph_formula_l]
  apply exists_congr
  intro f
  apply exists_congr
  intro old
  rw [PowerlessBMSPrefixRepresentation.formula_l hℳ hω (he := he) (h₀ := h₀) (F := F)
    _ H _ _ _ _ _ _ _ _ _ _ _ _ y q
    (by simpa only [Term.eval_weakenBound] using hw)
    (by simpa only [Term.eval_weakenBound] using hz)
    (by simpa only [Term.eval_weakenBound] using ha)
    (by simpa only [Term.eval_weakenBound] using hv)]
  simp only [Term.eval_weakenBound, hw, hz, hb]
  rfl

/-- 中间长度和后继数均由已有纯算术图量化，未增加新的语言符号。 -/
def state_m {Γ Δ : SortContext ℒ} (H : Nat)
    (ω e T t₁ t₂ t₃ c N y p d α β g copy : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) :=
    ((t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .existsE .set (.existsE .set (.existsE .set (.conj
    (coordinate_m (w ω) (w e) (w p) (w d) (w copy) (.bvar (.there (.there .here))))
    (.conj (PowerlessNaturalStep.successor_m (w copy) (.bvar (.there .here)))
      (.conj (coordinate_m (w ω) (w e) (w p) (w d) (.bvar (.there .here)) (.bvar .here))
        (graphs_m H (w ω) (w e) (w T) (w t₁) (w t₂) (w t₃) (w c) (w N) (w y)
          (.bvar (.there (.there .here))) (.bvar .here) (w α) (w β) (w g)))))))

/-- 状态公式对任意项环境精确保持实际长度、拼接以及所有祖先边条件。 -/
theorem formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (H : Nat)
    (w z T t₁ t₂ t₃ c N a b v α β g i : Term ℒ Γ Δ .set)
    (y p d copy : PowerlessArithmetic.num_l ω)
    (hw : w.eval η = ω) (hz : z.eval η = e) (ha : a.eval η = y.val)
    (hb : b.eval η = p.val) (hv : v.eval η = d.val) (hi : i.eval η = copy.val) :
    (state_m H w z T t₁ t₂ t₃ c N a b v α β g i).satisfies η ↔
      state_l (he := he) (h₀ := h₀) (F := F) (T.eval η) (t₁.eval η) (t₂.eval η)
        (t₃.eval η) (c.eval η) (N.eval η) H y p d (α.eval η) (β.eval η) (g.eval η) copy := by
  simp only [state_m, Formula.satisfies, coordinate_formula_l,
    PowerlessNaturalStep.successor_formula_l, Term.eval_weakenBound, hw, hz, hb, hv, hi]
  let w₃ (t : Term ℒ Γ Δ .set) :=
    ((t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  constructor
  · rintro ⟨q, s, r, hq, hs, hr, hG⟩
    change coordinate_l ω e p.val d.val copy.val q at hq
    change PowerlessNatural.successor_l copy.val s at hs
    change coordinate_l ω e p.val d.val s r at hr
    have hq₀ := (coordinate_value_l (he := he) (h₀ := h₀) (F := F) hℳ hω p d copy q).mp hq
    have hs₀ := PowerlessNatural.successor_unique_l hℳ hs (F.succ_graph_l copy)
    have hr₀ := (coordinate_value_l (he := he) (h₀ := h₀) (F := F) hℳ hω p d (succ copy) r).mp
      (by simpa only [SecondOrderModel.succ_l, PowerlessArithmetic.structure_l, hs₀] using hr)
    have h := (graphs_formula_l hℳ hω (he := he) (h₀ := h₀) (F := F)
      (((η.pushBound q).pushBound s).pushBound r) H
      (w₃ w) (w₃ z) (w₃ T) (w₃ t₁) (w₃ t₂) (w₃ t₃) (w₃ c) (w₃ N) (w₃ a)
      (.bvar (.there (.there .here))) (.bvar .here) (w₃ α) (w₃ β) (w₃ g)
      y (add p (mul d copy)) (add p (mul d (succ copy)))
      (by simpa only [w₃, Term.eval_weakenBound] using hw)
      (by simpa only [w₃, Term.eval_weakenBound] using hz)
      (by simpa only [w₃, Term.eval_weakenBound] using ha) hq₀ hr₀).mp hG
    simpa only [state_l, w₃, Term.eval_weakenBound] using h
  · intro h
    refine ⟨(add p (mul d copy)).val, (succ copy).val, (add p (mul d (succ copy))).val,
      (coordinate_value_l (he := he) (h₀ := h₀) (F := F) hℳ hω p d copy _).mpr rfl,
      F.succ_graph_l copy,
      (coordinate_value_l (he := he) (h₀ := h₀) (F := F) hℳ hω p d (succ copy) _).mpr rfl, ?_⟩
    apply (graphs_formula_l hℳ hω (he := he) (h₀ := h₀) (F := F)
      _ H (w₃ w) (w₃ z) (w₃ T) (w₃ t₁) (w₃ t₂) (w₃ t₃) (w₃ c) (w₃ N) (w₃ a)
      (.bvar (.there (.there .here))) (.bvar .here) (w₃ α) (w₃ β) (w₃ g)
      y (add p (mul d copy)) (add p (mul d (succ copy)))
      (by simpa only [w₃, Term.eval_weakenBound] using hw)
      (by simpa only [w₃, Term.eval_weakenBound] using hz)
      (by simpa only [w₃, Term.eval_weakenBound] using ha) rfl rfl).mpr
    simpa only [state_l, w₃, Term.eval_weakenBound] using h

/-- 有界副本归纳在模型的真实内部 ω 上进行；可覆盖非标准副本数。 -/
theorem bounded_induction_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    (T t₁ t₂ t₃ c N : carrier_l ℳ) (H : Nat) (y p d : PowerlessArithmetic.num_l ω)
    (α β g : carrier_l ℳ) (k : PowerlessArithmetic.num_l ω)
    (hbase : state_l (he := he) (h₀ := h₀) (F := F) T t₁ t₂ t₃ c N H y p d α β g
      (SecondOrderModel.zero_l 𝒩))
    (hstep : ∀ copy, SecondOrderOrder.lt_l (ℳ := 𝒩) copy k →
      state_l (he := he) (h₀ := h₀) (F := F) T t₁ t₂ t₃ c N H y p d α β g copy →
      state_l (he := he) (h₀ := h₀) (F := F) T t₁ t₂ t₃ c N H y p d α β g (succ copy)) :
    state_l (he := he) (h₀ := h₀) (F := F) T t₁ t₂ t₃ c N H y p d α β g k := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 15 :=
    { bound := Fin.cases ω (Fin.cases e (Fin.cases T (Fin.cases t₁ (Fin.cases t₂
        (Fin.cases t₃ (Fin.cases c (Fin.cases N (Fin.cases y.val (Fin.cases p.val
          (Fin.cases d.val (Fin.cases α (Fin.cases β (Fin.cases g (fun _ => k.val)))))))))))))),
      free := fun _ => ω }
  let v (i : Fin 15) : Term ℒ [] (.set :: List.replicate 15 .set) .set :=
    .fvar (.there (SetTheory.Definitional.Project.fo_bound_variable i))
  let φ : Formula ℒ [] (.set :: List.replicate 15 .set) :=
    .imp (PowerlessNaturalCompare.le_m (.fvar .here) (v 14))
      (state_m H (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)
        (v 8) (v 9) (v 10) (v 11) (v 12) (v 13) (.fvar .here))
  have hφ (a : PowerlessArithmetic.num_l ω) :
      φ.satisfies ((PowerlessComprehension.env_l η).pushFree a.val) ↔
        ((member_l ℳ a.val k.val ∨ a.val = k.val) →
          state_l (he := he) (h₀ := h₀) (F := F) T t₁ t₂ t₃ c N H y p d α β g a) := by
    change ((PowerlessNaturalCompare.le_m _ _).satisfies _ → (state_m H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).satisfies _) ↔ _
    rw [PowerlessNaturalCompare.le_formula_l,
      formula_l hℳ hω (he := he) (h₀ := h₀) (F := F) _ H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ y p d a
        rfl rfl rfl rfl rfl rfl]
    rfl
  have hI := PowerlessNatural.induction_l hℳ φ η hω
    (fun z hz => by
      have hz₀ := PowerlessNatural.zero_unique_l hℳ hz he
      subst z
      exact (hφ ⟨e, h₀⟩).mpr (fun _ => hbase))
    (fun a b ha hb hI => by
      let copy : PowerlessArithmetic.num_l ω := ⟨a, ha⟩
      have hb₀ : (succ copy).val = b := PowerlessNatural.successor_unique_l hℳ (F.succ_graph_l copy) hb
      rw [← hb₀]
      apply (hφ (succ copy)).mpr
      intro hbound
      have hak : member_l ℳ a k.val := by
        have hab : member_l ℳ a (succ copy).val := (F.succ_graph_l copy a).mpr (Or.inr rfl)
        rcases hbound with hbk | hbk
        · exact PowerlessNaturalOrder.member_transitive_l hℳ hω k.val k.property (succ copy).val a hbk hab
        · exact hbk ▸ hab
      exact hstep copy ((PowerlessArithmeticOrder.lt_l hℳ hω (he := he) (h₀ := h₀) (F := F) copy k).mpr hak)
        ((hφ copy).mp hI (Or.inl hak)))
  exact (hφ k).mp (hI k.val k.property) (Or.inr rfl)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSCopyState
