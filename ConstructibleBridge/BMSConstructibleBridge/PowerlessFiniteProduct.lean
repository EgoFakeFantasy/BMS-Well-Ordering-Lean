import BMSConstructibleBridge.PowerlessTheory
import BMSConstructibleBridge.PowerlessBasic
import BMSConstructibleBridge.PowerlessComprehension
import BMSConstructibleBridge.PowerlessProduct
import BMSConstructibleBridge.PowerlessMapping
import BMSConstructibleBridge.PowerlessFunction
import BMSConstructibleBridge.PowerlessNatural
import BMSConstructibleBridge.PowerlessNaturalOrder
import BMSConstructibleBridge.PowerlessAddition
import BMSConstructibleBridge.PowerlessAdditionSyntax
import BMSConstructibleBridge.PowerlessAdditionLaws
import BMSConstructibleBridge.PowerlessAdditionOrder
import BMSConstructibleBridge.PowerlessAdditionBounds

/-!
# 内部有限笛卡尔积的实际枚举

对 p, q ∈ ω 与实际乘积集 P = p×q，构造一个以内部自然数为定义域的原函数 f，
使 f 的值覆盖 P 的全部元素。定义域不必等于 p 的 q 倍积、值允许重复，
且覆盖 p、q 非标准与空乘积的全部情形。

全部构造只消费实际纯公式、内部收集与单个自然数归纳；不使用宿主 Nat/Fin、
不把外部选取的函数冒充内部图、不把枚举存在本身作为前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteProduct

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 量词绑定层增加时的单项弱化。 -/
private abbrev wb {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) : Term ℒ (SetTheory.SetSort.set :: Γ) Δ .set :=
  t.weakenBound SetTheory.SetSort.set

/-! ## 乘积隶属的实际纯公式 -/

/-- c = a×b 的纯公式：逐元素双向量化，消费原有序对模板。 -/
def product_m {Γ Δ : SortContext ℒ} (a b c : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.iff (SecondOrderObjectSyntax.member_m (.bvar .here) (wb c))
    (.existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (wb (wb a)))
      (.existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (wb (wb (wb b))))
        (SecondOrderObjectSyntax.ordered_m (.bvar (.there .here)) (.bvar .here)
          (.bvar (.there (.there .here)))))))))

theorem product_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (a b c : Term ℒ Γ Δ .set) :
    (product_m a b c).satisfies η ↔
      PowerlessProduct.product_l (a.eval η) (b.eval η) (c.eval η) := by
  simp only [product_m, PowerlessProduct.product_l, wb, Formula.satisfies,
    SecondOrderObjectSyntax.member_m, ordered_formula_l, Arguments.eval, Term.eval_weakenBound]
  rfl

/-! ## 覆盖谓词的纯公式 -/

/-- f 的像覆盖 D：D 的每个元素都是 f 的某个原下标处的值；不要求无重复。 -/
def cover_l (f D : carrier_l ℳ) : Prop := ∀ x, member_l ℳ x D → ∃ i, value_l f i x

/-- 覆盖谓词的实际纯公式。 -/
def cover_m {Γ Δ : SortContext ℒ} (f D : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.imp (SecondOrderObjectSyntax.member_m (.bvar .here) (wb D))
    (.existsE .set (SecondOrderObjectSyntax.value_m (wb (wb f)) (.bvar .here)
      (.bvar (.there .here)))))

theorem cover_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (f D : Term ℒ Γ Δ .set) :
    (cover_m f D).satisfies η ↔ cover_l (f.eval η) (D.eval η) := by
  simp only [cover_m, cover_l, wb, Formula.satisfies, value_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

/-! ## 内部加法的初始段分解 -/

/-- 原加法关系 ∀c∈ω. a+b=c → ∀i∈c, i∈a ∨ ∃j∈b, a+j=i 的实际纯公式；
自由槽自内向外依次是第二加数、ω、零、第一加数。 -/
private def seg_m : Formula ℒ [] (.set :: [.set, .set, .set]) :=
  let ω₀ : Term ℒ [] (.set :: [.set, .set, .set]) .set := .fvar (.there .here)
  let e₀ : Term ℒ [] (.set :: [.set, .set, .set]) .set := .fvar (.there (.there .here))
  let a₀ : Term ℒ [] (.set :: [.set, .set, .set]) .set := .fvar (.there (.there (.there .here)))
  let b₀ : Term ℒ [] (.set :: [.set, .set, .set]) .set := .fvar .here
  .forallE .set (.imp
    (PowerlessAdditionSyntax.addition_m (wb ω₀) (wb e₀) (wb a₀) (wb b₀) (.bvar .here))
    (.forallE .set (.imp
      (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here)))
      (.disj (SecondOrderObjectSyntax.member_m (.bvar .here) (wb (wb a₀)))
        (.existsE .set (.conj
          (SecondOrderObjectSyntax.member_m (.bvar .here) (wb (wb (wb b₀))))
          (PowerlessAdditionSyntax.addition_m (wb (wb (wb ω₀))) (wb (wb (wb e₀)))
            (wb (wb (wb a₀))) (.bvar .here) (.bvar (.there .here)))))))))

/-- seg_formula_l 语句用的三段环境，先注解再进入 env_l。 -/
private def seg_η (ω e a : carrier_l ℳ) :
    SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 3 :=
  { bound := Fin.cases ω (Fin.cases e (fun _ => a)), free := fun _ => ω }

/-- seg_m 的语义：只展开原加法公式与隶属，无额外语言扩张。 -/
private theorem seg_formula_l (a ω e b : carrier_l ℳ) :
    seg_m.satisfies ((PowerlessComprehension.env_l (seg_η ω e a)).pushFree b) ↔
      ∀ c, PowerlessAddition.addition_l ω e a b c →
        ∀ i, member_l ℳ i c → member_l ℳ i a ∨
          ∃ j, member_l ℳ j b ∧ PowerlessAddition.addition_l ω e a j i := by
  simp only [seg_m, seg_η, wb, Formula.satisfies, PowerlessAdditionSyntax.addition_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

/-- 内部和的每个元素要么落在第一个加数里，要么是唯一前缀和加第二个加数的一个元素；
对第二个加数作实际纯公式归纳，非标准数一律按内部隶属处理。 -/
theorem sum_cases_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e a b c i : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (ha : member_l ℳ a ω) (hb : member_l ℳ b ω) (hc : PowerlessAddition.addition_l ω e a b c)
    (hi : member_l ℳ i c) :
    member_l ℳ i a ∨ ∃ j, member_l ℳ j b ∧ PowerlessAddition.addition_l ω e a j i := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 3 :=
    { bound := Fin.cases ω (Fin.cases e (fun _ => a)), free := fun _ => ω }
  have hs (b : carrier_l ℳ) :
      seg_m.satisfies ((PowerlessComprehension.env_l η).pushFree b) ↔
        ∀ c, PowerlessAddition.addition_l ω e a b c →
          ∀ i, member_l ℳ i c → member_l ℳ i a ∨
            ∃ j, member_l ℳ j b ∧ PowerlessAddition.addition_l ω e a j i :=
    seg_formula_l a ω e b
  have h₀ := PowerlessNatural.induction_l hℳ seg_m η hω
    (fun z hz => (hs z).mpr (by
      obtain rfl := PowerlessNatural.zero_unique_l hℳ hz he
      intro c hc i hi
      have hz' := PowerlessAdditionLaws.right_zero_l hℳ hω he ha
      exact Or.inl ((PowerlessAddition.unique_l hℳ hω he hc hz') ▸ hi)))
    (fun n m hn hm h₁ => (hs m).mpr (by
      intro c' hc' i hi
      obtain ⟨c, _, hc⟩ := PowerlessAddition.exists_l hℳ hω he ha hn
      have hsc := PowerlessAddition.successor_l hℳ hω he hn hm hc hc'
      rcases (hsc i).mp hi with hic | hic
      · rcases ((hs n).mp h₁) c hc i hic with hia | ⟨j, hj, hji⟩
        · exact Or.inl hia
        · exact Or.inr ⟨j, (hm j).mpr (Or.inl hj), hji⟩
      · obtain rfl := hic
        exact Or.inr ⟨n, (hm n).mpr (Or.inr rfl), hc⟩))
  exact ((hs b).mp (h₀ b hb)) c hc i hi

/-! ## 两段枚举沿内部加法的拼接 -/

/-- 图关系 (i∈n₁ ∧ f₁(i)=v) ∨ ∃j∈n₂, n₁+j=i ∧ f₂(j)=v 的实际纯公式；
自由槽自内向外依次是值、下标、ω、零、n₁、f₁、n₂、f₂。 -/
private def cc_m : Formula ℒ [] (.set :: .set :: [.set, .set, .set, .set, .set, .set]) :=
  let ω₀ : Term ℒ [] (.set :: .set :: [.set, .set, .set, .set, .set, .set]) .set :=
    .fvar (.there (.there .here))
  let e₀ : Term ℒ [] (.set :: .set :: [.set, .set, .set, .set, .set, .set]) .set :=
    .fvar (.there (.there (.there .here)))
  let n₁₀ : Term ℒ [] (.set :: .set :: [.set, .set, .set, .set, .set, .set]) .set :=
    .fvar (.there (.there (.there (.there .here))))
  let f₁₀ : Term ℒ [] (.set :: .set :: [.set, .set, .set, .set, .set, .set]) .set :=
    .fvar (.there (.there (.there (.there (.there .here)))))
  let n₂₀ : Term ℒ [] (.set :: .set :: [.set, .set, .set, .set, .set, .set]) .set :=
    .fvar (.there (.there (.there (.there (.there (.there .here))))))
  let f₂₀ : Term ℒ [] (.set :: .set :: [.set, .set, .set, .set, .set, .set]) .set :=
    .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
  let i₀ : Term ℒ [] (.set :: .set :: [.set, .set, .set, .set, .set, .set]) .set :=
    .fvar (.there .here)
  let v₀ : Term ℒ [] (.set :: .set :: [.set, .set, .set, .set, .set, .set]) .set := .fvar .here
  .disj (.conj (SecondOrderObjectSyntax.member_m i₀ n₁₀)
    (SecondOrderObjectSyntax.value_m f₁₀ i₀ v₀))
    (.existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (wb n₂₀))
      (.conj (PowerlessAdditionSyntax.addition_m (wb ω₀) (wb e₀) (wb n₁₀) (.bvar .here) (wb i₀))
        (SecondOrderObjectSyntax.value_m (wb f₂₀) (.bvar .here) (wb v₀)))))

/-- cc_formula_l 语句用的六段环境，先注解再进入 env_l。 -/
private def cc_η (ω e n₁ f₁ n₂ f₂ : carrier_l ℳ) :
    SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 6 :=
  { bound := Fin.cases ω (Fin.cases e (Fin.cases n₁ (Fin.cases f₁ (Fin.cases n₂ (fun _ => f₂))))),
    free := fun _ => ω }

private theorem cc_formula_l (ω e n₁ f₁ n₂ f₂ i v : carrier_l ℳ) :
    cc_m.satisfies
        (((PowerlessComprehension.env_l (Γ := [.set, .set, .set, .set, .set, .set])
            (cc_η ω e n₁ f₁ n₂ f₂)).pushFree i).pushFree v) ↔
      (member_l ℳ i n₁ ∧ value_l f₁ i v) ∨
        ∃ j, member_l ℳ j n₂ ∧ PowerlessAddition.addition_l ω e n₁ j i ∧ value_l f₂ j v := by
  simp only [cc_m, cc_η, wb, Formula.satisfies, PowerlessAdditionSyntax.addition_formula_l,
    value_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

/-- 沿内部加法拼接两图，保留每个实际下标的分段取值规格；不只给出像集覆盖。 -/
theorem concat_graph_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e n₁ n₂ c f₁ f₂ S : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hn₁ : member_l ℳ n₁ ω) (hn₂ : member_l ℳ n₂ ω)
    (hc : PowerlessAddition.addition_l ω e n₁ n₂ c)
    (hf₁ : map_l f₁ n₁ S) (hf₂ : map_l f₂ n₂ S) :
    ∃ f, map_l f c S ∧ ∀ i, member_l ℳ i c → ∀ v, value_l f i v ↔
      (member_l ℳ i n₁ ∧ value_l f₁ i v) ∨
        ∃ j, member_l ℳ j n₂ ∧ PowerlessAddition.addition_l ω e n₁ j i ∧ value_l f₂ j v := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 6 :=
    { bound := Fin.cases ω (Fin.cases e (Fin.cases n₁ (Fin.cases f₁ (Fin.cases n₂ (fun _ => f₂))))),
      free := fun _ => ω }
  have hs (i v : carrier_l ℳ) :
      cc_m.satisfies (((PowerlessComprehension.env_l η).pushFree i).pushFree v) ↔
        (member_l ℳ i n₁ ∧ value_l f₁ i v) ∨
          ∃ j, member_l ℳ j n₂ ∧ PowerlessAddition.addition_l ω e n₁ j i ∧ value_l f₂ j v :=
    cc_formula_l ω e n₁ f₁ n₂ f₂ i v
  have htot : ∀ i, member_l ℳ i c → ∃ v,
      cc_m.satisfies (((PowerlessComprehension.env_l η).pushFree i).pushFree v) := by
    intro i hi
    rcases sum_cases_l hℳ hω he hn₁ hn₂ hc hi with hia | ⟨j, hj, hji⟩
    · obtain ⟨v, ⟨_, hv⟩, _⟩ := hf₁.2 i hia
      exact ⟨v, (hs i v).mpr (Or.inl ⟨hia, hv⟩)⟩
    · obtain ⟨v, ⟨_, hv⟩, _⟩ := hf₂.2 j hj
      exact ⟨v, (hs i v).mpr (Or.inr ⟨j, hj, hji, hv⟩)⟩
  have huniq : ∀ i, member_l ℳ i c → ∀ v w,
      cc_m.satisfies (((PowerlessComprehension.env_l η).pushFree i).pushFree v) →
        cc_m.satisfies (((PowerlessComprehension.env_l η).pushFree i).pushFree w) → v = w := by
    intro i _ v w hv hw
    rcases (hs i v).mp hv with ⟨hia, hfv⟩ | ⟨j, _, hji, hfv⟩
    · rcases (hs i w).mp hw with ⟨_, hfw⟩ | ⟨k, _, hki, hfw⟩
      · exact PowerlessFunction.value_unique_l hℳ hf₁ hfv hfw
      · rcases PowerlessAdditionBounds.lower_l hℳ hω he hn₁ hki with hni | hni
        · exact (PowerlessNatural.asymmetry_l hℳ hni hia).elim
        · obtain rfl := hni
          exact (PowerlessNatural.asymmetry_l hℳ hia hia).elim
    · rcases (hs i w).mp hw with ⟨hia, _⟩ | ⟨k, _, hki, hfw⟩
      · rcases PowerlessAdditionBounds.lower_l hℳ hω he hn₁ hji with hni | hni
        · exact (PowerlessNatural.asymmetry_l hℳ hni hia).elim
        · obtain rfl := hni
          exact (PowerlessNatural.asymmetry_l hℳ hia hia).elim
      · have hjk := PowerlessAdditionOrder.cancel_l hℳ hω he hji hki
        subst hjk
        exact PowerlessFunction.value_unique_l hℳ hf₂ hfv hfw
  obtain ⟨f, _, hf, _, hV⟩ := PowerlessMapping.exists_l hℳ cc_m η c htot huniq
  refine ⟨f, PowerlessFunction.range_l hℳ hf ?_, ?_⟩
  · intro i v hv
    have hin := (PowerlessFunction.value_mem_l hℳ hf hv).1
    rcases (hs i v).mp ((hV i hin v).mp hv) with ⟨_, hfv⟩ | ⟨_, _, _, hfv⟩
    · exact (PowerlessFunction.value_mem_l hℳ hf₁ hfv).2
    · exact (PowerlessFunction.value_mem_l hℳ hf₂ hfv).2
  · intro i hi v
    exact (hV i hi v).trans (hs i v)

/-- 精确拼接图覆盖两个旧像的全部元素；不要求两段的值互不相同。 -/
theorem concat_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e n₁ n₂ c f₁ f₂ S : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hn₁ : member_l ℳ n₁ ω) (hn₂ : member_l ℳ n₂ ω)
    (hc : PowerlessAddition.addition_l ω e n₁ n₂ c)
    (hf₁ : map_l f₁ n₁ S) (hf₂ : map_l f₂ n₂ S) :
    ∃ f, map_l f c S ∧
      (∀ x, (∃ i, value_l f₁ i x) ∨ (∃ j, value_l f₂ j x) → ∃ k, value_l f k x) := by
  obtain ⟨f, hf, hV⟩ := concat_graph_l hℳ hω he hn₁ hn₂ hc hf₁ hf₂
  refine ⟨f, hf, ?_⟩
  intro x hx
  rcases hx with ⟨i, hi⟩ | ⟨j, hj⟩
  · have hia := (PowerlessFunction.value_mem_l hℳ hf₁ hi).1
    have hin : member_l ℳ i c := by
      rcases PowerlessAdditionBounds.lower_l hℳ hω he hn₁ hc with hni | hni
      · exact PowerlessNaturalOrder.member_transitive_l hℳ hω c
          (PowerlessAdditionBounds.output_l hℳ hω he hn₁ hc) n₁ i hni hia
      · obtain rfl := hni
        exact hia
    exact ⟨i, (hV i hin x).mpr (Or.inl ⟨hia, hi⟩)⟩
  · obtain ⟨i, _, hadd⟩ := PowerlessAddition.exists_l hℳ hω he hn₁
      (PowerlessNaturalOrder.omega_transitive_l hℳ hω n₂ j hn₂
        (PowerlessFunction.value_mem_l hℳ hf₂ hj).1)
    have hin : member_l ℳ i c := PowerlessAdditionOrder.monotone_l hℳ hω he
      (PowerlessFunction.value_mem_l hℳ hf₂ hj).1 hadd hc
    exact ⟨i, (hV i hin x).mpr
      (Or.inr ⟨j, (PowerlessFunction.value_mem_l hℳ hf₂ hj).1, hadd, hj⟩)⟩

/-! ## 固定左坐标的列枚举 -/

/-- 固定左坐标 z 的列：定义域恰为 q，b 处的值恰为有序对 ⟨z, b⟩。 -/
theorem column_enum_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (q z : carrier_l ℳ) :
    ∃ c S, map_l c q S ∧
      ∀ b, member_l ℳ b q → ∀ p, value_l c b p ↔ ordered_l z b p := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => z, free := fun _ => q }
  let φ : Formula ℒ [] [.set, .set, .set] :=
    SecondOrderObjectSyntax.ordered_m (.fvar (.there (.there .here))) (.fvar (.there .here))
      (.fvar .here)
  have h : ∀ b p, φ.satisfies (((PowerlessComprehension.env_l η).pushFree b).pushFree p) ↔
      ordered_l z b p := by
    intro b p
    dsimp only [φ]
    rw [ordered_formula_l]
    rfl
  obtain ⟨c, S, hc, _, hV⟩ := PowerlessMapping.exists_l hℳ φ η q
    (fun b _ => (PowerlessBasic.ordered_exists_l hℳ z b).imp fun p hp => (h b p).mpr hp)
    (fun b _ p w hp hw =>
      PowerlessBasic.ordered_unique_l hℳ ((h b p).mp hp) ((h b w).mp hw))
  exact ⟨c, S, hc, fun b hb p => (hV b hb p).trans (h b p)⟩

/-! ## 主枚举：对第一因子作内部归纳 -/

/-- “与第二因子 q 的乘积有内部自然数域枚举”的实际纯公式；
自由槽自内向外依次是归纳变量、q、ω。 -/
private def chi_m : Formula ℒ [] (.set :: [.set, .set]) :=
  let z₀ : Term ℒ [] [.set, .set, .set] .set := .fvar .here
  let q₀ : Term ℒ [] [.set, .set, .set] .set := .fvar (.there .here)
  let ω₀ : Term ℒ [] [.set, .set, .set] .set := .fvar (.there (.there .here))
  .existsE .set (.conj (product_m (wb z₀) (wb q₀) (.bvar .here))
    (.existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (wb (wb ω₀)))
      (.existsE .set (.conj
        (SecondOrderObjectSyntax.map_m (.bvar .here) (.bvar (.there .here))
          (.bvar (.there (.there .here))))
        (cover_m (.bvar .here) (.bvar (.there (.there .here)))))))))

/-- chi_formula_l 语句用的两段环境，先注解再进入 env_l。 -/
private def chi_η (q ω : carrier_l ℳ) :
    SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 2 :=
  { bound := Fin.cases q (fun _ => ω), free := fun _ => ω }

private theorem chi_formula_l (q ω z : carrier_l ℳ) :
    chi_m.satisfies
        ((PowerlessComprehension.env_l (Γ := [.set, .set]) (chi_η q ω)).pushFree z) ↔
      ∃ S, PowerlessProduct.product_l z q S ∧
        ∃ n, member_l ℳ n ω ∧ ∃ f, map_l f n S ∧ cover_l f S := by
  simp only [chi_m, chi_η, wb, Formula.satisfies, product_formula_l, cover_formula_l, map_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

/-- 内部笛卡尔积 P = p×q 总被某个以内部自然数为定义域的原函数覆盖；
定义域不必等于积、值允许重复，涵盖 p、q 非标准与空乘积。 -/
theorem enumeration_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω p q P : carrier_l ℳ} (hω : omega_l ω) (hp : member_l ℳ p ω) (hq : member_l ℳ q ω)
    (hP : PowerlessProduct.product_l p q P) :
    ∃ n f, member_l ℳ n ω ∧ map_l f n P ∧
      ∀ x, member_l ℳ x P → ∃ i, value_l f i x := by
  obtain ⟨e, he, _⟩ := ((PowerlessNatural.inductive_iff_l ω).mp hω.1).1
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 2 :=
    { bound := Fin.cases q (fun _ => ω), free := fun _ => ω }
  have hχ (z : carrier_l ℳ) :
      chi_m.satisfies ((PowerlessComprehension.env_l η).pushFree z) ↔
        ∃ S, PowerlessProduct.product_l z q S ∧
          ∃ n, member_l ℳ n ω ∧ ∃ f, map_l f n S ∧ cover_l f S :=
    chi_formula_l q ω z
  have hstep := PowerlessNatural.induction_l hℳ chi_m η hω
    (fun z hz => (hχ z).mpr (by
      obtain ⟨S, hS⟩ := PowerlessProduct.exists_l hℳ z q
      refine ⟨S, hS, z, PowerlessNatural.zero_mem_l hℳ hω hz, z,
        ⟨fun p hp => (hz p hp).elim, fun x hx => (hz x hx).elim⟩, ?_⟩
      intro x hx
      obtain ⟨a, ha, _, _⟩ := (hS x).mp hx
      exact (hz a ha).elim))
    (fun n m _ hm h₁ => (hχ m).mpr (by
      obtain ⟨S₁, hS₁, n₁, hn₁, f₁, hf₁, hcover₁⟩ := (hχ n).mp h₁
      obtain ⟨S₂, hS₂⟩ := PowerlessProduct.exists_l hℳ m q
      obtain ⟨col, _, hcol, hcolv⟩ := column_enum_l hℳ q n
      obtain ⟨k, hkω, hk⟩ := PowerlessAddition.exists_l hℳ hω he hn₁ hq
      have hfold : map_l f₁ n₁ S₂ := PowerlessFunction.range_l hℳ hf₁ (fun _ x hv => by
        obtain ⟨a, ha, b, hb, h₀⟩ := (hS₁ x).mp (PowerlessFunction.value_mem_l hℳ hf₁ hv).2
        exact (hS₂ x).mpr ⟨a, (hm a).mpr (Or.inl ha), b, hb, h₀⟩)
      have hcolmap : map_l col q S₂ := PowerlessFunction.range_l hℳ hcol (fun b p hv =>
        (hS₂ p).mpr ⟨n, (hm n).mpr (Or.inr rfl), b,
          (PowerlessFunction.value_mem_l hℳ hcol hv).1,
          (hcolv b (PowerlessFunction.value_mem_l hℳ hcol hv).1 p).mp hv⟩)
      obtain ⟨g, hg, hglue⟩ := concat_l hℳ hω he hn₁ hq hk hfold hcolmap
      refine ⟨S₂, hS₂, k, hkω, g, hg, ?_⟩
      intro x hx
      obtain ⟨a, ha, b, hb, h₀⟩ := (hS₂ x).mp hx
      rcases (hm a).mp ha with han | harfl
      · exact hglue x (Or.inl (hcover₁ x ((hS₁ x).mpr ⟨a, han, b, hb, h₀⟩)))
      · obtain rfl := harfl
        exact hglue x (Or.inr ⟨b, (hcolv b hb x).mpr h₀⟩)))
  obtain ⟨S, hS, n, hn, f, hf, hcover⟩ := hstep p hp
  have hSP : S = P :=
    (PowerlessTheory.ext_l hℳ).eq_of_same_members S P fun x => (hS x).trans (hP x).symm
  subst hSP
  exact ⟨n, f, hn, hf, hcover⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteProduct
