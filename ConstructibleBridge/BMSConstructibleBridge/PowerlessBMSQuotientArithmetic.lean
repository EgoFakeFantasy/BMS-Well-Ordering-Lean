import BMSConstructibleBridge.PowerlessBMSQuotientCoding
import BMSConstructibleBridge.PowerlessAddition
import BMSConstructibleBridge.PowerlessBMSQuotientFunctions
import BMSConstructibleBridge.PowerlessBMSQuotientMapSpec
import BMSConstructibleBridge.PowerlessBMSQuotientSuccessor
import BMSConstructibleBridge.SecondOrderRelations

/-!
# Z₂ 模型加乘关系的实数化与 quotient 逐点提升

固定一个目标模型参数 `a`，用对象理解公理构造 `x ↦ a + x` 与 `x ↦ a * x` 的关系实数，
证明其配对图对每个内部数 total、unique，再经 `exists_map_with_spec_l` 提升为 quotient
内部 `ω` 上的全函数图，并用 `value_iff_relation_l` 把成员规格折回逐点值对应。
出口 `additionMapGraph_l` / `multiplicationMapGraph_l` 在同一句陈述里给出
`map_l f ω ω`（值落在 `ω` 内）与经 `numberEquiv_l` 回读的原模型算式，
故这是真正的编码保持对应，不是从裸存在性用选择函数取出的运算。

零与后继的编码保持在 `PowerlessBMSQuotientSuccessor` 内已有集合论后继关系出口。
本文件在其上补出加法迭代层：固定加数的 quotient 图实际满足
`PowerlessAddition.iteration_l`（含纯公式后继步与零点值），于是每对目标数在商
结构里都满足纯算术加法关系 `addition_l`，并且商内部数上有实际加法运算。

乘法侧本文件只交付正向半边：右加法图在 `ω` 上取值给出 `addition_l` 实例，以及
乘法图的逐点回读与后继步的加法关系式。`PowerlessMultiplication.multiplication_l`
还需要 `operator_l` 的反向半边，即由任意迭代图的值折回唯一数值。本文件保留
正向构造；`PowerlessBMSQuotientRecursion` 现用原 Z₂ 公式归纳证明商侧唯一性，
`PowerlessBMSQuotientMultiplication` 据此完成反向算子规格、乘法迭代及实际
`operations_l`、`correspondence_l`，不要求商满足 Collection。 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientArithmetic

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {M : FirstOrder.Structure.{0, 0, 0, u} signature_m}
  {hM : Theory.Models M SecondOrderArithmetic.theory_m}

/-- quotient 内部 ω 上的数。 -/
abbrev qnum_l (C : PowerlessBMSQuotientCoding.source_coding_l hM) :=
  PowerlessArithmetic.num_l (ℳ := SecondOrderQuotient.structure_l hM) C.omega

/-- 商数码经双射回读即原模型数。 -/
theorem numberEquiv_numberCode_l (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    (n : SecondOrderModel.num_l M) :
    PowerlessBMSQuotientCoding.numberEquiv_l C
      (PowerlessBMSQuotientCoding.numberCode_l C n) = n :=
  Equiv.apply_symm_apply (PowerlessBMSQuotientCoding.numberEquiv_l C) n

/-- 商对象层面：数码双射可还原为 quotient 数自身。 -/
private theorem numberCode_val_numberEquiv_l
    (C : PowerlessBMSQuotientCoding.source_coding_l hM) (x : qnum_l C) :
    (PowerlessBMSQuotientCoding.numberCode_l C
      (PowerlessBMSQuotientCoding.numberEquiv_l C x)).val = x.val :=
  congrArg Subtype.val
    (Equiv.symm_apply_apply (PowerlessBMSQuotientCoding.numberEquiv_l C) x)

/-- 后继的编码保持：原模型后继的数码等于 quotient 后继函数取值。 -/
theorem numberCode_succ_val_l (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    (n : SecondOrderModel.num_l M) :
    (PowerlessBMSQuotientCoding.numberCode_l C
      (SecondOrderModel.succ_l n)).val =
      (PowerlessBMSQuotientSuccessor.successorFunction_l C
        (PowerlessBMSQuotientCoding.numberCode_l C n)).val := by
  have h : PowerlessBMSQuotientCoding.numberEquiv_l C
      (PowerlessBMSQuotientCoding.numberCode_l C n) = n := numberEquiv_numberCode_l C n
  show (PowerlessBMSQuotientCoding.numberCode_l C (SecondOrderModel.succ_l n)).val =
    (PowerlessBMSQuotientCoding.numberCode_l C
      (SecondOrderModel.succ_l (PowerlessBMSQuotientCoding.numberEquiv_l C
        (PowerlessBMSQuotientCoding.numberCode_l C n)))).val
  rw [h]

/-- 加法图模板：第二坐标等于固定参数与第一坐标之和。 -/
def addFormula_m : Formula signature_m [] (.num :: .num :: [.num]) :=
  .equal (.fvar (.there .here))
    (Term.app (σ := signature_m) .add
      (.cons (.fvar (.there (.there .here))) (.cons (.fvar .here) .nil)))

theorem addFormula_pure_m : language_m addFormula_m = true := rfl

theorem addFormula_l (a m n : SecondOrderModel.num_l M) :
    Formula.satisfies
        ((((Env.empty (M := M)).pushFree a).pushFree n).pushFree m) addFormula_m ↔
      n = SecondOrderModel.add_l a m := Iff.rfl

/-- 每个固定参数都给出加法函数自己的图，作为一张内部二阶关系实数。 -/
theorem additionRelation_exists_l (hℳ : Theory.Models M SecondOrderArithmetic.theory_m)
    (a : SecondOrderModel.num_l M) :
    ∃ S : SecondOrderModel.set_l M, ∀ m n, SecondOrderPairing.relation_l S m n ↔
      n = SecondOrderModel.add_l a m := by
  obtain ⟨S, hS⟩ := SecondOrderRelations.comprehension_l hℳ addFormula_m
    addFormula_pure_m ((Env.empty (M := M)).pushFree a)
  refine ⟨S, fun m n => (hS m n).trans (addFormula_l a m n)⟩

theorem additionRelation_total_l (a : SecondOrderModel.num_l M)
    (S : SecondOrderModel.set_l M)
    (hS : ∀ m n, SecondOrderPairing.relation_l S m n ↔ n = SecondOrderModel.add_l a m)
    (m : SecondOrderModel.num_l M) : ∃ n, SecondOrderPairing.relation_l S m n :=
  ⟨SecondOrderModel.add_l a m, (hS _ _).mpr rfl⟩

theorem additionRelation_unique_l (a : SecondOrderModel.num_l M)
    (S : SecondOrderModel.set_l M)
    (hS : ∀ m n, SecondOrderPairing.relation_l S m n ↔ n = SecondOrderModel.add_l a m)
    (m n₁ n₂ : SecondOrderModel.num_l M)
    (h₁ : SecondOrderPairing.relation_l S m n₁)
    (h₂ : SecondOrderPairing.relation_l S m n₂) : n₁ = n₂ :=
  ((hS _ _).mp h₁).trans (((hS _ _).mp h₂).symm)

/-- 加法实数提升为 quotient 全函数图，并保留逐点成员规格。 -/
theorem additionMapSpec_l (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    (a : SecondOrderModel.num_l M) (S : SecondOrderModel.set_l M)
    (hS : ∀ m n, SecondOrderPairing.relation_l S m n ↔ n = SecondOrderModel.add_l a m) :
    ∃ f : SecondOrderQuotient.type_l hM,
      ThirdOrderSemantics.map_l (ℳ := SecondOrderQuotient.structure_l hM)
        f C.omega C.omega ∧
        ∀ p, SecondOrderQuotient.mem_l hM p f ↔
          ∃ m n, SecondOrderPairing.relation_l S m n ∧
            SecondOrderPairObjects.ordered_l hM
              (PowerlessBMSQuotientCoding.numberCode_l C m).val
              (PowerlessBMSQuotientCoding.numberCode_l C n).val p :=
  PowerlessBMSQuotientFunctions.exists_map_with_spec_l C S
    (additionRelation_total_l a S hS) (additionRelation_unique_l a S hS)

/-- 规格像的逐点值 iff。 -/
theorem additionValue_iff_l (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    (a : SecondOrderModel.num_l M) (S : SecondOrderModel.set_l M)
    (hS : ∀ m n, SecondOrderPairing.relation_l S m n ↔ n = SecondOrderModel.add_l a m)
    (f : SecondOrderQuotient.type_l hM)
    (hSpec : ∀ p, SecondOrderQuotient.mem_l hM p f ↔
      ∃ m n, SecondOrderPairing.relation_l S m n ∧
        SecondOrderPairObjects.ordered_l hM
          (PowerlessBMSQuotientCoding.numberCode_l C m).val
          (PowerlessBMSQuotientCoding.numberCode_l C n).val p)
    (m n : SecondOrderModel.num_l M) :
    ThirdOrderSemantics.value_l (ℳ := SecondOrderQuotient.structure_l hM)
      f (PowerlessBMSQuotientCoding.numberCode_l C m).val
        (PowerlessBMSQuotientCoding.numberCode_l C n).val ↔
      n = SecondOrderModel.add_l a m :=
  (PowerlessBMSQuotientFunctions.value_iff_relation_l C S f hSpec m n).trans (hS m n)

/-- 加法主出口：值落在 `ω` 内的商函数图，逐点等价于回读后的原模型加法。 -/
theorem additionMapGraph_l (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    (a : SecondOrderModel.num_l M) :
    ∃ f : SecondOrderQuotient.type_l hM,
      ThirdOrderSemantics.map_l (ℳ := SecondOrderQuotient.structure_l hM)
        f C.omega C.omega ∧
        ∀ x y : qnum_l C, ThirdOrderSemantics.value_l
            (ℳ := SecondOrderQuotient.structure_l hM) f x.val y.val ↔
          PowerlessBMSQuotientCoding.numberEquiv_l C y =
            SecondOrderModel.add_l a (PowerlessBMSQuotientCoding.numberEquiv_l C x) := by
  obtain ⟨S, hS⟩ := additionRelation_exists_l hM a
  obtain ⟨f, hmap, hspec⟩ := additionMapSpec_l C a S hS
  refine ⟨f, hmap, fun x y => ?_⟩
  simpa only [numberCode_val_numberEquiv_l C] using
    additionValue_iff_l C a S hS f hspec
      (PowerlessBMSQuotientCoding.numberEquiv_l C x)
      (PowerlessBMSQuotientCoding.numberEquiv_l C y)

/-- 乘法图模板：第二坐标等于固定参数与第一坐标之积。 -/
def mulFormula_m : Formula signature_m [] (.num :: .num :: [.num]) :=
  .equal (.fvar (.there .here))
    (Term.app (σ := signature_m) .mul
      (.cons (.fvar (.there (.there .here))) (.cons (.fvar .here) .nil)))

theorem mulFormula_pure_m : language_m mulFormula_m = true := rfl

theorem mulFormula_l (a m n : SecondOrderModel.num_l M) :
    Formula.satisfies
        ((((Env.empty (M := M)).pushFree a).pushFree n).pushFree m) mulFormula_m ↔
      n = SecondOrderModel.mul_l a m := Iff.rfl

theorem multiplicationRelation_exists_l
    (hℳ : Theory.Models M SecondOrderArithmetic.theory_m)
    (a : SecondOrderModel.num_l M) :
    ∃ S : SecondOrderModel.set_l M, ∀ m n, SecondOrderPairing.relation_l S m n ↔
      n = SecondOrderModel.mul_l a m := by
  obtain ⟨S, hS⟩ := SecondOrderRelations.comprehension_l hℳ mulFormula_m
    mulFormula_pure_m ((Env.empty (M := M)).pushFree a)
  refine ⟨S, fun m n => (hS m n).trans (mulFormula_l a m n)⟩

theorem multiplicationRelation_total_l (a : SecondOrderModel.num_l M)
    (S : SecondOrderModel.set_l M)
    (hS : ∀ m n, SecondOrderPairing.relation_l S m n ↔ n = SecondOrderModel.mul_l a m)
    (m : SecondOrderModel.num_l M) : ∃ n, SecondOrderPairing.relation_l S m n :=
  ⟨SecondOrderModel.mul_l a m, (hS _ _).mpr rfl⟩

theorem multiplicationRelation_unique_l (a : SecondOrderModel.num_l M)
    (S : SecondOrderModel.set_l M)
    (hS : ∀ m n, SecondOrderPairing.relation_l S m n ↔ n = SecondOrderModel.mul_l a m)
    (m n₁ n₂ : SecondOrderModel.num_l M)
    (h₁ : SecondOrderPairing.relation_l S m n₁)
    (h₂ : SecondOrderPairing.relation_l S m n₂) : n₁ = n₂ :=
  ((hS _ _).mp h₁).trans (((hS _ _).mp h₂).symm)

theorem multiplicationMapSpec_l (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    (a : SecondOrderModel.num_l M) (S : SecondOrderModel.set_l M)
    (hS : ∀ m n, SecondOrderPairing.relation_l S m n ↔ n = SecondOrderModel.mul_l a m) :
    ∃ f : SecondOrderQuotient.type_l hM,
      ThirdOrderSemantics.map_l (ℳ := SecondOrderQuotient.structure_l hM)
        f C.omega C.omega ∧
        ∀ p, SecondOrderQuotient.mem_l hM p f ↔
          ∃ m n, SecondOrderPairing.relation_l S m n ∧
            SecondOrderPairObjects.ordered_l hM
              (PowerlessBMSQuotientCoding.numberCode_l C m).val
              (PowerlessBMSQuotientCoding.numberCode_l C n).val p :=
  PowerlessBMSQuotientFunctions.exists_map_with_spec_l C S
    (multiplicationRelation_total_l a S hS)
    (multiplicationRelation_unique_l a S hS)

theorem multiplicationValue_iff_l (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    (a : SecondOrderModel.num_l M) (S : SecondOrderModel.set_l M)
    (hS : ∀ m n, SecondOrderPairing.relation_l S m n ↔ n = SecondOrderModel.mul_l a m)
    (f : SecondOrderQuotient.type_l hM)
    (hSpec : ∀ p, SecondOrderQuotient.mem_l hM p f ↔
      ∃ m n, SecondOrderPairing.relation_l S m n ∧
        SecondOrderPairObjects.ordered_l hM
          (PowerlessBMSQuotientCoding.numberCode_l C m).val
          (PowerlessBMSQuotientCoding.numberCode_l C n).val p)
    (m n : SecondOrderModel.num_l M) :
    ThirdOrderSemantics.value_l (ℳ := SecondOrderQuotient.structure_l hM)
      f (PowerlessBMSQuotientCoding.numberCode_l C m).val
        (PowerlessBMSQuotientCoding.numberCode_l C n).val ↔
      n = SecondOrderModel.mul_l a m :=
  (PowerlessBMSQuotientFunctions.value_iff_relation_l C S f hSpec m n).trans (hS m n)

/-- 乘法主出口：与加法同形，逐点回读原模型乘法。 -/
theorem multiplicationMapGraph_l (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    (a : SecondOrderModel.num_l M) :
    ∃ f : SecondOrderQuotient.type_l hM,
      ThirdOrderSemantics.map_l (ℳ := SecondOrderQuotient.structure_l hM)
        f C.omega C.omega ∧
        ∀ x y : qnum_l C, ThirdOrderSemantics.value_l
            (ℳ := SecondOrderQuotient.structure_l hM) f x.val y.val ↔
          PowerlessBMSQuotientCoding.numberEquiv_l C y =
            SecondOrderModel.mul_l a (PowerlessBMSQuotientCoding.numberEquiv_l C x) := by
  obtain ⟨S, hS⟩ := multiplicationRelation_exists_l hM a
  obtain ⟨f, hmap, hspec⟩ := multiplicationMapSpec_l C a S hS
  refine ⟨f, hmap, fun x y => ?_⟩
  simpa only [numberCode_val_numberEquiv_l C] using
    multiplicationValue_iff_l C a S hS f hspec
      (PowerlessBMSQuotientCoding.numberEquiv_l C x)
      (PowerlessBMSQuotientCoding.numberEquiv_l C y)

/-- 商对象层面：数码在 `val` 上仍单射。 -/
private theorem numberCode_val_injective_l (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    {n m : SecondOrderModel.num_l M}
    (h : (PowerlessBMSQuotientCoding.numberCode_l C n).val =
      (PowerlessBMSQuotientCoding.numberCode_l C m).val) : n = m :=
  (SecondOrderNaturalNumbers.eq_l hM C.less C.less_spec n m).mp
    ((SecondOrderQuotient.eq_iff_l hM _ _).mp h)

/-- 同一对象的集合后继在商结构里外延唯一；只用图商外延性，不用 Collection。 -/
private theorem successor_right_unique_l (hℳ : Theory.Models M SecondOrderArithmetic.theory_m)
    {a b c : SecondOrderQuotient.type_l hℳ}
    (hb : PowerlessNatural.successor_l (ℳ := SecondOrderQuotient.structure_l hℳ) a b)
    (hc : PowerlessNatural.successor_l (ℳ := SecondOrderQuotient.structure_l hℳ) a c) : b = c :=
  SecondOrderQuotient.ext_l hℳ b c fun x => Iff.trans (hb x) (Iff.symm (hc x))

/-- 提升后的加法图每次取值都可回到目标模型的两个数坐标，且坐标满足原加法。 -/
theorem additionValue_coord_l (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    (a : SecondOrderModel.num_l M) (S : SecondOrderModel.set_l M)
    (hS : ∀ m n, SecondOrderPairing.relation_l S m n ↔ n = SecondOrderModel.add_l a m)
    (f : SecondOrderQuotient.type_l hM)
    (hSpec : ∀ p, SecondOrderQuotient.mem_l hM p f ↔
      ∃ m n, SecondOrderPairing.relation_l S m n ∧
        SecondOrderPairObjects.ordered_l hM
          (PowerlessBMSQuotientCoding.numberCode_l C m).val
          (PowerlessBMSQuotientCoding.numberCode_l C n).val p)
    {u v : SecondOrderQuotient.type_l hM}
    (h : ThirdOrderSemantics.value_l (ℳ := SecondOrderQuotient.structure_l hM) f u v) :
    ∃ m n : SecondOrderModel.num_l M,
      u = (PowerlessBMSQuotientCoding.numberCode_l C m).val ∧
        v = (PowerlessBMSQuotientCoding.numberCode_l C n).val ∧
        n = SecondOrderModel.add_l a m := by
  obtain ⟨p, hp, hpair⟩ := h
  change SecondOrderQuotient.mem_l hM p f at hp
  obtain ⟨m, n, hmn, hp'⟩ := (hSpec p).mp hp
  have hcoord := (SecondOrderPairObjects.ordered_eq_l hM hpair hp').mp rfl
  exact ⟨m, n, hcoord.1, hcoord.2, (hS m n).mp hmn⟩

/-- 固定加数的 quotient 加法图满足纯语言 `ω` 递归谓词：零点取加数自身，逐步走
集合后继并落到 `step_m` 的实例。 -/
theorem additionIteration_l (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    (a : SecondOrderModel.num_l M) (S : SecondOrderModel.set_l M)
    (hS : ∀ m n, SecondOrderPairing.relation_l S m n ↔ n = SecondOrderModel.add_l a m)
    (f : SecondOrderQuotient.type_l hM)
    (hmap : ThirdOrderSemantics.map_l (ℳ := SecondOrderQuotient.structure_l hM)
      f C.omega C.omega)
    (hSpec : ∀ p, SecondOrderQuotient.mem_l hM p f ↔
      ∃ m n, SecondOrderPairing.relation_l S m n ∧
        SecondOrderPairObjects.ordered_l hM
          (PowerlessBMSQuotientCoding.numberCode_l C m).val
          (PowerlessBMSQuotientCoding.numberCode_l C n).val p) :
    PowerlessAddition.iteration_l (ℳ := SecondOrderQuotient.structure_l hM) C.omega
      (PowerlessBMSQuotientCoding.numberCode_l C (SecondOrderModel.zero_l M)).val
      (PowerlessBMSQuotientCoding.numberCode_l C a).val f := by
  refine ⟨C.omega, hmap, ?_, ?_⟩
  · exact (additionValue_iff_l C a S hS f hSpec (SecondOrderModel.zero_l M) a).mpr
      ((SecondOrderModel.add_zero_l hM a).symm)
  · intro n m x y _ hsucc hx hy
    obtain ⟨p, q, hnp, hxq, hpq⟩ := additionValue_coord_l C a S hS f hSpec hx
    obtain ⟨r, s, hmr, hys, hrs⟩ := additionValue_coord_l C a S hS f hSpec hy
    have hsuccCode : PowerlessNatural.successor_l (ℳ := SecondOrderQuotient.structure_l hM)
        (PowerlessBMSQuotientCoding.numberCode_l C p).val
        (PowerlessBMSQuotientCoding.numberCode_l C r).val := by
      rw [← hnp, ← hmr]
      exact hsucc
    have hr : r = SecondOrderModel.succ_l p :=
      numberCode_val_injective_l C
        (successor_right_unique_l hM hsuccCode
          (PowerlessBMSQuotientSuccessor.successor_l C p))
    have hs : s = SecondOrderModel.succ_l q :=
      hrs.trans (congrArg (SecondOrderModel.add_l a) hr)
        |>.trans (SecondOrderModel.add_succ_l hM a p)
        |>.trans (congrArg SecondOrderModel.succ_l hpq.symm)
    exact (PowerlessAddition.step_formula_l (ℳ := SecondOrderQuotient.structure_l hM)
      C.omega x y).mpr (by
        rw [hxq, hys, hs]
        exact PowerlessBMSQuotientSuccessor.successor_l C q)

/-- 每个固定加数都在 quotient 上给出满足加法递归谓词的实际图。 -/
theorem additionIteration_exists_l (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    (a : SecondOrderModel.num_l M) :
    ∃ f : SecondOrderQuotient.type_l hM,
      PowerlessAddition.iteration_l (ℳ := SecondOrderQuotient.structure_l hM) C.omega
        (PowerlessBMSQuotientCoding.numberCode_l C (SecondOrderModel.zero_l M)).val
        (PowerlessBMSQuotientCoding.numberCode_l C a).val f ∧
        ThirdOrderSemantics.map_l (ℳ := SecondOrderQuotient.structure_l hM)
          f C.omega C.omega := by
  obtain ⟨S, hS⟩ := additionRelation_exists_l hM a
  obtain ⟨f, hmap, hspec⟩ := additionMapSpec_l C a S hS
  exact ⟨f, additionIteration_l C a S hS f hmap hspec, hmap⟩

/-- 迭代图的每个值都是纯算术加法关系的实例。 -/
theorem additionValue_addition_l (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    (a : SecondOrderModel.num_l M)
    (f : SecondOrderQuotient.type_l hM)
    (hf : PowerlessAddition.iteration_l (ℳ := SecondOrderQuotient.structure_l hM) C.omega
      (PowerlessBMSQuotientCoding.numberCode_l C (SecondOrderModel.zero_l M)).val
      (PowerlessBMSQuotientCoding.numberCode_l C a).val f)
    (x y : SecondOrderQuotient.type_l hM)
    (h : ThirdOrderSemantics.value_l (ℳ := SecondOrderQuotient.structure_l hM) f x y) :
    PowerlessAddition.addition_l (ℳ := SecondOrderQuotient.structure_l hM) C.omega
      (PowerlessBMSQuotientCoding.numberCode_l C (SecondOrderModel.zero_l M)).val
      (PowerlessBMSQuotientCoding.numberCode_l C a).val x y :=
  ⟨f, hf, h⟩

/-- 商结构对任意一对目标数根码都满足纯算术加法关系。 -/
theorem additionInstance_l (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    (a b : SecondOrderModel.num_l M) :
    PowerlessAddition.addition_l (ℳ := SecondOrderQuotient.structure_l hM) C.omega
      (PowerlessBMSQuotientCoding.numberCode_l C (SecondOrderModel.zero_l M)).val
      (PowerlessBMSQuotientCoding.numberCode_l C a).val
      (PowerlessBMSQuotientCoding.numberCode_l C b).val
      (PowerlessBMSQuotientCoding.numberCode_l C (SecondOrderModel.add_l a b)).val := by
  obtain ⟨S, hS⟩ := additionRelation_exists_l hM a
  obtain ⟨f, hmap, hspec⟩ := additionMapSpec_l C a S hS
  refine ⟨f, additionIteration_l C a S hS f hmap hspec, ?_⟩
  exact (additionValue_iff_l C a S hS f hspec b (SecondOrderModel.add_l a b)).mpr rfl

/-- quotient 内部数上的实际加法：经数码双射将目标加法搬到商数域。 -/
noncomputable def addNumbers_l (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    (x y : qnum_l C) : qnum_l C :=
  PowerlessBMSQuotientCoding.numberCode_l C
    (SecondOrderModel.add_l (PowerlessBMSQuotientCoding.numberEquiv_l C x)
      (PowerlessBMSQuotientCoding.numberEquiv_l C y))

/-- 上述实际加法的图规格：对全部商内部数满足 `addition_l`，即
`PowerlessArithmetic.operations_l.add_graph_l` 的义务形状。 -/
theorem additionGraph_l (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    (x y : qnum_l C) :
    PowerlessAddition.addition_l (ℳ := SecondOrderQuotient.structure_l hM) C.omega
      (PowerlessBMSQuotientCoding.numberCode_l C (SecondOrderModel.zero_l M)).val
      x.val y.val (addNumbers_l C x y).val := by
  have h := additionInstance_l C (PowerlessBMSQuotientCoding.numberEquiv_l C x)
    (PowerlessBMSQuotientCoding.numberEquiv_l C y)
  rw [numberCode_val_numberEquiv_l C x, numberCode_val_numberEquiv_l C y] at h
  exact h

/-- 上述实际加法经双射回读正是目标模型加法，即 `hAdd` 形状的等式。 -/
theorem numberEquiv_addNumbers_l (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    (x y : qnum_l C) :
    PowerlessBMSQuotientCoding.numberEquiv_l C (addNumbers_l C x y) =
      SecondOrderModel.add_l (PowerlessBMSQuotientCoding.numberEquiv_l C x)
        (PowerlessBMSQuotientCoding.numberEquiv_l C y) :=
  numberEquiv_numberCode_l C
    (SecondOrderModel.add_l (PowerlessBMSQuotientCoding.numberEquiv_l C x)
      (PowerlessBMSQuotientCoding.numberEquiv_l C y))

/-- 右加法图模板：第二坐标等于第一坐标与固定参数之和。 -/
def addRightFormula_m : Formula signature_m [] (.num :: .num :: [.num]) :=
  .equal (.fvar (.there .here))
    (Term.app (σ := signature_m) .add
      (.cons (.fvar .here) (.cons (.fvar (.there (.there .here))) .nil)))

theorem addRightFormula_pure_m : language_m addRightFormula_m = true := rfl

theorem addRightFormula_l (a m n : SecondOrderModel.num_l M) :
    Formula.satisfies
        ((((Env.empty (M := M)).pushFree a).pushFree n).pushFree m) addRightFormula_m ↔
      n = SecondOrderModel.add_l m a := Iff.rfl

/-- 固定右加数的右加法提升图，及其逐点回读规格。 -/
theorem rightAdditionGraph_l (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    (a : SecondOrderModel.num_l M) :
    ∃ f : SecondOrderQuotient.type_l hM,
      ThirdOrderSemantics.map_l (ℳ := SecondOrderQuotient.structure_l hM)
        f C.omega C.omega ∧
        ∀ x y : qnum_l C, ThirdOrderSemantics.value_l
            (ℳ := SecondOrderQuotient.structure_l hM) f x.val y.val ↔
          PowerlessBMSQuotientCoding.numberEquiv_l C y =
            SecondOrderModel.add_l (PowerlessBMSQuotientCoding.numberEquiv_l C x) a := by
  obtain ⟨S, hS⟩ := SecondOrderRelations.comprehension_l hM addRightFormula_m
    addRightFormula_pure_m ((Env.empty (M := M)).pushFree a)
  have hSpec (m n : SecondOrderModel.num_l M) :
      SecondOrderPairing.relation_l S m n ↔ n = SecondOrderModel.add_l m a :=
    (hS m n).trans (addRightFormula_l a m n)
  obtain ⟨f, hmap, hmem⟩ := PowerlessBMSQuotientFunctions.exists_map_with_spec_l C S
    (fun m => ⟨SecondOrderModel.add_l m a, (hSpec _ _).mpr rfl⟩)
    (fun m n₁ n₂ h₁ h₂ => ((hSpec _ _).mp h₁).trans (((hSpec _ _).mp h₂).symm))
  refine ⟨f, hmap, fun x y => ?_⟩
  have hiff := PowerlessBMSQuotientFunctions.value_iff_relation_l C S f hmem
    (PowerlessBMSQuotientCoding.numberEquiv_l C x)
    (PowerlessBMSQuotientCoding.numberEquiv_l C y)
  constructor
  · intro h
    rw [← numberCode_val_numberEquiv_l C x, ← numberCode_val_numberEquiv_l C y] at h
    exact (hSpec _ _).mp (hiff.mp h)
  · intro h
    have h' := hiff.mpr ((hSpec _ _).mpr h)
    rw [numberCode_val_numberEquiv_l C x, numberCode_val_numberEquiv_l C y] at h'
    exact h'

/-- 乘法 `operator_l` 的正向半边：右加法图的值都是 `addition_l` 实例。
反向半边需要迭代唯一性，见本文件头部缺口说明。 -/
theorem rightAdditionValue_addition_l (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    (a : SecondOrderModel.num_l M)
    (H : SecondOrderQuotient.type_l hM)
    (hGraph : ∀ x y : qnum_l C, ThirdOrderSemantics.value_l
        (ℳ := SecondOrderQuotient.structure_l hM) H x.val y.val ↔
      PowerlessBMSQuotientCoding.numberEquiv_l C y =
        SecondOrderModel.add_l (PowerlessBMSQuotientCoding.numberEquiv_l C x) a)
    (x y : qnum_l C)
    (h : ThirdOrderSemantics.value_l (ℳ := SecondOrderQuotient.structure_l hM) H x.val y.val) :
    PowerlessAddition.addition_l (ℳ := SecondOrderQuotient.structure_l hM) C.omega
      (PowerlessBMSQuotientCoding.numberCode_l C (SecondOrderModel.zero_l M)).val
      x.val (PowerlessBMSQuotientCoding.numberCode_l C a).val y.val := by
  have hxy : y.val =
      (PowerlessBMSQuotientCoding.numberCode_l C
        (SecondOrderModel.add_l (PowerlessBMSQuotientCoding.numberEquiv_l C x) a)).val := by
    rw [← numberCode_val_numberEquiv_l C y, (hGraph x y).mp h]
  have h := additionInstance_l C (PowerlessBMSQuotientCoding.numberEquiv_l C x) a
  rw [numberCode_val_numberEquiv_l C x] at h
  rwa [← hxy] at h

/-- 乘法图的后继步在商结构里就是已构造的纯加法关系实例。 -/
theorem multiplication_succ_addition_l (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    (a n : SecondOrderModel.num_l M) :
    PowerlessAddition.addition_l (ℳ := SecondOrderQuotient.structure_l hM) C.omega
      (PowerlessBMSQuotientCoding.numberCode_l C (SecondOrderModel.zero_l M)).val
      (PowerlessBMSQuotientCoding.numberCode_l C (SecondOrderModel.mul_l a n)).val
      (PowerlessBMSQuotientCoding.numberCode_l C a).val
      (PowerlessBMSQuotientCoding.numberCode_l C
        (SecondOrderModel.mul_l a (SecondOrderModel.succ_l n))).val := by
  have h := additionInstance_l C (SecondOrderModel.mul_l a n) a
  rw [← SecondOrderModel.mul_succ_l hM a n] at h
  exact h

#print axioms additionIteration_l
#print axioms additionIteration_exists_l
#print axioms additionInstance_l
#print axioms additionGraph_l
#print axioms numberEquiv_addNumbers_l
#print axioms addRightFormula_pure_m
#print axioms rightAdditionGraph_l
#print axioms rightAdditionValue_addition_l
#print axioms multiplication_succ_addition_l
#print axioms numberEquiv_numberCode_l
#print axioms numberCode_succ_val_l
#print axioms addFormula_pure_m
#print axioms additionRelation_exists_l
#print axioms additionMapGraph_l
#print axioms multiplicationRelation_exists_l
#print axioms multiplicationMapGraph_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientArithmetic
