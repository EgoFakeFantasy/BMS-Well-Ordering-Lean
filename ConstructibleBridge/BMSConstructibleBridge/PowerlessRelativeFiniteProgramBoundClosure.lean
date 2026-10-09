import BMSConstructibleBridge.PowerlessRelativeFiniteProgramCall
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramPairClosure

/-! # 带绑定执行代表的配对与调用

存在消去所得程序词、长度、坐标和输出可以直接放入绑定上下文。
开放这些参数后复用原实际程序构造，再沿完整历史对应传回原算子。
不把新绑定槽加入常量种子，不改变原代码域，也不抽取 Type 选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramBoundClosure

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeFiniteProgramInstruction (functional_l)
open PowerlessRelativeFiniteProgramBoundOutput (run_l prefix_m prefix_formula_l prefix_run_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem pair_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C ω e t₀ t₁ t₂ a n w m z Q k x l y : Term ℒ Γ Δ .set)
    (hB : ∀ u, mem_l hℳ u (B.eval η) → ∀ v, mem_l hℳ v u → mem_l hℳ v (B.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval η))
    (hωC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (ω.eval η))
    (hQ : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (Q.eval η))
    (he : ∀ u, ¬mem_l hℳ u (e.eval η))
    (ha : PowerlessRelativeFiniteProgramStep.record_l
      (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (ht : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hφ : functional_l φ (parameters_l η) (B.eval η))
    (hAlphabet : ∀ q, mem_l hℳ q (Q.eval η) ↔
      PowerlessRelativeFiniteProgramAlphabet.instruction_l (C.eval η) (ω.eval η)
        (t₀.eval η) (t₁.eval η) (t₂.eval η) q)
    (hn : mem_l hℳ (n.eval η) (ω.eval η)) (hm : mem_l hℳ (m.eval η) (ω.eval η))
    (hw : map_l (ℳ := 𝒱) (w.eval η) (n.eval η) (Q.eval η))
    (hz : map_l (ℳ := 𝒱) (z.eval η) (m.eval η) (Q.eval η))
    (hx : run_l φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) (w.eval η)
      (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (n.eval η) (k.eval η) (x.eval η))
    (hy : run_l φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) (z.eval η)
      (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (m.eval η) (l.eval η) (y.eval η)) :
    ∃ N v i p, ordered_l (ℳ := 𝒱) (x.eval η) (y.eval η) p ∧
      mem_l hℳ N (ω.eval η) ∧ mem_l hℳ i N ∧
        PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) v ∧
          PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) p ∧
            map_l (ℳ := 𝒱) v N (Q.eval η) ∧
              run_l φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) v (e.eval η)
                (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) N i p := by
  let ξ := PowerlessSourceOpening.env_l η
  let t := @PowerlessSourceRebinding.term_m Γ Δ
  let ψ := prefix_m Γ.length φ
  have ht' (v : Term ℒ Γ Δ .set) : (t v).eval ξ = v.eval η :=
    PowerlessSourceRebinding.term_l v η
  have hφ' : functional_l ψ ξ (B.eval η) := by
    simpa only [ψ, ξ, functional_l, prefix_formula_l] using hφ
  have hx' := (prefix_run_l φ η (B.eval η) (C.eval η) (ω.eval η) (w.eval η)
    (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η)
      (n.eval η) (k.eval η) (x.eval η)).mpr hx
  have hy' := (prefix_run_l φ η (B.eval η) (C.eval η) (ω.eval η) (z.eval η)
    (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η)
      (m.eval η) (l.eval η) (y.eval η)).mpr hy
  have h := PowerlessRelativeFiniteProgramPairClosure.exists_l K ψ ξ
    (t B) (t C) (t ω) (t e) (t t₀) (t t₁) (t t₂) (t a) (t n) (t w)
      (t m) (t z) (t Q) (t k) (t x) (t l) (t y)
    (by simpa only [ht'] using hB) (by simpa only [ht'] using hC)
    (by simpa only [ht'] using hω) (by simpa only [ht'] using hωC)
    (by simpa only [ht'] using hQ) (by simpa only [ht'] using he)
    (by simpa only [ht'] using ha) (by simpa only [ht'] using ht)
    (by simpa only [ht'] using hφ') (by simpa only [ht'] using hAlphabet)
    (by simpa only [ht'] using hn) (by simpa only [ht'] using hm)
    (by simpa only [ht'] using hw) (by simpa only [ht'] using hz)
    (by simpa only [ht', ψ, ξ] using hx') (by simpa only [ht', ψ, ξ] using hy')
  simpa only [ht', ψ, ξ, prefix_run_l] using h

theorem call_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C ω w n Q e t₀ t₁ t₂ a k x y : Term ℒ Γ Δ .set)
    (hB : ∀ z, mem_l hℳ z (B.eval η) → ∀ u, mem_l hℳ u z → mem_l hℳ u (B.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hω : ω.eval η = K.omega) (he : ∀ z, ¬mem_l hℳ z (e.eval η))
    (ha : PowerlessRelativeFiniteProgramStep.record_l
      (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (hwC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (w.eval η))
    (hQ : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (Q.eval η))
    (hw : map_l (ℳ := 𝒱) (w.eval η) (n.eval η) (Q.eval η))
    (ht : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hφ : functional_l φ (parameters_l η) (B.eval η))
    (hn : mem_l hℳ (n.eval η) K.omega)
    (hAlphabet : ∀ q, mem_l hℳ q (Q.eval η) ↔
      PowerlessRelativeFiniteProgramAlphabet.instruction_l (C.eval η) (ω.eval η)
        (t₀.eval η) (t₁.eval η) (t₂.eval η) q)
    (hx : run_l φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) (w.eval η)
      (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (n.eval η) (k.eval η) (x.eval η))
    (hyC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (y.eval η))
    (hy : φ.satisfies (((parameters_l η).pushFree (x.eval η)).pushFree (y.eval η))) :
    ∃ S v q, ordered_l (ℳ := 𝒱) (t₁.eval η) (k.eval η) q ∧
      PowerlessRelativeFiniteProgramWordAppend.append_l
        (B.eval η) (w.eval η) (n.eval η) (Q.eval η) q S v ∧
          run_l φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) v (e.eval η)
            (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) S (n.eval η) (y.eval η) := by
  let ξ := PowerlessSourceOpening.env_l η
  let t := @PowerlessSourceRebinding.term_m Γ Δ
  let ψ := prefix_m Γ.length φ
  have ht' (v : Term ℒ Γ Δ .set) : (t v).eval ξ = v.eval η :=
    PowerlessSourceRebinding.term_l v η
  have hφ' : functional_l ψ ξ (B.eval η) := by
    simpa only [ψ, ξ, functional_l, prefix_formula_l] using hφ
  have hx' := (prefix_run_l φ η (B.eval η) (C.eval η) (ω.eval η) (w.eval η)
    (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η)
      (n.eval η) (k.eval η) (x.eval η)).mpr hx
  have hy' := (prefix_formula_l φ η (x.eval η) (y.eval η)).mpr hy
  have h := PowerlessRelativeFiniteProgramCall.exists_l K ψ ξ
    (t B) (t C) (t ω) (t w) (t n) (t Q) (t e) (t t₀) (t t₁) (t t₂) (t a)
      (t k) (t x) (t y)
    (by simpa only [ht'] using hB) (by simpa only [ht'] using hC)
    (by simpa only [ht'] using hω) (by simpa only [ht'] using he)
    (by simpa only [ht'] using ha) (by simpa only [ht'] using hwC)
    (by simpa only [ht'] using hQ) (by simpa only [ht'] using hw)
    (by simpa only [ht'] using ht) (by simpa only [ht'] using hφ')
    (by simpa only [ht'] using hn) (by simpa only [ht'] using hAlphabet)
    (by simpa only [ht', ψ, ξ] using hx') (by simpa only [ht'] using hyC)
    (by simpa only [ht', ψ, ξ] using hy')
  simpa only [ht', ψ, ξ, prefix_run_l] using h

#print axioms PowerlessRelativeFiniteProgramBoundOutput.prefix_run_l
#print axioms pair_l
#print axioms call_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramBoundClosure
