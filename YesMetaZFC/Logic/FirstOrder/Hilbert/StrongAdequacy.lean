import YesMetaZFC.Logic.FirstOrder.Hilbert.Hilbertization
import YesMetaZFC.Logic.FirstOrder.Hilbert.Adequacy
/-!
# 自然演绎与 Hilbert 演绎的强充分必要性
该层闭合三项独立结果：
* 自然演绎逐构造编译到 Hilbert；
* Hilbert 推导可在任意自然演绎理论解释下回放；
* 每个 admissible 公式与其 `hilbertize` 结果双向可达。
最终得到带有限局部上下文、多排序、量词与等词的完整互译。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
universe u v w
namespace HilbertDerives
/-- Hilbert 化理论和上下文上的证明可反射回原自然演绎判断。 -/
theorem reflect_hilbertize_context
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (anchorSort : σ.SortSymbol)
    {theory : Theory σ} {context : Context σ}
    {formula : Formula σ} (hDerives :
      HilbertDerives (Theory.hilbertize_context
          anchorSort theory context) (Formula.hilbertize anchorSort formula)) :
    Derives theory context formula := by
  have hFormula :
      Formula.Admissible formula :=
    Formula.Admissible.hilbertize_source
      hDerives.admissible
  have hEncoded :
      Derives theory context (Formula.hilbertize anchorSort formula) := by
    apply hDerives.interpret_m
    intro encoded hEncodedTheory hEncodedAdmissible
    rcases Theory.mem_hilbertize_context_iff.mp hEncodedTheory with
      ⟨source, hSource, rfl⟩
    have hSourceAdmissible :
        Formula.Admissible source :=
      Formula.Admissible.hilbertize_source
        hEncodedAdmissible
    have hSourceDerives :
        Derives theory context source :=
      hSource.elim (fun hTheory =>
          Derives.theory_axiom hTheory) (fun hContext =>
          Derives.assumption hContext)
    have hEquivalent :=
      DerivationEquivalent.hilbertize (theory := theory) (context := context)
        anchorSort source hSourceAdmissible
    exact hEquivalent.forward.imp_elim hSourceDerives
  have hEquivalent :=
    DerivationEquivalent.hilbertize (theory := theory) (context := context)
      anchorSort formula hFormula
  exact hEquivalent.backward.imp_elim hEncoded
end HilbertDerives
/--
完整强 adequacy：自然演绎可证，当且仅当合并理论/上下文后的 Hilbert 归约可证。
-/
theorem derives_iff_hilbert_derives
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {anchorSort : σ.SortSymbol}
    {theory : Theory σ} {context : Context σ}
    {formula : Formula σ} :
    Derives theory context formula ↔
      HilbertDerives (Theory.hilbertize_context
          anchorSort theory context) (Formula.hilbertize anchorSort formula) := by
  constructor
  · exact Derives.to_hilbert anchorSort
  · exact HilbertDerives.reflect_hilbertize_context anchorSort
/--
自然演绎可证，当且仅当存在以 Hilbert 化目标为末行的标准有限 Hilbert 列表。
-/
theorem derives_iff_finite_hilbert_proof
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {anchorSort : σ.SortSymbol}
    {theory : Theory σ} {context : Context σ}
    {formula : Formula σ} :
    Derives theory context formula ↔
      ∃ initial,
        HilbertProof (Theory.hilbertize_context
            anchorSort theory context) (initial ++
            [Formula.hilbertize anchorSort formula]) := by
  rw [derives_iff_hilbert_derives]
  exact hilbert_derives_iff_finite_proof
end FirstOrder
end Logic
end YesMetaZFC
