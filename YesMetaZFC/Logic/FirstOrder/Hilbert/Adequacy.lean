import YesMetaZFC.Logic.FirstOrder.Hilbert.Compilation
/-!
# Hilbert 演绎对自然演绎的充分性
`Derives` 已内生携带全部 proof-layer 合法性，因此 Hilbert 回放不再经过额外的
严格包装层。本模块只保留三类长期接口：
* 把源 Hilbert 理论解释到任意目标自然演绎背景；
* 在 Hilbert 归约像内给出双向等价；
* 同时携带自然演绎回放与有限 Hilbert 列表的充分性证书。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
universe u v w
namespace HilbertDerives
/--
把源 Hilbert 理论的每条公理解释为目标自然演绎后，整棵 Hilbert 推导可在目标理论
和上下文中回放。
-/
theorem interpret_m
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {source target : Theory σ} {targetContext : Context σ} (hTheory :
      ∀ formula, source formula →
        Formula.Admissible formula →
          Derives target targetContext formula)
    {formula : Formula σ} (hDerives : HilbertDerives source formula) :
    Derives target targetContext formula := by
  induction hDerives with
  | logical_axiom hAxiom hAdmissible =>
      exact (hAxiom.derives_empty hAdmissible).of_empty
  | theory_axiom hSource hAdmissible =>
      exact hTheory _ hSource hAdmissible
  | modus_ponens hAntecedent hImplication
      ihAntecedent ihImplication =>
      exact ihImplication.imp_elim ihAntecedent
end HilbertDerives
namespace HilbertProof
/-- 标准有限 Hilbert 列表中的任意一行都可回放为自然演绎。 -/
theorem derives_mem_m
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {theory : Theory σ} {proof : List (Formula σ)} (hProof : HilbertProof theory proof)
    {formula : Formula σ} (hFormula : formula ∈ proof) :
    Derives theory [] formula := (hProof.derives_of_mem hFormula).to_derives
end HilbertProof
/-- 在 Hilbert 归约像内，标准 Hilbert 演绎与自然演绎完全等价。 -/
theorem hilbert_derives_iff_m
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {anchorSort : σ.SortSymbol}
    {sourceTheory : Theory σ} {sourceContext : Context σ}
    {sourceFormula : Formula σ} :
    HilbertDerives (Theory.hilbertize_context
          anchorSort sourceTheory sourceContext) (Formula.hilbertize anchorSort sourceFormula) ↔
      Derives (Theory.hilbertize_context
          anchorSort sourceTheory sourceContext)
        [] (Formula.hilbertize anchorSort sourceFormula) := by
  constructor
  · exact HilbertDerives.to_derives
  · exact Derives.normalized_to_hilbert anchorSort
/-- Hilbert 推导对应的外部充分性证书。 -/
structure HilbertAdequacyCertificate
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (theory : Theory σ) (formula : Formula σ) where
  derivation : Derives theory [] formula
  initial : List (Formula σ)
  proof : HilbertProof theory (initial ++ [formula])
namespace HilbertAdequacyCertificate
/-- 充分性证书自动给出目标公式 admissibility。 -/
theorem admissible_m
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {theory : Theory σ} {formula : Formula σ} (certificate : HilbertAdequacyCertificate theory formula) :
    Formula.Admissible formula :=
  certificate.derivation.admissible
end HilbertAdequacyCertificate
namespace HilbertDerives
/-- 一棵 Hilbert 推导一次性给出自然演绎回放与标准有限证明。 -/
noncomputable def adequacy_certificate_m
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {theory : Theory σ} {formula : Formula σ} (hDerives : HilbertDerives theory formula) :
    HilbertAdequacyCertificate theory formula := by
  let witness := HilbertProof.exists_finite hDerives
  let initial := Classical.choose witness
  let hProof := Classical.choose_spec witness
  exact
    { derivation := hDerives.to_derives
      initial := initial
      proof := hProof }
end HilbertDerives
/-- Hilbert 可演绎性等价于存在充分性证书。 -/
theorem hilbert_certificate_iff_m
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {theory : Theory σ} {formula : Formula σ} :
    HilbertDerives theory formula ↔
      Nonempty (HilbertAdequacyCertificate theory formula) := by
  constructor
  · intro hDerives
    exact ⟨hDerives.adequacy_certificate_m⟩
  · rintro ⟨certificate⟩
    exact certificate.proof.derives_of_mem (by simp)
end FirstOrder
end Logic
end YesMetaZFC
