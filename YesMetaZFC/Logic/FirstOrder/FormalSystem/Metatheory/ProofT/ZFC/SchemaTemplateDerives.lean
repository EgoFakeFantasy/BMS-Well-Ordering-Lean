import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaTemplate
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicKernel

/-!
# 三类模式模板的同一对象公式与正负推导

输入为模板标签、三个正文码槽位及任意候选输出码。公式既不嵌入宿主算出的结论，
也不依赖参数数目。槽位的正文识别和重命名由前一层提供；本层证明固定装配步骤。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaTemplate
open Nonlogical.BasicSetTheory QuineEncoding NatPacket IntrinsicQuotation
open _root_.YesMetaZFC.Automation ObjectTreeTemplate
open _root_.YesMetaZFC.SetTheory
open _root_.YesMetaZFC.SetTheory.Definitional
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def program : List (Nat × Template 3) :=
  [(0, separation), (1, collection), (2, replacement)]

theorem program_entry (kind : Kind) : (kind.tag, kind.shape) ∈ program := by
  cases kind <;> simp [program, Kind.tag, Kind.shape]

theorem shape_of_tag (kind : Kind) (entry : Nat × Template 3)
    (hEntry : entry ∈ program) (hTag : kind.tag = entry.1) : entry.2 = kind.shape := by
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at hEntry
  rcases hEntry with rfl | rfl | rfl <;> cases kind <;> simp_all [Kind.tag, Kind.shape]

def condition {bound free : SetContext} (tag : SetTerm bound free)
    (inputs : Fin 3 → SetTerm bound free) (output : SetTerm bound free) : SetFormula bound free :=
  ObjectTreeTemplate.graph program tag inputs output

theorem condition_delta0 {bound free : SetContext} (tag : SetTerm bound free)
    (inputs : Fin 3 → SetTerm bound free) (output : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound (condition tag inputs output) :=
  ObjectTreeTemplate.graph_delta0 program tag inputs output

@[simp] theorem condition_substituteMapped {sb sf tb tf : SetContext}
    (tag : SetTerm sb sf) (inputs : Fin 3 → SetTerm sb sf) (output : SetTerm sb sf)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (condition tag inputs output).substituteMapped bs fs =
      condition (tag.substituteMapped bs fs) (fun i => (inputs i).substituteMapped bs fs)
        (output.substituteMapped bs fs) := ObjectTreeTemplate.graph_substituteMapped _ _ _ _ _ _

/-- 五个固定 free 槽位：种类、三个正文位置、输出。 -/
def template : FormulaTemplate [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set] where
  body := condition (.fvar .here)
    (fun i => if i.val = 0 then .fvar (.there .here)
      else if i.val = 1 then .fvar (.there (.there .here))
      else .fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))

theorem template_apply {bound free : SetContext} (tag : SetTerm bound free)
    (inputs : Fin 3 → SetTerm bound free) (output : SetTerm bound free) :
    template.instantiate (VariableSubstitution.cons tag
      (VariableSubstitution.cons (inputs 0) (VariableSubstitution.cons (inputs 1)
        (VariableSubstitution.cons (inputs 2) (VariableSubstitution.cons output
          VariableSubstitution.empty))))) = condition tag inputs output := by
  simp only [FormulaTemplate.instantiate, template, condition_substituteMapped]
  congr 1
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> rfl

theorem template_delta0 : Formula.IsDelta0 set_levy_bound template.body := condition_delta0 _ _ _

/-- 标准数值槽位可以是任意自然数，不预先要求它们是合法正文树码。 -/
theorem positive (kind : Kind) (inputs : Fin 3 → Nat) (output : Nat)
    (h : kind.shape.expr.eval inputs = output) :
    Derives intrinsic_zfc_theory []
      (condition (numₘ(kind.tag)) (fun i => numₘ(inputs i)) (numₘ(output) : Code)) :=
  ObjectTreeTemplate.graph_positive program kind.tag _ _ kind.shape (program_entry kind)
    (kind.shape.positive intrinsic_zfc_certificate_core inputs output h)

theorem negative (kind : Kind) (inputs : Fin 3 → Nat) (output : Nat)
    (h : kind.shape.expr.eval inputs ≠ output) :
    Derives intrinsic_zfc_theory []
      (¬ₘ condition (numₘ(kind.tag)) (fun i => numₘ(inputs i)) (numₘ(output) : Code)) := by
  apply ObjectTreeTemplate.graph_negative intrinsic_zfc_certificate_core
  intro entry hEntry hTag
  rw [shape_of_tag kind entry hEntry hTag]
  exact kind.shape.negative intrinsic_zfc_certificate_core inputs output h

theorem positive_at_tree (kind : Kind) (inputs : Fin 3 → Tree) (output : Tree)
    (h : build kind inputs = output) :
    Derives intrinsic_zfc_theory []
      (condition (numₘ(kind.tag)) (fun i => tree (inputs i)) (tree output)) :=
  ObjectTreeTemplate.graph_positive program kind.tag _ _ kind.shape (program_entry kind)
    (kind.shape.positive_at_tree inputs output h)

/-- 候选输出允许任意畸形原始树；只要不是逐节点装配结果就可否定。 -/
theorem negative_at_tree (kind : Kind) (inputs : Fin 3 → Tree) (output : Tree)
    (h : build kind inputs ≠ output) :
    Derives intrinsic_zfc_theory []
      (¬ₘ condition (numₘ(kind.tag)) (fun i => tree (inputs i)) (tree output)) := by
  apply ObjectTreeTemplate.graph_negative intrinsic_zfc_certificate_core
  intro entry hEntry hTag
  rw [shape_of_tag kind entry hEntry hTag]
  exact kind.shape.negative_at_tree intrinsic_zfc_certificate_core inputs output h

/-- 未知模板标签在任意闭项槽位上被拒绝，不需要槽位可解析。 -/
theorem unknown_tag_negative (tag : Nat) (inputs : Fin 3 → Code) (output : Code)
    (h0 : tag ≠ 0) (h1 : tag ≠ 1) (h2 : tag ≠ 2) :
    Derives intrinsic_zfc_theory [] (¬ₘ condition (numₘ(tag)) inputs output) := by
  apply ObjectTreeTemplate.graph_negative intrinsic_zfc_certificate_core
  intro entry hEntry hTag
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at hEntry
  rcases hEntry with rfl | rfl | rfl
  · exact False.elim (h0 hTag)
  · exact False.elim (h1 hTag)
  · exact False.elim (h2 hTag)

/-- 以下出口直接连接仓库中的实际模式核心，参数数目任意。 -/
theorem separation_positive {n : Nat}
    (schema : Project.UnarySchema n) :
    Derives intrinsic_zfc_theory [] (condition (numₘ(0))
      (fun i => tree (one (ProjectEncode.formula (schema.body.rename
        BoundEmbedding.unaryUnderTwo)) i))
      (tree (ProjectEncode.formula (Axioms.Schema.separationCore schema)))) :=
  positive_at_tree .separation _ _ (separation_core schema)

theorem collection_positive {n : Nat}
    (schema : Project.BinarySchema n) :
    Derives intrinsic_zfc_theory [] (condition (numₘ(1))
      (fun i => tree (two
        (ProjectEncode.formula (schema.body.rename BoundEmbedding.binaryUnderOne))
        (ProjectEncode.formula (schema.body.rename BoundEmbedding.binaryUnderTwo)) i))
      (tree (ProjectEncode.formula (Axioms.Schema.collectionCore schema)))) :=
  positive_at_tree .collection _ _ (collection_core schema)

theorem replacement_positive {n : Nat}
    (schema : Project.BinarySchema n) :
    Derives intrinsic_zfc_theory [] (condition (numₘ(2))
      (fun i => tree (three
        (ProjectEncode.formula (schema.body.rename Axioms.Schema.ReplacementEmbedding.firstOutput))
        (ProjectEncode.formula (schema.body.rename Axioms.Schema.ReplacementEmbedding.secondOutput))
        (ProjectEncode.formula (schema.body.rename Axioms.Schema.ReplacementEmbedding.imageBody)) i))
      (tree (ProjectEncode.formula (Axioms.Schema.replacementCore schema)))) :=
  positive_at_tree .replacement _ _ (replacement_core schema)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaTemplate
