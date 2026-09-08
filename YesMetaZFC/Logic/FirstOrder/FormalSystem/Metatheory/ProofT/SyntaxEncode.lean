import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SyntaxDecode

/-! # 内在语法的逆向编码与往返定理 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SyntaxEncode
open Nonlogical.BasicSetTheory NatPacket
set_option autoImplicit false

def context (free : SetContext) : Tree := leaf free.length

@[simp] theorem context_roundtrip (free : SetContext) : SyntaxDecode.context (context free) = some free := by
  have h : List.replicate free.length SetSort.set = free := by
    induction free with
    | nil => rfl
    | cons sort tail ih => cases sort; simp only [List.length_cons, List.replicate_succ, ih]
  simp [context, SyntaxDecode.context, scalar, leaf, h]

@[simp] theorem variable_roundtrip {free : SetContext} (entry : Variable free SetSort.set) :
    SyntaxDecode.decodeVariable free entry.index = some entry := by
  induction free with
  | nil => cases entry
  | cons sort tail ih =>
      cases sort
      cases entry with
      | here => rfl
      | there entry => simp only [Variable.index, SyntaxDecode.decodeVariable]; rw [ih entry]; rfl

@[simp] theorem function_roundtrip (symbol : FunctionSymbol) :
    SyntaxDecode.functionSymbols[symbol.ctorIdx]? = some symbol := by cases symbol <;> rfl

@[simp] theorem relation_roundtrip (symbol : RelationSymbol) :
    SyntaxDecode.relationSymbols[symbol.ctorIdx]? = some symbol := by cases symbol <;> rfl

mutual

def term {bound free : SetContext} {sort : SetSort} : Term signature bound free sort → Tree
  | .bvar entry => .node 0 [leaf entry.index]
  | .fvar entry => .node 1 [leaf entry.index]
  | .app symbol args => .node 2 (leaf symbol.ctorIdx :: argumentsList args)

def argumentsList {bound free sorts : SetContext} : Arguments signature bound free sorts → List Tree
  | .nil => []
  | .cons head tail => term head :: argumentsList tail
end

@[simp] theorem term_bvar {bound free : SetContext} {sort : SetSort} (entry : Variable bound sort) :
    term (.bvar entry : Term signature bound free sort) = .node 0 [leaf entry.index] := rfl
@[simp] theorem term_fvar {bound free : SetContext} {sort : SetSort} (entry : Variable free sort) :
    term (.fvar entry : Term signature bound free sort) = .node 1 [leaf entry.index] := rfl
@[simp] theorem term_app {bound free : SetContext} (symbol : FunctionSymbol)
    (args : Arguments signature bound free (signature.funcDomain symbol)) :
    term (.app symbol args) = .node 2 (leaf symbol.ctorIdx :: argumentsList args) := by
  cases symbol <;> rfl

def arguments {bound free sorts : SetContext} (args : Arguments signature bound free sorts) : Tree :=
  .node 0 (argumentsList args)

mutual
@[simp] theorem term_roundtrip {bound free : SetContext} : (input : SetTerm bound free) →
    SyntaxDecode.term bound free (term input) = some input
  | .bvar entry => by
      rw [term_bvar, SyntaxDecode.term.eq_def]
      change (SyntaxDecode.decodeVariable bound entry.index).bind (fun value => some (Term.bvar value)) = some (Term.bvar entry)
      rw [variable_roundtrip entry]
      rfl
  | .fvar entry => by
      rw [term_fvar, SyntaxDecode.term.eq_def]
      change (SyntaxDecode.decodeVariable free entry.index).bind (fun value => some (Term.fvar value)) = some (Term.fvar entry)
      rw [variable_roundtrip entry]
      rfl
  | .app symbol args => by
      rw [term_app, SyntaxDecode.term.eq_def]
      change SyntaxDecode.functionSymbols[symbol.ctorIdx]?.bind
        (fun f => (SyntaxDecode.argumentsList bound free (signature.funcDomain f) (argumentsList args)).bind (fun value => some ((SyntaxDecode.application f) value))) = some (.app symbol args)
      rw [function_roundtrip]
      change (SyntaxDecode.argumentsList bound free (signature.funcDomain symbol) (argumentsList args)).bind (fun value => some ((SyntaxDecode.application symbol) value)) = some (.app symbol args)
      rw [argumentsList_roundtrip args]
      cases symbol <;> rfl

termination_by input => sizeOf (term input)
decreasing_by rw [term_app]; simp_wf; omega

@[simp] theorem argumentsList_roundtrip {bound free : SetContext} :
    {sorts : SetContext} → (args : Arguments signature bound free sorts) →
    SyntaxDecode.argumentsList bound free sorts (argumentsList args) = some args
  | [] , .nil => by rw [argumentsList, SyntaxDecode.argumentsList.eq_def]
  | .set :: _, .cons head tail => by
      rw [argumentsList, SyntaxDecode.argumentsList.eq_def]
      change (SyntaxDecode.term bound free (term head)).bind
        (fun t => (SyntaxDecode.argumentsList bound free _ (argumentsList tail)).bind (fun value => some ((Arguments.cons t) value))) = some (.cons head tail)
      rw [term_roundtrip head]
      change (SyntaxDecode.argumentsList bound free _ (argumentsList tail)).bind (fun value => some ((Arguments.cons head) value)) = some (.cons head tail)
      rw [argumentsList_roundtrip tail]
      rfl
termination_by _ args => sizeOf (argumentsList args)
decreasing_by all_goals simp only [argumentsList]; all_goals simp_wf; all_goals omega
end

@[simp] theorem arguments_roundtrip {bound free sorts : SetContext} (args : Arguments signature bound free sorts) :
    SyntaxDecode.arguments bound free sorts (arguments args) = some args := by
  simp [arguments, SyntaxDecode.arguments]

def formula {bound free : SetContext} : SetFormula bound free → Tree
  | .falsum => leaf 0
  | .truth => leaf 1
  | .rel symbol args => .node 2 (leaf symbol.ctorIdx :: argumentsList args)
  | .equal left right => .node 3 [term left, term right]
  | .neg body => .node 4 [formula body]
  | .conj left right => .node 5 [formula left, formula right]
  | .disj left right => .node 6 [formula left, formula right]
  | .imp left right => .node 7 [formula left, formula right]
  | .iff left right => .node 8 [formula left, formula right]
  | .forallE _ body => .node 9 [formula body]
  | .existsE _ body => .node 10 [formula body]

@[simp] theorem formula_roundtrip {bound free : SetContext} (input : SetFormula bound free) :
    SyntaxDecode.formula bound free (formula input) = some input := by
  induction input with
  | falsum => rw [formula, leaf, SyntaxDecode.formula.eq_def]; rfl
  | truth => rw [formula, leaf, SyntaxDecode.formula.eq_def]; rfl
  | rel symbol args =>
      rw [formula, SyntaxDecode.formula.eq_def]
      change SyntaxDecode.relationSymbols[symbol.ctorIdx]?.bind
        (fun r => (SyntaxDecode.argumentsList _ _ (signature.relDomain r) (argumentsList args)).bind (fun value => some ((Formula.rel r) value))) = some (.rel symbol args)
      rw [relation_roundtrip]
      change (SyntaxDecode.argumentsList _ _ _ (argumentsList args)).bind (fun value => some ((Formula.rel symbol) value)) = some (.rel symbol args)
      rw [argumentsList_roundtrip args]
      rfl
  | @equal b f sort left right =>
      cases sort
      rw [formula, SyntaxDecode.formula.eq_def]
      change (SyntaxDecode.term b f (term left)).bind (fun l => (SyntaxDecode.term b f (term right)).bind (fun value => some ((Formula.equal l) value))) = some (.equal left right)
      rw [term_roundtrip]
      change (SyntaxDecode.term b f (term right)).bind (fun value => some ((Formula.equal left) value)) = some (.equal left right)
      rw [term_roundtrip right]
      rfl
  | neg body ih =>
      rw [formula, SyntaxDecode.formula.eq_def]
      change (SyntaxDecode.formula _ _ (formula body)).bind (fun value => some (Formula.neg value)) = some (.neg body)
      rw [ih]
      rfl
  | conj left right ihLeft ihRight =>
      rw [formula, SyntaxDecode.formula.eq_def]
      change (SyntaxDecode.formula _ _ (formula left)).bind
        (fun l => (SyntaxDecode.formula _ _ (formula right)).bind (fun value => some ((Formula.conj l) value))) = some (.conj left right)
      rw [ihLeft]
      change (SyntaxDecode.formula _ _ (formula right)).bind (fun value => some ((Formula.conj left) value)) = some (.conj left right)
      rw [ihRight]
      rfl
  | disj left right ihLeft ihRight =>
      rw [formula, SyntaxDecode.formula.eq_def]
      change (SyntaxDecode.formula _ _ (formula left)).bind
        (fun l => (SyntaxDecode.formula _ _ (formula right)).bind (fun value => some ((Formula.disj l) value))) = some (.disj left right)
      rw [ihLeft]
      change (SyntaxDecode.formula _ _ (formula right)).bind (fun value => some ((Formula.disj left) value)) = some (.disj left right)
      rw [ihRight]
      rfl
  | imp left right ihLeft ihRight =>
      rw [formula, SyntaxDecode.formula.eq_def]
      change (SyntaxDecode.formula _ _ (formula left)).bind
        (fun l => (SyntaxDecode.formula _ _ (formula right)).bind (fun value => some ((Formula.imp l) value))) = some (.imp left right)
      rw [ihLeft]
      change (SyntaxDecode.formula _ _ (formula right)).bind (fun value => some ((Formula.imp left) value)) = some (.imp left right)
      rw [ihRight]
      rfl
  | iff left right ihLeft ihRight =>
      rw [formula, SyntaxDecode.formula.eq_def]
      change (SyntaxDecode.formula _ _ (formula left)).bind
        (fun l => (SyntaxDecode.formula _ _ (formula right)).bind (fun value => some ((Formula.iff l) value))) = some (.iff left right)
      rw [ihLeft]
      change (SyntaxDecode.formula _ _ (formula right)).bind (fun value => some ((Formula.iff left) value)) = some (.iff left right)
      rw [ihRight]
      rfl
  | forallE sort body ih =>
      cases sort
      rw [formula, SyntaxDecode.formula.eq_def]
      change (SyntaxDecode.formula _ _ (formula body)).bind (fun value => some ((Formula.forallE SetSort.set) value)) = some (Formula.forallE (σ := signature) SetSort.set body)
      rw [ih]
      rfl
  | existsE sort body ih =>
      cases sort
      rw [formula, SyntaxDecode.formula.eq_def]
      change (SyntaxDecode.formula _ _ (formula body)).bind (fun value => some ((Formula.existsE SetSort.set) value)) = some (Formula.existsE (σ := signature) SetSort.set body)
      rw [ih]
      rfl

/-- 把函数形式的统一替换按源上下文顺序还原成有限参数列。 -/
def substitutionArguments {bound free : SetContext} : (source : SetContext) →
    VariableSubstitution signature source bound free → Arguments signature bound free source
  | [] , _ => .nil
  | .set :: tail, subst => .cons (subst .here) (substitutionArguments tail (fun entry => subst (.there entry)))

@[simp] theorem substitution_roundtrip {bound free : SetContext} (source : SetContext)
    (subst : VariableSubstitution signature source bound free) :
    @SyntaxDecode.substitution bound free source (substitutionArguments source subst) = @subst := by
  induction source with
  | nil => funext sort entry; cases entry
  | cons sort tail ih =>
      cases sort
      funext sort entry
      cases entry with
      | here => rfl
      | there entry => exact congrFun (congrFun (ih (fun entry => subst (.there entry))) _) entry
end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SyntaxEncode
