import fo.basic
import fo.substitution

structure signature.interpretation (σ : signature) (domain : Type) :=
  (fint (f : σ.function) (v : (fin (σ.farity f) → domain)) : domain)
  (rint (r : σ.relation) (v : (fin (σ.rarity r) → domain)) : Prop)    

structure signature.model (σ : signature) :=
  (domain : Type)
  (int : σ.interpretation domain)

def signature.model.var_assign {σ : signature} (M : σ.model) :=
  σ.var → M.domain

def signature.model.var_assign.modify {σ : signature} {M : σ.model} (β : M.var_assign) : σ.var → M.domain → M.var_assign :=
  (λ v' d v, 
    if v' = v then
      d
    else
      (β v)
  )

def signature.term.evaluate {σ : signature} : σ.term → Π (M : σ.model) (β : M.var_assign), M.domain
  | (signature.term.var v) M β := β v
  | (signature.term.app f ts) M β := (M.int.fint f) (λ i, (ts i).evaluate M β)

def signature.formula.evaluate {σ : signature} : σ.formula → Π (M : σ.model) (β : M.var_assign), Prop 
  | (signature.formula.tt) M β := true
  | (signature.formula.neg φ) M β := ¬ φ.evaluate M β
  | (signature.formula.conj hn Φ) M β := ∀ i, (Φ i).evaluate M β
  | (signature.formula.disj hn Φ) M β := ∃ i, (Φ i).evaluate M β
  | (signature.formula.fall v φ) M β := ∀ d, φ.evaluate M (β.modify v d)
  | (signature.formula.xist v φ) M β := ∃ d, φ.evaluate M (β.modify v d)
  | (signature.formula.rel r ts) M β := (M.int.rint r) (λ i, (ts i).evaluate M β)
  | φ M β := false

def signature.model.is_model {σ : signature} (M : σ.model) (φ : σ.formula) : Prop :=
  ∀ β : M.var_assign, φ.evaluate M β

def signature.formula.is_valid {σ : signature} (φ : σ.formula) : Prop :=
  ∀ M : σ.model, M.is_model φ

def signature.formula.is_unsatisfiable {σ : signature} (φ : σ.formula) : Prop :=
  ∀ M : σ.model, ¬ M.is_model φ

def signature.formula.consequence {σ : signature} (φ ψ : σ.formula) : Prop :=
  ∀ M : σ.model, M.is_model φ → M.is_model ψ

def signature.formula.equivalent {σ : signature} (φ ψ : σ.formula) : Prop :=
  φ.consequence ψ ∧ ψ.consequence φ