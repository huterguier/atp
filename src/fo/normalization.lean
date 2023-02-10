import fo.basic
import fo.herbrand


@[reducible] 
def signature.clause (σ : signature) : Type := multiset σ.literal

@[reducible] 
def signature.cnf (σ : signature) : Type := finset σ.clause

def signature.symbols (σ : signature) :=
  σ.function ⊕ σ.relation

def signature.formula.is_closed {σ : signature} (φ : σ.formula) : Prop :=
  ∀ v, φ.is_free v

def signature.formula.is_prenex {σ : signature} (φ : σ.formula) : Prop :=


def signature.formula.prenex_normal_form {σ : signature} (φ : σ.formula) : σ.formula :=
  

def signature.formula.normal_form {σ : signature} (φ : σ.formula) :  := 


theorem normal_form {σ : signature}  : ∃ f, ∀ φ, f.
