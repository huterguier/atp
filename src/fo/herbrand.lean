import fo.basic
import fo.semantics

universe u

open signature

def signature.herbrand_model (σ : signature) (int : (σ.interpretation σ.ground_term)) : σ.model :=
  signature.model.mk σ.ground_term int

inductive signature.function_extension (σ : signature)
  | function : σ.function → signature.function_extension
  | skolem : nat → signature.function_extension

def signature.function.skolem_extension {σ : signature} (f : σ.function) : σ.function_extension :=
  function_extension.function f

def signature.arity_extension (σ : signature) : σ.function_extension → nat
  | (function_extension.function f) := (σ.farity f)
  | (function_extension.skolem n) := n

def signature.skolem_extension (σ : signature) : signature :=
  signature.mk 
    (σ.function_extension)
    σ.relation
    (σ.arity_extension)
    σ.rarity

def signature.term.skolem_extension {σ : signature} : σ.term → σ.skolem_extension.term 
  | (term.app f ts) := (term.app (f.skolem_extension) (λ i, (ts i).skolem_extension))
  | (term.var v) := (term.var v)

def signature.formula.skolem_extension {σ : signature} : σ.formula → σ.skolem_extension.formula
  | (formula.tt) := formula.tt
  | (formula.ff) := formula.ff
  | (formula.neg φ) := φ.skolem_extension
  | (formula.conj hn Φ) := formula.conj hn (λ i, (Φ i).skolem_extension)
  | (formula.disj hn Φ) := formula.disj hn (λ i, (Φ i).skolem_extension)
  | (formula.fall x φ) := formula.fall x φ.skolem_extension
  | (formula.xist x φ) := formula.xist x φ.skolem_extension
  | (signature.formula.rel r ts) := (signature.formula.rel r (λ i, (ts i).skolem_extension))


variable σ : signature

constant d : σ.function_extension

#check d.arity