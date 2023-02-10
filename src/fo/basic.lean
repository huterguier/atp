import data.finset

universe u

structure signature : Type (u + 1) :=
  (function : Type u)
  (relation : Type u)
  (farity : function → nat)
  (rarity : relation → nat)


def signature.var (σ : signature) := nat

def signature.nary (σ : signature) (n : ℕ) := 
  subtype {f : σ.function | σ.farity f = n}  

def signature.rnary (σ : signature) (n : ℕ) :=
  subtype {r : σ.relation | σ.rarity r = n} 

def signature.function.arity {σ : signature} (f : σ.function) :=
  σ.farity f

def signature.relation.arity {σ : signature} (r : σ.relation) :=
  σ.rarity r

----------
-- term --
----------

inductive signature.term (σ : signature) 
  | var : σ.var → signature.term
  | func (f : σ.function) (ts : fin (σ.farity f) → signature.term) : signature.term

def signature.term.var_finset {σ : signature} : σ.term → finset σ.var
  | (term.var v) := {v}
  | (term.func f ts) := finset.univ.bUnion (λ i, (ts i).var_finset)

def signature.term.arity {σ : signature} : σ.term → nat 
  | (term.var v) := 0
  | (term.func f ts) := f.arity

@[reducible]
def signature.function.input {σ : signature} (f : σ.function) := 
  (fin f.arity) → σ.term

inductive signature.term.position {σ : signature} (t : σ.term) 
  | ε : signature.term.position
  | pos (i : fin t.arity) (p : signature.term.position) : signature.term.position
  

def signature.term.is_ground {σ : signature} : σ.term → Prop 
  | (term.var v) := false
  | (term.func f ts) := ∀ i, (ts i).is_ground

def signature.ground_term (σ : signature) :=
  subtype {t : σ.term | t.is_ground}

def signature.term.is_subterm {σ : signature} : σ.term → σ.term → Prop
  | t (term.func f ts) := t = (term.func f ts) ∨ ∃ i, t.is_subterm (ts i)
  | t₁ t₂ := t₁ = t₂

section term_order
  variable σ : signature

inductive less_than_or_equal (a : ℕ) : ℕ → Prop
    | refl : less_than_or_equal a
    | step : Π {b}, less_than_or_equal b → less_than_or_equal (nat.succ b)

  variable f : σ.function
  variable ts : (fin f.arity) → σ.term  

  lemma signature.argument_is_subterm : ∀ (i : fin f.arity), (ts i) ≤ (term.func f ts) :=
    begin 
      intro i,
      unfold has_le.le,
      right,
      existsi i,
      exact σ.refl_is_subterm (ts i),
    end

end term_order

@[reducible]
def signature.term.subterm {σ : signature} (t : σ.term) :=
  subtype {t' : σ.term | t' ≤ t}

def signature.term.position.next_term {σ : signature} : Π (t : σ.term) (p : t.position), t.subterm 
  | (term.func f ts) (position.pos i p') := ⟨(ts i), σ.argument_is_subterm f ts i⟩
  | t p := ⟨t, σ.refl_is_subterm t⟩


def signature.substitution (σ : signature) :=
  σ.var → σ.term

class signature.substitutable (σ : signature) (α : Type u) :=
  (substitute : α → σ.substitution → α)

infix ` ↓ `: 80 := (signature.substitutable.substitute) 

-------------
-- formula --
-------------


inductive signature.formula (σ : signature)
  | tt: signature.formula
  | ff : signature.formula
  | neg : signature.formula → signature.formula
  | conj {n : nat} (ngeq : n ≥ 2) (f : (fin n) → signature.formula) : signature.formula
  | disj {n : nat} (ngeq : n ≥ 2) (f : (fin n) → signature.formula) : signature.formula
  | fall (v : nat) (f : signature.formula) : signature.formula
  | xist (v : nat) (f : signature.formula) : signature.formula
  | rel (r : σ.relation) (ts : (fin (σ.rarity r)) → σ.term) : signature.formula

def signature.formula.complement {σ : signature} : σ.formula → σ.formula 
  | (formula.neg φ) := φ
  | φ := (formula.neg φ)

def signature.formula.is_subformula {σ : signature} : σ.formula → σ.formula → Prop
  | ψ (formula.neg φ) := (formula.neg φ) = ψ ∨ ψ.is_subformula φ
  | ψ (formula.conj hn Φ) := ψ = (formula.conj hn Φ) ∨ ∃ i, ψ.is_subformula (Φ i)
  | ψ (formula.disj hn Φ) := ψ = (formula.disj hn Φ) ∨ ∃ i, ψ.is_subformula (Φ i)
  | ψ (formula.fall v φ) := ψ = (formula.fall v φ) ∨ ψ.is_subformula φ
  | ψ (formula.xist v φ) := ψ = (formula.xist v φ) ∨ ψ.is_subformula φ
  | φ ψ := φ = ψ

def signature.formula.subformula {σ : signature} (φ : σ.formula) :=
  subtype {ψ : σ.formula | ψ.is_subformula φ}

def signature.literal (σ : signature) :=
  subtype {f : σ.formula | ∃ r ts, f = formula.rel r ts ∨ f = formula.neg (formula.rel r ts)}

def signature.formula.is_free {σ : signature} : σ.formula → σ.var → Prop
  | (formula.neg φ) v := φ.is_free v
  | (formula.conj hn Φ) v := ∀ i, (Φ i).is_free v
  | (formula.disj hn Φ) v := ∀ i, (Φ i).is_free v
  | (formula.fall v' φ) v := v ≠ v' ∧ φ.is_free v
  | (formula.xist v' φ) v := v ≠ v' ∧ φ.is_free v
  | f v := true 

