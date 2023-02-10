import fo.substitution

universe u

open signature

def signature.term.unifier {σ : signature} (t₁ t₂ : σ.term) (ν : σ.substitution) : Prop :=
  t₁.substitute ν = t₂.substitute ν


def signature.substitution.subst {σ : signature} {α : Type} (ν : σ.substitution) [inst : σ.substitutable α] (s : finset α) : finset α :=
  finset.map (λ a : α, (a ↓ ν)) s

def signature.substitution.unifies {σ : signature} (ν : σ.substitution) (ts : finset σ.term) →
  

def signature.