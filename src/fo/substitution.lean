import fo.basic
import tactic

open signature


def signature.substitution.domain {σ : signature} (ν : σ.substitution) :=
  subtype {v : σ.var | ν v ≠ (term.var v)}


@[simp]
def signature.substitution.is_ground {σ : signature} (ν : σ.substitution) :=
  ∀ v, (ν v).is_ground

def signature.ground_substitution (σ : signature) : Type :=
  subtype {ν : σ.substitution | ν.is_ground}

def signature.variable_renaming (σ : signature) (r : σ.var → σ.var) (h : function.bijective r) : σ.substitution :=
  (λ v, term.var (r v))

def signature.substitution.free {σ : signature} : σ.substitution → σ.var → σ.substitution :=
  (λ ν v v',
      if (v = v') then
        term.var v
      else
        (ν v)
  )

@[reducible]
def signature.term.substitute {σ : signature} : σ.term → σ.substitution → σ.term 
  | (term.var v) ν := (ν v)
  | (term.func f ts) ν := term.func f (λ i, (ts i).substitute ν)

@[reducible]
instance signature.subst_term {σ : signature} : σ.substitutable σ.term :=
  {substitute := signature.term.substitute}

@[reducible]
def signature.substitution.substitute {σ : signature} (ρ ν : σ.substitution) : σ.substitution :=
  (λ v : σ.var, (ρ v) ↓ ν)

@[reducible]
instance signature.subst_substitution {σ : signature} : σ.substitutable σ.substitution :=
  {
    substitute := signature.substitution.substitute
  }

@[reducible]
def signature.var.occurrs {σ : signature} : σ.var → σ.term → Prop 
  | v (term.var v') := v = v'
  | v (term.func f ts) := ∃ i, v.occurrs (ts i)

def signature.var.is_bound {σ : signature} (v : σ.var) (φ : σ.formula) : Prop :=
  ¬φ.is_free v

@[simp]
def signature.formula.substitute {σ : signature} : σ.formula → σ.substitution → σ.formula
  | (formula.neg φ) ν := φ.substitute ν
  | (formula.conj hn Φ) ν := formula.conj hn (λ i, (Φ i).substitute ν)
  | (formula.disj hn Φ) ν := formula.disj hn (λ i, (Φ i).substitute ν)
  | (formula.fall x φ) ν := formula.fall x (φ.substitute (ν.free x))
  | (formula.xist x φ) ν := formula.xist x (φ.substitute (ν.free x))
  | (formula.rel r ts) ν := formula.rel r (λ i, (ts i).substitute ν)
  | φ ν := φ

@[reducible]
instance signature.sub_formula {σ : signature} : σ.substitutable σ.formula :=
  {
    substitute := signature.formula.substitute
  }

def signature.term.contains {σ : signature} : σ.term → σ.var → Prop 
  | (term.var v') v := v' = v
  | (term.func f ts) v := ∃ i, (ts i).contains v
  
@[reducible]
def signature.formula.contains {σ : signature} : σ.formula → σ.var → Prop 
  | (formula.neg φ) v := φ.contains v
  | (formula.conj hn Φ) v := ∃ i, (Φ i).contains v
  | (formula.disj hn Φ) v := ∃ i, (Φ i).contains v
  | (formula.fall x φ) v := φ.contains v
  | (formula.xist x φ) v := φ.contains v
  | (formula.rel r ts) v := (∃ i, v.occurrs (ts i))
  | φ v := false

@[reducible]
def signature.substitution.is_free {σ : signature} : σ.substitution → σ.formula → Prop 
  | ν (formula.neg φ) := ν.is_free φ
  | ν (formula.conj hn Φ) := ∀ i, ν.is_free (Φ i)
  | ν (formula.disj hn Φ) := ∀ i, ν.is_free (Φ i)
  | ν (formula.fall x φ) := (∀ v : σ.var, (φ.contains v → φ.is_free v → ¬(ν v).contains x)) ∧ ν.is_free φ
  | ν (formula.xist x φ) := (∀ v : σ.var, (φ.contains v → φ.is_free v → ¬(ν v).contains x)) ∧ ν.is_free φ
  | ν φ := true


@[reducible]
def signature.substitution.is_free1 {σ : signature} (ν : σ.substitution) (φ : σ.formula) : Prop :=
  ∀ (v : σ.var), (φ.is_free v) → ∀ (v' : σ.var), v'.occurrs (ν v) → φ.is_free v'
 
def signature.substitution.compose {σ : signature} (ν₁ : σ.substitution) (ν₂ : σ.substitution) : σ.substitution :=
  (λ v, (ν₁ v).substitute ν₂)

def signature.substitution.id {σ : signature} : σ.substitution :=
  (λ v, term.var v)

def signature.id_subst (σ : signature) : σ.substitution :=
  (λ v : σ.var, term.var v)

def subid {σ : signature} : σ.substitution := 
  (λ v : σ.var, term.var v)

lemma signature.term.term_eq_term_subst_id {σ : signature} : ∀ t : σ.term, t ↓ σ.id_subst = t :=
  begin
    intro t,
    induction t with v f ts,
    simp,
    refl,
    simp [signature.term.substitute],
    dsimp at t_ih,
    ext i,
    exact (t_ih i),
  end 

def signature.term.more_general {σ : signature} (t₁ t₂ : σ.term) : Prop :=
  ∃ (ν : σ.substitution), t₁ ↓ ν = t₂


section more_general_preorder

  variable σ : signature
  variable t : σ.term
  variable ν₁ : σ.substitution
  variable ν₂ : σ.substitution

  lemma signature.compose_sub : ((t ↓ ν₁) ↓ ν₂) = t ↓ (ν₁ ↓ ν₂) :=
    begin
      induction t with v f ts ih,
      simp,
      dsimp at ih,
      simp [signature.term.substitute],
      ext i,
      exact ih i,
    end

  lemma refl_more_general : (reflexive (@signature.term.more_general σ)) :=
    begin
      intro t,
      existsi signature.substitution.id,
      exact signature.term.term_eq_term_subst_id t,
    end

  lemma trans_more_general : (transitive (@signature.term.more_general σ)) :=
    begin
      intros x y z hxy hyz,
      cases hxy with νx hνx,
      cases hyz with νy hνy,
      rw [← hνy, ← hνx],
      use (νx ↓ νy),
      rw signature.compose_sub,
    end

end more_general_preorder


section

  variable σ : signature
  variable t : σ.term
  variable φ : σ.formula
  variable ν₁ : σ.substitution
  variable ν₂ : σ.substitution

  lemma signature.compose_free (h : ν₁.is_free φ) : ∀ v, (φ ↓ (ν₁.free v ↓ ν₂.free v)) = (φ ↓ (ν₁ ↓ ν₂).free v) :=
    begin
      sorry,
    end

  lemma signature.sub_free_eq_imp_sub_eq (h : ν₁.is_free φ) : ∀ v, (φ ↓ ν₁) ↓ ν₂ = φ ↓ (ν₁ ↓ ν₂) → (φ ↓ ν₁.free v ↓ ν₂.free v) = (φ ↓ (ν₁.free v ↓ ν₂.free v)) :=
    begin
      intro v,
      intro h',
      induction φ,
      simp,
      simp,
      simp,
      {
        exact (φ_ih h) h',
      },
      {
        simp [signature.formula.substitute],
        ext j,
        simp [signature.substitution.is_free] at h,
        simp at h',
        dsimp at φ_ih,
        exact φ_ih i (h j) (h' j),
      }
      sorry,
      sorry,
      sorry,
      sorry,
      sorry,
      sorry,
    end

  theorem signature.compose_sub_formula1 (h : ν₁.is_free φ) : (φ ↓ ν₁) ↓ ν₂ = φ ↓ (ν₁ ↓ ν₂) :=
    begin
      induction φ,
      refl,refl,
      {
        simp [signature.formula.substitute],
        exact φ_ih h,
      },
      {
        simp [signature.formula.substitute],
        ext i,
        dsimp at *,
        have h' := φ_ih i,
        simp [signature.substitution.is_free] at h,
        exact h' (h i),
      },
      {
        simp [signature.formula.substitute],
        ext i,
        dsimp at *,
        have h' := φ_ih i,
        simp [signature.substitution.is_free] at h,
        exact h' (h i),
      },
      {
        simp [signature.formula.substitute],
        simp [signature.substitution.is_free] at h,
        have h' := signature.compose_free σ φ_f ν₁ ν₂ (h.right) φ_v,
        simp [signature.formula.substitute] at h',
        rw ← h',
        apply signature.sub_free_eq_imp_sub_eq,
        exact h.right,
        exact φ_ih h.right,
      },
      {
        simp [signature.formula.substitute],
        simp [signature.substitution.is_free] at h,
        have h' := signature.compose_free σ φ_f ν₁ ν₂ (h.right) φ_v,
        simp [signature.formula.substitute] at h',
        rw ← h',
        apply signature.sub_free_eq_imp_sub_eq,
        exact h.right,
        exact φ_ih h.right,
      },
      {
        simp [signature.formula.substitute],
        ext i,
        exact signature.compose_sub σ (φ_ts i) _ _,
      },
    end

end




def signature.term.equivalent {σ : signature} (t₁ t₂ : σ.term) : Prop :=
  t₁.more_general t₂ ∧ t₂.more_general t₁


lemma signature.term.refl_equivalent {σ : signature} : reflexive (@signature.term.equivalent σ) :=
  begin 
    intro t,
    use σ.id_subst,
    rw signature.term.term_eq_term_subst_id,
    use σ.id_subst,
    rw signature.term.term_eq_term_subst_id,
  end

lemma signature.term.trans_equivalent {σ : signature} : transitive (@signature.term.equivalent σ) :=
  begin 
    intros x y z hxy hyz,
    split,
    {
      cases hxy.left with νxy h₁,
      cases hyz.left with νyz h₂,
      use (νxy ↓ νyz),
      rw ← signature.compose_sub,
      rw [h₁, h₂],
    },
    {
      cases hxy.right with νxy h₁,
      cases hyz.right with νyz h₂,
      use (νyz ↓ νxy),
      rw ← signature.compose_sub,
      rw [h₂, h₁],
    }
  end

lemma signature.term.symm_equivalent {σ : signature} : symmetric (@signature.term.equivalent σ) :=
  begin 
    intros x y hxy,
    split,
    exact hxy.right,
    exact hxy.left,
  end

lemma signature.term.equiv_equivalent {σ : signature} : equivalence (@signature.term.equivalent σ) :=
  begin
    split,
    exact signature.term.refl_equivalent, 
    split,
    exact signature.term.symm_equivalent,
    exact signature.term.trans_equivalent, 
  end

instance signature.equiv_setoid (σ : signature) : setoid σ.term :=
  {
    r := signature.term.equivalent,
    iseqv := signature.term.equiv_equivalent,
  }

@[reducible]
def signature.term_equiv (σ : signature) := quotient σ.equiv_setoid



example (σ : signature) (t : σ.term) : ⟦t⟧ = quotient.mk t :=
  begin
    refl,
  end 

lemma signature.term.substitution_is_well_defined {σ : signature} (ν : σ.substitution) (t₁ t₂ : σ.term)  (h : t₁ ≈ t₂) : ⟦t₁ ↓ ν⟧ = ⟦t₂ ↓ ν⟧ :=
  begin
    apply quotient.sound,
    cases h,
    split,
    cases h_left with ν_left hν_left,
    cases h_right with ν_right hν_right,
    sorry, sorry,
  end

def signature.term_equiv.substitute {σ : signature} (ν : σ.substitution) : σ.term_equiv → σ.term_equiv := 
  quotient.lift (λ (t : σ.term) , ⟦t ↓ ν⟧) (signature.term.substitution_is_well_defined ν)

@[reducible]
instance signature.subst_term_equiv (σ : signature) : σ.substitutable σ.term_equiv :=
  {
    substitute := (λ t ν, signature.term_equiv.substitute ν t)
  }



