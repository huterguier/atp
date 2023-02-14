import data.real.basic

inductive test1 
  | anker : test1
  | recc (n : nat) (r : fin n → test1 ) : test1



lemma limit_inv_succ_my : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1/(n + 1 : ℝ) ≤ ε :=
  begin
    intro ε,
    intro ε_pos,
    suffices : ∃ N : ℕ, 1/(N:ℝ) ≤ ε,
      cases this with N HN,
    use N,
    intro n,
    intro hn,
    have hq : 1 / (n + 1) ≤ 1 / N,
    rw one_div_le_one_div,
  end



theorem trans_more_general : transitive more_general :=
  begin
    unfold transitive,
    intros t₁ t₂ t₃,
    intros h₁ h₂,
    unfold more_general at h₁,
    cases h₁ with σ₁ h₁,
    unfold more_general at h₂,
    cases h₂ with σ₂ h₂,
    unfold more_general,
    existsi (λ v : var, subst_term σ₂ (σ₁ v)),
    rw subst_comp,
    rw h₂,
    rw h₁,
  end

lemma term_more_general_subst_term : ∀ (σ : subst) (t : term), more_general t (subst_term σ t) :=
  begin
    intro σ,
    intro t,
    unfold more_general,
    cases t,
    existsi σ,
    refl,
    existsi σ,
    refl,
  end

def term_equiv (t₁ : term) (t₂ : term) : Prop :=
  more_general t₁ t₂ ∧ more_general t₂ t₁



lemma refl_term_equiv : reflexive term_equiv :=
  begin
    unfold reflexive,
    intro x,
    unfold term_equiv,
    apply and.intro,
    existsi id_subst,
    exact (term_eq_id_subst_term x),
    existsi id_subst,
    exact (term_eq_id_subst_term x),
  end

lemma trans_term_equiv : transitive term_equiv :=
  begin
    unfold transitive,
    intros t₁ t₂ t₃,
    intros h₁ h₂,
    unfold term_equiv,
    unfold term_equiv at h₁ h₂,
    cases h₁,
    cases h₂,
    split,
    exact trans_more_general h₁_left h₂_left,
    exact trans_more_general h₂_right h₁_right,
  end

lemma symm_term_equiv : symmetric term_equiv :=
  begin
    unfold symmetric,
    intros t₁ t₂,
    intro h,
    unfold term_equiv,
    unfold term_equiv at h,
    cases h with h₁ h₂,
    split,
    exact h₂,
    exact h₁,
  end

theorem equiv_term_equiv : equivalence term_equiv :=
  begin
    unfold equivalence,
    split,
    exact refl_term_equiv,
    split,
    exact symm_term_equiv,
    exact trans_term_equiv,
  end





