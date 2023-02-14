import order.lattice dynamics.fixed_points.basic
import dynamics.fixed_points.basic
import order.hom.order

constant α : Type

theorem knaster_tarski [lat : complete_lattice α] (f : α →o α) (a : α)  : 
  (a = Sup {a : α | a ≤ (f a)}) → (f a = a) :=
  begin
    intro h,
    have mf := f.monotone,
    let P := {a : α | a ≤ (f a)},
    have hua : ∀ u ∈ P, u ≤ a := by {
      intros u hu,
      rw h,
      exact le_Sup hu,
    },
    have hufu : ∀ u ∈ P, u ≤ f u := by {
      simp,
    },
    have hfufa : ∀ u ∈ P, f u ≤ f a := by {
      intros u hu,
      apply mf,
      exact hua u hu,
    },
    have ha : a ∈ {a : α | a ≤ (f a)} := by
    {
      begin
        simp,
        by_contra,
        sorry,
      end
    },
    have pfa : f a ≤ f (f a) := by {
      apply mf,
      exact ha,
    },
    have hfaa : f a ≤ a := by {
      exact hua (f a) pfa,
    },
    exact ge_antisymm ha hfaa,
  end

theorem shroeder_bernstein (X Y : set α) (f g : α → α) : ∃ A, A ⊆ X ∧ g(Y \ f A)) = X 𝔸 :=
begin

end

theorem test (p : (nat → Prop)) : (∀ a, p a) → ∃ a, p a :=
  begin
    intro h,
    fapply exists.intro 0,
    exact h 0,
  end