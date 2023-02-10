import fo.normalization

constant σ : signature
constant l₁ : σ.literal

def signature.clause (σ : signature) := multiset σ.literal

noncomputable def c₁ : σ.clause := {l₁}

noncomputable def c₂ : σ.clause := ({l₁} : multiset σ.literal)