import fo.normalization



def σ : signature := 
  {
    function := nat,
    relation := nat,
    farity := id,
    rarity := id,
  }

def t₁ : σ.term := signature.term.var (2:nat)

def t₂ : σ.term := signature.term.app (2:nat) (λ i, t₁)

def φ₁ : σ.formula := signature.formula.tt

lemma geq2 : 2 ≥ 2 :=
  by simp

def φ₂ : σ.formula := signature.formula.conj geq2 (λ i, φ₁)

def φ₃ : σ.formula := signature.formula.rel (1:nat) (λ i, t₂)

lemma φ₃_isliteral : ∃ r ts, φ₃ = signature.formula.rel r ts ∨ φ₃ = signature.formula.neg (signature.formula.rel r ts) :=
  begin
    existsi (1:nat),
    existsi (λ i, t₂),
    left,
    refl,
  end
universe u

@[reducible]
def tstyp := nat

def a : tstyp := (3:nat)

def b : tstyp := (4:nat)

def tst : multiset tstyp := {1,3}


def l₁ : σ.literal := subtype.mk φ₃ φ₃_isliteral

variable σ : signature

def c₁ : σ.clause := {l₁}

constant σ : signature

constant ll1 : ss2.literal

noncomputable def cc : ss2.clause := {ll1}