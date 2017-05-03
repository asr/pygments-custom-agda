------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Syntax definitions.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.Prop.Syntax ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Bool
  renaming ( _∧_ to _&&_; _∨_ to _||_ )
  using    ( Bool; true; false; not )

open import Data.Fin  using ( Fin; #_ )
open import Data.List using ( List ; [] ; _∷_ ; _++_ ; [_] )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; cong; trans; sym; subst)

------------------------------------------------------------------------------

-- Proposition data type.

data Prop : Set where
  Var              : Fin n → Prop
  ⊤                : Prop
  ⊥                : Prop
  _∧_ _∨_ _⇒_ _⇔_  : (φ ψ : Prop) → Prop
  ¬_               : (φ : Prop) → Prop

infix  11 ¬_
infixl 8 _∧_ _∨_
infixr 7 _⇒_ _⇔_

-- Context is a list (set) of hypotesis and axioms.

Ctxt : Set
Ctxt = List Prop

infixl 5 _,_
_,_ : Ctxt → Prop → Ctxt
Γ , φ = Γ ++ [ φ ]

∅ : Ctxt
∅ = []

infix 30 _⨆_
_⨆_ : Ctxt → Ctxt → Ctxt
Γ ⨆ Δ = Γ ++ Δ

infix 4 _∈_
data _∈_ (φ : Prop) : Ctxt → Set where
  here   : ∀ {Γ} → φ ∈ Γ , φ
  there  : ∀ {Γ} → (ψ : Prop) → φ ∈ Γ → φ ∈ Γ , ψ
  ⨆-ext  : ∀ {Γ} → (Δ : Ctxt) → φ ∈ Γ → φ ∈ Γ ⨆ Δ

_⊆_ : Ctxt → Ctxt → Set
Γ ⊆ Η = ∀ {φ} → φ ∈ Γ → φ ∈ Η

------------------------------------------------------------------------
-- Theorem data type.

infix 3 _⊢_

data _⊢_ : (Γ : Ctxt)(φ : Prop) → Set where

-- Hyp.

  assume   : ∀ {Γ} → (φ : Prop)           → Γ , φ ⊢ φ

  axiom    : ∀ {Γ} → (φ : Prop)           → φ ∈ Γ
                                          → Γ ⊢ φ

  weaken   : ∀ {Γ} {φ} → (ψ : Prop)       → Γ ⊢ φ
                                          → Γ , ψ ⊢ φ

  weaken₂   : ∀ {Γ} {φ} → (ψ : Prop)      → Γ ⊢ φ
                                          → ψ ∷ Γ ⊢ φ
-- Top and Bottom.

  ⊤-intro  : ∀ {Γ}                        → Γ ⊢ ⊤

  ⊥-elim   : ∀ {Γ} → (φ : Prop)           → Γ ⊢ ⊥
                                          → Γ ⊢ φ
-- Negation.

  ¬-intro  : ∀ {Γ} {φ}                    → Γ , φ ⊢ ⊥
                                          → Γ ⊢ ¬ φ

  ¬-elim   : ∀ {Γ} {φ}                    → Γ ⊢ ¬ φ → Γ ⊢ φ
                                          → Γ ⊢ ⊥
-- Conjunction.

  ∧-intro  : ∀ {Γ} {φ ψ}                  → Γ ⊢ φ → Γ ⊢ ψ
                                          → Γ ⊢ φ ∧ ψ

  ∧-proj₁  : ∀ {Γ} {φ ψ}                  → Γ ⊢ φ ∧ ψ
                                          → Γ ⊢ φ

  ∧-proj₂  : ∀ {Γ} {φ ψ}                  → Γ ⊢ φ ∧ ψ
                                          → Γ ⊢ ψ
-- Disjunction.

  ∨-intro₁ : ∀ {Γ} {φ} → (ψ : Prop)       → Γ ⊢ φ
                                          → Γ ⊢ φ ∨ ψ

  ∨-intro₂ : ∀ {Γ} {ψ} → (φ : Prop)       → Γ ⊢ ψ
                                          → Γ ⊢ φ ∨ ψ

  ∨-elim  : ∀ {Γ} {φ ψ χ}                 → Γ , φ ⊢ χ
                                          → Γ , ψ ⊢ χ
                                          → Γ , φ ∨ ψ ⊢ χ
-- Implication.

  ⇒-intro  : ∀ {Γ} {φ ψ}                  → Γ , φ ⊢ ψ
                                          → Γ ⊢ φ ⇒ ψ

  ⇒-elim   : ∀ {Γ} {φ ψ}                  → Γ ⊢ φ ⇒ ψ → Γ ⊢ φ
                                          → Γ ⊢ ψ
-- Biconditional.

  ⇔-intro  : ∀ {Γ} {φ ψ}                  → Γ , φ ⊢ ψ
                                          → Γ , ψ ⊢ φ
                                          → Γ ⊢ φ ⇔ ψ

  ⇔-elim₁ : ∀ {Γ} {φ ψ}                   → Γ ⊢ φ → Γ ⊢ φ ⇔ ψ
                                          → Γ ⊢ ψ

  ⇔-elim₂ : ∀ {Γ} {φ ψ}                   → Γ ⊢ ψ → Γ ⊢ φ ⇔ ψ
                                          → Γ ⊢ φ

------------------------------------------------------------------------

------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Theorems of ∧ connective.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.Prop.Theorems.Conjunction ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Prop.Syntax n
open import Data.Prop.Theorems.Classical n

open import Function using ( _$_ ; _∘_  )

------------------------------------------------------------------------------

∧-assoc
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ φ ∧ (ψ ∧ ω)
  → Γ ⊢ (φ ∧ ψ) ∧ ω

∧-comm
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ φ ∧ ψ
  → Γ ⊢ ψ ∧ φ

∧-dist₁
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ φ ∧ (ψ ∨ ω)
  → Γ ⊢ (φ ∧ ψ) ∨ (φ ∧ ω)

∧-dist₂
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ (φ ∧ ψ) ∨ (φ ∧ ω)
  → Γ ⊢ φ ∧ (ψ ∨ ω)

∧-dist
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ φ ∧ (ψ ∨ ω) ⇔ (φ ∧ ψ) ∨ (φ ∧ ω)

∧-dmorgan₁
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ¬ (φ ∧ ψ)
  → Γ ⊢ ¬ φ ∨ ¬ ψ
¬∧-to-¬∨¬ = ∧-dmorgan₁

∧-dmorgan₂
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ¬ φ ∨ ¬ ψ
  → Γ ⊢ ¬ (φ ∧ ψ)
¬∨¬-to-¬∧ = ∧-dmorgan₂

∧-dmorgan
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ¬ φ ∨ ¬ ψ ⇔ ¬ (φ ∧ ψ)
¬∨¬-⇔-¬∧ = ∧-dmorgan

subst⊢∧₁
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ φ ⇒ ω
  → Γ ⊢ φ ∧ ψ
  → Γ ⊢ ω ∧ ψ

subst⊢∧₂
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ ψ ⇒ ω
  → Γ ⊢ φ ∧ ψ
  → Γ ⊢ φ ∧ ω

------------------------------------------------------------------------------
-- Proofs.
------------------------------------------------------------------------------

∧-assoc Γ⊢φ∧ψ∧ω =
  ∧-intro
    (∧-intro
      (∧-proj₁  Γ⊢φ∧ψ∧ω)
      ((∧-proj₁ ∘ ∧-proj₂) Γ⊢φ∧ψ∧ω))
    ((∧-proj₂ ∘ ∧-proj₂) Γ⊢φ∧ψ∧ω)

∧-comm Γ⊢φ∧ψ =
  ∧-intro
    (∧-proj₂ Γ⊢φ∧ψ)
    (∧-proj₁ Γ⊢φ∧ψ)

∧-dist₁ {Γ}{φ}{ψ}{ω} Γ⊢φ∧ψ∨ω =
  ⇒-elim
    (⇒-intro $
      ∨-elim {Γ = Γ}
        (∨-intro₁ (φ ∧ ω)
          (∧-intro
            (weaken ψ (∧-proj₁ Γ⊢φ∧ψ∨ω))
            (assume {Γ = Γ} ψ)))
        (∨-intro₂ (φ ∧ ψ)
          (∧-intro
            (weaken ω  (∧-proj₁ Γ⊢φ∧ψ∨ω))
            (assume {Γ = Γ} ω))))
    (∧-proj₂ Γ⊢φ∧ψ∨ω)

∧-dist₂ {Γ}{φ}{ψ}{ω} =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∧-intro
          (∧-proj₁
            (assume {Γ = Γ} (φ ∧ ψ)))
          (∨-intro₁ ω
            (∧-proj₂
              (assume {Γ = Γ} (φ ∧ ψ)))))
        (∧-intro
          (∧-proj₁
            (assume {Γ = Γ} (φ ∧ ω)))
          (∨-intro₂ ψ
            (∧-proj₂
              (assume {Γ = Γ} (φ ∧ ω)))))))

∧-dist {Γ}{φ}{ψ}{ω} =
  ⇔-intro
    (∧-dist₁ (assume {Γ = Γ} (φ ∧ (ψ ∨ ω))))
    (∧-dist₂ (assume {Γ = Γ} (φ ∧ ψ ∨ (φ ∧ ω))))

∧-dmorgan₁ {Γ}{φ}{ψ} =
  ⇒-elim $
    ⇒-intro $
      RAA $
        ¬-elim
          (weaken (¬ (¬ φ ∨ ¬ ψ)) $
            assume {Γ = Γ} $ ¬ (φ ∧ ψ))
          (∧-intro
            (RAA
              (¬-elim
                (weaken (¬ φ) $
                  assume {Γ = Γ , ¬ (φ ∧ ψ)} $ ¬ (¬ φ ∨ ¬ ψ))
                (∨-intro₁ (¬ ψ)
                  (assume {Γ = Γ , ¬ (φ ∧ ψ) , ¬ (¬ φ ∨ ¬ ψ)} $ ¬ φ))))
            (RAA
              (¬-elim {Γ = Γ , ¬ (φ ∧ ψ) , ¬ (¬ φ ∨ ¬ ψ) , ¬ ψ}
                (weaken (¬ ψ) $
                  assume {Γ = Γ , ¬ (φ ∧ ψ)} $ ¬ (¬ φ ∨ ¬ ψ))
                (∨-intro₂ (¬ φ)
                  (assume {Γ = Γ , ¬ (φ ∧ ψ) , ¬ (¬ φ ∨ ¬ ψ)} $ ¬ ψ )))))

∧-dmorgan₂ {Γ}{φ}{ψ} =
  ⇒-elim $
    ⇒-intro $
      ∨-elim {Γ = Γ}
        (¬-intro $
          ¬-elim
            (weaken (φ ∧ ψ) $
              assume {Γ = Γ} (¬ φ))
            (∧-proj₁ $
              assume {Γ = Γ , ¬ φ} (φ ∧ ψ)))
        (¬-intro $
          ¬-elim
            (weaken (φ ∧ ψ) $ assume {Γ = Γ} (¬ ψ))
          (∧-proj₂ $
            assume {Γ = Γ , ¬ ψ} (φ ∧ ψ)))

∧-dmorgan {Γ}{φ}{ψ} =
  ⇔-intro
    (∧-dmorgan₂
      (assume {Γ = Γ} (¬ φ ∨ ¬ ψ)))
    (∧-dmorgan₁
      (assume {Γ = Γ} (¬ (φ ∧ ψ))))

subst⊢∧₁ {Γ}{φ}{ψ} Γ⊢φ⇒ψ Γ⊢φ∧ψ =
  ∧-intro
    (⇒-elim (∧-proj₁ (∧-intro Γ⊢φ⇒ψ Γ⊢φ∧ψ)) (∧-proj₁ Γ⊢φ∧ψ))
    (∧-proj₂ Γ⊢φ∧ψ)

subst⊢∧₂ {Γ}{φ}{ψ} Γ⊢φ⇒ψ Γ⊢φ∧ψ =
  ∧-intro
    (∧-proj₁ Γ⊢φ∧ψ)
    (⇒-elim Γ⊢φ⇒ψ (∧-proj₂ Γ⊢φ∧ψ))

------------------------------------------------------------------------------
-- Athena version 0.1-21d73e9.
-- TSTP file: test/prop-pack/problems/conjunction/conj-3.tstp.
------------------------------------------------------------------------------

module conj-3 where

------------------------------------------------------------------------------

open import ATP.Metis 2 public
open import Data.Prop 2 public

------------------------------------------------------------------------------

-- Variables.

p : Prop
p = Var (# 0)

q : Prop
q = Var (# 1)

-- Axiom.

a : Prop
a = (p ∧ q)

-- Premise.

Γ : Ctxt
Γ = [ a ]

-- Conjecture.

goal : Prop
goal = (q ∧ p)

-- Subgoals.

subgoal₀ : Prop
subgoal₀ = q

subgoal₁ : Prop
subgoal₁ = (q ⇒ p)

------------------------------------------------------------------------------
-- Proof.
------------------------------------------------------------------------------

proof₀ : Γ ⊢ subgoal₀
proof₀ =
  (RAA
    (atp-canonicalize
      (atp-simplify
        (atp-canonicalize
          (atp-strip
            (assume {Γ = Γ}
              (atp-negate subgoal₀))))
        (atp-conjunct (q)
          (atp-canonicalize
            (weaken (atp-negate subgoal₀)
              (assume {Γ = ∅} a)))))))

proof₁ : Γ ⊢ subgoal₁
proof₁ =
  (RAA
    (atp-canonicalize
      (atp-simplify
        (atp-conjunct (q)
          (atp-canonicalize
            (weaken (atp-negate subgoal₁)
              (assume {Γ = ∅} a))))
        (atp-simplify
          (atp-canonicalize
            (atp-strip
              (assume {Γ = Γ}
                (atp-negate subgoal₁))))
          (atp-conjunct (p)
            (atp-canonicalize
              (weaken (atp-negate subgoal₁)
                (assume {Γ = ∅} a))))))))

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    (∧-intro proof₀ proof₁)

------------------------------------------------------------------------------
-- Proof.
------------------------------------------------------------------------------

proof₀ : Γ ⊢ subgoal₀
proof₀ =
  (RAA
    (atp-canonicalize
      (atp-simplify
        (atp-canonicalize
          (atp-strip
            (assume {Γ = Γ}
              (atp-negate subgoal₀))))
        (atp-canonicalize
          (weaken (atp-negate subgoal₀)
            (assume {Γ = ∅} a₁))))))

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    proof₀

atp-conjunct
  : ∀ {Γ} {φ}
  → (ω : Prop)
  → Γ ⊢ φ
  → Γ ⊢ conjunct φ ω

atp-conjunct {Γ} {φ ∧ ψ} ω Γ⊢φ
  with ⌊ eq φ ω ⌋ | ⌊ eq ψ ω ⌋
... | true  | _     = ∧-proj₁ Γ⊢φ
... | false | true  = ∧-proj₂ Γ⊢φ
... | false | false =
  atp-conjunct {Γ = Γ} {φ = φ} ω (∧-proj₁ Γ⊢φ)
atp-conjunct {_} {Var x}  _ = id
atp-conjunct {_} {⊤}      _ = id
atp-conjunct {_} {⊥}      _ = id
atp-conjunct {_} {φ ∨ ψ}  _ = id
atp-conjunct {_} {φ ⇒ ψ}  _ = id
atp-conjunct {_} {φ ⇔ ψ}  _ = id
atp-conjunct {_} {¬ φ}    _ = id