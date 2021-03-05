variables p q r s : Prop

open classical

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  iff.intro (λ x : _, ⟨x.right, x.left⟩) (λ x : _, ⟨x.right, x.left⟩)

example : p ∨ q ↔ q ∨ p :=
  iff.intro
    (λ pq : _, or.elim pq (λ p0 : p, or.inr p0) (λ q0 : q, or.inl q0))
    (λ qp : _, or.elim qp (λ q0 : q, or.inr q0) (λ p0 : p, or.inl p0))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := 
  iff.intro
    (λ pqr : _, and.intro (pqr.left).left (and.intro (pqr.left).right pqr.right))
    
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry
-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry
-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ false ↔ p := sorry
example : p ∧ false ↔ false := sorry
example : ¬(p ↔ ¬p) := sorry
example : (p → q) → (¬q → ¬p) := sorry
-- these require classical reasoning
example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := sorry
example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
example : ¬(p → q) → p ∧ ¬q := sorry
example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry

def raa_pem : ∀ P : Prop, (P ∨ ¬ P) :=
begin
  assume P,
  show P ∨ ¬P, by_contradiction N,

    have p : P, by_contradiction np,
      have ponp : P ∨ ¬P, from or.inr np,
    show false, from N ponp,

    have np : ¬P, by_contradiction p,
      have ponp : P ∨ ¬P, from or.inl p,
    show false, from N ponp,

  show false, from np p,
end