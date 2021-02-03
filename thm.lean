namespace exc

theorem and_comm {P Q : Prop} : P ∧ Q → Q ∧ P :=
begin
  assume h : P ∧ Q,
  have hp : P, from h.left,
  have hq : Q, from h.right,
  show Q ∧ P, from and.intro hq hp
end

theorem and_comm_1 {P Q : Prop} : P ∧ Q → Q ∧ P :=
  fun x : P ∧ Q , and.intro x.right x.left


theorem or_comm (P Q : Prop) : P ∨ Q → Q ∨ P :=
begin
  assume h : P ∨ Q,
  cases h with hp hq,
    right, exact hp,
    left, exact hq
end

theorem or_elim_0 (p q r : Prop) : (p ∨ q) → (p → r) → (q → r) → r :=
begin
  assume poq : p ∨ q,
  assume par : p → r,
  assume qar : q → r,
  cases poq with hp hq,
    show r, from par(hp),
    show r, from qar(hq)
end

variable S : Type
variable P : S -> S -> Prop

example : (∃ x : S, ∀ y : S, P x y) -> (∀ x : S, ∃ y : S, P y x) :=
begin
  intro h,
  intro x,
  cases h with x0,
  existsi x0,
  exact (h_h x),
end

theorem contrapostition (R Q : Prop) : (R → Q) → ¬ Q → ¬ R :=
begin
  assume h0,
  assume h1,
  assume h2,
  exact h1(h0(h2))
end

theorem id_S : S → S := fun (x : S), x

theorem transitivity (P Q R : Prop) : (P → Q) → (Q → R) → P → R :=
begin
  assume pq,
  assume qr,
  assume p,
  exact qr (pq p)
end


theorem transitivity_0 (P Q R : Prop) : (P → Q) → (Q → R) → P → R :=
  fun pq : P → Q,
    fun qr : Q → R,
      fun p : P,
        qr (pq p)



variable R : Prop
variable r : R
variable Q : Prop
variable q : Q
example : R ∨ Q := or.inl r
example : R ∨ Q := or.inr q

example (P Q : Prop) : (P ∧ Q) → (P ∨ Q) :=
  fun pq : P ∧ Q,
    or.inl pq.left

example (P Q : Prop) : (P ∧ Q) → (P ∨ Q) :=
  fun pq : P ∧ Q,
    or.inr pq.right

end exc