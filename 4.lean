import init.data.nat.basic

variable A : Type*
variables P Q : A → Prop
variable R : Prop

-- 1
example : (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) :=
begin
  split,
  assume h, split,
    assume x, from (h x).left,
    assume x, from (h x).right,
  assume h, assume x, split,
    from h.left x,
    from h.right x
end

example : (∀ x, P x → Q x) → (∀ x, P x) → (∀ x, Q x) :=
begin
  assume h h' x,
  from h x (h' x)
end

example : (∀ x, P x) ∨ (∀ x, Q x) → ∀ x, P x ∨ Q x :=
begin
  assume h x, cases h,
    left, from h x,
    right, from h x
end

-- 2

example : A → ((∀ x : A, R) ↔ R) :=
begin
  assume x, split,
    assume f, from f x,
    assume r, from assume _, r
end

example : (∀ x, P x ∨ R) ↔ (∀ x, P x) ∨ R :=
begin
  split,

  assume h, by_cases r : R,
    right, from r,
    left, assume x,
      have h' : P x ∨ R, from h x,
      cases h' with px r',
        from px,
        exfalso, from r r',

  assume h, cases h with px r,
    assume x, left, from px x,
    assume x, right, from r
end

example : (∀ x, R → P x) ↔ (R → ∀ x, P x) :=
begin
  split,
    assume f r x, from f x r,
    assume f x r, from f r x
end

-- 3
variables (men : Type*) (barber : men)
variable (shaves : men → men → Prop)
example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false :=
begin
  have hb : shaves barber barber ↔ ¬ shaves barber barber,
    from h barber,
  cases hb with hn hp,
  have f : ¬ shaves barber barber,
    assume s, show false, from (hn s) s,
  have t : shaves barber barber,
    from hp f,
  
  show false, from f t
end

-- 4
def exp : ℕ → ℕ → ℕ
| x 0 := 1
| x (y+1) := x * (exp x y)

def even (n : ℕ) : Prop := nat.mod n 2 = 0

def prime (n : ℕ) : Prop :=
  ∀ x : ℕ, nat.mod n x = 0 → (x = 1 ∨ x = n)
def infinitely_many_primes : Prop :=
  ∀ x : ℕ, ∃ y : ℕ, x ≤ y ∧ prime y
def Fermat_prime (n : ℕ) : Prop :=
  prime n ∧ ∃ x : ℕ, n = (exp 2 (exp 2 x)) + 1
def infinitely_many_Fermat_primes : Prop :=
  ∀ x : ℕ, ∃ y : ℕ, x ≤ y ∧ Fermat_prime y
def goldbach_conjecture : Prop :=
  ∀ x : ℕ, even x → 2 ≤ x → ∃ y z : ℕ, prime y ∧ prime z ∧ x = y + z
def Goldbach's_weak_conjecture : Prop :=
  ∀ x : ℕ, ¬ even x → 5 ≤ x →
    ∃ w y z : ℕ, prime w ∧ prime y ∧ prime z ∧ x = w + y + z
def Fermat's_last_theorem : Prop := ∀ n a b c : ℕ,
  3 ≤ n → ¬ (exp a n = (exp b n) + (exp c n))

-- ex
example : (∃ x : A, R) → R :=
begin
  assume ex, cases ex with _ r, exact r
end

variable a : A

example : R → (∃ x : A, R) :=
  assume : R, exists.intro a ‹ R ›

example : (∃ x, P x ∧ R) ↔ (∃ x, P x) ∧ R :=
begin split,
    assume h : ∃ x, P x ∧  R ,
    exact match h with ⟨ w , ℘₁ , ℘₂ ⟩ := ⟨ ⟨ w , ℘₁⟩ , ℘₂ ⟩ end,

    assume h : (∃ x, P x) ∧ R ,
    exact match h with ⟨ ⟨ w , ℘₁ ⟩ , ℘₂ ⟩ := ⟨ w , ℘₁ , ℘₂ ⟩ end
end

example : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) :=
begin split,
  assume : ∃ x, P x ∨ Q x,
  cases ‹ ∃ x, P x ∨ Q x › with x,
  cases ‹ P x ∨ Q x ›,
    left, existsi x, exact ‹ P x ›,
    right, existsi x, exact ‹ Q x ›,

  assume : (∃ x, P x) ∨ (∃ x, Q x),
  cases ‹ (∃ x, P x) ∨ (∃ x, Q x) ›,
    cases ‹ ∃ x, P x › with x,
    existsi x,
      show P x ∨ Q x, left, exact ‹ P x ›,
    cases ‹ ∃ x, Q x › with x,
    existsi x,
      show P x ∨ Q x, right, exact ‹ Q x ›
end

example : (∀ x, P x) ↔ ¬ (∃ x, ¬ P x) :=
begin split,
  assume : ∀ x, P x, assume : ∃ x, ¬ P x,
  cases ‹ ∃ x, ¬ P x › with x,
  show false, from ‹ ¬ P x › (‹ ∀ x, P x › x),

  assume : ¬∃ (x : A), ¬P x, assume x,by_contradiction,
  have : ∃ x, ¬ P x,
    existsi x, from ‹ ¬ P x ›,
  show false, from ‹ ¬∃ (x : A), ¬P x › this,
end
 
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := 
begin
  split,
  intros epx all_np,
    cases epx with x px,
      exact (all_np x) px ,
  intro h₀,
    by_contradiction ,
      have all : ∀ x, ¬p x ,
        assume x ,
        assume hpx ,
        exact h ( ⟨ x , hpx ⟩ ),
      exact h₀ all ,
end
example : (¬ ∃ x, P x) ↔ (∀ x, ¬ P x) := sorry
example : (¬ ∀ x, P x) ↔ (∃ x, ¬ P x) := sorry

example : (∀ x, P x → R) ↔ (∃ x, P x) → R := sorry
example : (∃ x, P x → R) ↔ (∀ x, P x) → R := sorry
example : (∃ x, R → P x) ↔ (R → ∃ x, P x) := sorry
