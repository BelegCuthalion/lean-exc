namespace ind

  inductive nat : Type
  | O : nat
  | S : nat → nat

  namespace nat
    def add : nat → nat → nat
    | O n := n
    | (S m) n := S (add m n)

    notation x `+` y := add x y

    def mul : nat → nat → nat
    | O n := O
    | (S m) n := add n (mul m n)

    #reduce (S (S O)) + (S (S (S O)))

    theorem add_zero_id : ∀ n : nat, n = n + O :=
    begin
      intro,
      induction n with n IH,
        refl,
        simp [add], apply IH
    end

    theorem add_comm : ∀ m n : nat, m + n = n + m :=
    begin
      intro,
      induction m with m IH,
        intro,
        simp [add], rewrite <- add_zero_id n,

        intro,
        simp [add],
        rewrite IH,
        induction n with n IHn,
          simp [add],
          rewrite <- IH,

          simp [add],
          rewrite IH,
          simp [add],
          exact IHn,
    end
  end nat

  inductive l  : Type
  | E : l
  | A : nat → l → l

  variable x : nat
  variable y : nat
  variable z : nat

  namespace l
    #check A
    #check E  -- ()
    #check A x E  -- (x)
    #check A x (A x E)  -- (x, x)
    #check A z (A y (A x E))  -- (x, y, z)

    def len : l → nat
    | E := nat.O
    | (A t s) := nat.S (len s)

    example : ∀ s : l, ∀ n : nat, len (A n s) = nat.S (len s) :=
    begin
      intro, intro, refl
    end
  end l

  inductive p (A B : Type) : Type -- A x B
  | con : A → B → p

  namespace p
    def p1 (A B : Type) : (p A B) → A
    | (con m n) := m

    def p2 (A B : Type) : (p A B) → B
    | (con m n) := n

    def s (A B : Type) : (p A B) -> (p B A)
    | (con m n) := con n m

    def s1 (A B : Type) : (p A B) -> (p B A):= fun x : (p A B),
                            con (p2 A B x) (p1 A B x)
  end p

end ind