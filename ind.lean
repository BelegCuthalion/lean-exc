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
  end nat

  inductive l (T : Type) : Type
  | E : l
  | A : T → l → l

  variable x : nat
  variable y : nat
  variable z : nat

  namespace l
    #check A
    #check E  -- ()
    #check A x E  -- (x)
    #check A x (A x E)  -- (x, x)
    #check A z (A y (A x E))  -- (x, y, z)
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
                            con (p2 A B x) (p1 x)


  end p

end ind