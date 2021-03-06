variables P Q R S : Prop

open classical

-- commutativity of ∧ and ∨
example : P ∧ Q ↔ Q ∧ P :=
  iff.intro (λ x : _, ⟨x.right, x.left⟩) (λ x : _, ⟨x.right, x.left⟩)

example : P ∧ Q ↔ Q ∧ P :=
begin
  split,
    assume pq,
    show Q ∧ P, from ⟨pq.right, pq.left⟩,

    assume qp,
    show P ∧ Q, from ⟨qp.right, qp.left⟩
end

example : P ∨ Q ↔ Q ∨ P :=
  iff.intro
    (λ pq : _, or.elim pq (λ p : P, or.inr p) (λ q : Q, or.inl q))
    (λ qp : _, or.elim qp (λ q : Q, or.inr q) (λ p : P, or.inl p))

example : P ∨ Q ↔ Q ∨ P :=
begin
  split,
    assume pq, cases pq with p q,
      show Q ∨ P, from or.inr p,
      show Q ∨ P, from or.inl q,

    assume qp, cases qp with q p,
      show P ∨ Q, from or.inr q,
      show P ∨ Q, from or.inl p
end

-- associativity of ∧ and ∨
example : (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R) := 
  iff.intro
    (λ pqr : _, and.intro pqr.left.left (and.intro pqr.left.right pqr.right))
    (λ pqr : _, and.intro (and.intro pqr.left pqr.right.left) pqr.right.right)
    
example : (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R) := 
begin
  split,
    assume pqr,
    split,
      show P, from pqr.left.left,
      split,
        show Q, from pqr.left.right,
        show R, from pqr.right,
    assume pqr,
    split,
      split,
        show P, from pqr.left,
        show Q, from pqr.right.left,
        show R, from pqr.right.right
end

example : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) :=
begin
  split,
    assume pqr, cases pqr with pq r,
      cases pq with p q,
        show P ∨ Q ∨ R, from or.inl p,
        show P ∨ Q ∨ R, from or.inr (or.inl q),
      show P ∨ Q ∨ R, from or.inr (or.inr r),
    assume pqr, cases pqr with p qr,
      from or.inl (or.inl p),
      cases qr with q r,
        from or.inl (or.inr q),
        from or.inr r
end

-- distributivity
example : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) :=
begin
  split,
    assume pqr,
      cases pqr.right with q r,
        from or.inl ⟨pqr.left, q⟩,
        from or.inr ⟨pqr.left, r⟩,
    assume pqr,
      cases pqr with pq pr,
        from ⟨pq.left, or.inl pq.right⟩,
        from ⟨pr.left, or.inr pr.right⟩
end

example : P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  split,
    assume pqr,
    split,
      cases pqr with p qr,
        show P ∨ Q, from or.inl p,
        show P ∨ Q, from or.inr qr.left,
      cases pqr with p qr,
        show P ∨ R, from or.inl p,
        show P ∨ R, from or.inr qr.right,
    assume pqpr,
      cases pqpr.left with p q,
        show P ∨ Q ∧ R, from or.inl p,
        cases pqpr.right with p r,
          show P ∨ Q ∧ R, from or.inl p,
          show P ∨ Q ∧ R, from or.inr ⟨q, r⟩
end

-- other properties
example : (P → (Q → R)) ↔ (P ∧ Q → R) := 
begin
  split,
    assume (f : P → Q → R) (pq : P ∧ Q),
      show R, from f pq.left pq.right,
    assume (f : P ∧ Q → R) (p : P) (q : Q),
      show R, from f ⟨p, q⟩
end

example : ((P ∨ Q) → R) ↔ (P → R) ∧ (Q → R) :=
begin
  split,
    assume f : P ∨ Q → R, split,
      assume p, show R, from f (or.inl p),
      assume q, show R, from f (or.inr q),
    assume pqr : (P → R) ∧ (Q → R),
      assume pq : P ∨ Q, cases pq with p q,
        show R, from pqr.left p,
        show R, from pqr.right q,
end

example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q :=
begin
  split,
  assume npq : ¬(P ∨ Q), split,
    show ¬P, by_contradiction p,
      from npq (or.inl p),
    show ¬Q, by_contradiction q,
      from npq (or.inr q),
  assume npnq : ¬P ∧ ¬Q,
    show ¬(P ∨ Q), by_contradiction pq,
      cases pq with p q,
        from npnq.left p,
        from npnq.right q
end

example : ¬P ∨ ¬Q → ¬(P ∧ Q) :=
begin
  assume h : ¬P ∨ ¬Q,
    show ¬(P ∧ Q), by_contradiction n,
    cases h with np nq,
      show false, from np n.left,
      show false, from nq n.right
end

example : ¬(P ∧ ¬P) := λ x : P ∧ ¬P, x.right x.left

example : ¬(P ∧ ¬P) :=
begin
  by_contradiction f, from f.right f.left
end

example : P ∧ ¬Q → ¬(P → Q) :=
begin
  assume h : P ∧ ¬Q,
  show ¬(P → Q), by_contradiction f,
    from h.right (f h.left)
end

example : ¬P → (P → Q) :=
begin
  assume np p, exfalso, from np p
end

example : (¬P ∨ Q) → (P → Q) :=
begin
  assume npq p, cases npq with np q,
    exfalso, from np p,
    exact q
end

example : P ∨ false ↔ P :=
begin
  split,
  assume pf,
    cases pf with p f,
      exact p,
      exfalso, exact f,
    assume p,
      show P ∨ false, from or.inl p
end

example : P ∧ false ↔ false :=
begin
  split,
    assume pf, exact pf.right,
    assume f, exfalso, exact f
end

example : ¬(P ↔ ¬P) :=
begin
  assume pnp,
  cases pnp with pAnp npAp,
  have np : ¬P,
    assume p, show false, from (pAnp p) p,
  have p : P, from npAp np,
  show false, from np p
end

example : (P → Q) → (¬Q → ¬P) :=
begin
  assume pAq nq p,
  show false, from nq (pAq p)
end

example : (P → R ∨ S) → ((P → R) ∨ (P → S)) :=
begin
  assume f : P → R ∨ S,
  have mat : ¬P ∨ (R ∨ S),
    by_cases p : P,
      from or.inr (f p),
      from or.inl p,
  have dis : (¬P ∨ R) ∨ (¬P ∨ S),
    cases mat with np rs,
      from or.inl (or.inl np),
      cases rs with r s,
        from or.inl (or.inr r),
        from or.inr (or.inr s),
  cases dis with npr nps,
    have pAr : P → R, assume p : P,
      cases npr with np r,
        exfalso, from np p,
        from r,
      from or.inl pAr,
    have pAs : P → S, assume p : P,
      cases nps with np s,
        exfalso, from np p,
        from s,
      from or.inr pAs
end

example : ¬(P ∧ Q) → ¬P ∨ ¬Q :=
begin
  assume h : ¬(P ∧ Q),
  by_contradiction N,

    have p : P, by_contradiction np,
      have npnq : ¬P ∨ ¬Q, from or.inl np,
    show false, from N npnq,

    have q : Q, by_contradiction nq,
      have npnq : ¬P ∨ ¬Q, from or.inr nq,
    show false, from N npnq,

  show false, from h ⟨p, q⟩
end

example : ¬(P → Q) → P ∧ ¬Q :=
begin
  suffices con : ¬(P ∧ ¬Q) → ¬(¬(P → Q)),
    assume nipq, by_contradiction n, from con n nipq,

  assume napnq,
  suffices ipq : P → Q,
    assume f, show false, from f ipq,
  assume p : P,
  by_contradiction nq,
    show false, from napnq ⟨p, nq⟩
end

example : (P → Q) → (¬P ∨ Q) :=
begin
  assume ipa : P → Q,
  by_contradiction f,
    have p : P,
      by_contradiction np, show false, from f (or.inl np),
    show false, from f (or.inr (ipa p))
end

example : (¬Q → ¬P) → (P → Q) :=
begin
  assume inqnp, assume p, by_contradiction nq,
  have np, from inqnp nq,
  show false, from np p
end

example : P ∨ ¬P :=
begin
  by_contradiction N,

    have p : P, by_contradiction np,
      have ponp : P ∨ ¬P, from or.inr np,
    show false, from N ponp,

    have np : ¬P, exfalso,
      have ponp : P ∨ ¬P, from or.inl p,
    show false, from N ponp,

  show false, from np p,
end

example : (((P → Q) → P) → P) :=
begin
  assume iipqp,
  by_contradiction np,
  suffices ipq : P → Q,
    show false, from np (iipqp ipq),
  assume p : P, exfalso, show false, from np p
end