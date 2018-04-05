Require Import HoTT.
From GR Require Import path_over.

Inductive globe
          {A : Type}
  : forall {a₁ a₂ : A} (p q : a₁ = a₂), Type
  :=
  | globe_id : forall {a : A}, @globe A a a idpath idpath.

Definition path_to_globe
           {A : Type}
           {a₁ a₂ : A}
           {p q : a₁ = a₂}
           (h : p = q)
  : globe p q
  := match h with
     | idpath =>
       match p with
       | idpath => globe_id
       end
     end.

Arguments globe_id {_} {_}.

Inductive globe_over
          {A : Type}
          (Y : A -> Type)
  : forall {a₁ a₂ : A}
           {c₁ : Y a₁} {c₂ : Y a₂}
           {p₁ p₂ : a₁ = a₂}
           (h : globe p₁ p₂)
           (q₁ : path_over Y p₁ c₁ c₂)
           (q₂ : path_over Y p₂ c₁ c₂),
    Type
  :=
  | globe_over_id : forall {a : A} {c₁ c₂ : Y a} (q : path_over Y idpath c₁ c₂),
      globe_over Y globe_id q q.

Definition const_globe_over
           {A B : Type}
           {a₁ a₂ : A}
           {b₁ b₂ : B}
           {p₁ p₂ : a₁ = a₂}
           (h₁ : globe p₁ p₂)
           (q₁ q₂ : b₁ = b₂)
           (h₂ : globe q₁ q₂) 
  : globe_over (fun _ => B) h₁ (const_path_over q₁) (const_path_over q₂).
Proof.
  induction h₁, h₂.
  apply globe_over_id.
Defined.