Require Import HoTT.
From GR Require Import path_over.

(** A globe represents an equality between two paths. *)
Inductive globe
          {A : Type}
  : forall {a₁ a₂ : A} (p q : a₁ = a₂), Type
  :=
  | globe_id : forall {a : A}, @globe A a a idpath idpath.

(** A globe is thus the same as a path between two paths. *)
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

Definition globe_to_path
           {A : Type}
           {a₁ a₂ : A}
           {p q : a₁ = a₂}
           (h : globe p q)
  : p = q
  := match h with
     | globe_id _ => idpath
     end.

Global Instance path_to_globe_isequiv
       {A : Type}
       {a₁ a₂ : A}
       {p q : a₁ = a₂}
  : IsEquiv (@path_to_globe A a₁ a₂ p q).
Proof.
  simple refine (isequiv_adjointify _ globe_to_path _ _).
  - intros x.
    induction x ; reflexivity.
  - intros x.
    induction x, p ; reflexivity.
Defined.

Arguments globe_id {_} {_}.

(** We can also define `globe_over`, which represents an equality between two `path_over`. *)
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

(** In a constant fibration, this is the same as proving two paths are equal. *)
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

(** This changes the sides of a `globe_over`. *)
Definition globe_over_whisker
           {A : Type}
           (Y : A -> Type)
           {a₁ a₂ : A}
           {c₁ : Y a₁} {c₂ : Y a₂}
           {p₁ p₂ : a₁ = a₂}
           (h : globe p₁ p₂)
           {q₁ q₃ : path_over Y p₁ c₁ c₂}
           {q₂ q₄ : path_over Y p₂ c₁ c₂}
           (s₁ : q₁ = q₃) (s₂ : q₂ = q₄)
  : globe_over Y h q₁ q₂ -> globe_over Y h q₃ q₄
  := match s₁, s₂ with
     | idpath, idpath => idmap
     end.

(** One way to provide a `globe_over`, is by giving a path between two paths. *)
Definition path_to_globe_over
           {A : Type}
           (Y : A -> Type)
           {a₁ a₂ : A}
           {c₁ : Y a₁} {c₂ : Y a₂}
           {p₁ p₂ : a₁ = a₂}
           (h : globe p₁ p₂)
           (q₁ : path_over Y p₁ c₁ c₂)
           (q₂ : path_over Y p₂ c₁ c₂)
           (s : path_over_to_path (transport (fun r => path_over Y r c₁ c₂)
                                             (globe_to_path h)
                                             q₁)
                = path_over_to_path q₂)
  : globe_over Y h q₁ q₂.
Proof.
  pose (ap path_over_to_path^-1 s) as p.
  rewrite !eissect in p.
  induction p, h ; clear s.
  exact (globe_over_id Y q₁).
Defined.

(** `globe_over` in a family of sets. *)
Definition path_globe_over_hset
           {A : Type}
           (Y : A -> Type)
           `{forall (a : A), IsHSet (Y a)}
           {a₁ a₂ : A}
           {c₁ : Y a₁} {c₂ : Y a₂}
           {p₁ p₂ : a₁ = a₂}
           (h : globe p₁ p₂)
           (q₁ : path_over Y p₁ c₁ c₂)
           (q₂ : path_over Y p₂ c₁ c₂)
  : globe_over Y h q₁ q₂.
Proof.
  apply path_to_globe_over.
  apply path_ishprop.
Defined.