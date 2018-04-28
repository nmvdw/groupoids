Require Import HoTT.

Definition tarwe
           {A : Type}
           {B : A -> A -> Type}
           (f : forall (a : A), B a a)
           (h : forall (a₁ a₂ : A), B a₁ a₂ -> a₁ = a₂)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
  : p^ @ h a₁ a₁ (f a₁) @ p = h a₂ a₂ (transport (fun a => B a a) p (f a₁)).
Proof.
  induction p ; cbn.
  exact (concat_p1 _ @ concat_1p _).
Defined.

Definition wat
           {A : Type}
           {B : A -> A -> Type}
           (f : forall (a : A), B a a)
           (h : forall (a₁ a₂ : A), B a₁ a₂ -> a₁ = a₂)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
  : apD (fun a => h a a (f a)) p
    =
    (transport_paths_FlFr p (h a₁ a₁ (f a₁)))
      @ (ap (fun z => (z^ @ h a₁ a₁ (f a₁)) @ z) (ap_idmap p))
      @ (tarwe f h p)
      @ (ap (h a₂ a₂) (apD f p)).
Proof.
  induction p ; cbn.
  rewrite !concat_p1.
  rewrite <- inv_pp.
  rewrite (concat_p1 (concat_p1 (1 @ h a₁ a₁ (f a₁)) @ concat_1p (h a₁ a₁ (f a₁)))^).
  hott_simpl.
Defined.

  
Definition apd_idpath
           {B : Type}
           {b₁ b₂ : B}
           (p : b₁ = b₂)
  : apD (@idpath B) p
    =
    (transport_paths_FlFr p idpath)
      @ (ap (fun z => (z^ @ idpath) @ z) (ap_idmap p))
      @ (ap (fun z => z @ p) (concat_p1 p^))
      @ (concat_Vp p)
  := match p with
     | idpath => idpath
     end.

Definition transport_paths_FlFr_fun
      {A B : Type}
      {f g : A -> B}
      {a₁ a₂ : A}
      (p : a₁ = a₂)
  : transport (fun a : A => f a = g a) p == fun r => (ap f p)^ @ r @ ap g p
  := transport_paths_FlFr p.

Definition transport_paths_id_id_fun
      {A : Type}
      {a₁ a₂ : A}
      (p : a₁ = a₂)
  : transport (fun a : A => a = a) p == fun r => p^ @ r @ p
  := fun r =>
       transport_paths_FlFr_fun p r @ ap (fun z => (z^ @ r) @ z) (ap_idmap p).

Definition ap_fun_eq
      {A B : Type}
      {f g : A -> B}
      (e : f == g)
      {a₁ a₂ : A}
      (p : a₁ = a₂)
  : ap f p = e a₁ @ ap g p @ (e a₂)^
  := match p with
     | idpath => (ap (fun z => z @ (e a₁)^) (concat_p1 (e a₁)) @ concat_pV (e a₁))^
     end.

Definition ap_transport_apD_idpath
           {A B : Type}
           (f : A -> B)
           {a₁ a₂ : A}
           (p : f a₁ = f a₂)
           {q : forall (a : A), f a = f a}
           (s : forall (a : A), q a = idpath)
  : (ap (transport (fun b : B => b = b) p) (s a₁))
      @ apD (@idpath B) p
    = ((transport_paths_FlFr p (q a₁))
        @ (ap (fun z => (z^ @ _) @ z) (ap_idmap p))
        @ (ap (fun z => (p^ @ z) @ p) (s a₁))
        @ (ap (fun z => z @ p) (concat_p1 p^) @ concat_Vp p)
        @ ((s a₂)^))
        @ s a₂.
Proof.
  rewrite apd_idpath.
  rewrite (ap_fun_eq (transport_paths_id_id_fun p) (s a₁)).
  rewrite inv_pp.
  hott_simpl.
Defined.
