Require Import HoTT.
Require Import groupoid_quotient.
Require Import groupoid path_over globe_over general square.
Require Import setoid squot_properties.
Require Import gquot_encode_decode.

(*
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
*)

(** A `1`-type is a groupoid quotient. *)
Section one_type_is_groupoid_quotient.
  Variable (A : Type).
  Context `{IsTrunc 1 A}.

  (** Every `1`-type induces a groupoid.
      Taking the groupoid quotient over this gives an equivalent type.
   *)
  Definition one_type_path_groupoid : groupoid A
    := {|hom := fun x y => BuildhSet(x = y) ;
         e := fun _ => idpath ;
         inv := fun _ _ => inverse ;
         comp := fun _ _ _ => concat ;
         ca := fun _ _ _ _ => concat_p_pp ;
         ce := fun _ _ => concat_p1 ;
         ec := fun _ _ => concat_1p ;
         ci := fun _ _ => concat_pV ;
         ic := fun _ _ => concat_Vp
       |}.
    
  Definition gquot_to_A : gquot one_type_path_groupoid -> A.
  Proof.
    simple refine (gquot_rec A idmap _ _ _ _ _) ; cbn.
    - exact (fun _ _ => idmap).
    - exact (fun _ => idpath).
    - exact (fun _ _ _ => idpath).
    - exact (fun _ _ _ _ _ => idpath).
  Defined.

  Definition path_over_help
             {a₁ a₂ : A}
             (g : hom one_type_path_groupoid a₁ a₂)
    : path_over (fun z : gquot _ => gcl _ (gquot_to_A z) = z)
                (gcleq _ g)
                idpath
                idpath.
  Proof.
    apply map_path_over.
    induction g ; cbn.
    refine (whisker_square idpath _ _ idpath _).
    - refine (ap_compose _ _ _ @ ap _ _)^.
      apply gquot_rec_beta_gcleq.
    - refine (ap_idmap _ @ _)^.
      apply ge.
    - exact id_square.
  Defined.

  Global Instance gquot_to_A_isequiv : IsEquiv gquot_to_A.
  Proof.
    simple refine (isequiv_adjointify _ (gcl _) _ _).
    - intros x ; reflexivity.
    - intros x.
      simple refine (gquot_ind_set (fun z => _) _ _ _ x).
      + intros a ; cbn.
        reflexivity.
      + intros.
        apply path_over_help.
  Defined.
End one_type_is_groupoid_quotient.

(** Every setoid induces a groupoid.
    The setoid quotients of a setoid coincides with the groupoid quotient over
    its induced groupoid.
 *)
Section squot_is_gquot.
  Variable (A : Type)
           (R : setoid A).
  Context `{Univalence}.

  Definition gquot_to_squot : gquot (setoid_to_groupoid R) -> squot R.
  Proof.
    simple refine (gquot_rec (squot R) (class_of (rel R)) _ _ _ _ _).
    - exact (fun _ _ p => related_classes_eq _ p).
    - intros ; apply path_ishprop.
    - intros ; apply path_ishprop.
    - intros ; apply path_ishprop.
  Defined.

  Definition hset_allpath_eq
             (X : Type)
    : (forall (x y : X), IsHProp (x = y)) -> IsHSet X.
  Proof.
    apply _.
  Defined.

  (** If you take the groupoid quotient over a setoid, then it is a set. *)
  Global Instance gquot_setoid_set
    : IsHSet (gquot (setoid_to_groupoid R)).
  Proof.
    apply hset_allpath_eq.
    simple refine (gquot_double_ind_prop _ _ _).
    cbn ; intros.
    rewrite (path_universe (encode_gquot _ _
                                      (gcl (setoid_to_groupoid R) a)
                                      (gcl (setoid_to_groupoid R) b))).
    simpl.
    apply _.
  Defined.

  (** Now we can show the two quotients coincide. *)
  Definition squot_to_gquot : squot R -> gquot (setoid_to_groupoid R).
  Proof.
    simple refine (quotient_rec _ (gcl _) _).
    simpl ; intros.
    apply gcleq ; assumption.
  Defined.

  Definition squot_to_gquot_to_squot
    : forall (x : squot R), gquot_to_squot(squot_to_gquot x) = x.
  Proof.
    simple refine (quotient_ind _ _ _ _).
    - reflexivity.
    - intros ; apply path_ishprop.
  Defined.

  Definition gquot_to_squot_to_gquot
    : forall (x : gquot (setoid_to_groupoid R)), squot_to_gquot(gquot_to_squot x) = x.
  Proof.
    simple refine (gquot_ind_prop _ _ _).
    reflexivity.
  Defined.
End squot_is_gquot.