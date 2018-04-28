Require Import HoTT.
From GR Require Import general polynomial setoid.

(** The quotient over an setoid. *)
Definition squot {A : Type} (R : setoid A)
  : Type
  := quotient (rel R).

(** The equality of `squot` is given by the setoid. *)
Definition setoid_quotient_path
           {A : Type}
           (R : setoid A)
           `{Univalence}
  : forall {a₁ a₂ : A}, class_of (rel R) a₁ = class_of (rel R) a₂ <~> rel R a₁ a₂
  := sets_exact (rel R).

(** Every `0`-type (set) can be written as a `squot`. *)
Section set_is_setoid_quotient.
  Variable (A : Type).
  Context `{IsHSet A}.

  (** Every set induces a setoid via its path space.
      Taking the setoid quotient over this setoid, gives the original type.
   *)
  Definition set_path_setoid : setoid A
    := {|rel := fun x y => BuildhProp(x = y) ;
         refl := fun _ => idpath ;
         sym := fun _ _ => inverse ;
         trans := fun _ _ _ => concat
       |}.
    
  Definition squot_to_A : squot set_path_setoid -> A
    := quotient_rec (rel set_path_setoid) idmap (fun _ _ => idmap).

  Global Instance squot_to_A_isequiv : IsEquiv squot_to_A.
  Proof.
    simple refine (isequiv_adjointify _ (class_of (rel set_path_setoid)) _ _).
    - intros x ; reflexivity.
    - unfold Sect.
      simple refine (quotient_ind _ _ _ _).
      + reflexivity.
      + intros.
        apply path_ishprop.
  Defined.
End set_is_setoid_quotient.

(** For arbitrary types, we use a similar construction.
    However, then it gives the set truncation of that type.
 *)
Section path_setoid_quotient.
  Variable (A : Type).
    
  Definition squot_to_TA : squot (path_setoid A) -> Trunc 0 A.
  Proof.
    simple refine (quotient_rec _ tr _).
    cbn ; intros x y H.
    simple refine (Trunc_rec _ H).
    exact (ap tr).
  Defined.

  Global Instance squot_to_TA_isequiv : IsEquiv squot_to_TA.
  Proof.
    simple refine (isequiv_adjointify _ _ _ _).
    - intros x.
      simple refine (Trunc_rec _ x).
      apply class_of.
    - unfold Sect.
      simple refine (Trunc_ind _ _) ; reflexivity.
    - unfold Sect.
      simple refine (quotient_ind _ _ _ _).
      + reflexivity.
      + intros.
        apply path_ishprop.
  Defined.
End path_setoid_quotient.

(** Taking the setoid quotient commutes with sums. *)
Section squot_sum.
  Variable (A B : Type)
           (R₁ : setoid A) (R₂ : setoid B).

  Definition squot_sum_in
             (z : squot R₁ + squot R₂)
    : squot (sum_setoid R₁ R₂).
  Proof.
    destruct z as [z | z].
    - simple refine (quotient_rec _ _ _ z).
      + exact (fun a => class_of _ (inl a)).
      + intros a₁ a₂ p ; cbn in *.
        apply related_classes_eq ; assumption.
    - simple refine (quotient_rec _ _ _ z).
      + exact (fun a => class_of _ (inr a)).
      + intros b₁ b₂ p ; cbn in *.
        apply related_classes_eq ; assumption.
  Defined.

  Definition squot_sum_out
    : squot (sum_setoid R₁ R₂) -> squot R₁ + squot R₂.
  Proof.
    simple refine (quotient_rec _ _ _).
    - intros [z | z].
      + exact (inl(class_of _ z)).
      + exact (inr(class_of _ z)).
    - intros [x | x] [y | y] r ; try contradiction
      ; apply ap ; apply related_classes_eq ; assumption.
  Defined.

  Lemma squot_sum_out_in_sect : Sect squot_sum_out squot_sum_in.
  Proof.
    unfold Sect.
    simple refine (quotient_ind _ _ _ _).
    - intros [z | z] ; reflexivity.
    - intros ; apply path_ishprop.
  Defined.

  Lemma squot_sum_in_out_sect : Sect squot_sum_in squot_sum_out.
  Proof.
    intros [x | x] ; revert x.
    - simple refine (quotient_ind _ _ _ _).
      + intros ; reflexivity.
      + intros ; apply path_ishprop.
    - simple refine (quotient_ind _ _ _ _).
      + intros ; reflexivity.
      + intros ; apply path_ishprop.
  Defined.

  Global Instance squot_sum_out_isequiv : IsEquiv squot_sum_out
    := isequiv_adjointify _ squot_sum_in squot_sum_in_out_sect squot_sum_out_in_sect.
End squot_sum.

(** Taking the setoid quotient commutes with products (assuming function extensionality. *)
Section squot_prod.
  Variable (A B : Type)
           (R₁ : setoid A) (R₂ : setoid B).
  Context `{Funext}.

  Definition squot_prod_in
             (z : squot R₁ * squot R₂)
    : squot (prod_setoid R₁ R₂).
  Proof.
    destruct z as [z₁ z₂]. revert z₁ z₂.
    simple refine (quotient_rec _ _ _).
    - intros a.
      simple refine (quotient_rec _ _ _).
      + intros b.
        exact (class_of _ (a,b)).
      + simpl ; intros b₁ b₂ p.
        apply related_classes_eq.
        exact (refl _,p).
    - simpl ; intros a₁ a₂ p₁.
      funext b. revert b.
      simple refine (quotient_ind _ _ _ _).
      + intros b ; simpl.
        apply related_classes_eq.
        exact (p₁,refl _).
      + intros ; apply path_ishprop.
  Defined.

  Definition squot_prod_out
    : squot (prod_setoid R₁ R₂) -> squot R₁ * squot R₂.
  Proof.
    simple refine (quotient_rec _ _ _).
    - exact (fun z => (class_of _ (fst z),class_of _ (snd z))).
    - simpl ; intros z₁ z₂ p.
      apply path_prod' ; apply related_classes_eq ; apply p.
  Defined.

  Lemma squot_prod_out_in_sect : Sect squot_prod_out squot_prod_in.
  Proof.
    unfold Sect.
    simple refine (quotient_ind _ _ _ _).
    - simpl ; intros [z₁ z₂] ; reflexivity.
    - intros ; apply path_ishprop.
  Defined.

  Lemma squot_prod_in_out_sect : Sect squot_prod_in squot_prod_out.
  Proof.
    intros [z₁ z₂]. revert z₁ z₂.
    simple refine (quotient_ind _ _ _ _).
    - simpl ; intros a.
      simple refine (quotient_ind _ _ _ _).
      + simpl ; intros b.
        reflexivity.
      + intros ; apply path_ishprop.
    - intros ; apply path_ishprop.
  Defined.

  Global Instance squot_prod_out_isequiv : IsEquiv squot_prod_out
    := isequiv_adjointify _ squot_prod_in squot_prod_in_out_sect squot_prod_out_in_sect.
End squot_prod.

(** Suppose that we have a polynomial `P` and a setoid `R`.
    Then we have a natural map from the quotient of `P R` to the set truncation of `P` applied to the quotient of `R`.
 *)
Definition poly_squot_to_squot
           (P : polynomial)
           {A : Type}
           (R : setoid A)
  : squot (lift_setoid R P) -> Trunc 0 (poly_act P (squot R)).
Proof.
  induction P as [ | | P IHP Q IHQ | P IHP Q IHQ] ; cbn.
  - exact tr.
  - exact (squot_to_TA T).
  - exact ((Trunc_prod 0)
             o (functor_prod IHP IHQ)
             o squot_prod_out _ _ _ _).
  - exact ((Trunc_sum 0)
              o (functor_sum IHP IHQ)
              o squot_sum_out _ _ _ _).
Defined.

(** This map is an equivalence. *)
Global Instance squot_polynomial
       (Q : polynomial)
       {A : Type} `{IsHSet A}
       (R : setoid A)
       `{Funext}
  : IsEquiv (poly_squot_to_squot Q R).    
Proof.
  induction Q.
  - apply _.
  - apply _.
  - apply _.
  - simpl.
    refine isequiv_compose.
    apply Trunc_sum_isequiv.
    exact tt.
Defined.
