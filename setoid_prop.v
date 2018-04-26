Require Import HoTT.
Require Import setoid.

Definition squot {A : Type} (R : setoid A)
  : Type
  := quotient (rel R).

Definition setoid_quotient_path
           {A : Type}
           (R : setoid A)
           `{Univalence}
  : forall {a₁ a₂ : A}, class_of (rel R) a₁ = class_of (rel R) a₂ <~> rel R a₁ a₂
  := sets_exact (rel R).

Section set_is_setoid_quotient.
  Variable (A : Type).
  Context `{IsHSet A}.

  Definition P : setoid A
    := {|rel := fun x y => BuildhProp(x = y) ;
         refl := fun _ => idpath ;
         sym := fun _ _ => inverse ;
         trans := fun _ _ _ => concat
       |}.
    
  Definition squot_to_A : squot P -> A
    := quotient_rec (rel P) idmap (fun _ _ => idmap).

  Global Instance squot_to_A_isequiv : IsEquiv squot_to_A.
  Proof.
    simple refine (isequiv_adjointify _ (class_of (rel P)) _ _).
    - intros x ; reflexivity.
    - unfold Sect.
      simple refine (quotient_ind _ _ _ _).
      + reflexivity.
      + intros.
        apply path_ishprop.
  Defined.
End set_is_setoid_quotient.

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

