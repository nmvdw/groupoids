Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     general_category bicategory.bicategory univalent.

Section OneTypesBiCategory.
  Context `{Funext}.
  
  Definition maps (A B : 1 -Type) : PreCategory.
  Proof.
    simple refine (@Build_PreCategory (A -> B) (fun f g => f = g) _ _ _ _ _ _).
    - reflexivity.
    - intros ? ? ? p q ; exact (q @ p).
    - cbn ; intros.
      apply concat_p_pp.
    - cbn ; intros.
      apply concat_p1.
    - cbn ; intros.
      apply concat_1p.
  Defined.

  Definition maps_cat (A B : 1 -Type) : IsCategory (maps A B).
  Proof.
    intros f g ; cbn in *.
    simple refine (isequiv_adjointify _ _ _ _).
    - intros α.
      apply α.
    - intros α.
      apply path_isomorphic.
      destruct α as [α αiso].
      induction α ; cbn in *.
      reflexivity.
    - intros p ; induction p.
      reflexivity.
  Defined.
  
  Definition one_types_d : BiCategory_d.
  Proof.
    make_bicategory.
    - exact (1 -Type).
    - exact (fun X Y => maps X Y).
    - exact (fun _ => idmap).
    - exact (fun _ _ _ p => Datatypes.fst p o Datatypes.snd p)%function.
    - intros X Y Z [f₁ f₂] [g₁ g₂] [p₁ p₂] ; cbn in *.
      funext x.
      exact (ap10 p₁ (f₂ x) @ ap g₁ (ap10 p₂ x)).
    - intros X Y f ; simpl in *.
      reflexivity.
    - intros X Y f ; simpl in *.
      reflexivity.
    - intros X Y f ; simpl in *.
      reflexivity.
    - intros X Y f ; simpl in *.
      reflexivity.
    - intros W X Y Z f g h ; simpl in *.
      reflexivity.
    - intros W X Y Z f g h ; simpl in *.
      reflexivity.
  Defined.

  Definition one_types_is_bicategory : is_bicategory one_types_d.
  Proof.
    make_is_bicategory.
    - intros X Y Z [f₁ f₂] ; simpl in *.
      rewrite path_forall_1.
      reflexivity.
    - intros X Y Z [f₁ f₂] [g₁ g₂] [h₁ h₂] [p₁ p₂] [q₁ q₂] ; simpl in *.
      induction p₁, p₂, q₁, q₂ ; simpl.
      rewrite path_forall_1.
      reflexivity.
    - intros X Y f g p ; simpl in *.
      induction p ; simpl.
      rewrite path_forall_1.
      reflexivity.
    - intros X Y f g p ; simpl in *.
      induction p ; simpl.
      rewrite path_forall_1.
      reflexivity.
    - intros X Y f g p ; simpl in *.
      induction p ; simpl.
      rewrite path_forall_1.
      reflexivity.
    - intros X Y f g p ; simpl in *.
      induction p ; simpl.
      rewrite path_forall_1.
      reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - intros W X Y Z h₁ h₂ g₁ g₂ f₁ f₂ ph pg pf ; simpl in *.
      induction ph, pg, pf ; simpl.
      rewrite !path_forall_1.
      reflexivity.
    - intros W X Y Z h₁ h₂ g₁ g₂ f₁ f₂ ph pg pf ; simpl in *.
      induction ph, pg, pf ; simpl.
      rewrite !path_forall_1.
      reflexivity.
    - reflexivity.
    - reflexivity.
    - intros X Y Z g f ; simpl in *.
      rewrite path_forall_1.
      reflexivity.
    - intros V W X Y Z k h g f ; simpl in *.
      rewrite path_forall_1.
      reflexivity.
  Qed.

  Definition one_types : BiCategory
    := Build_BiCategory one_types_d one_types_is_bicategory.

  Definition one_types_locally_univalent
    : locally_univalent one_types.
  Proof.
    intro ; apply _.
  Qed.

  Definition one_types_is_21
             `{Funext}
    : is_21 one_types.
  Proof.
    intros X Y f g p ; simpl in *.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - exact p^.
    - apply concat_pV.
    - apply concat_Vp.
  Defined.
End OneTypesBiCategory.