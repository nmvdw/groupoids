Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     general_category bicategory.bicategory.

Section OneTypesBiCategory.
  Context `{Univalence}.

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
    - intros X Y Z [f₁ f₂] [g₁ g₂] [p₁ p₂] ; simpl in *.
      induction p₁, p₂ ; simpl.
      reflexivity.
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
      reflexivity.
    - intros X Y Z [f₁ f₂] [g₁ g₂] [h₁ h₂] [p₁ p₂] [q₁ q₂] ; simpl in *.
      induction p₁, p₂, q₁, q₂ ; simpl.
      reflexivity.
    - intros X Y f g p ; simpl in *.
      induction p ; simpl.
      reflexivity.
    - intros X Y f g p ; simpl in *.
      induction p ; simpl.
      reflexivity.
    - intros X Y f g p ; simpl in *.
      induction p ; simpl.
      reflexivity.
    - intros X Y f g p ; simpl in *.
      induction p ; simpl.
      reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - intros W X Y Z h₁ h₂ g₁ g₂ f₁ f₂ ph pg pf ; simpl in *.
      induction ph, pg, pf ; simpl.
      reflexivity.
    - intros W X Y Z h₁ h₂ g₁ g₂ f₁ f₂ ph pg pf ; simpl in *.
      induction ph, pg, pf ; simpl.
      reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Defined.
End OneTypesBiCategory.