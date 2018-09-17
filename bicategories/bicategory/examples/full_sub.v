Require Import HoTT.
From HoTT.Categories Require Import
     Functor.
From GR Require Import
     bicategory.bicategory
     bicategory.univalent
     bicategory.adjoint
     bicategory.adjoint_unique.

Section FullSub.
  Variable (C : BiCategory)
           (P : Obj C -> hProp).

  Definition full_sub_d : BiCategory_d.
  Proof.
    make_bicategory.
    - exact {X : C & P X}.
    - exact (fun X Y => C⟦X.1,Y.1⟧).
    - exact (fun X => id₁ X.1).
    - exact (fun X Y Z => hcomp X.1 Y.1 Z.1).
    - exact (fun X Y Z f g p => morphism_of (hcomp X.1 Y.1 Z.1) p).
    - exact (fun X Y f => left_unit f).
    - exact (fun X Y f => left_unit_inv f).
    - exact (fun X Y f => right_unit f).
    - exact (fun X Y f => right_unit_inv f).
    - exact (fun W X Y Z f g h => assoc f g h).
    - exact (fun W X Y Z f g h => assoc_inv f g h).
  Defined.

  Definition full_sub_d_is_bicategory : is_bicategory full_sub_d.
  Proof.
    make_is_bicategory ; intros ; apply C.
  Qed.

  Definition full_sub
    : BiCategory
    := Build_BiCategory
         full_sub_d
         full_sub_d_is_bicategory.

  Global Instance locally_univalent_full_sub
         `{Univalence}
         {HC : Univalent C}
    : LocallyUnivalent full_sub.
  Proof.
    intros X Y.
    apply HC.
  Defined.

  Lemma id_to_adjequiv_full_sub
        `{Univalence}
         {HC : Univalent C} 
        {X Y : full_sub}
        (p : X = Y)
    : id_to_adjequiv X Y (path_sigma_hprop X Y p..1)
      =
      id_to_adjequiv X.1 Y.1 p..1.
  Proof.
    induction p ; cbn.
    rewrite path_sigma_hprop_1.
    apply path_adjoint_equivalence.
    reflexivity.
  Qed.

  Global Instance univalent_0_full_sub
         `{Univalence}
         {HC : Univalent C}
    : Univalent_0 full_sub.
  Proof.
    intros X Y.
    simple refine (isequiv_adjointify _ _ _ _) ; cbn.
    - exact (fun e => path_sigma_hprop _ _ (adjequiv_to_id X.1 Y.1 e)).
    - intros e.
      apply path_adjoint_equivalence ; f_ap.
      refine (_ @ @eisretr _ _ (id_to_adjequiv X.1 Y.1) _ e).
      refine (_ @ (id_to_adjequiv_full_sub
                     (path_sigma_hprop _ _ (adjequiv_to_id X.1 Y.1 e)))
                @ _).
      + rewrite pr1_path_path_sigma_hprop.
        reflexivity.
      + rewrite pr1_path_path_sigma_hprop.
        reflexivity.
    - intros p.
      induction p ; cbn.
      rewrite <- path_sigma_hprop_1.
      f_ap.
      rewrite <- (eissect (id_to_adjequiv _ _)) ; cbn.
      f_ap.
      apply path_adjoint_equivalence.
      reflexivity.
  Defined.

  Global Instance univalent_full_sub
         `{Univalence}
         {HC : Univalent C}
    : Univalent full_sub.
  Proof.
    split ; apply _.
  Defined.
End FullSub.
