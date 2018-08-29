Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR Require Import
     bicategory.bicategory bicategory.univalent.

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
             {HC : LocallyUnivalent C}
    : LocallyUnivalent full_sub.
  Proof.
    intros X Y.
    apply HC.
  Defined.
End FullSub.
