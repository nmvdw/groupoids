Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR Require Import
     bicategory.bicategory.

Definition full_sub
           `{Univalence}
           (C : BiCategory)
           (P : Obj C -> hProp)
  : BiCategory
  := Build_BiCategory
       {X : Obj C & P X}
       (fun X Y => Hom C X.1 Y.1)
       (fun X => id_m X.1)
       (fun X Y Z => @c_m _ C X.1 Y.1 Z.1)
       (fun X Y => un_l X.1 Y.1)
       (fun X Y => un_r X.1 Y.1)
       (fun W X Y Z => assoc)
       (fun X Y Z => @triangle_r _ C X.1 Y.1 Z.1)
       (fun V W X Y Z => @pentagon _ C V.1 W.1 X.1 Y.1 Z.1).