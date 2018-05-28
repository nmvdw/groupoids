Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
Require Import bicategory.

Definition full_sub
           `{Univalence}
           (C : BiCategory)
           (P : Obj C -> hProp)
  : BiCategory
  := {|Obj := {X : Obj C & P X} ;
       Hom := fun X Y => Hom C X.1 Y.1 ;
       id_m := fun X => id_m X.1 ;
       c_m := fun X Y Z => @c_m _ C X.1 Y.1 Z.1 ;
       un_l := fun X Y => un_l X.1 Y.1 ;
       un_l_iso := fun X Y => un_l_iso C X.1 Y.1 ;
       un_r := fun X Y => un_r X.1 Y.1 ;
       un_r_iso := fun X Y => un_r_iso C X.1 Y.1 ;
       assoc := fun W X Y Z => assoc ;
       assoc_iso := fun W X Y Z => assoc_iso C W.1 X.1 Y.1 Z.1 ;
       triangle_r := fun X Y Z => @triangle_r _ C X.1 Y.1 Z.1 ;
       pentagon := fun V W X Y Z => @pentagon _ C V.1 W.1 X.1 Y.1 Z.1|}.
