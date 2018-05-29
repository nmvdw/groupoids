Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
Require Import bicategory.

Local Open Scope bicategory_scope.

Record LaxFunctor
       `{Univalence}
       (C D : BiCategory)
  := { Fobj :> Obj C -> Obj D ;
       Fmor : forall {X Y : C}, Functor (Hom C X Y) (Hom D (Fobj X) (Fobj Y)) ;
       Fcomp : forall {X Y Z : C},
           NaturalTransformation
             (c_m o (Functor.pair (@Fmor Y Z) (@Fmor X Y)))
             ((@Fmor X Z) o c_m);
       Fid : forall (X : C), morphism _ (id_m (Fobj X)) (Fmor (id_m X));
       Fun_r : forall {X Y : C} (f : Hom C X Y),
           un_r (Fobj X) (Fobj Y) (Fmor f)
           =
           ((morphism_of Fmor (un_r _ _ f))
              o (Fcomp (f,id_m X))
              o (1 ∗ Fid X))%morphism ;
       Fun_l : forall (X Y : C) (f : Hom C X Y),
           un_l (Fobj X) (Fobj Y) (Fmor f)
           =
           ((morphism_of Fmor (un_l X Y f))
              o (Fcomp (id_m Y,f))
              o (Fid Y ∗ 1))%morphism ;
       Fassoc : forall (W X Y Z : C) (h : Hom C Y Z) (g : Hom C X Y) (f : Hom C W X),
           ((Fcomp (h, (g ⋅ f)))
              o (1 ∗ (Fcomp (g,f)))
              o (assoc (Fmor h,
                        Fmor g,
                       Fmor f))
           =
           (morphism_of Fmor (assoc (h,g,f)))
             o Fcomp (h ⋅ g,f)
             o (Fcomp (h,g) ∗ 1))%morphism
    }.

Definition laxmorphism_of
           `{Univalence}
           {C D : BiCategory} (F : LaxFunctor C D)
           {X Y : C} : Functor (Hom C X Y) (Hom D (F X) (F Y))
  := Fmor _ _ F.

Arguments Fobj {_ C D} F : rename.
Arguments Fmor {_ C D} F {X Y} : rename.
Arguments Fcomp {_ C D} F {X Y Z} : rename.
Arguments Fid {_ C D} F X : rename.