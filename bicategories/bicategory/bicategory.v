Require Import HoTT.
From HoTT.Categories Require Export
     Category Functor NaturalTransformation FunctorCategory.
From HoTT.Categories Require Import
     GroupoidCategory.
From GR Require Import bicategories.general_category.

Record BiCategory `{Univalence} :=
  Build_BiCategory {
      Obj :> Type ;
      Hom : Obj -> Obj -> PreCategory ;
      id_m : forall (x : Obj), Hom x x ;
      c_m : forall {x y z : Obj}, Functor (Category.prod (Hom y z) (Hom x y)) (Hom x z) ;
      un_l : forall (X Y : Obj),
          NaturalTransformation (@c_m X Y Y o (const_functor (id_m Y) * 1))
                                1 ;
      un_l_iso :> forall (X Y : Obj),
         @IsIsomorphism (Hom X Y -> Hom X Y) _ _ (un_l X Y) ;
      un_r : forall (X Y : Obj),
          NaturalTransformation (@c_m X X Y o (1 * const_functor (id_m X)))
                                1 ;
      un_r_iso :> forall (X Y : Obj),
          @IsIsomorphism (Hom X Y -> Hom X Y) _ _ (un_r X Y) ;
      assoc : forall (w x y z : Obj),
        NaturalTransformation
          ((c_m o (c_m, 1)))
          (c_m o (1, c_m) o (assoc_prod (Hom y z) (Hom x y) (Hom w x))) ;
      assoc_iso :> forall (w x y z : Obj), @IsIsomorphism
                                            ((Hom y z * Hom x y) * Hom w x -> Hom w z)
                                            _
                                            _
                                            (assoc w x y z) ;
      triangle_r : (forall (x y z : Obj) (g : Hom y z) (f : Hom x y),
                     @morphism_of _
                                  _
                                  c_m
                                  (c_m (g,id_m y),f)
                                  (g,f)
                                  ((un_r y z) g, 1)
                     =
                     (@morphism_of _
                                   _
                                   c_m
                                   (g,c_m (id_m y,f))
                                   (g,f)
                                   (1,un_l x y f))
                       o
                       (assoc x y y z) (g, id_m y, f))%morphism ;
      pentagon : (forall (v w x y z : Obj)
                         (k : Hom y z) (h : Hom x y) (g : Hom w x) (f : Hom v w),
                     (assoc v x y z (k,h,c_m (g,f)))
                       o assoc v w x z (c_m (k, h), g, f)
                     = (@morphism_of _
                                     _
                                     (@c_m v y z)
                                     (k,c_m (c_m (h,g),f))
                                     (k,c_m (h,c_m (g,f)))
                                     (1,assoc v w x y (h,g,f)))
                         o (assoc v w y z (k,c_m (h,g),f))
                         o
                         (@morphism_of _
                                       _
                                       (@c_m v w z)
                                       (c_m (c_m (k,h),g),f)
                                       (c_m (k,c_m (h,g)),f)
                                       (assoc w x y z (k,h,g),1)))%morphism
    }.

Arguments id_m {_} {B} x : rename.
Arguments c_m {_} {B} {x y z} : rename.
Arguments un_l {_ B} X Y : rename.
Arguments un_r {_ B} X Y : rename.
Arguments assoc {_ B w x y z} : rename.

Delimit Scope bicategory_scope with bicategory.
Bind Scope bicategory_scope with BiCategory.
Notation "f '⋅' g" := (c_m (f,g)) (at level 40): bicategory_scope.

Instance un_r_iso_componenetwise `{Univalence} {B : BiCategory} {X Y : B} f :
  Morphisms.IsIsomorphism (un_r X Y f).
Proof.
  unshelve eapply isisomorphism_components_of.
  - apply _.
  - apply B.
Defined.

Instance un_l_iso_componenetwise `{Univalence} {B : BiCategory} {X Y : B} f :
  Morphisms.IsIsomorphism (un_l X Y f).
Proof.
  unshelve eapply isisomorphism_components_of.
  - apply _.
  - apply B.
Defined.

Instance assoc_iso_componenetwise `{Univalence} {B : BiCategory} {W X Y Z : B} f :
  Morphisms.IsIsomorphism (@assoc _ _ W X Y Z f).
Proof.
  unshelve eapply isisomorphism_components_of.
  - apply _.
  - apply B.
Qed.

Section BiCategory.
  Context `{Univalence}.

  Definition one_cell {BC : BiCategory} := Hom BC.
  
  Definition two_cell
             {BC : BiCategory}
             {A B : BC}
             (f g : one_cell A B)
    := morphism _ f g.

  Definition hcomp
             {BC : BiCategory}
             {A B C : BC}
             {f f' : one_cell A B} {g g' : one_cell B C}
             (α : two_cell f f') (β : two_cell g g')
    : (two_cell (g ⋅ f) (g' ⋅ f'))%bicategory
    := (c_m _1 ((β, α) : morphism (Hom _ B C * Hom _ A B) (g,f) (g',f')))%morphism.

  Local Notation "f '∗' g" := (hcomp g f) (at level 40) : bicategory_scope.

  Local Open Scope bicategory_scope.

  Definition interchange
             (C : BiCategory)
             {X Y Z : C}
             {p q r : one_cell X Y}
             {p' q' r' : one_cell Y Z}
             (h : two_cell p q) (h' : two_cell p' q')
             (k : two_cell q r) (k' : two_cell q' r')
    : ((k' o h') ∗ (k o h) = (k' ∗ k) o (h' ∗ h))%morphism.
  Proof.
    rewrite <- composition_of.
    reflexivity.
  Defined.
End BiCategory.

Notation "f '∗' g" := (hcomp g f) (at level 40) : bicategory_scope.

Section whiskering.
  Context `{Univalence}.
  Variable (BC : BiCategory).

  Definition bc_whisker_r
             {A B C : BC}
             {f₁ : one_cell A B} (f₂ : one_cell A B)
             (g : one_cell B C)
             (α : two_cell f₁ f₂)
    : (two_cell (g ⋅ f₁) (g ⋅ f₂))%bicategory.
  Proof.
    refine (morphism_of _ _).
    split ; cbn.
    - exact 1%morphism.
    - exact α.
  Defined.

  Definition bc_whisker_l
             {A B C : BC}
             (f : one_cell A B)
             {g₁ : one_cell B C} (g₂ : one_cell B C)
             (β : two_cell g₁ g₂)
    : (two_cell (g₁ ⋅ f) (g₂ ⋅ f))%bicategory.
  Proof.
    refine (morphism_of _ _).
    split ; cbn.
    - exact β.
    - exact 1%morphism.
  Defined.

  Definition bc_whisker_lr
             {A B C : BC}
             {f₁ f₂ : one_cell A B} {g₁ g₂ : one_cell B C}
             (α : two_cell f₁ f₂) (β : two_cell g₁ g₂)
    : (two_cell (g₁ ⋅ f₁) (g₂ ⋅ f₂))%bicategory
    := (bc_whisker_l f₂ _ β o bc_whisker_r _ g₁ α)%morphism.
End whiskering.

Arguments bc_whisker_r {_ BC A B C f₁} f₂ g α.
Arguments bc_whisker_l {_ BC A B C} f {g₁} g₂ β.
Arguments bc_whisker_lr {_ BC A B C f₁} f₂ {g₁} g₂ α β.

Definition is_21 `{Univalence} (C : BiCategory)
  : hProp
  := BuildhProp (forall (X Y : C), IsGroupoid (Hom C X Y)).