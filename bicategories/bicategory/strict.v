Require Import HoTT.
Require Import GR.bicategories.general_category.
From GR.bicategories Require Import bicategory.bicategory.

Record IsStrict (C : BiCategory) :=
    Build_Strict {
        strict_left_unit :
          forall {X Y : C} (f : C⟦X,Y⟧),
            id₁ Y · f = f ;
        strict_right_unit :
          forall {X Y : C} (f : C⟦X,Y⟧),
            f · id₁ X = f ;
        strict_assoc :
          forall {W X Y Z : C}
                 (h : C⟦Y,Z⟧) (g : C⟦X,Y⟧) (f : C⟦W,X⟧),
            (h · g) · f = h · (g · f) ;
        strict_triangle_r :
          forall {X Y Z : C}
                 (g : C⟦Y,Z⟧)
                 (f : C⟦X,Y⟧),
            ap (fun z => z · f) (strict_right_unit g)
            =
            strict_assoc g (id₁ Y) f @ ap (fun z => g · z) (strict_left_unit f) ;
        strict_pentagon :
          forall {V W X Y Z : C}
                 (k : C⟦Y,Z⟧) (h : C⟦X,Y⟧)
                 (g : C⟦W,X⟧) (f : C⟦V,W⟧),
            strict_assoc (k · h) g f @ strict_assoc k h (g · f)
            = (ap (fun z => z · f) (strict_assoc k h g))
                @ ((strict_assoc k (h · g) f)
                     @ ap (fun z => k · z) (strict_assoc h g f)) ;
        idtoiso_strict_left_unit :
          forall {X Y : C} (f : C⟦X,Y⟧),
            @morphism_isomorphic _ _ _ (idtoiso _ (strict_left_unit f))
            =
            left_unit f ;
        idtoiso_strict_right_unit :
          forall {X Y : C} (f : C⟦X,Y⟧),
            @morphism_isomorphic _ _ _ (idtoiso _ (strict_right_unit f))
            =
            right_unit f ;
        idtoiso_strict_assoc :
          forall {W X Y Z : C}
                 (h : C⟦Y,Z⟧) (g : C⟦X,Y⟧) (f : C⟦W,X⟧),
            @morphism_isomorphic _ _ _ (idtoiso _ (strict_assoc h g f))
            =
            assoc h g f ;
      }.

Arguments Build_Strict {C} _ _ _ _ _ _ _ _.

Ltac make_strict := simple refine (Build_Strict _ _ _ _ _ _ _ _).

Arguments strict_left_unit {C} _ {X Y} f.
Arguments strict_right_unit {C} _ {X Y} f.
Arguments strict_assoc {C} _ {W X Y Z} h g f.
Arguments strict_triangle_r {C} _ {X Y Z} g f.
Arguments strict_pentagon {C} _ {V W X Y Z} k h g f.