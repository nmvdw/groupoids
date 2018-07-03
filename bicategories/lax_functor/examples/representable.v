Require Import HoTT.
From GR.bicategories Require Import
     bicategory.bicategory
     bicategory.bicategory_laws
     lax_functor.lax_functor
     lax_functor.examples.composition
     lax_transformation.lax_transformation
     general_category.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories.bicategory.examples Require Import
     precat
     opposite.

Definition precompose_by
           `{Univalence}
           {C : BiCategory}
           (X : C)
           {Y Z : C}
           (f : Hom C Z Y)
  : Functor (Hom C Y X) (Hom C Z X).
Proof.
  simple refine (Build_Functor _ _ _ _ _ _).
  - exact (fun g => c_m (g,f)).
  - intros g₁ g₂ α ; cbn.
    exact (@morphism_of _ _ (@c_m _ C Z Y X) (g₁,f) (g₂,f) (α,1%morphism)).
  - intros g₁ g₂ g₃ α₁ α₂ ; cbn.
    rewrite <- composition_of ; simpl.
    rewrite left_identity.
    reflexivity.
  - intros g ; cbn.
    apply identity_of.
Defined.

Definition precompose_morphism
           `{Univalence}
           {C : BiCategory}
           (X : C)
           {Y Z : C}
           {f₁ f₂ : Hom C Z Y}
           (α : morphism (Hom C Z Y) f₁ f₂)
  : Core.NaturalTransformation (precompose_by X f₁) (precompose_by X f₂).
Proof.
  simple refine (Build_NaturalTransformation _ _ _ _).
  - intros g ; simpl in *.
    exact (@morphism_of _ _ (@c_m _ C Z Y X) (g,f₁) (g,f₂) (1%morphism,α)).
  - intros g₁ g₂ β ; simpl in *.
    rewrite <- !composition_of ; simpl.
    rewrite !left_identity, !right_identity.
    reflexivity.
Defined.

Definition precompose_morphism_compose
           `{Univalence}
           {C : BiCategory}
           {X Y Z : C}
           {f₁ f₂ f₃ : Hom C Z Y}
           (α₁ : morphism (Hom C Z Y) f₁ f₂)
           (α₂ : morphism (Hom C Z Y) f₂ f₃)
  : precompose_morphism X (α₂ o α₁)
    =
    (precompose_morphism X α₂ o precompose_morphism X α₁)%natural_transformation.
Proof.
  apply path_natural_transformation.
  intros g ; simpl.
  rewrite <- !composition_of ; simpl.
  rewrite left_identity.
  reflexivity.
Qed.


Definition precompose_morphism_identity
           `{Univalence}
           {C : BiCategory}
           {X Y Z : C}
           {f : Hom C Z Y}
  : precompose_morphism X (1 : morphism (Hom C Z Y) f f)
    =
    1%natural_transformation.
Proof.
  apply path_natural_transformation.
  intros g ; simpl.
  apply identity_of.
Qed.

Definition precompose_functor
           `{Univalence}
           {C : BiCategory}
           (X Y Z : C)
  : Functor (Hom C Z Y) (Hom C Y X -> Hom C Z X).
Proof.
  simple refine (Build_Functor _ _ _ _ _ _).
  - apply precompose_by.
  - intros ? ? ; apply precompose_morphism.
  - intros ? ? ? ; apply precompose_morphism_compose.
  - intros ; apply precompose_morphism_identity.
Defined.

Definition representable_d
           `{Univalence}
           {C : BiCategory}
           (X : C)
  : LaxFunctor_d (op C) PreCat.
Proof.
  simple refine {|Fobj_d := _|}.
  - exact (fun Y => Hom C Y X).
  - intros ; cbn in *.
    apply precompose_functor.
  - intros Y₁ Y₂ Y₃ ; cbn in *.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros [f₁ f₂] ; cbn.
      simple refine (Build_NaturalTransformation _ _ _ _).
      * intros h ; cbn.
        exact (assoc (h,f₂,f₁)).
      * intros g₁ g₂ α ; cbn.
        pose (commutes (@assoc _ C Y₃ Y₂ Y₁ X) (g₁,f₂,f₁) (g₂,f₂,f₁) (α,1,1)%morphism) as p.
        rewrite p ; cbn.
        rewrite identity_of.
        reflexivity.
    + intros [f₁ f₂] [g₁ g₂] [α₁ α₂] ; cbn in *.
      apply path_natural_transformation.
      intros h ; cbn.
      rewrite <- !composition_of ; simpl.
      rewrite !left_identity, !right_identity.
      pose (commutes (@assoc _ C _ _ _ _) (h,f₂,f₁) (h,g₂,g₁) (1,α₂,α₁)%morphism) as p.
      rewrite p ; cbn.
      reflexivity.
  - intros Y ; cbn in *.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros f ; simpl.
      exact (@morphism_inverse (_ -> _) _ _ (un_r Y X) _ f).
    + intros f₁ f₂ α ; cbn.
      rewrite (commutes (@morphism_inverse (_ -> _) _ _ (un_r Y X) _) f₁ f₂ α) ; cbn.
      reflexivity.
Defined.

Definition representable_d_is_lax
           `{Univalence}
           {C : BiCategory}
           (X : C)
  : is_lax (representable_d X).
Proof.
  repeat split.
  - intros Y Z f ; cbn.
    apply path_natural_transformation.
    intros h ; cbn in *.
    rewrite left_identity.
    rewrite <- triangle_r.
    rewrite <- composition_of ; cbn.
    rewrite right_identity.
    pose (@right_inverse (Hom (op C) X Y -> _) _ _ (un_r Y X) _) as p.
    pose (equiv_path_natural_transformation _ _ p h) as q.
    cbn in q.
    rewrite q.
    rewrite identity_of.
    reflexivity.
  - intros Y Z f ; cbn.
    apply path_natural_transformation.
    intros h ; cbn in *.
    rewrite <- un_r_assoc.
    rewrite right_identity.
    pose (@right_inverse (Hom C Z X -> _) _ _ (un_r Z X) _) as p.
    pose (equiv_path_natural_transformation _ _ p (c_m (h,f))) as q.
    cbn in q.
    rewrite q.
    reflexivity.
  - intros Y₁ Y₂ Y₃ Y₄ g₁ g₂ g₃.
    apply path_natural_transformation.
    intros h ; cbn.
    rewrite identity_of, left_identity, right_identity, identity_of, right_identity.
    pose (pentagon C _ _ _ _ _ h g₃ g₂ g₁) as p.
    rewrite !associativity.
    rewrite p.
    rewrite <- !associativity.
    rewrite <- composition_of.
    refine ((left_identity _ _ _ _)^ @ _).
    rewrite <- !associativity.
    repeat f_ap ; cbn.
    rewrite left_identity, left_inverse.
    rewrite identity_of.
    reflexivity.
Qed.

Definition representable
           `{Univalence}
           {C : BiCategory}
           (X : C)
  : LaxFunctor (op C) PreCat
  := (representable_d X;representable_d_is_lax X).