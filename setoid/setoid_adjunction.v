Require Import HoTT.
Require Import setoid squot_properties.
From HoTT.Categories Require Import
  Category Functor NaturalTransformation FunctorCategory Adjoint.

Definition setoid_map (R₁ R₂ : setoid) : Type
  := {f : under R₁ -> under R₂ & forall (x₁ x₂ : under R₁),
              rel R₁ x₁ x₂ -> rel R₂ (f x₁) (f x₂)}.

Definition setoid_idmap (R : setoid) : setoid_map R R.
Proof.
  exists idmap.
  intros ? ? .
  exact idmap.
Defined.

Definition setoid_compose
           {R₁ R₂ R₃ : setoid}
           (g : setoid_map R₂ R₃) (f : setoid_map R₁ R₂)
  : setoid_map R₁ R₃.
Proof.
  exists (g.1 o f.1).
  intros x y p.
  exact (g.2 _ _ (f.2 _ _ p)).
Defined.

Global Instance setoid_map_hset
       (R₁ R₂ : setoid)
       `{Univalence}
  : IsHSet (setoid_map R₁ R₂)
  := _.

Definition setoids_precat `{Univalence} : PreCategory.
Proof.
  simple refine {|object := setoid ;
                  morphism := setoid_map ;
                  Core.identity := setoid_idmap ;
                  Category.Core.compose := @setoid_compose|}
  ; try reflexivity.
Defined.

Definition set_precat `{Univalence} : PreCategory.
Proof.
  simple refine {|object := hSet ;
                  morphism := fun X Y => BuildhSet(X -> Y) ;
                  Core.identity := fun _ x => x ;
                  Category.Core.compose := fun _ _ _ g f => g o f|}
  ; try reflexivity.
Defined.

Definition path_setoid_functor `{Univalence}
  : Functor set_precat setoids_precat.
Proof.
  unshelve esplit.
  - apply path_setoid.
  - intros X Y f ; cbn in *.
    exact (f;fun x y => ap f).
  - intros X Y Z g f ; cbn in *.
    simple refine (path_sigma' _ _ _).
    + reflexivity.
    + apply path_ishprop.
  - intros X ; cbn in *.
    simple refine (path_sigma' _ _ _).
    + reflexivity.
    + apply path_ishprop.
Defined.

Definition squot_functor `{Univalence}
  : Functor setoids_precat set_precat.
Proof.
  unshelve esplit.
  - exact (fun R => BuildhSet (squot R)).
  - intros R₁ R₂ f ; cbn in *.
    simple refine (quotient_rec _ _ _).
    + exact (class_of _ o f.1).
    + intros x y p; cbn in *.
      apply related_classes_eq.
      exact (f.2 x y p).
  - intros R₁ R₂ R₃ g f ; cbn in *.
    funext z ; cbn in * ; revert z.
    simple refine (quotient_ind _ _ _ _).
    + reflexivity.
    + intros ; apply path_ishprop.
  - intros X ; cbn in *.
    funext z ; cbn in * ; revert z.
    simple refine (quotient_ind _ _ _ _).
    + reflexivity.
    + intros ; apply path_ishprop.
Defined.

Definition adjunction_squot `{Univalence}
  : AdjunctionUnitCounit squot_functor path_setoid_functor.
Proof.
  unshelve esplit.
  - simple refine (Build_NaturalTransformation _ _ _ _).
    + intros R ; cbn in *.
      refine (class_of (rel R);_) ; cbn.
      exact (fun _ _ p => related_classes_eq (rel R) p).
    + intros R₁ R₂ f ; cbn in *.
      simple refine (path_sigma' _ _ _).
      * reflexivity.
      * apply path_ishprop.
  - simple refine (Build_NaturalTransformation _ _ _ _).
    + intros X ; cbn in *.
      simple refine (quotient_rec _ _ _).
      * exact idmap.
      * intros ; assumption.
    + intros X Y f ; cbn in *.
      funext z ; revert z.
      simple refine (quotient_ind _ _ _ _).
      * reflexivity.
      * intros ; apply path_ishprop.
  - intros X ; cbn.
    funext z ; revert z.
    simple refine (quotient_ind _ _ _ _).
    + reflexivity.
    + intros ; apply path_ishprop.
  - intros R ; cbn.
    simple refine (path_sigma' _ _ _).
    + reflexivity.
    + apply path_ishprop.
Defined.

Definition squot_path_setoid `{Univalence}
  : NaturalTransformation (squot_functor o path_setoid_functor) 1.
Proof.
  simple refine (Build_NaturalTransformation _ _ _ _).
  - intros X ; cbn in *.
    simple refine (quotient_rec _ _ _).
    + exact idmap.
    + intros x y p ; cbn in *.
      exact p.
  - intros X Y f ; cbn in *.
    funext z ; revert z.
    simple refine (quotient_ind _ _ _ _).
    + reflexivity.
    + intros ; apply path_ishprop.
Defined.

Global Instance squot_path_setoid_isiso `{Univalence}
  : @IsIsomorphism (set_precat -> set_precat) _ _ squot_path_setoid.
Proof.
  apply isisomorphism_natural_transformation.
  intros X ; cbn in *.
  unshelve esplit ; cbn.
  - exact (class_of _).
  - funext z ; revert z.
    simple refine (quotient_ind _ _ _ _).
    + reflexivity.
    + intros ; apply path_ishprop.
  - funext z ; revert z.
    reflexivity.
Defined.