Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory bicategory.bicategory_laws
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     modification.modification
     modification.examples.identity
     modification.examples.composition.

Definition transformation_category
           `{Univalence}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
  : PreCategory.
Proof.
  simple refine (@Build_PreCategory (LaxTransformation F G)
                                    (fun x y => modification x y) _ _ _ _ _ _).
  - apply id_modification.
  - cbn ; intros ? ? ? p q.
    apply (comp_modification p q).
  - cbn ; intros.
    apply path_modification ; cbn.
    funext x.
    apply associativity.
  - cbn ; intros.
    apply path_modification ; cbn.
    funext x.
    apply left_identity.
  - cbn ; intros.
    apply path_modification ; cbn.
    funext x.
    apply right_identity.
Defined.