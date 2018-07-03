Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory bicategory.bicategory_laws
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     modification.modification.

Definition comp_modification
           `{Univalence}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           {η₁ η₂ η₃ : LaxTransformation F G}
           (q : modification η₂ η₃) (p : modification η₁ η₂)
  : modification η₁ η₃.
Proof.
  simple refine (Build_Modification _ _).
  - exact (fun A => mod_component q A o mod_component p A)%morphism.
  - intros A B f.
    rewrite bc_whisker_r_compose, bc_whisker_l_compose.
    rewrite <- !associativity.
    rewrite !mod_commute.
    rewrite !associativity.
    rewrite mod_commute.
    reflexivity.
Defined.