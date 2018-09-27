Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories.bicategory Require Import
     bicategory
     examples.prod
     examples.lax_functors_bicat.
From GR.bicategories.lax_functor Require Import
     lax_functor
     examples.identity
     examples.composition.
From GR.bicategories.lax_transformation Require Import
     lax_transformation
     transformation_category
     examples.whisker_L
     examples.whisker_R
     examples.right_identity
     examples.left_identity
     examples.associativity
     examples.right_identity_inv
     examples.left_identity_inv
     examples.associativity_inv
     examples.restriction
     examples.identity
     examples.composition.
From GR.bicategories.modification Require Import
     modification
     examples.composition
     examples.whisker_L
     examples.whisker_R.

Definition yolo {A} : A.
Admitted.

Definition test
           `{Funext}
           (C D E : BiCategory)
  : LaxFunctor_d (prod (Lax D E) (Lax C D )) (Lax C E).
Proof.
  make_laxfunctor.
  - cbn.
    intros [G F].
    exact (lax_comp G F).
  - intros [G₁ F₁] [G₂ F₂] ; cbn.
    simple refine (Build_Functor _ _ _ _ _ _) ; cbn.
    + intros [η₁ η₂].
      refine (compose (whisker_L _ η₂) (whisker_R _ η₁)).
      apply yolo.
    + intros [η₁ ε₁] [η₂ ε₂] [m₁ m₂] ; cbn in *.
      refine (comp_modification (whisker_L_mod _ _) (whisker_R_mod _ _)).
      * simple refine (Build_Modification _ _).
        ** intros X ; cbn.
           exact (m₁ (F₂ X)).
        ** intros A B f ; cbn.
           unfold bc_whisker_l, bc_whisker_r.
           apply m₁.
      * simple refine (Build_Modification _ _).
        ** intros X ; cbn.
           exact (G₁ ₂ (m₂ X)).
        ** intros A B f ; cbn.
           pose (mod_commute m₂ f).
           unfold bc_whisker_l, bc_whisker_r in *.
           rewrite <- !vcomp_assoc.
           rewrite <- !Fmor₂_id₂.
           rewrite <- Fcomp₁_inv_naturality.
           rewrite !vcomp_assoc.
           f_ap.
           rewrite Fcomp₂.
           rewrite <- !vcomp_assoc.
           f_ap.
           rewrite <- !Fmor₂_vcomp.
           rewrite !Fmor₂_id₂.
           rewrite p.
           reflexivity.
           rewrite !vcomp_assoc.
           pose @Fcomp₂.
           _naturality.
           pose @vcomp_2.
           Search Fcomp₁_inv.
           pose @Fcomp₂_inv.
           Search modification.
           cbn.