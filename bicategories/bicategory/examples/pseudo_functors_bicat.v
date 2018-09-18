Require Import HoTT.
From GR Require Import
     bicategories.bicategory.bicategory
     bicategories.lax_functor.lax_functor
     bicategories.lax_transformation.lax_transformation
     bicategories.lax_transformation.examples.identity
     bicategories.lax_transformation.examples.composition
     bicategories.bicategory.examples.full_sub
     bicategories.bicategory.examples.lax_functors_bicat
     bicategories.bicategory.examples.arrow_subcategory.

Definition Pseudo `{Univalence} (C D : BiCategory) : BiCategory.
Proof.
  refine (arrow_subcat
            (full_sub (Lax C D) (fun F => BuildhProp (is_pseudo F)))
            (fun _ _ η => BuildhProp (is_pseudo_transformation η)) 
            _
            _
         ).
  - intros F ; simpl in *.
    apply identity_transformation.
  - intros F₁ F₂ F₃ η₁ η₂ Hη₁ Hη₂ ; simpl in *.
    apply (compose_pseudo (η₁;Hη₁) (η₂;Hη₂)).
Defined.