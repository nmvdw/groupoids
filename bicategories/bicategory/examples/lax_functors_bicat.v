Require Import HoTT.
From GR.bicategories Require Import
     bicategory.bicategory
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     lax_transformation.transformation_category
     lax_transformation.examples.identity
     lax_transformation.examples.composition
     modification.modification
     modification.examples.identity
     modification.examples.composition
     general_category.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.

Section LaxFunctors.
  Context `{Univalence}.
  Variable (C D : BiCategory).

  Definition lax_func_obj : Type := LaxFunctor C D.
  
  Definition lax_func_maps (F G : lax_func_obj) : PreCategory
    := transformation_category F G.

  Definition todo A : A.
  Admitted.
  
  Definition comp_functor (F₁ F₂ F₃ : lax_func_obj)
    : Functor (lax_func_maps F₂ F₃ * lax_func_maps F₁ F₂) (lax_func_maps F₁ F₃).
  Proof.
    simple refine (Build_Functor _ _ _ _ _ _).
    - intros [α₁ α₂].
      exact (composition.compose α₁ α₂).
    - intros [α₁ α₂] [β₁ β₂] [σ₁ σ₂] ; cbn in *.
      simple refine (_;_).
      + intros A ; cbn.
        unfold compose_component ; cbn.
        exact (bc_whisker_r _ _ (σ₂.1 A) o bc_whisker_l _ _ (σ₁.1 A))%morphism.
      + cbn.
        intros.
        rewrite !right_identity.
        unfold bc_whisker_r, bc_whisker_l ; simpl.
        rewrite <- !composition_of ; simpl.
        rewrite !left_identity, !right_identity.
        Search Category.Core.compose.
        rewrite <- !associativity.
        apply Morphisms.iso_moveL_pV.
        rewrite !associativity.
        apply Morphisms.iso_moveR_Vp.
        apply todo.
    - intros [f₁ f₂] [g₁ g₂] [h₁ h₂] [α₁ α₂] [β₁ β₂].
      refine (path_sigma_hprop _ _ _) ; cbn.
      funext x ; simpl.
      unfold bc_whisker_r, bc_whisker_l ; simpl.
      rewrite <- !composition_of ; simpl.
      rewrite !left_identity, !right_identity.
      reflexivity.
    - intros [f₁ f₂] ; cbn.
      refine (path_sigma_hprop _ _ _) ; cbn.
      funext x ; simpl.
      unfold bc_whisker_r, bc_whisker_l ; simpl.
      rewrite <- !composition_of ; simpl.
      rewrite !left_identity, identity_of.
      reflexivity.
  Defined.

  Definition cUnitor_l (A B : 1 -Type)
    : NaturalTransformation
        (comp_functor A B B o (@const_functor _ (maps B B) idmap * 1))
        1.
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + reflexivity.
    + cbn ; intros ? ? p.
      induction p.
      reflexivity.
  Defined.

  Definition cUnitor_l_inv (A B : 1 -Type)
    : NaturalTransformation
        1
        (comp_functor A B B o (@const_functor (maps A B) (maps B B) idmap * 1)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + reflexivity.
    + intros ? ? p ; cbn.
      induction p.
      reflexivity.
  Defined.

  Global Instance cUnitor_l_iso (A B : 1 -Type)
    : @IsIsomorphism (maps A B -> maps A B) _ _ (cUnitor_l A B).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply cUnitor_l_inv.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      reflexivity.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      reflexivity.
  Defined.

  Definition cUnitor_r (A B : 1 -Type)
    : NaturalTransformation
        (comp_functor A A B o (1 * @const_functor (maps A B) (maps A A) idmap))
        1.
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + reflexivity.
    + intros ? ? p ; induction p ; cbn.
      reflexivity.
  Defined.

  Definition cUnitor_r_inv (A B : 1 -Type)
    : NaturalTransformation
        1
        (comp_functor A A B o (1 * @const_functor (maps A B) (maps A A) idmap)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + reflexivity.
    + intros ? ? p ; induction p ; cbn.
      reflexivity.
  Defined.

  Global Instance cUnitor_r_iso (A B : 1 -Type)
    : @IsIsomorphism (maps A B -> maps A B) _ _ (cUnitor_r A B).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply cUnitor_r_inv.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      reflexivity.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      reflexivity.
  Defined.

  Definition cAssociator (A B C D : 1 -Type)
    : NaturalTransformation
        (comp_functor A B D o (comp_functor B C D, 1))
        (comp_functor A C D o (1, comp_functor A B C)
                        o assoc_prod (maps C D) (maps B C) (maps A B)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros [[f₁ f₂] f₃] ; cbn in *.
      reflexivity.
    + intros [[f₁ f₂] f₃] [[g₁ g₂] g₃] [[h₁ h₂] h₃] ; cbn in *.
      induction h₁, h₂, h₃ ; cbn.
      reflexivity.
  Defined.

  Definition cAssociator_inv (A B C D : 1 -Type)
    : NaturalTransformation
        (comp_functor A C D o (1, comp_functor A B C)
                      o assoc_prod (maps C D) (maps B C) (maps A B))
        (comp_functor A B D o (comp_functor B C D, 1)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros [[f₁ f₂] f₃] ; cbn in *.
      reflexivity.
    + intros [[f₁ f₂] f₃] [[g₁ g₂] g₃] [[h₁ h₂] h₃] ; cbn in *.
      induction h₁, h₂, h₃ ; cbn.
      reflexivity.
  Defined.

  Global Instance cAssociator_iso (A B C D : 1 -Type)
    : @IsIsomorphism ((maps C D * maps B C) * maps A B
                      -> maps A D)
                     _ _ (cAssociator A B C D).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply cAssociator_inv.
    - cbn.
      apply path_natural_transformation.
      intros [[f₁ f₂] f₃] ; cbn in *.
      reflexivity.
    - cbn.
      apply path_natural_transformation.
      intros [[f₁ f₂] f₃] ; cbn in *.
      reflexivity.
  Defined.

  Definition one_types : BiCategory.
  Proof.
    simple refine {|Obj := 1 -Type ;
                    Hom := maps ;
                    id_m := fun _ => idmap ;
                    c_m := comp_functor ;
                    un_l := cUnitor_l ;
                    un_r := cUnitor_r ;
                    assoc := cAssociator|}.
    - intros A B C g f ; cbn.
      reflexivity.
    - intros A B C D E k h g f ; cbn.
      reflexivity.
  Defined.

  Definition one_types_21 : is_21 one_types.
  Proof.
    intros X Y ; cbn.
    apply _.
  Defined.
End OneTypesBiCategory.