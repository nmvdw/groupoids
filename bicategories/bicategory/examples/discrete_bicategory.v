Require Import HoTT.
From HoTT.Categories Require Import
     Category Category.Prod NaturalTransformation FunctorCategory DiscreteCategory.
From GR.bicategories Require Import
     general_category bicategory.bicategory.

Section DiscreteBiCategory.
  Context `{Univalence}.
  Variable (C : PreCategory).

  Definition d_obj : Type := C.
  
  Definition d_hom : d_obj -> d_obj -> PreCategory
    := fun x y => discrete_category (morphism C x y).
  
  Definition d_id_m : forall (x : d_obj), d_hom x x
    := fun x => 1%morphism.

  Definition d_c_m : forall (x y z : d_obj), Functor (d_hom y z * d_hom x y) (d_hom x z).
  Proof.
    intros x y z.
    simple refine (Build_Functor _ _ _ _ _ _) ; simpl.
    - intros [g f].
      exact (g o f)%morphism.
    - intros [g₁ f₁] [g₂ f₂] [α₁ α₂] ; cbn in *.
      exact (ap (fun z => z o f₁) α₁ @ ap (fun z => g₂ o z) α₂)%morphism.
    - intros [g₁ f₁] [g₂ f₂] [g₃ f₃] [α₁ β₁] [α₂ β₂] ; cbn in *.
      induction α₁, β₁, α₂, β₂ ; cbn.
      reflexivity.
    - reflexivity.
  Defined.

  Definition dUnitor_l (x y : d_obj)
    : NaturalTransformation
        (d_c_m x y y o (@const_functor _ (d_hom y y) (d_id_m y) * 1))
        1.
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros ; cbn.
      apply left_identity.
    - intros ? ? p.
      induction p ; cbn.
      exact (concat_1p _ @ (concat_p1 _)^).
  Defined.

  Definition dUnitor_l_inv (x y : d_obj)
    : NaturalTransformation
        1
        (d_c_m x y y o (@const_functor _ (d_hom y y) (d_id_m y) * 1)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros ; cbn.
      exact (left_identity _ _ _ _)^.
    + intros ? ? p ; cbn.
      induction p.
      exact (concat_1p _ @ (concat_p1 _)^).
  Defined.

  Global Instance cdnitor_l_iso (x y : d_obj)
    : @IsIsomorphism (_ -> _) _ _ (dUnitor_l x y).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply dUnitor_l_inv.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      apply concat_pV.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      apply concat_Vp.
  Defined.

  Definition dUnitor_r (x y : d_obj)
    : NaturalTransformation
        (d_c_m x x y o (1 * @const_functor (d_hom x y) (d_hom x x) (d_id_m x)))
        1.
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros ; cbn.
      apply right_identity.
    + intros ? ? p ; cbn.
      induction p.
      exact (concat_1p _ @ (concat_p1 _)^).
  Defined.

  Definition dUnitor_r_inv (x y : d_obj)
    : NaturalTransformation
        1
        (d_c_m x x y o (1 * @const_functor (d_hom x y) (d_hom x x) (d_id_m x))).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros ; cbn.
      exact (right_identity _ _ _ _)^.
    + intros ? ? p ; cbn.
      induction p.
      exact (concat_1p _ @ (concat_p1 _)^).
  Defined.

  Global Instance dUnitor_r_iso (x y : d_obj)
    : @IsIsomorphism (_ -> _) _ _ (dUnitor_r x y).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply dUnitor_r_inv.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      apply concat_pV.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      apply concat_Vp.
  Defined.

  Definition dAssociator (w x y z : d_obj)
    : NaturalTransformation
        (d_c_m w x z o (d_c_m x y z, 1))
        (d_c_m w y z o (1, d_c_m w x y)
                        o assoc_prod (d_hom y z) (d_hom x y) (d_hom w x)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros [[f₁ f₂] f₃] ; cbn in *.
      apply associativity.
    + intros [[f₁ f₂] f₃] [[g₁ g₂] g₃] [[h₁ h₂] h₃] ; cbn in *.
      induction h₁, h₂, h₃ ; cbn.
      exact (concat_1p _ @ (concat_p1 _)^).
  Defined.

  Definition dAssociator_inv (w x y z : d_obj)
    : NaturalTransformation
        (d_c_m w y z o (1, d_c_m w x y)
               o assoc_prod (d_hom y z) (d_hom x y) (d_hom w x))
        (d_c_m w x z o (d_c_m x y z, 1)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros [[f₁ f₂] f₃] ; cbn in *.
      apply (associativity _ _ _ _ _ _ _ _)^.
    + intros [[f₁ f₂] f₃] [[g₁ g₂] g₃] [[h₁ h₂] h₃] ; cbn in *.
      induction h₁, h₂, h₃ ; cbn.
      exact (concat_1p _ @ (concat_p1 _)^).
  Defined.

  Global Instance dAssociator_iso (w x y z : d_obj)
    : @IsIsomorphism (_ -> _) _ _ (dAssociator w x y z).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply dAssociator_inv.
    - cbn.
      apply path_natural_transformation.
      intros [[f₁ f₂] f₃] ; cbn in *.
      apply concat_pV.
    - cbn.
      apply path_natural_transformation.
      intros [[f₁ f₂] f₃] ; cbn in *.
      apply concat_Vp.
  Defined.

  Definition discrete_bicategory : BiCategory.
  Proof.
    simple refine (Build_BiCategory d_obj
                                    d_hom
                                    d_id_m
                                    d_c_m
                                    dUnitor_l
                                    dUnitor_r
                                    dAssociator
                                    _
                                    _).
    - intros ; apply path_ishprop.
    - intros ; apply path_ishprop.
  Defined.
End DiscreteBiCategory.