Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     general_category bicategory.bicategory.

Section TwoTypeBiGroupoid.
  Context `{Univalence}.

  Variable (X : Type).
  Context `{IsTrunc 2 X}.

  Definition oneto (Z : Type) `{IsTrunc 1 Z} : PreCategory
    := Core.groupoid_category Z.

  Definition oneto_cat (x y : X) : IsCategory (oneto (x = y)).
  Proof.
    intros p q ; cbn in *.
    simple refine (isequiv_adjointify _ _ _ _).
    - intros α.
      apply α.
    - intros α. simpl.
      apply path_isomorphic.
      destruct α as [α αiso].
      induction α ; cbn in *.
      reflexivity.
    - intros r ; induction r.
      reflexivity.
  Defined.

  Definition concat_functor (x y z : X)
    : Functor (oneto (y = z) * oneto (x = y)) (oneto (x = z)).
  Proof.
    simple refine (Build_Functor _ _ _ _ _ _).
    - exact (fun p => snd p @ fst p).
    - intros [p₁ p₂] [q₁ q₂] [r₁ r₂] ; cbn in *.
      induction r₁, r₂ ; reflexivity.
    - intros [p₁ p₂] [q₁ q₂] [r₁ r₂] [s₁ s₂] [t₁ t₂] ; cbn in *.
      induction s₁, t₁, s₂, t₂ ; reflexivity.
    - intros [p₁ p₂] ; reflexivity.
  Defined.

  Definition pUnitor_l (x y : X)
    : NaturalTransformation
        (concat_functor x y y o (@const_functor _ (oneto (y = y)) idpath * 1))
        1.
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + exact concat_p1.
    + intros ? ? p ; induction p.
      refine (concat_1p _ @ (concat_p1 _)^).
  Defined.

  Definition pUnitor_l_inv (x y : X)
    : NaturalTransformation
        1
        (concat_functor x y y o (@const_functor _ (oneto (y = y)) idpath * 1)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + exact (fun p => (concat_p1 p)^).
    + intros ? ? p ; induction p.
      refine (concat_1p _ @ (concat_p1 _)^).
  Defined.

  Global Instance pUnitor_l_iso (x y : X)
    : @IsIsomorphism (oneto (x = y) -> oneto (x = y)) _ _ (pUnitor_l x y).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply pUnitor_l_inv.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      induction p ; reflexivity.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      induction p ; reflexivity.
  Defined.

  Definition pUnitor_r (x y : X)
    : NaturalTransformation
        (concat_functor x x y o (1 * @const_functor _ (oneto (x = x)) idpath))
        1.
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + exact (fun p => concat_1p p).
    + intros ? ? p ; induction p ; cbn.
      refine (concat_1p _ @ (concat_p1 _)^).
  Defined.

  Definition pUnitor_r_inv (x y : X)
    : NaturalTransformation
        1
        (concat_functor x x y o (1 * @const_functor _ (oneto (x = x)) idpath)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + exact (fun p => (concat_1p p)^).
    + intros ? ? p ; induction p.
      refine (concat_1p _ @ (concat_p1 _)^).
  Defined.

  Global Instance pUnitor_r_iso (x y : X)
    : @IsIsomorphism (oneto (x = y) -> oneto (x = y)) _ _ (pUnitor_r x y).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply pUnitor_r_inv.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      induction p ; reflexivity.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      induction p ; reflexivity.
  Defined.

  Definition pAssociator (w x y z : X)
    : NaturalTransformation
        (concat_functor w x z o (concat_functor x y z, 1))
        (concat_functor w y z o (1, concat_functor w x y)
                        o assoc_prod (oneto (y = z)) (oneto (x = y)) (oneto (w = x))).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros [[p₁ p₂] p₃] ; cbn in *.
      apply concat_p_pp.
    + intros [[p₁ p₂] p₃] [[q₁ q₂] q₃] [[r₁ r₂] r₃] ; cbn in *.
      induction p₁, p₂, p₃ ; cbn.
      rewrite <- r₁, <- r₂, <- r₃ ; cbn.
      reflexivity.
  Defined.

  Definition pAssociator_inv (w x y z : X)
    : NaturalTransformation
        (concat_functor w y z o (1, concat_functor w x y)
                        o assoc_prod (oneto (y = z)) (oneto (x = y)) (oneto (w = x)))
        (concat_functor w x z o (concat_functor x y z, 1)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + cbn ; intros [[p q] r].
      apply concat_pp_p.
    + intros [[p₁ p₂] p₃] [[q₁ q₂] q₃] [[r₁ r₂] r₃] ; cbn in *.
      induction p₁, p₂, p₃ ; cbn.
      rewrite <- r₁, <- r₂, <- r₃ ; cbn.
      reflexivity.
  Defined.

  Global Instance pAssociator_iso (w x y z : X)
    : @IsIsomorphism ((oneto (y = z) * oneto (x = y)) * oneto (w = x)
                      -> oneto (w = z))
                     _ _ (pAssociator w x y z).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply pAssociator_inv.
    - cbn.
      apply path_natural_transformation.
      intros [[p₁ p₂] p₃] ; cbn in *.
      induction p₁, p₂, p₃ ; reflexivity.
    - cbn.
      apply path_natural_transformation.
      intros [[p₁ p₂] p₃] ; cbn in *.
      induction p₁, p₂, p₃ ; reflexivity.
  Defined.

  Definition path_bigroupoid : BiCategory.
  Proof.
    simple refine (Build_BiCategory X
                                    (fun x y => oneto (x = y))
                                    (fun _ => idpath)
                                    concat_functor
                                    pUnitor_l
                                    pUnitor_r
                                    pAssociator
                                    _
                                    _).
    - intros x y z p q ; cbn in *.
      induction p, q ; cbn.
      reflexivity.
    - cbn ; intros v w x y z s r q p.
      induction p, q, r, s ; cbn.
      reflexivity.
  Defined.
End TwoTypeBiGroupoid.