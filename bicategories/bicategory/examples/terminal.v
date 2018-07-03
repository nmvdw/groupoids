Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     general_category bicategory.bicategory.

Section TerminalBiCategory.
  Context `{Univalence}.

  Definition terminal_cat : PreCategory.
  Proof.
    simple refine (@Build_PreCategory
                     Unit
                     (fun _ _ => Unit)
                     (fun _ => tt)
                     (fun _ _ _ _ _ => tt)
                     _ _ _ _)
    ; intros ; apply path_ishprop.
  Defined.

  Definition constant (C : PreCategory) : Functor C terminal_cat.
  Proof.
    simple refine (Build_Functor _ _ _ _ _ _) ; simpl.
    - exact (fun _ => tt).
    - exact (fun _ _ _ => tt).
    - reflexivity.
    - reflexivity.
  Defined.

  Definition maps (x y : Unit) : PreCategory
    := terminal_cat.
        
  Definition comp_functor (x y z : Unit)
    : Functor (maps y z * maps x y) (maps x z)
    := constant (maps y z * maps x y).

  Definition tUnitor_l (x y : Unit)
    : NaturalTransformation
        (comp_functor x y y o (@const_functor _ (maps y y) tt * 1))
        1.
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _) ; reflexivity.
  Defined.

  Definition tUnitor_l_inv (x y : Unit)
    : NaturalTransformation
        1
        (comp_functor x y y o (@const_functor (maps x y) (maps y y) tt * 1)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _) ; reflexivity.
  Defined.

  Global Instance tUnitor_l_iso (x y : Unit)
    : @IsIsomorphism (_ -> _) _ _ (tUnitor_l x y).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply tUnitor_l_inv.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      reflexivity.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      reflexivity.
  Defined.

  Definition tUnitor_r (x y : Unit)
    : NaturalTransformation
        (comp_functor x x y o (1 * @const_functor (maps x y) (maps x x) tt))
        1.
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _) ; reflexivity.
  Defined.

  Definition tUnitor_r_inv (x y : Unit)
    : NaturalTransformation
        1
        (comp_functor x x y o (1 * @const_functor (maps x y) (maps x x) tt)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _) ; reflexivity.
  Defined.

  Global Instance tUnitor_r_iso (x y : Unit)
    : @IsIsomorphism (_ -> _) _ _ (tUnitor_r x y).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply tUnitor_r_inv.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      reflexivity.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      reflexivity.
  Defined.

  Definition tAssociator (a b c d : Unit)
    : NaturalTransformation
        (comp_functor a b d o (comp_functor b c d, 1))
        (comp_functor a c d o (1, comp_functor a b c)
                        o assoc_prod (maps c d) (maps b c) (maps a b)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _) ; reflexivity.
  Defined.

  Definition tAssociator_inv (a b c d : Unit)
    : NaturalTransformation
        (comp_functor a c d o (1, comp_functor a b c)
                      o assoc_prod (maps c d) (maps b c) (maps a b))
        (comp_functor a b d o (comp_functor b c d, 1)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _) ; reflexivity.
  Defined.

  Global Instance tAssociator_iso (a b c d : Unit)
    : @IsIsomorphism (_ -> _) _ _ (tAssociator a b c d).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply tAssociator_inv.
    - cbn.
      apply path_natural_transformation.
      intro ; reflexivity.
    - cbn.
      apply path_natural_transformation.
      intro ; reflexivity.
  Defined.

  Definition terminal_bicategory : BiCategory.
  Proof.
    simple refine (Build_BiCategory Unit
                                    maps
                                    (fun _ => tt)
                                    comp_functor
                                    tUnitor_l
                                    tUnitor_r
                                    tAssociator
                                    _
                                    _)
    ; reflexivity.
  Defined.
End TerminalBiCategory.
