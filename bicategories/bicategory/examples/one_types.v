Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     general_category bicategory.bicategory.

Section OneTypesBiCategory.
  Context `{Univalence}.

  Definition maps (A B : 1 -Type) : PreCategory.
  Proof.
    simple refine (@Build_PreCategory (A -> B) (fun f g => f = g) _ _ _ _ _ _).
    - reflexivity.
    - intros ? ? ? p q ; exact (q @ p).
    - cbn ; intros.
      apply concat_p_pp.
    - cbn ; intros.
      apply concat_p1.
    - cbn ; intros.
      apply concat_1p.
  Defined.

  Definition maps_cat (A B : 1 -Type) : IsCategory (maps A B).
  Proof.
    intros f g ; cbn in *.
    simple refine (isequiv_adjointify _ _ _ _).
    - intros α.
      apply α.
    - intros α.
      apply path_isomorphic.
      destruct α as [α αiso].
      induction α ; cbn in *.
      reflexivity.
    - intros p ; induction p.
      reflexivity.
  Defined.

  Definition comp_functor (A B C : 1 -Type)
    : Functor (maps B C * maps A B) (maps A C).
  Proof.
    simple refine (Build_Functor _ _ _ _ _ _).
    - exact (fun f => (fst f) o (snd f)).
    - intros [f₁ f₂] [g₁ g₂] [h₁ h₂] ; cbn in *.
      exact (ap (fun z => z o f₂) h₁ @ ap (fun z => g₁ o z) h₂).
    - intros [f₁ f₂] [g₁ g₂] [h₁ h₂] [p₁ p₂] [q₁ q₂] ; cbn in *.
      induction p₁, p₂, q₁, q₂ ; cbn.
      reflexivity.
    - intros [f₁ f₂] ; cbn in *.
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