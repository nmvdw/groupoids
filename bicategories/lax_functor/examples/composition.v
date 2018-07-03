Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory
     lax_functor.lax_functor.

Section FunctorComposition.
  Context `{Univalence}
          {C D E : BiCategory}.
  Variable (G : LaxFunctor D E) (F : LaxFunctor C D).
  
  Definition lax_comp_obj : C -> E
    := G o F.

  Definition lax_comp_mor (X Y : C)
    : Functor (Hom C X Y) (Hom E (lax_comp_obj X) (lax_comp_obj Y))
    := (Fmor G o Fmor F)%functor.

  Definition lax_comp_c_m (X Y Z : C)
    : NaturalTransformation
        (c_m o (lax_comp_mor Y Z, lax_comp_mor X Y))
        (lax_comp_mor X Z o c_m).
  Proof.
    refine (_ o whisker_l (Fmor G) (Fcomp F)
              o _
              o whisker_r (Fcomp G) (Fmor F, Fmor F)
              o _)%natural_transformation.
    - apply Composition.associator_2.
    - apply Composition.associator_1.
    - refine (_ o _)%natural_transformation.
      + apply Composition.associator_2.
      + apply whisker_l.
        simple refine (Build_NaturalTransformation _ _ _ _).
        * intros [f g].
          split ; cbn.
          ** apply identity.
          ** apply identity.
        * intros [f₁ g₁] [f₂ g₂] [a₁ a₂] ; cbn.
          rewrite !left_identity, !right_identity.
          reflexivity.
  Defined.

  Definition lax_comp_id (X : C)
    : morphism (Hom E (lax_comp_obj X) (lax_comp_obj X))
               (id_m (lax_comp_obj X))
               ((Fmor G) _0 ((Fmor F) _0 (id_m X)))%object
    := ((morphism_of (Fmor G) (Fid F X)) o Fid G (F X))%morphism.

  Definition lax_comp_d : LaxFunctor_d C E
    := Build_LaxFunctor_d lax_comp_obj lax_comp_mor lax_comp_c_m lax_comp_id.

  Definition comp_is_lax : is_lax lax_comp_d.
  Proof.
    repeat split.
    - intros a b p ; cbn in *.
      rewrite !identity_of, !left_identity, !right_identity.
      rewrite !Fun_r, !composition_of.
      rewrite !associativity.
      repeat f_ap.
      unfold hcomp.
      pose (commutes (@Fcomp _ _ _ G (F a) (F a) (F b))) as p0.
      cbn in p0.
      specialize (p0 (Fmor F p,id_m (F a)) (Fmor F p,(Fmor F) (id_m a)) (1%morphism,Fid F a)).
      rewrite <- !associativity.
      rewrite <- p0.
      rewrite !associativity.
      rewrite <- composition_of.
      cbn.
      rewrite identity_of, left_identity.
      reflexivity.
    - intros a b p ; cbn in *.
      rewrite !identity_of, !left_identity, !right_identity.
      rewrite !Fun_l, !composition_of.
      rewrite !associativity.
      repeat f_ap.
      unfold hcomp.
      pose (commutes (@Fcomp _ _ _ G (F a) (F b) (F b))) as p0.
      cbn in p0.
      specialize (p0 (id_m (F b),Fmor F p) ((Fmor F) (id_m b),Fmor F p) (Fid F b,1%morphism)).
      rewrite <- !associativity.
      rewrite <- p0.
      rewrite !associativity.
      rewrite <- composition_of.
      cbn.
      rewrite identity_of, left_identity.
      reflexivity.
    - intros a b c d p q r ; cbn ; unfold hcomp.
      rewrite !identity_of, !left_identity, !right_identity.
      rewrite <- (left_identity _ _ _ 1).
      rewrite (composition_of
                 c_m
                 (Fmor G (Fmor F p),c_m (Fmor G (Fmor F q),Fmor G (Fmor F r)))
                 (Fmor G (Fmor F p),Fmor G (c_m (Fmor F q,Fmor F r)))
                 (Fmor G (Fmor F p),Fmor G (Fmor F (c_m(q,r))))
                 (1%morphism,_)
                 (1%morphism,((Fmor G) _1 (Core.components_of (Fcomp F) (q, r)))%morphism)
              ).
      rewrite <- (left_identity _ _ _ (Core.identity (Fmor G (Fmor F r)))).
      rewrite (composition_of
                 c_m
                 (c_m (Fmor G (Fmor F p),Fmor G (Fmor F q)),Fmor G (Fmor F r))
                 (Fmor G (c_m (Fmor F p,Fmor F q)),Fmor G (Fmor F r))
                 (Fmor G (Fmor F (c_m(p,q))),Fmor G (Fmor F r))
                 (_,1%morphism)
                 (_,1%morphism)
              ).
      rewrite (ap (fun z => z o _)%morphism (associativity _ _ _ _ _ _ _ _)).
      rewrite (ap (fun z => _ o z o _)%morphism (associativity _ _ _ _ _ _ _ _)^).
      pose (commutes (@Fcomp _ _ _ G (F a) (F c) (F d))) as p1.
      specialize (p1 (Fmor F p,Fmor F q · Fmor F r)
                     (Fmor F p,Fmor F (q · r))
                     (1%morphism,Core.components_of (Fcomp F) (q, r)))%bicategory.
      cbn in p1.
      rewrite identity_of in p1.
      rewrite p1. clear p1.
      pose (commutes (@Fcomp _ _ _ G (F a) (F b) (F d))) as p1.
      specialize (p1 (Fmor F p · Fmor F q,Fmor F r)
                     (Fmor F (p · q),Fmor F r)
                     (Core.components_of (Fcomp F) (p, q),1%morphism))%bicategory.
      cbn in p1.
      rewrite identity_of in p1.
      rewrite !associativity.
      rewrite !(ap (fun z => _ o (_ o z))%morphism (associativity _ _ _ _ _ _ _ _)^).
      rewrite p1. clear p1.
      rewrite Fassoc.
      rewrite <- !associativity.
      rewrite <- !composition_of.
      repeat f_ap.
      rewrite Fassoc.
      reflexivity.
  Qed.

  Definition lax_comp : LaxFunctor C E
    := Build_LaxFunctor lax_comp_d comp_is_lax.
  
  Global Instance lax_comp_id_iso
         (X : C)
         `{@is_pseudo_functor _ _ _ F} `{@is_pseudo_functor _ _ _ G}
    : IsIsomorphism (lax_comp_id X)
    := _.

  Global Instance lax_comp_c_m_iso
         (X Y Z : C)
         `{@is_pseudo_functor _ _ _ F} `{@is_pseudo_functor _ _ _ G}       
    : @IsIsomorphism (_ -> _) _ _ (lax_comp_c_m X Y Z)
    := _.

  Global Instance pseudo_comp
         `{@is_pseudo_functor _ C D F} `{@is_pseudo_functor _ D E G}
    : is_pseudo_functor lax_comp.
  Proof.
    simple refine {|Fcomp_iso := _|}.
  Defined.
End FunctorComposition.