Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory
     bicategory.bicategory_laws
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     general_category.

Section IdentityTransformation.
  Context `{Univalence}
          {C D : BiCategory}.
  Variable (F : LaxFunctor C D).
  
  Definition identity_component (X : C)
    : Hom D (F X) (F X)
    := id_m (F X).

  Definition identity_naturality (X Y : C)
    : NaturalTransformation
        (c_m o (1 * const_functor (id_m (F X))) o Fmor F)
        (c_m o (const_functor (id_m (F Y)) * 1) o Fmor F)
    := whisker_r
         (inverse (un_l (F X) (F Y)) o un_r (F X) (F Y))%natural_transformation
         (Fmor F).

  Global Instance identity_naturality_pseudo (X Y : C)
    : @IsIsomorphism (_ -> _) _ _ (identity_naturality X Y)
    := _.

  Definition identity_transformation_d
    : LaxTransformation_d F F
    := Build_LaxTransformation_d identity_component identity_naturality.

  Definition is_lax_identity_transformation
    : is_lax_transformation identity_transformation_d.
  Proof.
    split.
    - intros X ; cbn.
      unfold hcomp.
      pose (commutes (un_r (F X) (F X))).
      cbn in p.
      rewrite !associativity.
      rewrite p ; clear p.
      rewrite <- !associativity.
      pose (commutes (inverse (un_l (F X) (F X)))) as p.
      cbn in p.
      rewrite p ; clear p.
      repeat f_ap.
      + rewrite inv_un_l_is_inv_un_r.
        reflexivity.
      + apply un_l_is_un_r.
    - intros X Y Z f g ; cbn.
      unfold hcomp.
      pose (commutes (un_r (F X) (F Z))).
      cbn in p.
      rewrite !associativity.
      rewrite p ; clear p.
      rewrite <- !associativity.
      pose (commutes (inverse (un_l (F X) (F Z)))) as p.
      cbn in p.
      rewrite !p ; clear p.
      rewrite !associativity.
      f_ap.
      rewrite !un_r_assoc.
      rewrite <- !associativity.
      f_ap.
      symmetry.
      rewrite <- (left_identity _ _ _ 1)%morphism.
      pose (@composition_of _ _
                            (@c_m _ D (F X) (F Y) (F Z))
                            (c_m (Fmor F g,id_m (F Y)),Fmor F f)
                            (Fmor F g,_)
                            (c_m (id_m (F Z),Fmor F g),_)
                            (un_r (F Y) (F Z) (Fmor F g),1)
                            (inverse (un_l (F Y) (F Z)) (Fmor F g),1)
           )%morphism.
      cbn in p.
      rewrite !p ; clear p.
      rewrite triangle_r.
      rewrite !associativity.
      rewrite <- (associativity _ _ _ _ _ _ _ (assoc ((Fmor F) g, id_m (F Y), (Fmor F) f))).
      rewrite right_inverse, left_identity.
      rewrite <- composition_of ; cbn.
      rewrite left_identity.
      rewrite <- !associativity.
      pose (@right_inverse _ _ _ (un_l (F X) (F Y) (Fmor F f)) _) as p.
      cbn in p.
      rewrite p ; clear p.
      rewrite left_identity.
      repeat f_ap.
      rewrite <- inverse_id.
      pose (@inverse_of _
                        _
                        c_m
                        (c_m (id_m (F Z),Fmor F g),Fmor F f)
                        (Fmor F g,Fmor F f)
                        (un_l (F Y) (F Z) (Fmor F g),1) _)%morphism.
      rewrite p ; clear p.
      apply Morphisms.iso_moveR_pV.
      pose (un_l_assoc (F X) (F Y) (F Z) (Fmor F g) (Fmor F f)).
      rewrite p ; clear p.
      refine ((left_identity _ _ _ _)^ @ _).
      rewrite <- associativity.
      f_ap.
      pose (@left_inverse _ _ _ (un_l (F X) (F Z) (c_m (Fmor F g,Fmor F f))) _).
      rewrite p.
      reflexivity.
  Qed.

  Definition identity_transformation
    : LaxTransformation F F
    := Build_LaxTransformation identity_transformation_d is_lax_identity_transformation.

  Global Instance identity_pseudo
    : is_pseudo_transformation identity_transformation.
  Proof.
    simple refine {| laxnaturality_of_iso := _ |}.
  Defined.
End IdentityTransformation.