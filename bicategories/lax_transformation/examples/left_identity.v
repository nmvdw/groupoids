Require Import HoTT.
From GR.bicategories Require Import
     bicategory.bicategory
     bicategory.bicategory_laws
     lax_functor.lax_functor
     lax_functor.examples.composition
     lax_functor.examples.identity
     lax_transformation.lax_transformation
     lax_transformation.examples.identity
     general_category.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.

Section LaxLeftIdentity.
  Context `{Univalence}
          {C D : BiCategory}.
  Variable (F : LaxFunctor C D).
  
  Definition lax_left_identity_d
    : LaxTransformation_d (lax_comp (lax_id_functor D) F) F.
  Proof.
    simple refine (Build_LaxTransformation_d _ _).
    - intros X.
      cbn ; unfold lax_comp_obj, lax_id_functor ; cbn.
      apply id_m.
    - intros X Y ; cbn.
      unfold precomp, postcomp, lax_comp_mor, lax_id_functor ; cbn.
      refine ((whisker_l
                _
                _)
                o
                (whisker_r
                   (inverse (un_l (F X) (F Y)) o un_r (F X) (F Y))%natural_transformation
                   (Fmor F))
             )%natural_transformation.
      apply Composition.right_identity_natural_transformation_2.
  Defined.

  Definition is_lax_lax_left_d
    : is_lax_transformation lax_left_identity_d.
  Proof.
    split.
    - intros X ; cbn.
      unfold lax_comp_id, lax_comp_obj, hcomp ; cbn.
      pose (commutes (un_r (F X) (F X))).
      cbn in p.
      rewrite !associativity.
      rewrite p ; clear p.
      rewrite <- !associativity.
      rewrite !identity_of, !right_identity, !left_identity.
      pose (commutes (inverse (un_l (F X) (F X)))) as p.
      cbn in p.
      rewrite p ; clear p.
      repeat f_ap.
      + rewrite inv_un_l_is_inv_un_r.
        reflexivity.
      + apply un_l_is_un_r.
    - intros X Y Z f g ; cbn.
      unfold lax_comp_id, lax_comp_obj, hcomp ; cbn.
      pose (commutes (un_r (F X) (F Z))).
      cbn in p.
      rewrite !associativity.
      rewrite p ; clear p.
      rewrite <- !associativity.
      rewrite !identity_of, !left_identity, !right_identity.
      pose (commutes (inverse (un_l (F X) (F Z)))) as p.
      cbn in p.
      rewrite !p ; clear p.
      rewrite !associativity.
      repeat f_ap.
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

  Definition lax_left_identity
    : LaxTransformation (lax_comp (lax_id_functor D) F) F
    := Build_LaxTransformation lax_left_identity_d is_lax_lax_left_d.

  Global Instance left_identity_pseudo
    : is_pseudo_transformation lax_left_identity.
  Proof.
    simple refine {| laxnaturality_of_iso := _ |}.
  Defined.
End LaxLeftIdentity.