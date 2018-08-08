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

Section LaxAssociativityInv.
  Context `{Univalence}
          {C₁ C₂ C₃ C₄ : BiCategory}.
  Variable (F₃ : LaxFunctor C₃ C₄)
           (F₂ : LaxFunctor C₂ C₃)
           (F₁ : LaxFunctor C₁ C₂).
  
  Definition lax_associativity_inv_d
    : LaxTransformation_d (lax_comp F₃ (lax_comp F₂ F₁)) (lax_comp (lax_comp F₃ F₂) F₁).
  Proof.
    simple refine (Build_LaxTransformation_d _ _).
    - intros X.
      apply id_m.
    - intros X Y ; cbn.
      unfold precomp, postcomp, lax_comp_mor, lax_comp_obj ; cbn.
      unfold lax_comp_mor ; cbn.
      refine ((whisker_l
                _
                _)
                o
                (whisker_r
                   (inverse (un_l _ _) o un_r _ _)%natural_transformation
                   _)
             )%natural_transformation.
      apply Composition.associator_1.
  Defined.

  Definition is_lax_associativity_inv_d
    : is_lax_transformation lax_associativity_inv_d.
  Proof.
    split.
    - intros X ; cbn.
      unfold lax_comp_id, lax_comp_obj, hcomp ; cbn.
      unfold lax_comp_obj, lax_comp_id ; cbn.
      rewrite !identity_of, !left_identity.
      pose (commutes (un_r (F₃ (F₂ (F₁ X))) (F₃ (F₂ (F₁ X))))).
      cbn in p.
      rewrite !associativity.
      rewrite p ; clear p.
      rewrite <- !associativity.
      rewrite un_l_is_un_r.
      f_ap.
      rewrite !associativity.
      pose (commutes (inverse (un_l (F₃ (F₂ (F₁ X))) (F₃ (F₂ (F₁ X)))))) as p.
      cbn in p.
      rewrite p.
      rewrite <- !associativity.
      rewrite !inv_un_l_is_inv_un_r.        
      rewrite <- !composition_of.
      repeat f_ap ; cbn.
    - intros X Y Z f g.
      unfold lax_comp_id, lax_comp_obj, hcomp ; cbn.
      rewrite !identity_of, !left_identity, !right_identity.
      pose (commutes (un_r (F₃ (F₂ (F₁ X))) (F₃ (F₂ (F₁ Z))))).
      cbn in p.
      rewrite !associativity.
      rewrite p ; clear p.
      rewrite <- !associativity.
      pose (commutes (inverse (un_l (F₃ (F₂ (F₁ X))) (F₃ (F₂ (F₁ Z)))))) as p.
      cbn in p.
      rewrite !p ; clear p.
      symmetry.
      rewrite <- (left_identity _ _ _ 1)%morphism.
      rewrite !associativity.
      refine (ap (fun z => z o _)%morphism _ @ _).
      {
        exact (@composition_of
                 _
                 _
                 (@c_m _ C₄ (F₃(F₂(F₁ X))) (F₃(F₂(F₁ Z))) (F₃(F₂(F₁ Z))))
                 (id_m _,c_m (Fmor F₃ (Fmor F₂ (Fmor F₁ g)),Fmor F₃ (Fmor F₂ (Fmor F₁ f))))
                 (_,Fmor F₃ (c_m (Fmor F₂ (Fmor F₁ g),Fmor F₂ (Fmor F₁ f))))
                 (_,Fmor F₃ (Fmor F₂ (Fmor F₁ (c_m (g,f)))))
                 (1,Fcomp F₃ (Fmor F₂ (Fmor F₁ g), Fmor F₂ (Fmor F₁ f)))
                 (1,Fmor F₃ _1 (Fmor F₂ _1 (Fcomp F₁ (g,f)) o Fcomp F₂ (Fmor F₁ g, Fmor F₁ f)))
              )%morphism.
      }
      rewrite !associativity.
      repeat f_ap.
      rewrite !un_r_assoc.
      rewrite <- !associativity.
      repeat f_ap.
      rewrite !associativity.
      rewrite <- (left_identity _ _ _ 1)%morphism.
      (*pose (@composition_of
              _ _
              (@c_m _ C₄ _ _ _)
              (c_m (Fmor F g,id_m (F Y)),Fmor F f)
              (_,_)
              (c_m (id_m (F Z),Fmor F g),_)
              (un_r (F₃(F₂(F₁ Y))) (F₃(F₂(F₁ Z))) (Fmor F₃ (Fmor F₂ (Fmor F₁ g))),1)
              (inverse (un_l _ _) (Fmor F₃ (Fmor F₂ (Fmor F₁ g))),1)
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
      reflexivity.*)
  Admitted.

  Definition lax_associativity_inv
    : LaxTransformation (lax_comp F₃ (lax_comp F₂ F₁)) (lax_comp (lax_comp F₃ F₂) F₁)
    := Build_LaxTransformation lax_associativity_inv_d is_lax_associativity_inv_d.

  Global Instance lax_associativity_inv_pseudo
    : is_pseudo_transformation lax_associativity_inv.
  Proof.
    simple refine {| laxnaturality_of_iso := _ |}.
  Defined.
End LaxAssociativityInv.