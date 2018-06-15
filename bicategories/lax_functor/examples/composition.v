Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory
     lax_functor.lax_functor.

Definition lax_comp_obj
           `{Univalence}
           {C D E : BiCategory}
           (G : LaxFunctor D E) (F : LaxFunctor C D)
  : C -> E
  := G o F.

Definition lax_comp_mor
           `{Univalence}
           {C D E : BiCategory}
           (G : LaxFunctor D E) (F : LaxFunctor C D)
           (X Y : C)
  : Functor (Hom C X Y) (Hom E (lax_comp_obj G F X) (lax_comp_obj G F Y))
  := (Fmor G o Fmor F)%functor.

Definition lax_comp_c_m
           `{Univalence}
           {C D E : BiCategory}
           (G : LaxFunctor D E) (F : LaxFunctor C D)
           (X Y Z : C)
  : NaturalTransformation
      (c_m o (lax_comp_mor G F Y Z, lax_comp_mor G F X Y))
      (lax_comp_mor G F X Z o c_m).
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

Definition lax_comp_id
           `{Univalence}
           {C D E : BiCategory}
           (G : LaxFunctor D E) (F : LaxFunctor C D)
           (X : C)
  : morphism (Hom E (lax_comp_obj G F X) (lax_comp_obj G F X))
             (id_m (lax_comp_obj G F X))
             ((Fmor G) _0 ((Fmor F) _0 (id_m X)))%object
  := ((morphism_of (Fmor G) (Fid F X)) o Fid G (F X))%morphism.

Definition lax_comp_d
           `{Univalence}
           {C D E : BiCategory}
           (G : LaxFunctor D E) (F : LaxFunctor C D)
  : LaxFunctor_d C E.
Proof.
  simple refine {| Fobj_d := _ |}.
  - exact (lax_comp_obj G F).
  - exact (lax_comp_mor G F).
  - exact (lax_comp_c_m G F).
  - exact (lax_comp_id G F).
Defined.

Definition comp_is_lax
           `{Univalence}
           {C D E : BiCategory}
           (G : LaxFunctor D E) (F : LaxFunctor C D)
  : is_lax (lax_comp_d G F).
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
    specialize (p1 (Fmor F p,Fmor F q ⋅ Fmor F r)
                   (Fmor F p,Fmor F (q ⋅ r))
                   (1%morphism,Core.components_of (Fcomp F) (q, r)))%bicategory.
    cbn in p1.
    rewrite identity_of in p1.
    rewrite p1. clear p1.
    pose (commutes (@Fcomp _ _ _ G (F a) (F b) (F d))) as p1.
    specialize (p1 (Fmor F p ⋅ Fmor F q,Fmor F r)
                   (Fmor F (p ⋅ q),Fmor F r)
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

Definition lax_comp
           `{Univalence}
           {C D E : BiCategory}
           (G : LaxFunctor D E) (F : LaxFunctor C D)
  : LaxFunctor C E
  := (lax_comp_d G F;comp_is_lax G F).

Global Instance lax_comp_id_iso
       `{Univalence}
       {C D E : BiCategory}
       (G : LaxFunctor D E) (F : LaxFunctor C D)
       (X : C)
       `{@is_pseudo_functor _ C D F} `{@is_pseudo_functor _ D E G}
  : IsIsomorphism (lax_comp_id G F X).
Proof.
  unfold lax_comp_id.
  apply Category.isisomorphism_compose.
  - apply iso_functor.
    apply Fid_iso.
  - apply Fid_iso.
Defined.

Global Instance lax_comp_c_m_iso
           `{Univalence}
           {C D E : BiCategory}
           (G : LaxFunctor D E) (F : LaxFunctor C D)
           (X Y Z : C)
           `{@is_pseudo_functor _ C D F} `{@is_pseudo_functor _ D E G}       
  : @IsIsomorphism (_ -> _) _ _ (lax_comp_c_m G F X Y Z).
Proof.
  unfold lax_comp_c_m ; simpl.
  repeat (apply Category.isisomorphism_compose).
  - apply _.
  - apply iso_whisker_l.
    apply Fcomp_iso.
  - apply _.
  - apply iso_whisker_r.
    apply Fcomp_iso.
  - apply _.
  - apply iso_whisker_l ; simpl.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    + simple refine (Build_NaturalTransformation _ _ _ _).
      * intros [g f] ; simpl.
        split ; apply identity.
      * intros [g₁ f₁] [g₂ f₂] [α β] ; simpl.
        rewrite !left_identity, !right_identity.
        reflexivity.
    + apply path_natural_transformation.
      intros [g f] ; simpl.
      rewrite left_identity, right_identity.
      reflexivity.
    + apply path_natural_transformation.
      intros [g f] ; simpl.
      rewrite left_identity, right_identity.
      reflexivity.
Defined.

Global Instance pseudo_comp
       `{Univalence}
       {C D E : BiCategory}
       (G : LaxFunctor D E) (F : LaxFunctor C D)
       `{@is_pseudo_functor _ C D F} `{@is_pseudo_functor _ D E G}
  : is_pseudo_functor (lax_comp G F).
Proof.
  simple refine {|Fcomp_iso := _|}.
Defined.