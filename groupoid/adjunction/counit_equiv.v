Require Import HoTT.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory
     bicategory.examples.one_types
     bicategory.equivalence
     bicategory.adjoint
     lax_functor.lax_functor
     lax_functor.examples.identity
     lax_functor.examples.composition
     lax_transformation.lax_transformation
     lax_transformation.transformation_category
     lax_transformation.examples.identity
     lax_transformation.examples.composition
     modification.modification
     modification.examples.identity
     modification.examples.composition.
From GR.groupoid Require Import
     groupoid_quotient.gquot
     groupoid_quotient.gquot_functor
     groupoid_quotient.gquot_principles
     grpd_bicategory.grpd_bicategory
     path_groupoid.path_groupoid
     adjunction.counit
     adjunction.counit_inv.
From GR.basics Require Import
     general.

Definition todo A : A.
Admitted.

Definition inverse_assoc_one_type
           `{Univalence}
           (X₁ X₂ X₃ X₄ : 1 -Type)
  : inverse (@assoc _ one_types X₁ X₂ X₃ X₄)
    =
    cAssociator_inv _ _ _ _.
Proof.
  apply path_natural_transformation.
  intros [[f₁ f₂] f₃].
  apply iso_moveR_V1 ; cbn.
  reflexivity.
Defined.

Definition inverse_un_l_one_type
           `{Univalence}
           (X Y : 1 -Type)
  : inverse (@un_l _ one_types X Y)
    =
    cUnitor_l_inv _ _.
Proof.
  apply path_natural_transformation.
  intros f.
  apply iso_moveR_V1 ; cbn.
  reflexivity.
Defined.

Section CounitEquivalence.
  Context `{Univalence}.

  Definition counit_retr_map (A : 1 -Type)
    : two_cell (laxcomponent_of (compose counit_gq counit_inv) A)
               (laxcomponent_of (identity_transformation
                                   (lax_comp gquot_functor path_groupoid_functor)) A).
  Proof.
    unfold identity_transformation, compose, counit_gq, counit_inv ; cbn.
    funext x ; revert x.
    simple refine (gquot_ind_set _ _ _ _).
    - intros a ; simpl.
      reflexivity.
    - intros a₁ a₂ g ; simpl.
      apply map_path_over.
      induction g ; simpl.
      refine (whisker_square idpath
                             _
                             ((ap_idmap _)^)
                             idpath
                             _).
      + exact (ap _ (ge _ _))^.
      + apply path_to_square ; simpl.
        refine ((ge _ _)^ @ (concat_1p _)^).
  Defined.

  Opaque gquot_functor_rd_map.

  Definition counit_retr_naturality (A B : 1 -Type) (f : A -> B)
    : (((laxnaturality_of
           (identity_transformation
              (lax_comp gquot_functor path_groupoid_functor))) f)
         o (hcomp (counit_retr_map A) 1))%morphism
      =
      (hcomp 1 (counit_retr_map B)
           o
           (laxnaturality_of (compose counit_gq counit_inv)) f)%morphism.
  Proof.
    cbn -[inverse].
    rewrite !inverse_assoc_one_type.
    rewrite !concat_1p, !concat_p1.
    simpl.
    rewrite !ap_precompose.
    rewrite !ap_postcompose.
    rewrite <- path_forall_pp.
    f_ap.
    funext x ; revert x.
    simple refine (gquot_ind_prop _ _ _).
    reflexivity.
  Qed.

  Definition counit_retr
    : modification (compose counit_gq counit_inv) (identity_transformation _).
  Proof.
    simple refine (Build_Modification _ _).
    - exact counit_retr_map.
    - exact counit_retr_naturality.
  Defined.

  Definition retr_inv_map (A : 1 -Type)
    : two_cell
        (laxcomponent_of (identity_transformation
                            (lax_comp gquot_functor path_groupoid_functor)) A)
        (laxcomponent_of (compose counit_gq counit_inv) A).
  Proof.
    funext x ; revert x ; cbn.
    simple refine (gquot_ind_set _ _ _ _).
    - reflexivity.
    - intros a₁ a₂ g ; cbn.
      induction g.
      apply map_path_over.
      refine (whisker_square idpath
                             ((ap_idmap _)^)
                             _
                             idpath
                             _).
      + refine (_ @ (ap_compose _ _ _)^).
        exact (ap (ap (counit_inv_map A)) (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _)^).
      + apply path_to_square ; simpl.
        exact (concat_p1 _ @ ge _ _).
  Defined.

  
  Definition counit_retr_inv_naturality (A B : 1 -Type) (f : A -> B)
    : (((laxnaturality_of (compose counit_gq counit_inv)) f)
         o hcomp (retr_inv_map A) 1)%morphism
      =
      ((hcomp 1 (retr_inv_map B))
         o (laxnaturality_of
              (identity_transformation
                 (lax_comp gquot_functor path_groupoid_functor))) f)%morphism.
  Proof.
    unfold hcomp, retr_inv_map.
    cbn -[inverse counit_gq counit_inv].
    rewrite !inverse_assoc_one_type ; simpl.
    rewrite !concat_1p, !concat_p1.
    rewrite !ap_precompose.
    rewrite !ap_postcompose.
    rewrite <- path_forall_pp.
    f_ap.
    funext x ; revert x.
    simple refine (gquot_ind_prop _ _ _).
    reflexivity.
  Qed.

  Definition counit_retr_inv
    : modification (identity_transformation _) (compose counit_gq counit_inv).
  Proof.
    simple refine (Build_Modification _ _).
    - exact retr_inv_map.
    - exact counit_retr_inv_naturality.
  Defined.

  Definition retr_retr_inv
    : comp_modification counit_retr counit_retr_inv = id_modification _.
  Proof.
    apply path_modification ; cbn.
    funext A.
    unfold retr_inv_map, counit_retr_map.
    rewrite <- path_forall_pp.
    rewrite <- path_forall_1.
    f_ap.
    funext x ; revert x ; simpl.
    simple refine (gquot_ind_prop _ _ _).
    reflexivity.
  Qed.

  Definition retr_inv_retr
    : comp_modification counit_retr_inv counit_retr = id_modification _.
  Proof.
    apply path_modification ; cbn.
    funext A.
    unfold retr_inv_map, counit_retr_map.
    rewrite <- path_forall_pp.
    rewrite <- path_forall_1.
    f_ap.
    funext x ; revert x ; simpl.
    simple refine (gquot_ind_prop _ _ _).
    reflexivity.
  Qed.

  Global Instance counit_retr_isomorphism
    : @IsIsomorphism (transformation_category _ _) _ _ counit_retr.
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - exact counit_retr_inv.
    - exact retr_inv_retr.
    - exact retr_retr_inv.
  Defined.

  Definition counit_sect_naturality (A B : 1 -Type)
    : identity_naturality (lax_id_functor one_types) A B
      =
      compose_naturality counit_inv counit_gq A B.
  Proof.
    apply path_natural_transformation.
    intros g.
    cbn -[inverse counit_inv counit_gq gquot_functor_rd_map].
    rewrite !inverse_assoc_one_type.
    rewrite !inverse_un_l_one_type.
    rewrite !concat_1p, !concat_p1.
    rewrite !ap_postcompose.
    simpl.
    rewrite <- path_forall_1.
    reflexivity.
  Qed.

  Definition counit_sect
    : modification (compose counit_inv counit_gq) (identity_transformation _).
  Proof.
    simple refine (Build_Modification _ _).
    - reflexivity.
    - intros A B f.
      unfold bc_whisker_r, bc_whisker_l.
      rewrite !identity_of.
      rewrite right_identity, left_identity.
      f_ap ; cbn.
      apply counit_sect_naturality.
  Defined.

  Definition counit_sect_inv_naturality (A B : 1 -Type)
    : compose_naturality counit_inv counit_gq A B
      =
      identity_naturality (lax_id_functor one_types) A B.
  Proof.
    apply path_natural_transformation.
    intros g.
    cbn -[inverse counit_inv counit_gq gquot_functor_rd_map].
    rewrite !inverse_assoc_one_type.
    rewrite !inverse_un_l_one_type.
    rewrite !concat_1p, !concat_p1.
    rewrite !ap_postcompose.
    simpl.
    rewrite <- path_forall_1.
    reflexivity.
  Qed.

  Definition counit_sect_inv
    : modification (identity_transformation _) (compose counit_inv counit_gq).
  Proof.
    simple refine (Build_Modification _ _).
    - reflexivity.
    - intros A B f.
      unfold bc_whisker_r, bc_whisker_l.
      rewrite !identity_of.
      rewrite right_identity, left_identity.
      f_ap ; cbn.
      apply counit_sect_inv_naturality.
  Defined.

  Definition sect_sect_inv
    : comp_modification counit_sect counit_sect_inv = id_modification _.
  Proof.
    apply path_modification ; cbn.
    funext A.
    reflexivity.
  Defined.

  Definition sect_inv_sect
    : comp_modification counit_sect_inv counit_sect = id_modification _.
  Proof.
    apply path_modification ; cbn.
    funext A.
    reflexivity.
  Defined.

  Global Instance counit_sect_isomorphism
    : @IsIsomorphism (transformation_category _ _) _ _ counit_sect.
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - exact counit_sect_inv.
    - exact sect_inv_sect.
    - exact sect_sect_inv.
  Defined.
End CounitEquivalence.