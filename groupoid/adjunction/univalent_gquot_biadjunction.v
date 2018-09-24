Require Import HoTT.
From HoTT.Categories Require Import Category Functor NaturalTransformation.
From GR.bicategories Require Import
     general_category
     bicategories
     lax_functors
     lax_transformations
     modifications
     biadjunction.biadjunction
     biadjunction.examples.restriction.
From GR.groupoid Require Import
     groupoid_quotient.gquot
     groupoid_quotient.gquot_functor
     groupoid_quotient.gquot_principles
     grpd_bicategory.grpd_bicategory
     path_groupoid.path_groupoid
     adjunction.unit
     adjunction.unit_inv
     adjunction.counit
     adjunction.gquot_biadjunction.
From GR.basics Require Import
     general.

Section UnivalentGQuotAdjunction.
  Context `{Univalence}.

  Definition univalent_gquot_biadjunction
    : BiAdjunction univalent_grpd one_types.
  Proof.
    simple refine (restrict_adjunction gquot_biadjunction _ _).
    intros X ; simpl.
    apply _.
  Defined.

  Definition unit_ugq
    := unit univalent_gquot_biadjunction.

  Definition counit_ugq
    := counit univalent_gquot_biadjunction.

  Section UnitEquivalence.
    Definition gcl_functor
               {A : groupoid}
               `{is_univalent A}
    : Functor A.1 (path_groupoid (BuildTruncType 1 (gquot A))).1.
    Proof.
      simple refine (Build_Functor _ _ _ _ _ _) ; simpl.
      - apply gcl.
      - intros a₁ a₂ g ; simpl in *.
        exact (gcleq _ g).
      - intros ; simpl.
        apply gconcat.
      - intros ; simpl.
        apply ge.
    Defined.

    Definition ap_gcl_univalentgpd_eq
               {A : groupoid}
               `{is_univalent A}
               {a₁ a₂ : A}
               (g : A a₁ a₂)
      : ap (gcl A) (univalent_grpd_eq A g) = gcleq A g.
    Proof.
      rewrite <- (univalent_grpd_eq_functor gcl_functor) ; cbn.
      induction (gcleq A g) ; simpl.
      apply (@univalent_grpd_eq_e _ (path_groupoid (BuildTruncType 1 (gquot A)))).
    Qed.

    Definition unit_sect_d_help
               {A : groupoid}
               `{is_univalent A}
               {a₁ a₂ : A}
               (g : A a₁ a₂)
      : path_over
          (fun h : gquot A => gcl A (unit_inv_map_one A h) = h) 
          (gcleq A g)
          idpath
          idpath.
    Proof.
      apply map_path_over.
      refine (whisker_square
                idpath
                (ap (ap (gcl A)) (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)^
                 @ (ap_compose _ _ _)^)
                ((ap_idmap _)^)
                idpath
                _).
      apply path_to_square.
      refine (concat_p1 _ @ _ @ (concat_1p _)^).
      apply ap_gcl_univalentgpd_eq.
    Qed.

    Definition unit_sect_transformation_d
               (A : groupoid)
               `{is_univalent A}
      : forall c : gquot A, gcl A (unit_inv_map_one A c) = c.
    Proof.
      simple refine (gquot_ind_set _ _ _ _).
      - intros a ; simpl.
        reflexivity.
      - intros a₁ a₂ g ; simpl.
        apply unit_sect_d_help.
    Defined.

    Definition unit_sect_transformation_natural
               {A : grpd}
               `{is_univalent A}
               {x y : gquot A}
               (p : x = y)
      : gcleq A (unit_inv_map_two A x y p) @ unit_sect_transformation_d A y
        =
        unit_sect_transformation_d A x @ p.
    Proof.
      induction p ; simpl.
      revert x.
      simple refine (gquot_ind_prop _ _ _).
      intros a ; simpl.
      rewrite ge.
      reflexivity.
    Qed.

    Definition unit_sect_d
      : Modification_d
          (compose unit_inv unit_ugq)
          (identity_transformation
             (lax_comp (right_adjoint_d univalent_gquot_biadjunction.1)
                       (left_adjoint_d univalent_gquot_biadjunction.1))).
    Proof.
      intros [A UA].
      simple refine (Build_NaturalTransformation _ _ _ _).
      - simpl.
        exact (unit_sect_transformation_d A).
      - intros ; apply unit_sect_transformation_natural.
    Defined.

    Definition unit_sect_is_modification
      : is_modification unit_sect_d.
    Proof.
      intros A B f.
      apply path_natural_transformation.
      simple refine (gquot_ind_prop _ _ _).
      intros a ; simpl in *.
      rewrite !ge ; simpl.
      reflexivity.
    Qed.

    Definition unit_sect
      : Modification
          (compose unit_inv unit_ugq)
          (identity_transformation
             (lax_comp (right_adjoint_d univalent_gquot_biadjunction.1)
                       (left_adjoint_d univalent_gquot_biadjunction.1)))
      := Build_Modification unit_sect_d unit_sect_is_modification.

    Definition unit_retr_transformation_d
               {A : groupoid}
               `{is_univalent A}
               (a : A)
      : A a a
      := e a.

    Definition unit_retr_transformation_natural
               {A : groupoid}
               `{is_univalent A}
               {a b : A}
               (f : A a b)
      : unit_inv_map_two A (gcl A a) (gcl A b) (gcleq A f) ● unit_retr_transformation_d b
        =
        unit_retr_transformation_d a ● f.
    Proof.
      unfold unit_retr_transformation_d.
      rewrite grpd_left_identity, grpd_right_identity.
      unfold unit_inv_map_two ; cbn.
      rewrite transport_morphism_FlFr.
      rewrite gquot_rec_beta_gcleq.
      rewrite ap_const ; simpl.
      rewrite eisretr.
      rewrite !right_identity.
      reflexivity.
    Qed.

    Definition unit_retr_d
      : Modification_d
          (compose unit_ugq unit_inv)
          (identity_transformation (lax_id_functor univalent_grpd)).
    Proof.
      intros A.
      destruct A as [A UA].
      simple refine (Build_NaturalTransformation _ _ _ _).
      - intros a ; simpl in *.
        exact (unit_retr_transformation_d a).
      - intros a b f ; simpl in *.
        exact (unit_retr_transformation_natural f).
    Defined.

    Definition unit_retr_is_modification
      : is_modification unit_retr_d.
    Proof.
      intros A B f.
      apply path_natural_transformation.
      intros X ; cbn in *.
      rewrite identity_of, !left_identity, !right_identity.
      unfold unit_inv_map_two.
      rewrite !transport_morphism_FlFr.
      rewrite gquot_rec_beta_gcleq.
      rewrite ap_const ; simpl.
      rewrite !left_identity, identity_of, !right_identity.
      rewrite eisretr.
      reflexivity.
    Qed.

    Definition unit_retr
      : Modification
          (compose unit_ugq unit_inv)
          (identity_transformation (lax_id_functor univalent_grpd))
      := Build_Modification unit_retr_d unit_retr_is_modification.

    Definition unit_sect_inv_d_help
               {A : groupoid}
               `{is_univalent A}
               {a₁ a₂ : A}
               (g : A a₁ a₂)
      : path_over
          (fun h : gquot A => h = gcl A (unit_inv_map_one A h))
          (gcleq A g)
          idpath
          idpath.
    Proof.
      apply map_path_over.
      refine (whisker_square
                idpath
                ((ap_idmap _)^)
                (ap (ap (gcl A)) (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)^
                 @ (ap_compose _ _ _)^)
                idpath
                _).
      apply path_to_square.
      refine (concat_p1 _ @ _^ @ (concat_1p _)^).
      apply ap_gcl_univalentgpd_eq.
    Qed.

    Definition unit_sect_inv_transformation_d
               (A : groupoid)
               `{is_univalent A}
      : forall c : gquot A, c = gcl A (unit_inv_map_one A c).
    Proof.
      simple refine (gquot_ind_set _ _ _ _).
      - intros a ; simpl.
        reflexivity.
      - intros a₁ a₂ g ; simpl.
        apply unit_sect_inv_d_help.
    Defined.

    Definition unit_sect_inv_transformation_natural
               {A : grpd}
               `{is_univalent A}
               {x y : gquot A}
               (p : x = y)
      : p @ unit_sect_inv_transformation_d A y
        =
        unit_sect_inv_transformation_d A x @ gcleq A (unit_inv_map_two A x y p).
    Proof.
      induction p ; simpl.
      revert x.
      simple refine (gquot_ind_prop _ _ _).
      intros a ; simpl.
      rewrite ge.
      reflexivity.
    Qed.

    Definition unit_sect_inv_d
      : Modification_d
          (identity_transformation
             (lax_comp (right_adjoint_d univalent_gquot_biadjunction.1)
                       (left_adjoint_d univalent_gquot_biadjunction.1)))
          (compose unit_inv unit_ugq).
    Proof.
      intros [A UA].
      simple refine (Build_NaturalTransformation _ _ _ _).
      - exact (unit_sect_inv_transformation_d A).
      - intros.
        apply (unit_sect_inv_transformation_natural).
    Defined.

    Definition unit_sect_inv_is_modification
      : is_modification unit_sect_inv_d.
    Proof.
      intros A B f.
      apply path_natural_transformation.
      simple refine (gquot_ind_prop _ _ _).
      intros a ; simpl in *.
      rewrite !ge.
      reflexivity.
    Qed.

    Definition unit_sect_inv
      : Modification
          (identity_transformation
             (lax_comp (right_adjoint_d univalent_gquot_biadjunction.1)
                       (left_adjoint_d univalent_gquot_biadjunction.1)))
          (compose unit_inv unit_ugq)
      := Build_Modification unit_sect_inv_d unit_sect_inv_is_modification.

    Definition unit_retr_inv_transformation_natural
               {A : groupoid}
               `{is_univalent A}
               {a b : A}
               (f : A a b)
      : f ● unit_retr_transformation_d b
        =
        unit_retr_transformation_d a ● unit_inv_map_two A (gcl A a) (gcl A b) (gcleq A f).
    Proof.
      unfold unit_retr_transformation_d.
      rewrite grpd_left_identity, grpd_right_identity.
      unfold unit_inv_map_two ; cbn.
      rewrite transport_morphism_FlFr.
      rewrite gquot_rec_beta_gcleq.
      rewrite ap_const ; simpl.
      rewrite eisretr.
      rewrite !right_identity.
      reflexivity.
    Qed.

    Definition unit_retr_inv_d
      : Modification_d
          (identity_transformation (lax_id_functor univalent_grpd))
          (compose unit_ugq unit_inv).
    Proof.
      intros [A UA].
      simple refine (Build_NaturalTransformation _ _ _ _).
      - intros a ; cbn in *.
        apply unit_retr_transformation_d.
      - intros a b f ; cbn in *.
        apply unit_retr_inv_transformation_natural.
    Defined.

    Definition unit_retr_inv_is_modification
      : is_modification unit_retr_inv_d.
    Proof.
      intros A B f.
      apply path_natural_transformation.
      intros X ; cbn in *.
      rewrite !identity_of, !left_identity.
      reflexivity.
    Qed.

    Definition unit_retr_inv
      : Modification
          (identity_transformation (lax_id_functor univalent_grpd))
          (compose unit_ugq unit_inv)        
      := Build_Modification unit_retr_inv_d unit_retr_inv_is_modification.

    Definition unit_ugq_adjunction_d
      : @is_left_adjoint_d (Lax univalent_grpd univalent_grpd) _ _ unit_ugq.
    Proof.
      make_is_left_adjoint.
      - exact unit_inv.
      - exact unit_retr_inv.
      - exact unit_sect.
    Defined.

    Definition unit_ugq_is_adjunction
      : is_adjunction unit_ugq_adjunction_d.
    Proof.
      make_is_adjunction.
      - apply path_modification.
        funext [A UA].
        apply path_natural_transformation.
        intros x ; revert x.
        simpl.
        simple refine (gquot_ind_prop _ _ _).
        intros a ; simpl.
        rewrite !left_identity, !right_identity, ge.
        reflexivity.
      - apply path_modification.
        funext [A UA].
        apply path_natural_transformation.
        intros x ; cbn.
        rewrite !ge.
        reflexivity.
    Qed.

    Definition unit_ugq_adjunction
      :  @is_left_adjoint (Lax univalent_grpd univalent_grpd) _ _ unit_ugq
      := Build_is_left_adjoint unit_ugq_adjunction_d unit_ugq_is_adjunction.

    Definition unit_univalent_gquot_biadjunction_equiv
      : @is_adjoint_equivalence (Lax univalent_grpd univalent_grpd) _ _ unit_ugq.
    Proof.
      simple refine (unit_ugq_adjunction;_).
      split.
      - simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
        + exact unit_retr.
        + apply path_modification.
          funext G.
          apply path_natural_transformation.
          intros X.
          apply left_identity.
        + apply path_modification.
          funext G.
          apply path_natural_transformation.
          intros X.
          apply left_identity.
      - simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
        + exact unit_sect_inv.
        + apply path_modification.
          funext G.
          apply path_natural_transformation.
          intros x ; revert x.          
          simple refine (gquot_ind_prop _ _ _).
          intros a.
          reflexivity.
        + apply path_modification.
          funext G.
          apply path_natural_transformation.
          simple refine (gquot_ind_prop _ _ _).
          intros a.
          reflexivity.
    Defined.
  End UnitEquivalence.

  Section CounitEquivalence.
    Definition counit_ugq_inv_d
    : PseudoTransformation_d
        (lax_id_functor one_types)
        (lax_comp (left_adjoint_d univalent_gquot_biadjunction.1)
                  (right_adjoint_d univalent_gquot_biadjunction.1)).
    Proof.
      make_pseudo_transformation.
      - intros X ; cbn.
        exact (gcl (path_groupoid X)).
      - reflexivity.
      - reflexivity.
    Defined.

    Definition counit_ugq_inv_is_pseudo
      : is_pseudo_transformation_p counit_ugq_inv_d.
    Proof.
      make_is_pseudo_transformation.
      - intros X Y f g α.
        induction α.
        cbn.
        rewrite !concat_1p, concat_p1.
        f_ap.
        funext x.
        rewrite ap10_path_forall ; simpl.
        rewrite ge.
        reflexivity.
      - intros X.
        cbn.
        rewrite !concat_1p, !concat_p1.
        f_ap.
        funext x.
        rewrite concat_p1, <- path_forall_pp.
        rewrite ap10_path_forall ; simpl.
        rewrite ge.
        reflexivity.
      - intros X Y Z f g.
        cbn.
        rewrite !concat_p1, !concat_1p.
        rewrite <- !path_forall_pp.
        f_ap.
        funext x.
        rewrite ap10_path_forall ; simpl.
        rewrite ge.
        reflexivity.
      - reflexivity.
      - reflexivity.
    Qed.

    Definition counit_ugq_inv
      : PseudoTransformation
          (lax_id_functor one_types)
          (lax_comp (left_adjoint_d univalent_gquot_biadjunction.1)
                    (right_adjoint_d univalent_gquot_biadjunction.1))
      := Build_PseudoTransformation counit_ugq_inv_d counit_ugq_inv_is_pseudo.
    
    Definition counit_sect_d
      : Modification_d
          (compose counit_ugq_inv counit_ugq)
          (identity_transformation (lax_id_functor one_types))
      := fun _ => idpath.

    Definition counit_sect_is_modification
      : is_modification counit_sect_d.
    Proof.
      intros A B f ; cbn.
      rewrite !concat_1p, !concat_p1.
      rewrite <- !path_forall_pp.
      f_ap.
      funext x ; simpl.
      rewrite ap10_path_forall.
      rewrite !concat_p1.
      reflexivity.
    Qed.

    Definition counit_sect
      : Modification
          (compose counit_ugq_inv counit_ugq)
          (identity_transformation (lax_id_functor one_types))
      := Build_Modification counit_sect_d counit_sect_is_modification.

    Definition counit_sect_inv_d
      : Modification_d
          (identity_transformation (lax_id_functor one_types))
          (compose counit_ugq_inv counit_ugq)
      := fun _ => idpath.

    Definition counit_sect_inv_is_modification
      : is_modification counit_sect_inv_d.
    Proof.
      intros A B f ; cbn.
      rewrite !concat_1p, !concat_p1.
      rewrite <- !path_forall_pp.
      f_ap.
      funext x ; simpl.
      rewrite ap10_path_forall.
      rewrite !concat_p1.
      reflexivity.
    Qed.

    Definition counit_sect_inv
      : Modification
          (identity_transformation (lax_id_functor one_types))
          (compose counit_ugq_inv counit_ugq)
      := Build_Modification counit_sect_inv_d counit_sect_inv_is_modification.

    Definition counit_retr_help
               {A : 1 -Type}
               {a₁ a₂ : path_groupoid A}
               (g : a₁ = a₂)
      : path_over
          (fun h : gquot (path_groupoid A) => gcl (path_groupoid A) (counit_map A h) = h)
          (gcleq (path_groupoid A) g)
          1%path
          1%path.
    Proof.
      apply map_path_over.
      refine (whisker_square
                idpath
                _
                ((ap_idmap _)^)
                idpath
                _).
      - refine (_ @ (ap_compose _ _ _)^).
        exact (ap (ap _) (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)^).
      - apply path_to_square ; simpl.
        refine (concat_p1 _ @ _ @ (concat_1p _)^).
        induction g ; simpl.
        exact (ge _ _)^.
    Qed.
      
    Definition counit_retr_d
      : Modification_d
          (compose counit_ugq counit_ugq_inv)
          (identity_transformation
             (lax_comp (left_adjoint_d univalent_gquot_biadjunction.1)
                       (right_adjoint_d univalent_gquot_biadjunction.1))).
    Proof.
      intros A ; cbn.
      funext x ; revert x.
      simple refine (gquot_ind_set _ _ _ _).
      - reflexivity.
      - intros ; apply counit_retr_help.
    Defined.

    Definition counit_retr_is_modification
      : is_modification counit_retr_d.
    Proof.
      intros A B f ; cbn.
      rewrite !concat_1p, !concat_p1.
      rewrite <- !path_forall_pp.
      f_ap.
      funext x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intros a ; simpl.
      rewrite !concat_1p, !ap10_path_forall.
      reflexivity.
    Qed.

    Definition counit_retr
      : Modification
          (compose counit_ugq counit_ugq_inv)
          (identity_transformation
             (lax_comp (left_adjoint_d univalent_gquot_biadjunction.1)
                       (right_adjoint_d univalent_gquot_biadjunction.1)))
      := Build_Modification counit_retr_d counit_retr_is_modification.

    Definition counit_retr_inv_d
      : Modification_d
          (identity_transformation
             (lax_comp (left_adjoint_d univalent_gquot_biadjunction.1)
                       (right_adjoint_d univalent_gquot_biadjunction.1)))
          (compose counit_ugq counit_ugq_inv)
      := fun A => (counit_retr_d A)^.

    Definition counit_retr_inv_is_modification
      : is_modification counit_retr_inv_d.
    Proof.
      intros A B f ; cbn.
      rewrite !concat_1p, !concat_p1.
      rewrite <- !path_forall_pp.
      f_ap.
      funext x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intros a ; simpl.
      unfold counit_retr_inv_d, counit_retr_d ; cbn.
      rewrite !concat_1p, !concat_p1, <- !path_forall_V, !ap10_path_forall.
      reflexivity.
    Qed.

    Definition counit_retr_inv
      : Modification
          (identity_transformation
             (lax_comp (left_adjoint_d univalent_gquot_biadjunction.1)
                       (right_adjoint_d univalent_gquot_biadjunction.1)))
          (compose counit_ugq counit_ugq_inv)
      := Build_Modification counit_retr_inv_d counit_retr_inv_is_modification.

    Definition counit_ugq_adjunction_d
      : @is_left_adjoint_d (Lax one_types one_types) _ _ counit_ugq.
    Proof.
      make_is_left_adjoint.
      - exact counit_ugq_inv.1.
      - exact counit_retr_inv.
      - exact counit_sect.
    Defined.

    Definition counit_ugq_is_adjunction
      : is_adjunction counit_ugq_adjunction_d.
    Proof.
      make_is_adjunction.
      - apply path_modification.
        funext A.
        cbn.
        rewrite !concat_1p, !concat_p1, <- !path_forall_pp, <- path_forall_1.
        f_ap.
        funext x ; cbn.
        unfold counit_retr_inv, counit_retr_inv_d, counit_retr_d.
        rewrite !concat_p1, <- path_forall_V, ap10_path_forall.
        reflexivity.
      - apply path_modification.
        funext A.
        cbn.
        rewrite !concat_1p, !concat_p1, <- !path_forall_pp, <- path_forall_1.
        f_ap.
        funext x ; revert x.
        simple refine (gquot_ind_prop _ _ _).
        intros a ; simpl.
        rewrite !concat_1p, concat_p1.
        unfold counit_retr_inv_d, counit_retr_d.
        rewrite <- path_forall_V, ap10_path_forall.
        reflexivity.
    Qed.

    Definition counit_ugq_adjunction
      : @is_left_adjoint (Lax one_types one_types) _ _ counit_ugq
      := Build_is_left_adjoint counit_ugq_adjunction_d counit_ugq_is_adjunction.

    Definition counit_univalent_gquot_biadjunction_equiv
      : @is_adjoint_equivalence (Lax one_types one_types) _ _ counit_ugq.
    Proof.
      simple refine (counit_ugq_adjunction;_).
      split.
      - simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
        + exact counit_retr.
        + apply path_modification.
          funext A ; cbn.
          apply concat_Vp.
        + apply path_modification.
          funext A ; cbn.
          apply concat_pV.
      - simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
        + exact counit_sect_inv.
        + apply path_modification.
          funext A.
          reflexivity.
        + apply path_modification.
          funext A.
          reflexivity.
    Defined.
  End CounitEquivalence.

  Definition one_types_grpd_equiv
    : BiEquivalence univalent_grpd one_types.
  Proof.
    make_biequivalence.
    - exact univalent_gquot_biadjunction.
    - make_is_biequivalence.
      + exact unit_univalent_gquot_biadjunction_equiv.
      + exact counit_univalent_gquot_biadjunction_equiv.
  Defined.
End UnivalentGQuotAdjunction.