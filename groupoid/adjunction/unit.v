Require Import HoTT.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory
     bicategory.examples.one_types
     bicategory.examples.full_sub
     bicategory.examples.precat
     bicategory.equivalence
     bicategory.adjoint
     lax_functor.lax_functor
     lax_functor.examples.identity
     lax_functor.examples.composition
     lax_transformation.lax_transformation.
From GR.groupoid Require Import
     groupoid_quotient.gquot
     groupoid_quotient.gquot_functor
     groupoid_quotient.gquot_principles
     grpd_bicategory.grpd_bicategory
     path_groupoid.path_groupoid.
From GR.basics Require Import
     general.

Definition inverse_assoc_grpd
           `{Univalence}
           (G₁ G₂ G₃ G₄ : groupoid)
  : inverse (@assoc _ grpd G₁ G₂ G₃ G₄)
    =
    nAssociator_inv _ _ _ _.
Proof.
  apply path_natural_transformation.
  intros [[f₁ f₂] f₃].
  apply path_natural_transformation.
  intros y ; simpl.
  rewrite iso_component.
  apply iso_moveR_V1 ; cbn.
  rewrite right_identity.
  reflexivity.
Qed.

Section Unit.
  Context `{Univalence}.

  Definition unit_map (G : groupoid)
    : @one_cell _ grpd G (path_groupoid(gquot_functor G)).
  Proof.
    cbn.
    simple refine (Build_Functor _ _ _ _ _ _) ; simpl.
    - apply gcl.
    - intros ? ? g ; cbn in *.
      exact (gcleq _ g).
    - intros ? ? ? g₁ g₂ ; cbn in *.
      apply gconcat.
    - intros x ; cbn in *.
      apply ge.
  Defined.

  Definition unit_gq_rd
    : PseudoTransformation_d
        (lax_id_functor grpd)
        (lax_comp path_groupoid_functor gquot_functor).
  Proof.
    simple refine (Build_PseudoTransformation_d _ _ _).
    - exact unit_map.
    - intros G₁ G₂ F ; simpl.
      simple refine (Build_NaturalTransformation _ _ _ _).
      + reflexivity.
      + intros x y g ; simpl.
        refine (concat_p1 _ @ _ @ (concat_1p _)^).
        exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _).
    - intros G₁ G₂ F ; simpl.
      simple refine (Build_NaturalTransformation _ _ _ _).
      + reflexivity.
      + intros x y g ; simpl.
        refine (concat_p1 _ @ _ @ (concat_1p _)^).
        exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _)^.
  Defined.

  Definition unit_gq_rd_is_lax
    : is_pseudo_transformation_rd unit_gq_rd.
  Proof.
    repeat split.
    - intros G₁ G₂ F₁ F₂ α.
      apply path_natural_transformation.
      intros x.
      refine (concat_p1 _ @ concat_1p _ @ _ @ (concat_1p _ @ concat_p1 _)^).
      simpl in *.
      rewrite ap10_path_forall.
      reflexivity.
    - intros G.
      apply path_natural_transformation.
      intros x ; simpl in *.
      refine (concat_p1 _ @ concat_1p _ @ concat_1p _ @ _).
      refine (_ @ (concat_1p _ @ concat_1p _ @ concat_p1 _)^).
      rewrite ap10_path_forall.
      rewrite ge.
      reflexivity.
    - intros G₁ G₂ G₃ F₁ F₂.
      apply path_natural_transformation.
      intro x.
      rewrite !inverse_assoc_grpd ; simpl in *.
      rewrite !concat_1p, !concat_p1.
      rewrite ap10_path_forall.
      rewrite !ge ; simpl.
      reflexivity.
    - intros G₁ G₂ F₁ F₂ α.
      apply path_natural_transformation.
      intros x ; simpl in *.
      refine (concat_p1 _ @ concat_p1 _ @ _ @ (concat_1p _)^ @ (concat_1p _)^).
      rewrite ap10_path_forall.
      reflexivity.
    - intros G₁ G₂ F.
      apply path_natural_transformation.
      intro x ; simpl.
      reflexivity.
    - intros G₁ G₂ F.
      apply path_natural_transformation.
      intro x ; simpl.
      reflexivity.
  Qed.

  Definition unit_gq
    : LaxTransformation
        (lax_id_functor grpd)
        (lax_comp path_groupoid_functor gquot_functor)
    := Build_PseudoTransformation unit_gq_rd unit_gq_rd_is_lax.

  Global Instance unit_pseudo
    : is_pseudo_transformation unit_gq.
  Proof.
    apply _.
  Defined.
End Unit.

(*
  Definition unit_retr
    : @two_cell _ one_types _ _ (counit ⋅ counit_inv)%bicategory (id_m _)
    := idpath.

  Definition counit_sect
    : @two_cell _ one_types _ _ (counit_inv ⋅ counit)%bicategory (id_m _).
  Proof.
    funext x ; revert x.
    simple refine (gquot_ind_set _ _ _ _).
    - reflexivity.
    - intros ? ? g.
      apply map_path_over.
      apply path_to_square.
      refine (concat_p1 _ @ _ @ (concat_1p _)^) ; cbn in *.
      refine (_ @ (ap_idmap _)^).
      refine (ap_compose counit _ _ @ _).
      refine (ap _ (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _) @ _).
      induction g ; simpl.
      exact (ge _ _)^.
  Defined.

  Global Instance counit_sect_iso
    : IsIsomorphism counit_sect.
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - symmetry.
      apply counit_sect.
    - apply concat_pV.
    - apply concat_Vp.
  Defined.

  Definition counit_equivalence
    : is_equivalence counit.
  Proof.
    simple refine {| f_inv := counit_inv ;
                     retr := counit_retr ;
                     sect := counit_sect |}.
  Defined.

  Definition counit_adjunction
    : is_adjunction counit counit_inv.
  Proof.
    simple refine {| unit := _ |}.
    - cbn ; symmetry.
      apply counit_sect.
    - apply counit_retr.
    - unfold bc_whisker_r, bc_whisker_l ; cbn.
      hott_simpl.
      rewrite ap_V.
      rewrite ap_postcompose.
      rewrite <- path_forall_V, <- path_forall_1.
      reflexivity.
    - unfold bc_whisker_r, bc_whisker_l.
      simpl ; hott_simpl.
      rewrite ap_V.
      rewrite ap_precompose.
      rewrite <- !path_forall_V, <- path_forall_1.
      (* apply ap.
      funext x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      reflexivity. *)
  Admitted.
End counit.
 *)