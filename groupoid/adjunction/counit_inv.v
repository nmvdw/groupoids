Require Import HoTT.
Require Import HoTT.Categories.Functor.
Require Import GR.bicategories.bicategories.
Require Import GR.bicategories.lax_functors.
Require Import GR.bicategories.lax_transformations.
From GR.groupoid Require Import
     groupoid_quotient.gquot
     groupoid_quotient.gquot_functor
     groupoid_quotient.gquot_principles
     grpd_bicategory.grpd_bicategory
     path_groupoid.path_groupoid.
From GR.basics Require Import
     general.

Section CounitInverse.
  Context `{Univalence}.

  Definition counit_inv_map (A : 1 -Type)
    : one_types⟦A,gquot_functor(path_groupoid A)⟧
    := gcl (path_groupoid A).

  Definition counit_gq_inv_d
    : PseudoTransformation_d
        (lax_id_functor one_types)
        (lax_comp gquot_functor path_groupoid_functor).
  Proof.
    make_pseudo_transformation.
    - exact counit_inv_map.
    - reflexivity.
    - reflexivity.
  Defined.

  Definition counit_gq_inv_is_lax
    : is_pseudo_transformation_p counit_gq_inv_d.
  Proof.
    make_is_pseudo_transformation.
    - intros X Y f g α.
      induction α ; cbn.
      rewrite concat_1p, concat_p1.
      f_ap.
      funext x.
      rewrite ap10_path_forall ; simpl.
      rewrite ge.
      reflexivity.
    - intros X.
      cbn.
      rewrite !concat_1p, concat_p1.
      f_ap.
      funext x.
      rewrite <- path_forall_pp.
      rewrite ap10_path_forall ; simpl.
      rewrite ge.
      reflexivity.
    - intros X Y Z f g.
      cbn.
      rewrite !concat_1p, !concat_p1.
      rewrite <- !path_forall_pp.
      f_ap.
      funext x.
      rewrite ap10_path_forall.
      simpl.
      rewrite ge.
      reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  Definition counit_inv
    : LaxTransformation
        (lax_id_functor one_types)
        (lax_comp gquot_functor path_groupoid_functor)        
    := Build_PseudoTransformation counit_gq_inv_d counit_gq_inv_is_lax.

  Global Instance counit_inv_pseudo
    : is_pseudo_transformation counit_inv
    := _.
End CounitInverse.