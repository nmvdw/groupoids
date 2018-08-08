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
     lax_transformation.lax_transformation.
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
    : @one_cell _ one_types A (gquot_functor(path_groupoid A))
    := gcl (path_groupoid A).

  Definition counit_gq_inv_rd
    : PseudoTransformation_d
        (lax_id_functor one_types)
        (lax_comp gquot_functor path_groupoid_functor).
  Proof.
    simple refine (Build_PseudoTransformation_d _ _ _).
    - exact counit_inv_map.
    - reflexivity.
    - reflexivity.
  Defined.

  Definition counit_gq_inv_rd_is_lax
    : is_pseudo_transformation_rd counit_gq_inv_rd.
  Proof.
    repeat split.
    - intros X Y f g α.
      induction α.
      unfold hcomp ; simpl.
      rewrite !concat_p1.
      rewrite !ap_postcompose.
      rewrite <- path_forall_1.
      f_ap.
      funext x ; simpl.
      rewrite ge.
      reflexivity.
    - intros X.
      unfold hcomp ; cbn.
      rewrite !concat_p1.
      rewrite <- path_forall_pp.
      rewrite !ap_postcompose.
      rewrite <- path_forall_1.
      f_ap.
      funext x.
      simpl.
      rewrite ge.
      reflexivity.
    - intros X Y Z f g.
      assert ((inverse assoc)
                ((Fmor (lax_comp gquot_functor path_groupoid_functor)) g,
                 laxcomponent_of_rd _ _ counit_gq_inv_rd Y, (Fmor (lax_id_functor one_types) f))
              = 1%morphism) as ->.
      {
        apply Morphisms.iso_moveR_1V.
        reflexivity.
      }
      simpl.
      rewrite !concat_1p, !concat_p1.
      unfold hcomp ; simpl.
      rewrite <- path_forall_pp.
      rewrite ap_postcompose.
      rewrite !concat_p1.
      rewrite <- path_forall_1.
      f_ap.
      funext x.
      simpl.
      rewrite ge.
      reflexivity.
    - intros X Y f g α.
      induction α.
      unfold hcomp ; simpl.
      rewrite !concat_1p, !concat_p1.
      rewrite ap_postcompose.
      rewrite <- path_forall_1.
      f_ap.
      funext x.
      simpl.
      rewrite ge.
      reflexivity.
  Qed.

  Definition counit_inv
    : LaxTransformation
        (lax_id_functor one_types)
        (lax_comp gquot_functor path_groupoid_functor)        
    := Build_PseudoTransformation counit_gq_inv_rd counit_gq_inv_rd_is_lax.

  Global Instance counit_inv_pseudo
    : is_pseudo_transformation counit_inv.
  Proof.
    apply _.
  Defined.
End CounitInverse.