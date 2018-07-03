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
    : @one_cell _ one_types A (gquot_o(path_groupoid A))
    := gcl (path_groupoid A).

  Definition counit_inv_naturality (X Y : one_types)
    : NaturalTransformation
        (precomp (counit_inv_map X) ((lax_comp gquot_functor path_groupoid_functor) Y)
                 o Fmor (lax_comp gquot_functor path_groupoid_functor))
        (postcomp (counit_inv_map Y) ((lax_id_functor one_types) X)
                  o Fmor (lax_id_functor one_types)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - reflexivity.
    - intros f g p.
      induction p ; simpl.
      rewrite ap_postcompose, !concat_p1.
      rewrite <- path_forall_1.
      f_ap.
      funext x ; simpl.
      apply ge.
  Defined.

  Definition counit_inv_naturality_inv (X Y : one_types)
    : NaturalTransformation
        (postcomp (counit_inv_map Y) ((lax_id_functor one_types) X)
                  o Fmor (lax_id_functor one_types))
        (precomp (counit_inv_map X) ((lax_comp gquot_functor path_groupoid_functor) Y)
                 o Fmor (lax_comp gquot_functor path_groupoid_functor)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - reflexivity.
    - intros f g p ; simpl.
      induction p ; simpl.
      rewrite ap_postcompose, !concat_1p, concat_p1.
      rewrite <- path_forall_1.
      f_ap.
      funext x ; simpl.
      rewrite ge.
      reflexivity.
  Defined.

  Global Instance counit_inv_naturality_pseudo (X Y : one_types)
    : @IsIsomorphism (_ -> _) _ _ (counit_inv_naturality X Y).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply counit_inv_naturality_inv.
    - apply path_natural_transformation.
      intros f ; reflexivity.
    - apply path_natural_transformation.
      intros f ; reflexivity.
  Defined.

  Definition counit_inv_d
    : LaxTransformation_d
        (lax_id_functor one_types)
        (lax_comp gquot_functor path_groupoid_functor).
  Proof.
    simple refine (Build_LaxTransformation_d _ _).
    - exact counit_inv_map.
    - exact counit_inv_naturality.
  Defined.

  Definition is_lax_counit_inv
    : is_lax_transformation counit_inv_d.
  Proof.
    split.
    - intros X.
      simpl.
      unfold hcomp.
      simpl.
      rewrite !concat_p1 ; cbn.
      unfold Fid, lax_comp, gquot_id, counit_inv_map.
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
                 laxcomponent_of_d counit_inv_d Y, (Fmor (lax_id_functor one_types) f))
              = 1%morphism) as ->.
      {
        apply Morphisms.iso_moveR_1V.
        reflexivity.
      }
      unfold hcomp ; simpl.
      rewrite !concat_1p, !concat_p1.
      rewrite <- path_forall_pp.
      rewrite ap_postcompose.
      rewrite <- path_forall_1.
      f_ap.
      funext x.
      unfold gquot_functorial_natural.
      rewrite gquot_ind_set_beta_gcl.
      rewrite ge, concat_p1.
      reflexivity.
  Qed.

  Definition counit_inv
    : LaxTransformation
        (lax_id_functor one_types)
        (lax_comp gquot_functor path_groupoid_functor)        
    := Build_LaxTransformation counit_inv_d is_lax_counit_inv.

  Global Instance counit_inv_pseudo
    : is_pseudo_transformation counit_inv.
  Proof.
    split ; apply _.
  Defined.
End CounitInverse.