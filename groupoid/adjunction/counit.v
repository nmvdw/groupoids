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

Section Counit.
  Context `{Univalence}.

  Definition counit_map (X : 1 -Type)
    : @one_cell _ one_types (gquot_o(path_groupoid X)) X.
  Proof.
    simple refine (gquot_rec X _ _ _ _ _ _) ; cbn.
    - exact idmap.
    - exact (fun _ _ => idmap).
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Defined.
  
  Definition naturality_help
             {X Y : one_types}
             (f : X -> Y)
             {a₁ a₂ : path_groupoid X}
             (g : hom (path_groupoid X) a₁ a₂)
    : path_over
        (fun g0 : gquot (path_groupoid X) =>
           f (counit_map X g0)
           =
           counit_map Y ((Fmor (lax_comp gquot_functor path_groupoid_functor)) f g0))
        (gcleq (path_groupoid X) g)
        idpath
        idpath.
  Proof.
    apply map_path_over.
    simple refine (whisker_square
                     idpath
                     (ap (ap f) (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _)^
                      @ (ap_compose _ _ _)^)
                     _
                     idpath
                     _).
    - exact (ap f g).
    - refine (_ @ (ap_compose _ _ _)^).
      refine ((gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _)^ @ _).
      apply ap.
      exact ((gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _)^).
    - apply vrefl.
  Qed.

  Definition counit_gq_rd
    : PseudoTransformation_d
        (lax_comp gquot_functor path_groupoid_functor)
        (lax_id_functor one_types).
  Proof.
    simple refine (Build_PseudoTransformation_d _ _ _).
    - exact counit_map.
    - intros X Y f ; simpl.
      funext x ; simpl ; revert x.
      simple refine (gquot_ind_set _ _ _ _).
      + reflexivity.
      + intros ; simpl.
        pose (naturality_help f g) as p.
        cbn in *.
        apply p.
    - intros X Y f ; cbn.
      funext x ; simpl ; revert x.
      simple refine (gquot_ind_set _ _ _ _).
      + reflexivity.
      + intros a₁ a₂ g ; simpl.
        induction g.
        apply map_path_over.
        apply path_to_square.
        refine (concat_p1 _ @ _ @ (concat_1p _)^).
        rewrite ge.
        reflexivity.
  Defined.

  Definition counit_gq_rd_is_lax
    : is_pseudo_transformation_rd counit_gq_rd.
  Proof.
    repeat split.
    - intros X Y f g p.
      induction p.
      rewrite !identity_of, left_identity, !right_identity.
      reflexivity.
    - intros X.
      simpl.
      repeat refine (_ @ (concat_1p _)^).
      unfold hcomp.
      simpl.
      refine (concat_1p _ @ _).
      unfold lax_comp_id.
      cbn.
      unfold gquot_id.
      refine (_ @ ap _ (path_forall_pp _ _ _ _ _)).
      refine (_ @ (ap_precompose _ _)^).
      apply ap.
      funext x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intro a.
      cbn -[gquot_functorial gquot_functorial_idmap gquot_functorial_natural].
      rewrite ap_pp.
      rewrite concat_1p.
      assert (gquot_functorial_natural (path_groupoid_map_id X) (gcl (path_groupoid X) a)
            =
            gcleq _ (e a)) as ->.
      { reflexivity. }
      rewrite ge.
      reflexivity.
    - intros X Y Z f g.
      assert ((inverse assoc)
                ((Fmor (lax_id_functor one_types)) g, counit_map Y,
                 (Fmor (lax_comp gquot_functor path_groupoid_functor)) f)
              = 1%morphism) as ->.
      {
        apply Morphisms.iso_moveR_1V.
        reflexivity.
      }
      unfold hcomp.
      cbn -[gquot_functorial gquot_functorial_idmap gquot_functorial_natural].
      rewrite !concat_1p, !concat_p1.
      rewrite !ap_precompose, !ap_postcompose.
      rewrite concat_p_pp.
      rewrite <- !path_forall_pp.
      rewrite (ap_precompose (counit_map Z)).
      rewrite <- !path_forall_pp.
      repeat f_ap.
      funext x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intros a.
      cbn -[gquot_functorial
              gquot_functorial_natural gquot_functorial_idmap gquot_functorial_compose].
      rewrite ap_pp.
      rewrite concat_1p.
      refine ((concat_p1 _)^ @ _).
      f_ap.
      unfold gquot_functorial_natural.
      rewrite gquot_ind_set_beta_gcl.
      rewrite ge.
      reflexivity.
    - intros X Y f g p.
      induction p.
      cbn -[gquot_functor gquot_functorial].
      rewrite concat_1p, ap_precompose.
      rewrite <- path_forall_pp.
      rewrite concat_p1.
      f_ap.
      funext x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intro a.
      Opaque gquot_functor gquot_functorial gquot_functorial_natural.
      simpl.
      rewrite concat_p1.
      Transparent gquot_functorial_natural.
      unfold gquot_functorial_natural.
      rewrite gquot_ind_set_beta_gcl.
      rewrite ge.
      reflexivity.
    - intros X Y f ; simpl.
      rewrite <- path_forall_pp, <- path_forall_1.
      f_ap.
      funext x ; simpl ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      reflexivity.
    - intros X Y f ; simpl.
      rewrite <- path_forall_pp, <- path_forall_1.
      f_ap.
      funext x ; simpl ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      reflexivity.
  Qed.
  
  Definition counit_gq
    : LaxTransformation
        (lax_comp gquot_functor path_groupoid_functor)
        (lax_id_functor one_types)
    := Build_PseudoTransformation counit_gq_rd counit_gq_rd_is_lax.

  Global Instance counit_pseudo
    : is_pseudo_transformation counit_gq.
  Proof.
    apply _.
  Defined.
End Counit.








(*
Definition counit_adjunction_d
  : adjunction_d counit_map counit_inv_map.
Proof.
  simple refine {| unit_d := _ |}.
  - cbn ; symmetry.
    apply counit_sect.
  - apply counit_retr.
Defined.

Definition counit_is_adjunction
  : is_adjunction counit_adjunction_d.
Proof.
  split.
  - unfold bc_whisker_r, bc_whisker_l ; simpl.
    rewrite concat_1p, !concat_p1, ap_V.
    rewrite ap_postcompose.
    rewrite <- path_forall_V, <- path_forall_1.
    reflexivity.
  - apply Morphisms.iso_moveR_pV.
    unfold bc_whisker_r, bc_whisker_l.
    rewrite !left_identity.
    apply Morphisms.iso_moveR_Vp.
    simpl.      
    rewrite !concat_1p, ap_V.
    rewrite ap_precompose.
    rewrite <- path_forall_V, <- path_forall_1.
    f_ap.
    funext x ; revert x.
    simple refine (gquot_ind_prop _ _ _).
    reflexivity.
Qed.

Definition counit_adjunction
  : adjunction counit_map counit_inv_map
  := (counit_adjunction_d;counit_is_adjunction).
*)