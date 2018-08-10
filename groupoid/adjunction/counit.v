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
    : one_types⟦gquot_functor(path_groupoid X),X⟧.
  Proof.
    simple refine (gquot_rec X _ _ _ _ _ _) ; cbn.
    - exact idmap.
    - exact (fun _ _ => idmap).
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Defined.
  
  Definition naturality_help₁
             {X Y : one_types}
             (f : X -> Y)
             {a₁ a₂ : path_groupoid X}
             (g : path_groupoid X a₁ a₂)
    : path_over
        (fun h : gquot (path_groupoid X) =>
           f (counit_map X h)
           =
           counit_map Y ((Fmor (lax_comp gquot_functor path_groupoid_functor)) _ _ f h)
        )
        (gcleq (path_groupoid X) g)
        idpath
        idpath.
  Proof.
    induction g.
    apply map_path_over.
    apply path_to_square.
    refine (concat_p1 _ @ _ @ (concat_1p _)^).
    rewrite ge.
    reflexivity.
  Qed.

  Definition naturality_help₂
             {X Y : one_types}
             (f : X -> Y)
             {a₁ a₂ : path_groupoid X}
             (g : path_groupoid X a₁ a₂)
    : path_over
        (fun h : gquot (path_groupoid X) =>
           counit_map Y ((Fmor (lax_comp gquot_functor path_groupoid_functor)) _ _ f h)
           =
           f (counit_map X h)
        )
        (gcleq (path_groupoid X) g)
        idpath
        idpath.
  Proof.
    induction g.
    apply map_path_over.
    apply path_to_square.
    refine (concat_p1 _ @ _ @ (concat_1p _)^).
    rewrite ge.
    reflexivity.
  Qed.

  Definition counit_gq_d
    : PseudoTransformation_d
        (lax_comp gquot_functor path_groupoid_functor)
        (lax_id_functor one_types).
  Proof.
    make_pseudo_transformation.
    - exact counit_map.
    - intros X Y f ; simpl.
      funext x ; simpl ; revert x.
      simple refine (gquot_ind_set _ _ _ _).
      + reflexivity.
      + intros.
        pose (naturality_help₁ f g) as p.
        cbn in p.
        exact p.
    - intros X Y f.
      funext x ; simpl ; revert x.
      simple refine (gquot_ind_set _ _ _ _).
      + reflexivity.
      + intros a₁ a₂ g.
        pose (naturality_help₂ f g) as p.
        cbn in p.
        exact p.
  Defined.

  Definition counit_gq_is_lax
    : is_pseudo_transformation_p counit_gq_d.
  Proof.
    make_is_pseudo_transformation.
    - intros X Y f g p.
      induction p.
      cbn.
      rewrite <- !path_forall_pp.
      f_ap.
      funext x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intros a ; simpl.
      rewrite ap10_path_forall.
      rewrite gquot_rec_beta_gcleq ; simpl.
      reflexivity.
    - intros X.
      cbn.
      rewrite !concat_1p.
      rewrite <- !path_forall_pp.
      f_ap.
      funext x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intros  a ; simpl.
      rewrite ap10_path_forall, !concat_1p.
      rewrite gquot_rec_beta_gcleq ; simpl.
      reflexivity.
    - intros X Y Z f g.
      cbn.
      rewrite !concat_1p.
      rewrite <- !path_forall_pp.
      f_ap.
      funext x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intros a ; simpl.
      rewrite !ap10_path_forall ; simpl.
      rewrite !concat_1p.
      rewrite ge.
      reflexivity.
    - intros X Y f ; cbn.
      rewrite <- path_forall_pp, <- path_forall_1.
      f_ap.
      funext x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      reflexivity.
    - intros X Y f ; cbn.
      rewrite <- path_forall_pp, <- path_forall_1.
      f_ap.
      funext x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      reflexivity.
  Qed.
  
  Definition counit_gq
    : LaxTransformation
        (lax_comp gquot_functor path_groupoid_functor)
        (lax_id_functor one_types)
    := Build_PseudoTransformation counit_gq_d counit_gq_is_lax.

  Global Instance counit_pseudo
    : is_pseudo_transformation counit_gq
    := _.
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