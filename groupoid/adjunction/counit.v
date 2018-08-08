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

Definition test {A} : A.
Admitted.

Section Counit.
  Context `{Univalence}.

  Definition counit_map (X : 1 -Type)
    : @one_cell _ one_types (gquot_functor(path_groupoid X)) X.
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
             (g : hom (path_groupoid X) a₁ a₂)
    : path_over
        (fun h : gquot (path_groupoid X) =>
           f (counit_map X h)
           =
           counit_map Y ((Fmor (lax_comp gquot_functor path_groupoid_functor)) f h)
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
             (g : hom (path_groupoid X) a₁ a₂)
    : path_over
        (fun h : gquot (path_groupoid X) =>
           counit_map Y ((Fmor (lax_comp gquot_functor path_groupoid_functor)) f h)
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

  Definition counit_gq_rd_is_lax
    : is_pseudo_transformation_rd counit_gq_rd.
  Proof.
    repeat split.
    - intros X Y f g p.
      induction p.
      rewrite !identity_of, left_identity, !right_identity.
      reflexivity.
    - intros X.
      unfold hcomp ; simpl.
      repeat refine (_ @ (concat_1p _)^).
      refine (concat_1p _ @ _).
      cbn.
      refine (_ @ ap _ (path_forall_pp _ _ _ _ _)).
      refine (_ @ (ap_precompose _ _)^).
      apply ap.
      funext x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intro a.
      simpl.
      rewrite concat_1p.
      rewrite gquot_rec_beta_gcleq.
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
      simpl ; unfold hcomp.
      Opaque gquot_functor_rd_map.
      cbn.
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
      simpl.
      rewrite ap_pp.
      rewrite concat_1p.
      refine ((concat_p1 _)^ @ _).
      f_ap.
      rewrite ge.
      reflexivity.
    - intros X Y f g p.
      induction p.
      cbn.
      rewrite concat_1p, ap_precompose.
      rewrite <- path_forall_pp.
      rewrite concat_p1.
      f_ap.
      funext x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intro a.
      simpl.
      rewrite concat_p1.
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