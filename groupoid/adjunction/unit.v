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

Section Unit.
  Context `{Univalence}.

  Definition unit_map (G : groupoid)
    : grpd⟦G,path_groupoid(gquot_functor G)⟧.
  Proof.
    simple refine (Build_Functor _ _ _ _ _ _) ; simpl.
    - exact (gcl G).
    - exact (@gcleq G).
    - exact (@gconcat G).
    - exact (ge G).
  Defined.

  Definition unit_gq_1
             {G₁ G₂ : groupoid}
             {x y : G₁}
             (F : Functor G₁.1 G₂.1)
             (g : hom G₁ x y)
    : ap (gquot_functor_map F) (gcleq G₁ g) @ 1
      =
      1 @ gcleq G₂ (F _1 g)%morphism.
  Proof.
    exact ((concat_p1 _)
             @ (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _)
             @ (concat_1p _)^).
  Qed.

  Definition unit_gq_2
             {G₁ G₂ : groupoid}
             {x y : G₁}
             (F : Functor G₁.1 G₂.1)
             (g : hom G₁ x y)
    : gcleq G₂ (F _1 g)%morphism @ 1
      =
      1 @ ap (gquot_functor_map F) (gcleq G₁ g).
  Proof.
    exact ((concat_p1 _)
             @ (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _)^
             @ (concat_1p _)^).
  Qed.
  
  Definition unit_gq_d
    : PseudoTransformation_d
        (lax_id_functor grpd)
        (lax_comp path_groupoid_functor gquot_functor).
  Proof.
    make_pseudo_transformation.
    - exact unit_map.
    - intros G₁ G₂ F.
      simple refine (Build_NaturalTransformation _ _ _ _).
      + reflexivity.
      + intros x y g.
        exact (unit_gq_1 F g).
    - intros G₁ G₂ F.
      simple refine (Build_NaturalTransformation _ _ _ _).
      + reflexivity.
      + intros x y g.
        exact (unit_gq_2 F g).
  Defined.

  Definition unit_gq_is_lax
    : is_pseudo_transformation_p unit_gq_d.
  Proof.
    make_is_pseudo_transformation.
    - intros G₁ G₂ F₁ F₂ α.
      apply path_natural_transformation.
      intros x.
      unfold hcomp ; simpl in *.
      rewrite ap10_path_forall.
      rewrite !concat_1p, !concat_p1.
      reflexivity.
    - intros G.
      apply path_natural_transformation.
      intros x ; simpl.
      rewrite ap10_path_forall.
      rewrite ge.
      reflexivity.
    - intros G₁ G₂ G₃ F₁ F₂.
      apply path_natural_transformation.
      intro x ; simpl.
      rewrite ap10_path_forall.
      rewrite !ge.
      reflexivity.
    - intros G₁ G₂ F.
      apply path_natural_transformation.
      intros x ; simpl.
      reflexivity.
    - intros G₁ G₂ F.
      apply path_natural_transformation.
      intro ; reflexivity.
  Qed.

  Definition unit_gq
    : LaxTransformation
        (lax_id_functor grpd)
        (lax_comp path_groupoid_functor gquot_functor)
    := Build_PseudoTransformation unit_gq_d unit_gq_is_lax.

  Global Instance unit_pseudo
    : is_pseudo_transformation unit_gq
    := _.
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