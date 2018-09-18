Require Import HoTT.
From HoTT.Categories Require Import Category Functor NaturalTransformation.
Require Import GR.bicategories.bicategories.
Require Import GR.bicategories.lax_functors.
Require Import GR.bicategories.lax_transformations.
Require Import GR.bicategories.modifications.
Require Import GR.bicategories.biadjunction.biadjunction.
From GR.groupoid Require Import
     groupoid_quotient.gquot
     groupoid_quotient.gquot_functor
     groupoid_quotient.gquot_principles
     grpd_bicategory.grpd_bicategory
     path_groupoid.path_groupoid
     adjunction.unit
     adjunction.counit.
From GR.basics Require Import
     general.

Section BiAdjunction.
  Context `{Univalence}.

  Definition gquot_biadjunction_d
    : BiAdjunction_d grpd one_types
    := Build_BiAdjunction_d
         gquot_functor
         _
         path_groupoid_functor
         _
         unit_gq
         counit_gq.
  
  Definition gquot_triangle_l_map_help
             {G : groupoid}
             {a₁ a₂ : G}
             (g : G a₁ a₂)
    : path_over
        (fun h : gquot G =>
           counit_map (gquot_functor_obj G) (gquot_functor_map (unit_map G) h)
           = h) 
        (gcleq G g)
        1%path
        1%path.
  Proof.
    apply map_path_over ; apply path_to_square.
    rewrite ap_idmap.
    rewrite ap_compose.
    rewrite !gquot_rec_beta_gcleq.
    rewrite concat_1p, concat_p1.
    reflexivity.
  Qed.
  
  Definition gquot_triangle_l_map (G : grpd)
    : forall x : gquot G,
      counit_map (gquot_functor_obj G) (gquot_functor_map (unit_map G) x) = x.
  Proof.
    simple refine (gquot_ind_set _ _ _ _).
    - reflexivity.
    - intros.
      apply gquot_triangle_l_map_help.
  Defined.

  Definition gquot_triangle_l_d
    : Modification_d
        (triangle_l_lhs gquot_biadjunction_d)
        (identity_transformation gquot_functor).
  Proof.
    intros G ; cbn.
    funext x ; revert x ; simpl.
    apply gquot_triangle_l_map.
  Defined.

  Definition gquot_triangle_l_is_modification
    : is_modification gquot_triangle_l_d.
  Proof.
    intros G₁ G₂ F.
    cbn.
    rewrite !concat_1p, !concat_p1.
    rewrite <- !path_forall_pp.
    f_ap.
    refine (path_forall _ _ _).
    simple refine (gquot_ind_prop _ _ _).
    intros a ; simpl.
    rewrite !concat_1p, !ap10_path_forall.
    rewrite ap_idmap, !concat_1p.
    unfold gquot_triangle_l_map ; simpl.
    rewrite !concat_p1.
    rewrite gquot_rec_beta_gcleq.
    reflexivity.
  Qed.

  Definition gquot_triangle_l_modification
    : Modification
        (triangle_l_lhs gquot_biadjunction_d)
        (identity_transformation gquot_functor)
    := Build_Modification gquot_triangle_l_d gquot_triangle_l_is_modification.

  Definition gquot_triangle_l_is_iso
    : iso_modification gquot_triangle_l_modification.
  Proof.
    intros X ; cbn.
    apply one_types_is_21.
  Defined.

  Definition gquot_triangle_l
    : IsoModification
        (triangle_l_lhs gquot_biadjunction_d)
        (identity_transformation gquot_functor).
  Proof.
    make_iso_modification.
    - exact gquot_triangle_l_modification.
    - exact gquot_triangle_l_is_iso.
  Defined.
  
  Definition gquot_triangle_r_d
    : Modification_d
        (triangle_r_lhs gquot_biadjunction_d)
        (identity_transformation path_groupoid_functor).
  Proof.
    intros A ; simpl.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - reflexivity.
    - intros F G α ; cbn in *.
      refine (concat_p1 _ @ _ @ (concat_1p _)^).
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
  Defined.

  Definition gquot_triangle_r_is_modification
    : is_modification gquot_triangle_r_d.
  Proof.
    intros A B f.
    apply path_natural_transformation.
    intros x.
    cbn.
    rewrite ge, !concat_1p.
    rewrite !ap10_path_forall ; simpl.
    rewrite !ge ; simpl.
    reflexivity.
  Qed.

  Definition gquot_triangle_r_modification
    : Modification
        (triangle_r_lhs gquot_biadjunction_d)
        (identity_transformation path_groupoid_functor)
    := Build_Modification gquot_triangle_r_d gquot_triangle_r_is_modification.

  Global Instance gquot_triangle_r_is_iso
    : iso_modification gquot_triangle_r_modification.
  Proof.
    intros A ; simpl.
    unfold gquot_triangle_r_d ; simpl.
    apply _.
  Defined.

  Definition gquot_triangle_r
    : IsoModification
        (triangle_r_lhs gquot_biadjunction_d)
        (identity_transformation path_groupoid_functor).
  Proof.
    make_iso_modification.
    - exact gquot_triangle_r_modification.
    - exact gquot_triangle_r_is_iso.
  Defined.
  
  Definition gquot_is_biadjunction
    : is_biadjunction gquot_biadjunction_d
    := Build_is_biadjunction _ _ gquot_triangle_l gquot_triangle_r.

  Definition gquot_biadjunction
    : BiAdjunction grpd one_types
    := Build_BiAdjunction gquot_biadjunction_d gquot_is_biadjunction.
End BiAdjunction.