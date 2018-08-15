Require Import HoTT.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory
     bicategory.examples.one_types
     bicategory.equivalence
     biadjunction.biadjunction
     lax_functor.lax_functor
     lax_functor.examples.identity
     lax_functor.examples.composition
     lax_transformation.lax_transformation
     lax_transformation.transformation_category
     lax_transformation.examples.identity
     lax_transformation.examples.composition
     lax_transformation.examples.right_identity
     lax_transformation.examples.left_identity
     lax_transformation.examples.associativity
     lax_transformation.examples.right_identity_inv
     lax_transformation.examples.left_identity_inv
     lax_transformation.examples.associativity_inv
     lax_transformation.examples.whisker_R
     lax_transformation.examples.whisker_L.
From GR.bicategories Require Import
     modification.modification
     modification.examples.identity
     modification.examples.composition.
From GR.groupoid Require Import
     groupoid_quotient.gquot
     groupoid_quotient.gquot_functor
     groupoid_quotient.gquot_principles
     grpd_bicategory.grpd_bicategory
     path_groupoid.path_groupoid
     adjunction.unit
     adjunction.counit
     adjunction.counit_inv.
From GR.basics Require Import
     general.

Section BiAdjunction.
  Context `{Funext}.

  Definition gquot_biadjunction_d
    : BiAdjunction_d grpd one_types
    := Build_BiAdjunction_d gquot_functor _ path_groupoid_functor _ unit_gq counit_gq.
  
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
    : modification_d
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
    funext x ; revert x.
    simple refine (gquot_ind_prop _ _ _).
    intros a ; simpl.
    rewrite !concat_1p, !ap10_path_forall.
    rewrite ap_idmap, !concat_1p.
    unfold gquot_triangle_l_map ; simpl.
    rewrite !concat_p1.
    rewrite gquot_rec_beta_gcleq.
    reflexivity.
  Qed.

  Definition gquot_triangle_l
    : modification
        (triangle_l_lhs gquot_biadjunction_d)
        (identity_transformation gquot_functor)
    := Build_Modification gquot_triangle_l_d gquot_triangle_l_is_modification.

  Global Instance gquot_triangle_l_is_pseudo
    : is_pseudo_modification gquot_triangle_l.
  Proof.
    split.
    intros ; cbn.
    apply one_types_is_21.
  Defined.
  
  Definition gquot_triangle_r_d
    : modification_d
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

  Definition gquot_triangle_r
    : modification
        (triangle_r_lhs gquot_biadjunction_d)
        (identity_transformation path_groupoid_functor)
    := Build_Modification gquot_triangle_r_d gquot_triangle_r_is_modification.

  Global Instance gquot_triangle_r_is_pseudo
    : is_pseudo_modification gquot_triangle_r.
  Proof.
    split.
    intros A ; simpl.
    unfold gquot_triangle_r_d ; simpl.
    apply _.
  Defined.
  
  Definition gquot_is_biadjunction
    : is_biadjunction gquot_biadjunction_d
    := Build_is_biadjunction _ _ gquot_triangle_l _ gquot_triangle_r _.

  Definition gquot_biadjunction
    : BiAdjunction grpd one_types
    := Build_BiAdjunction gquot_biadjunction_d gquot_is_biadjunction.
End BiAdjunction.