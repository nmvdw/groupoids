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
     lax_functor.examples.restriction
     lax_functor.examples.factor_full_sub
     lax_transformation.lax_transformation.
From GR.groupoid Require Import
     groupoid_quotient.gquot
     groupoid_quotient.gquot_functor
     groupoid_quotient.gquot_principles
     grpd_bicategory.grpd_bicategory
     path_groupoid.path_groupoid
     adjunction.unit.
From GR.basics Require Import
     general.

Definition idtoiso_map
           {C : PreCategory}
           {X Y : C}
           (p : X = Y)
  : morphism C X Y
  := Category.Morphisms.idtoiso C p.

Definition idtoiso_map_1
           {C : PreCategory}
           (X : C)
  : idtoiso_map (idpath : X = X) = 1%morphism
  := idpath.

Definition idtoiso_map_pp
           {C : PreCategory}
           {X Y Z : C}
           (p : X = Y) (q : Y = Z)
  : idtoiso_map (p @ q) = (idtoiso_map q o idtoiso_map p)%morphism.
Proof.
  rewrite Morphisms.idtoiso_comp.
  reflexivity.
Defined.

Definition transport_morphism_FlFr
           {A : Type}
           {C : PreCategory}
           (f g : A -> C)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
           (h : morphism C (f a₁) (g a₁))
  : (transport (fun x : A => morphism C (f x) (g x)) p h
     =
     (Category.Morphisms.idtoiso C (ap g p))
       o
       h
       o (Category.Morphisms.idtoiso C (ap f p)^))%morphism.
Proof.
  induction p ; simpl.
  rewrite left_identity, right_identity.
  reflexivity.
Defined.

Definition univalent_grpd_eq
           `{Univalence}
           (G : groupoid)
           `{is_univalent G}
           {x y : G}
           (g : hom G x y)
  : x = y
  := @equiv_inv _
                _
                (@Category.idtoiso G.1 x y)
                (obj_cat x y)
                (Build_Isomorphic (G.2 _ _ g)).

Definition univalent_grpd_eq_e
           `{Univalence}
           (G : groupoid)
           `{is_univalent G}
           (x : G)
  : univalent_grpd_eq G (e x) = 1%path.
Proof.
  rewrite <- (@eissect _
                       _
                       (@Category.Morphisms.idtoiso G.1 x x)
                       (obj_cat x x)).
  unfold univalent_grpd_eq.
  apply ap.
  apply path_isomorphic ; cbn.
  reflexivity.
Defined.

Definition univalent_grpd_eq_comp
           `{Univalence}
           (G : groupoid)
           `{is_univalent G}
           {x y z : G}
           (g₁ : hom G x y) (g₂ : hom G y z)
  : univalent_grpd_eq G (g₁ · g₂)
    =
    univalent_grpd_eq G g₁ @ univalent_grpd_eq G g₂.
Proof.
  rewrite <-
          (@eissect _
                    _
                    (@Category.Morphisms.idtoiso G.1 x z)
                    (obj_cat x z)
                    (univalent_grpd_eq G (g₁ · g₂))
          ).
  rewrite <-
          (@eissect _
                    _
                    (@Category.Morphisms.idtoiso G.1 x z)
                    (obj_cat x z)
                    (univalent_grpd_eq G g₁ @ univalent_grpd_eq G g₂)
          ).
  apply ap ; simpl.
  apply path_isomorphic.
  rewrite <- (idtoiso_comp G.1
                           (univalent_grpd_eq G g₂)
                           (univalent_grpd_eq G g₁)).
  rewrite !eisretr.
  reflexivity.
Defined.

Definition univalent_grpd_eq_inv
           `{Univalence}
           (G : groupoid)
           `{is_univalent G}
           {x y : G}
           (g : hom G x y)
  : univalent_grpd_eq G (inv g) = (univalent_grpd_eq G g)^.
Proof.
  rewrite <-
          (@eissect _
                    _
                    (@Category.Morphisms.idtoiso G.1 y x)
                    (obj_cat y x)
                    (univalent_grpd_eq G (inv g))
          ).
  rewrite <-
          (@eissect _
                    _
                    (@Category.Morphisms.idtoiso G.1 y x)
                    (obj_cat y x)
                    (univalent_grpd_eq G g)^
          ).
  apply ap ; simpl.
  apply path_isomorphic.
  rewrite <- (idtoiso_inv G.1 (univalent_grpd_eq G g)).
  rewrite !eisretr.
  reflexivity.
Defined.

Definition univalent_grpd_eq_functor
           `{Univalence}
           {G₁ G₂ : groupoid}
           (F : Functor G₁.1 G₂.1)
           `{is_univalent G₁} `{is_univalent G₂}
           {x y : G₁}
           (g : hom G₁ x y)
  : univalent_grpd_eq G₂ (F _1 g)%morphism
    =
    ap (Core.object_of F) (univalent_grpd_eq G₁ g).
Proof.
  rewrite <-
          (@eissect _
                    _
                    (@Category.Morphisms.idtoiso G₂.1 (F x) (F y))
                    (obj_cat (F x) (F y))
                    (univalent_grpd_eq G₂ (F _1 g)%morphism)
          ).
  rewrite <-
          (@eissect _
                    _
                    (@Category.Morphisms.idtoiso G₂.1 (F x) (F y))
                    (obj_cat (F x) (F y))
                    (ap (Core.object_of F) (univalent_grpd_eq G₁ g))
          ).
  apply ap.
  rewrite eisretr.
  pose (@idtoiso_functor G₁.1 G₂.1 x y (univalent_grpd_eq G₁ g) F) as p.
  apply Morphisms.path_isomorphic.
  rewrite <- p.
  rewrite eisretr.
  reflexivity.
Defined.

Definition idtoiso_univalent_grpd_eq
           `{Univalence}
           {G : groupoid}
           `{is_univalent G}
           {x y : G}
           (f : hom G x y)
  : idtoiso_map (univalent_grpd_eq G f) = f.
Proof.
  unfold idtoiso_map, univalent_grpd_eq.
  rewrite eisretr.
  reflexivity.
Defined.

Definition univalent_gquot `{Univalence}
  : LaxFunctor univalent_grpd one_types
  := lax_restriction
       gquot_functor
       (fun G => BuildhProp (is_univalent G)).

Definition univalent_path_groupoid `{Univalence}
  : LaxFunctor one_types univalent_grpd
  := lax_factor
       path_groupoid_functor
       (fun G => BuildhProp (is_univalent G))
       path_groupoid_univalent.

Section UnitInv.
  Context `{Univalence}.

  Definition unit_inv_map_obj (G : groupoid) `{is_univalent G}
    : gquot G -> under G.
  Proof.
    simple refine (gquot_rec _ _ _ _ _ _ (univalent_one_type G)).
    - exact idmap.
    - exact (fun _ _ => univalent_grpd_eq G).
    - exact (univalent_grpd_eq_e G).
    - exact (fun _ _ => univalent_grpd_eq_inv G).
    - exact (fun _ _ _ => univalent_grpd_eq_comp G).
  Defined.
  
  Definition unit_inv_map (G : groupoid) `{UG : is_univalent G}
    : @one_cell _
                univalent_grpd
                (univalent_path_groupoid(univalent_gquot (G;UG)))
                (G;UG).
  Proof.
    simple refine (Build_Functor _ _ _ _ _ _) ; cbn.
    - apply unit_inv_map_obj.
      apply _.
    - intros x y p ; cbn.
      exact (transport
               (fun z => morphism G.1 (unit_inv_map_obj G x) (unit_inv_map_obj G z))
               p
               (e _)).
    - intros x y z p q.
      induction p, q ; simpl.
      exact (ce _)^.
    - reflexivity.
  Defined.

  Definition unit_gq_inv_rd
    : PseudoTransformation_d
        (lax_comp univalent_path_groupoid univalent_gquot)
        (lax_id_functor univalent_grpd).
  Proof.
    simple refine (Build_PseudoTransformation_d _ _ _).
    - intros [G UG] ; simpl.
      exact (@unit_inv_map G UG).
    - intros G₁ G₂ F ; simpl.
      simple refine (Build_NaturalTransformation _ _ _ _) ; cbn.
      + simple refine (gquot_ind_set _ _ _ _).
        * intros a ; simpl.
          apply 1%morphism.
        * intros a₁ a₂ g.
          apply path_to_path_over.
          rewrite transport_morphism_FlFr.
          rewrite ap_compose ; rewrite !gquot_rec_beta_gcleq.
          rewrite ap_compose ; rewrite !gquot_rec_beta_gcleq.
          rewrite right_identity.
          destruct G₁ as [G₁ UG₁], G₂ as [G₂ UG₂].
          rewrite <- (@univalent_grpd_eq_functor _ G₁ G₂ F UG₁ UG₂).
          rewrite <- Morphisms.idtoiso_inv.
          rewrite !eisretr ; cbn.
          apply right_inverse.
      + intros x y p.
        induction p.
        revert x.
        simple refine (gquot_ind_prop _ _ _).
        intros a ; simpl.
        rewrite left_identity, right_identity, identity_of.
        reflexivity.
    - intros [G₁ UG₁] [G₂ UG₂] F ; simpl.
      simple refine (Build_NaturalTransformation _ _ _ _) ; cbn.
      + simple refine (gquot_ind_set _ _ _ _).
        * intros a ; simpl.
          apply 1%morphism.
        * intros a₁ a₂ g.
          apply path_to_path_over.
          rewrite transport_morphism_FlFr.
          rewrite ap_compose ; rewrite !gquot_rec_beta_gcleq.
          rewrite <- (@univalent_grpd_eq_functor _ G₁ G₂ F UG₁ UG₂).
          rewrite ap_compose ; rewrite !gquot_rec_beta_gcleq.
          rewrite right_identity.
          rewrite <- Morphisms.idtoiso_inv.
          rewrite !eisretr ; cbn.
          apply right_inverse.
      + intros x y p.
        induction p.
        revert x.
        simple refine (gquot_ind_prop _ _ _).
        intros a ; simpl.
        rewrite left_identity, right_identity, identity_of.
        reflexivity.
  Defined.


  Definition unit_inv_is_lax
    : is_pseudo_transformation_rd unit_gq_inv_rd.
  Proof.
    repeat split.
    - intros [G₁ UG₁] [G₂ UG₂] F₁ F₂ α.
      apply path_natural_transformation.
      intro x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intro a ; simpl in *.
      rewrite identity_of, !right_identity, !left_identity.
      unfold gquot_id.
      rewrite ap10_path_forall.
      rewrite transport_morphism_FlFr.
      rewrite right_identity, ap_const, right_identity ; simpl.
      rewrite gquot_rec_beta_gcleq.
      unfold univalent_grpd_eq.
      rewrite eisretr ; simpl.
      reflexivity.
    - intros [G UG].
      apply path_natural_transformation.
      intros x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intro a ; simpl in *.
      rewrite !left_identity, !right_identity, concat_1p.
      rewrite ap10_path_forall.
      reflexivity.
    - intros [G₁ UG₁] [G₂ UG₂] [G₃ UG₃] F₁ F₂.
      apply path_natural_transformation.
      intro x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intro a ; simpl in *.
      rewrite !right_identity, !left_identity.
      rewrite !identity_of, !concat_1p, ap10_path_forall.
      rewrite !concat_p1, !right_identity.
      simpl.
      rewrite left_identity.
      rewrite iso_component.
      apply iso_moveL_V1.
      apply left_identity.
    - intros [G₁ UG₁] [G₂ UG₂] F₁ F₂ α.
      apply path_natural_transformation.
      intros x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intros a ; simpl in *.
      rewrite identity_of, !left_identity, !right_identity.
      rewrite ap10_path_forall.
      unfold gquot_functorial_natural.
      rewrite gquot_ind_set_beta_gcl.
      rewrite transport_morphism_FlFr.
      rewrite ap_const ; simpl.
      rewrite !right_identity.
      rewrite gquot_rec_beta_gcleq.
      unfold univalent_grpd_eq.
      rewrite eisretr ; simpl.
      reflexivity.
    - intros [G₁ UG₁] [G₂ UG₂] F.
      apply path_natural_transformation.
      intros x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intros a.
      apply right_identity.
    - intros [G₁ UG₁] [G₂ UG₂] F.
      apply path_natural_transformation.
      intros x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intros a.
      apply right_identity.
  Qed.

  Definition unit_inv
    : LaxTransformation
        (lax_comp univalent_path_groupoid univalent_gquot)
        (lax_id_functor univalent_grpd)
    := Build_PseudoTransformation unit_gq_inv_rd unit_inv_is_lax.

  Global Instance unit_inv_pseudo
    : is_pseudo_transformation unit_inv.
  Proof.
    apply _.
  Defined.
End UnitInv.