Require Import HoTT.
From HoTT.Categories Require Import Category Functor NaturalTransformation.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory
     bicategory.examples.one_types
     lax_functors
     lax_transformations.
From GR.groupoid Require Import
     groupoid_quotient.gquot
     groupoid_quotient.gquot_functor
     groupoid_quotient.gquot_principles
     grpd_bicategory.grpd_bicategory
     path_groupoid.path_groupoid.
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
  : idtoiso_map (p @ q) = (idtoiso_map q o idtoiso_map p)%morphism
  := (Morphisms.idtoiso_comp _ _ _)^.

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
Qed.

Definition univalent_grpd_eq
           `{Funext}
           (G : groupoid)
           `{is_univalent G}
           {x y : G}
           (g : G x y)
  : x = y
  := @equiv_inv _
                _
                (@Category.idtoiso G.1 x y)
                (obj_cat x y)
                (Build_Isomorphic (G.2 _ _ g)).

Definition univalent_grpd_eq_e
           `{Funext}
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
Qed.

Definition univalent_grpd_eq_comp
           `{Funext}
           (G : groupoid)
           `{is_univalent G}
           {x y z : G}
           (g₁ : G x y) (g₂ : G y z)
  : univalent_grpd_eq G (g₁ ● g₂)
    =
    univalent_grpd_eq G g₁ @ univalent_grpd_eq G g₂.
Proof.
  rewrite <-
          (@eissect _
                    _
                    (@Category.Morphisms.idtoiso G.1 x z)
                    (obj_cat x z)
                    (univalent_grpd_eq G (g₁ ● g₂))
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
Qed.

Definition univalent_grpd_eq_inv
           `{Funext}
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
Qed.

Definition univalent_grpd_eq_functor
           `{Funext}
           {G₁ G₂ : groupoid}
           (F : Functor G₁.1 G₂.1)
           `{is_univalent G₁} `{is_univalent G₂}
           {x y : G₁}
           (g : G₁ x y)
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
Qed.

Definition idtoiso_univalent_grpd_eq
           `{Funext}
           {G : groupoid}
           `{is_univalent G}
           {x y : G}
           (f : G x y)
  : idtoiso_map (univalent_grpd_eq G f) = f.
Proof.
  unfold idtoiso_map, univalent_grpd_eq.
  rewrite eisretr.
  reflexivity.
Qed.

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

  Definition unit_inv_map_one (G : groupoid) `{is_univalent G}
    : gquot G -> G.
  Proof.
    simple refine (gquot_rec _ _ _ _ _).
    - exact idmap.
    - exact (fun _ _ => univalent_grpd_eq G).
    - exact (univalent_grpd_eq_e G).
    - exact (fun _ _ _ => univalent_grpd_eq_comp G).
  Defined.
  
  Definition unit_inv_map_two
             (G : groupoid) 
             `{is_univalent G}
             (x y : gquot G)
             (p : x = y)
    : G (unit_inv_map_one G x) (unit_inv_map_one G y)
    := transport
         (fun z => morphism G.1 (unit_inv_map_one G x) (unit_inv_map_one G z))
         p
         (e _).

  Definition unit_inv_map_two_concat
             (G : groupoid) 
             `{is_univalent G}
             (x y z : gquot G)
             (p : x = y) (q : y = z)
    : unit_inv_map_two G x z (p @ q)
      =
      (unit_inv_map_two G y z q o unit_inv_map_two G x y p)%morphism.
  Proof.
    induction p, q.
    exact (grpd_right_identity _)^.
  Qed.
                                                              
  Definition unit_inv_map (G : groupoid) `{UG : is_univalent G}
    : univalent_grpd⟦univalent_path_groupoid(univalent_gquot (G;UG)),(G;UG)⟧.
  Proof.
    simple refine (Build_Functor _ _ _ _ _ _).
    - exact (unit_inv_map_one G).
    - exact (unit_inv_map_two G).
    - exact (unit_inv_map_two_concat G).
    - reflexivity.
  Defined.

  Definition unit_inv_naturality_map_po
             {G₁ G₂ : groupoid}
             `{is_univalent G₁} `{is_univalent G₂}
             (F : Functor G₁.1 G₂.1)
             (x y : G₁)
             (g : G₁ x y)
    : path_over
        (fun h : gquot G₁ =>
           Core.morphism
             G₂.1
             (F (unit_inv_map_one G₁ h))
             (unit_inv_map_one G₂ (gquot_functor_map F h)))
        (gcleq G₁ g)
        1%morphism
        1%morphism.
  Proof.
    apply path_to_path_over.
    rewrite transport_morphism_FlFr.
    rewrite ap_compose ; rewrite !gquot_rec_beta_gcleq.
    rewrite ap_compose ; rewrite !gquot_rec_beta_gcleq.
    rewrite right_identity.
    rewrite <- (@univalent_grpd_eq_functor _ G₁ G₂ F _ _).
    rewrite <- Morphisms.idtoiso_inv.
    rewrite !eisretr.
    apply right_inverse.
  Qed.

  Definition unit_inv_naturality_map
             {G₁ G₂ : grpd}
             `{is_univalent G₁} `{is_univalent G₂}
             (F : Functor G₁.1 G₂.1)
    : forall c : gquot G₁,
      Core.morphism G₂.1
                    (F (unit_inv_map_one G₁ c))
                    (unit_inv_map_one G₂ (gquot_functor_map F c)).
  Proof.
    simple refine (gquot_ind_set _ _ _ _).
    - intros a ; simpl.
      apply 1%morphism.
    - apply unit_inv_naturality_map_po.
  Defined.

  Definition unit_inv_naturality_commute
             {G₁ G₂ : grpd}
             `{is_univalent G₁} `{is_univalent G₂}
             (F : Functor G₁.1 G₂.1)
             (x y : gquot G₁)
             (p : x = y)
    : ((unit_inv_naturality_map F y o F _1 (unit_inv_map_two G₁ x y p))
      =
      (unit_inv_map_two G₂ (gquot_functor_map F x) (gquot_functor_map F y)
                        (ap (gquot_functor_map F) p) o unit_inv_naturality_map F x)
      )%morphism.
  Proof.
    induction p.
    revert x.
    simple refine (gquot_ind_prop _ _ _).
    intros a ; simpl.
    refine (left_identity _ _ _ _ @ _ @ (right_identity _ _ _ _)^).
    apply identity_of.
  Qed.
  
  Definition unit_inv_naturality
             {G₁ G₂ : univalent_grpd}
             (F : Hom univalent_grpd G₁ G₂)
    : (Core.NaturalTransformation
         (((Fmor (lax_id_functor univalent_grpd)) _ _ F)
            o unit_inv_map G₁.1)
         ((unit_inv_map G₂.1)
            o (Fmor (lax_comp univalent_path_groupoid univalent_gquot)) _ _ F))%morphism.
  Proof.
    destruct G₁ as [G₁ UG₁] ; destruct G₂ as [G₂ UG₂].
    simple refine (Build_NaturalTransformation _ _ _ _).
    - exact (unit_inv_naturality_map F).
    - exact (unit_inv_naturality_commute F).
  Defined.

  Definition unit_inv_naturality_map_inv_po
             {G₁ G₂ : groupoid}
             `{is_univalent G₁} `{is_univalent G₂}
             (F : Functor G₁.1 G₂.1)
             (x y : G₁)
             (g : G₁ x y)
    : path_over
        (fun h : gquot G₁ =>
           Core.morphism
             G₂.1
             (unit_inv_map_one G₂ (gquot_functor_map F h))
             (F (unit_inv_map_one G₁ h)))
        (gcleq G₁ g)
        1%morphism
        1%morphism.
  Proof.
    apply path_to_path_over.
    rewrite transport_morphism_FlFr.
    rewrite ap_compose ; rewrite !gquot_rec_beta_gcleq.
    rewrite <- (@univalent_grpd_eq_functor _ G₁ G₂ F _ _).
    rewrite ap_compose ; rewrite !gquot_rec_beta_gcleq.
    rewrite right_identity.
    rewrite <- Morphisms.idtoiso_inv.
    rewrite !eisretr ; cbn.
    apply right_inverse.
  Qed.

  Definition unit_inv_naturality_map_inv
             {G₁ G₂ : grpd}
             `{is_univalent G₁} `{is_univalent G₂}
             (F : Functor G₁.1 G₂.1)
    : forall c : gquot G₁,
      Core.morphism G₂.1
                    (unit_inv_map_one G₂ (gquot_functor_map F c))
                    (F (unit_inv_map_one G₁ c)).
  Proof.
    simple refine (gquot_ind_set _ _ _ _).
    - intros a ; simpl.
      apply 1%morphism.
    - apply unit_inv_naturality_map_inv_po.
  Defined.

  Definition unit_inv_naturality_inv_commute
             {G₁ G₂ : grpd}
             `{is_univalent G₁} `{is_univalent G₂}
             (F : Functor G₁.1 G₂.1)
             (x y : gquot G₁)
             (p : x = y)
    : ((unit_inv_naturality_map_inv F y)
         o (unit_inv_map_two
              G₂
              (gquot_functor_map F x)
              (gquot_functor_map F y)
              (ap (gquot_functor_map F) p)))%morphism
      =
      (F _1 (unit_inv_map_two G₁ x y p)
         o unit_inv_naturality_map_inv F x)%morphism.
  Proof.
    induction p.
    revert x.
    simple refine (gquot_ind_prop _ _ _).
    intros a ; simpl.
    refine (left_identity _ _ _ _ @ _ @ (right_identity _ _ _ _)^).
    exact (identity_of _ _)^.
  Qed.
  
  Definition unit_inv_naturality_inv
             {G₁ G₂ : univalent_grpd}
             (F : Hom univalent_grpd G₁ G₂)
    : (Core.NaturalTransformation
         ((unit_inv_map G₂.1)
            o (Fmor (lax_comp univalent_path_groupoid univalent_gquot)) _ _ F)
         (((Fmor (lax_id_functor univalent_grpd)) _ _ F)
            o unit_inv_map G₁.1))%morphism.
  Proof.
    destruct G₁ as [G₁ UG₁] ; destruct G₂ as [G₂ UG₂].
    simple refine (Build_NaturalTransformation _ _ _ _).
    - exact (unit_inv_naturality_map_inv F).
    - exact (unit_inv_naturality_inv_commute F).
  Defined.

  Definition unit_gq_inv_d
    : PseudoTransformation_d
        (lax_comp univalent_path_groupoid univalent_gquot)
        (lax_id_functor univalent_grpd).
  Proof.
    make_pseudo_transformation.
    - intros [G UG].
      exact (@unit_inv_map G UG).
    - exact (fun _ _ => unit_inv_naturality).
    - exact (fun _ _ => unit_inv_naturality_inv).
  Defined.

  Definition unit_inv_is_lax
    : is_pseudo_transformation_p unit_gq_inv_d.
  Proof.
    make_is_pseudo_transformation.
    - intros G₁ G₂ F₁ F₂ α.
      apply path_natural_transformation.
      intro x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intro a ; cbn.
      rewrite identity_of, !right_identity, !left_identity.      
      rewrite ap10_path_forall.
      unfold unit_inv_map_two ; simpl.
      rewrite transport_morphism_FlFr.
      rewrite right_identity, ap_const, right_identity ; simpl.
      rewrite gquot_rec_beta_gcleq.
      unfold univalent_grpd_eq.
      rewrite eisretr ; simpl.
      reflexivity.
    - intros G.
      apply path_natural_transformation.
      intros x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intro a ; cbn.
      rewrite !left_identity, !right_identity, concat_1p.
      rewrite ap10_path_forall.
      reflexivity.
    - intros G₁ G₂ G₃ F₁ F₂.
      apply path_natural_transformation.
      intro x ; revert x.
      refine (@gquot_ind_prop _ _ _ (fun a => istrunc_paths _ _ _ _)).
      intro a ; cbn.
      rewrite !right_identity, !left_identity.
      rewrite !identity_of, !concat_1p, ap10_path_forall.
      simpl.
      rewrite !right_identity.
      reflexivity.
    - intros G₁ G₂ F.
      apply path_natural_transformation.
      intros x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intros a.
      apply right_identity.
    - intros G₁ G₂ F.
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
    := Build_PseudoTransformation unit_gq_inv_d unit_inv_is_lax.

  Global Instance unit_inv_pseudo
    : is_pseudo_transformation unit_inv
    := _.
End UnitInv.