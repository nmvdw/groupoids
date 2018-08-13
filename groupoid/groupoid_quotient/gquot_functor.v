Require Import HoTT.
From HoTT.Categories Require Import
     Functor NaturalTransformation.
From GR.basics Require Import
     general.
From GR.bicategories.bicategory Require Import
     bicategory.
From GR.bicategories.bicategory.examples Require Import
     one_types precat.
From GR.bicategories.lax_functor Require Import
     lax_functor.
From GR.groupoid.groupoid_quotient Require Export
     gquot.
From GR.groupoid Require Import
     grpd_bicategory.grpd_bicategory
     groupoid_quotient.gquot_principles.

Section GQuotFunctor.
  Context `{Funext}.
  
  Definition gquot_functor_obj (G : groupoid)
    : 1 -Type
    := BuildTruncType 1 (gquot G).

  Definition gquot_functor_map
             {G₁ G₂ : grpd}
             (F : Functor G₁.1 G₂.1)
    : gquot_functor_obj G₁ -> gquot_functor_obj G₂.
  Proof.
    simple refine (gquot_rec _ _ _ _ _ _ _).
    - exact (fun g => gcl G₂ (F g)).
    - exact (fun _ _ g => gcleq G₂ (morphism_of F g)).
    - exact (fun a => ap (gcleq G₂) (identity_of F _) @ ge _ _).
    - exact (fun _ _ g => ap (gcleq G₂) (grpd_inverse_of F _) @ ginv _ _).
    - exact (fun _ _ _ g₁ g₂ => ap (gcleq G₂) (composition_of F _ _ _ g₁ g₂)
                                   @ gconcat _ _ _).
  Defined.

  Definition gquot_functor_map_natural_po
             {G₁ G₂ : groupoid}
             {F₁ F₂ : Functor G₁.1 G₂.1}
             (α : NaturalTransformation F₁ F₂)
             {x₁ x₂ : G₁}
             (g : G₁ x₁ x₂)
    : path_over
        (fun h : gquot G₁ => gquot_functor_map F₁ h = gquot_functor_map F₂ h)
        (gcleq G₁ g)
        (gcleq G₂ (α x₁))
        (gcleq G₂ (α x₂)).
  Proof.
    apply map_path_over.
    refine (whisker_square idpath
                           _
                           _
                           idpath
                           _).
    - exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _)^.
    - exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _)^.
    - apply path_to_square.
      refine ((gconcat _ _ _)^ @ ap (gcleq G₂) _ @ gconcat _ _ _).
      exact (commutes α _ _ g).
  Qed.

  Definition gquot_functor_map_natural
             {G₁ G₂ : grpd}
             {F₁ F₂ : Functor G₁.1 G₂.1}
             (α : NaturalTransformation F₁ F₂)
    : forall (x : gquot G₁),
      gquot_functor_map F₁ x = gquot_functor_map F₂ x.
  Proof.
    simple refine (gquot_ind_set _ _ _ _).
    - exact (fun x => gcleq G₂ (α x)).
    - apply gquot_functor_map_natural_po.
  Defined.

  Definition gquot_functor_map_compose_po
             {G₁ G₂ G₃ : groupoid}
             (F₂ : Functor G₂.1 G₃.1)
             (F₁ : Functor G₁.1 G₂.1)
             {x₁ x₂ : under G₁}
             (g : G₁ x₁ x₂)
    : path_over
        (fun h : gquot G₁ =>
           (gquot_functor_map F₂ o gquot_functor_map F₁) h
           =
           gquot_functor_map (F₂ o F₁) h)
        (gcleq G₁ g)
        idpath
        idpath.
  Proof.
    apply map_path_over.
    refine (whisker_square idpath
                           _
                           _
                           idpath
                           _).
    - unfold gquot_functor_map.
      refine (_ @ (ap_compose _ _ _)^).
      refine (_ @ ap (ap _) (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _)^).
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _)^.
    - exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _)^.
    - apply vrefl.
  Qed.
  
  Definition gquot_functor_map_compose
             {G₁ G₂ G₃ : grpd}
             (F₂ : Functor G₂.1 G₃.1)
             (F₁ : Functor G₁.1 G₂.1)
    : forall (x : gquot G₁),
      (gquot_functor_map F₂ o gquot_functor_map F₁) x
      =
      gquot_functor_map (F₂ o F₁)%functor x.
  Proof.
    simple refine (gquot_ind_set _ _ _ _).
    - reflexivity.
    - apply gquot_functor_map_compose_po.
  Defined.

  Definition gquot_functor_map_id_po
             (G : groupoid)
             {x₁ x₂ : G}
             (g : G x₁ x₂)
    : path_over
        (fun h : gquot G => h = gquot_functor_map 1 h)
        (gcleq G g)
        idpath
        idpath.
  Proof.
    apply map_path_over.
    refine (whisker_square idpath
                           ((ap_idmap _)^)
                           _
                           idpath
                           (vrefl _)).
    exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _)^.
  Qed.

  Definition gquot_functor_map_id (G : grpd)
    : forall (x : gquot G),
      x = gquot_functor_map 1%functor x.
  Proof.
    simple refine (gquot_ind_set _ _ _ _).
    - reflexivity.
    - apply gquot_functor_map_id_po.
  Defined.

  Definition gquot_functor_rd
    : PseudoFunctor_d grpd one_types.
  Proof.
    make_pseudo_functor.
    - exact gquot_functor_obj.
    - intros ? ? F; cbn.
      exact (gquot_functor_map F).
    - intros G₁ G₂ F₁ F₂ α ; cbn in *.
      funext x ; revert x.
      exact (gquot_functor_map_natural α).
    - intros G₁ G₂ G₃ F₁ F₂ ; cbn.
      funext x ; revert x.
      exact (gquot_functor_map_compose F₁ F₂).
    - intros G ; cbn.
      funext x ; revert x.
      exact (gquot_functor_map_id G).
    - intros G₁ G₂ G₃ F₁ F₂ ; cbn.
      funext x.
      exact (gquot_functor_map_compose F₁ F₂ x)^.
    - intros G ; cbn.
      funext x.
      exact (gquot_functor_map_id G x)^.
  Defined.

  Definition gquot_functor_rd_is_pseudo
    : is_pseudo_functor_p gquot_functor_rd.
  Proof.
    make_is_pseudo.
    - intros X Y f ; cbn in *.
      rewrite <- path_forall_1.
      f_ap.
      funext x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intros a ; simpl.
      apply ge.
    - intros G₁ G₂ F₁ F₂ F₃ α₁ α₂ ; cbn in *.
      rewrite <- !path_forall_pp.
      f_ap.
      funext x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intros a ; simpl.
      apply gconcat.
    - intros G₁ G₂ G₃ F₁ F₂ F₃ F₄ α₁ α₂ ; cbn in *.
      rewrite <- !path_forall_pp.
      f_ap.
      funext x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intros a ; simpl.
      rewrite !ap10_path_forall ; simpl.
      rewrite gquot_rec_beta_gcleq.
      rewrite concat_1p, concat_p1.
      rewrite <- gconcat.
      f_ap.
      apply α₂.
    - intros G₁ G₂ f ; cbn.
      rewrite <- !path_forall_pp.
      rewrite <- path_forall_1.
      f_ap.
      funext x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intros a ; simpl.
      rewrite !concat_1p.
      rewrite ap10_path_forall ; simpl.
      rewrite concat_1p, ge.
      reflexivity.
    - intros G₁ G₂ F ; cbn.
      rewrite <- !path_forall_pp.
      rewrite <- path_forall_1.
      f_ap.
      funext x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intros a ; simpl.
      rewrite ap10_path_forall ; simpl.
      rewrite ge.
      reflexivity.
    - intros G₁ G₂ G₃ G₄ F₁ F₂ F₃ ; cbn.
      rewrite <- path_forall_1.
      rewrite <- !path_forall_pp.
      f_ap.
      funext x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intros a ; simpl.
      rewrite !ap10_path_forall ; simpl.
      rewrite ge.
      reflexivity.
    - intros G₁ G₂ G₃ F₁ F₂ ; cbn.
      rewrite path_forall_V.
      apply concat_pV.
    - intros G₁ G₂ G₃ F₁ F₂ ; cbn.
      rewrite path_forall_V.
      apply concat_Vp.
    - intros G ; cbn.
      rewrite path_forall_V.
      apply concat_Vp.
    - intros G ; cbn.
      rewrite path_forall_V.
      apply concat_pV.
  Qed.

  Definition gquot_functor
    : LaxFunctor grpd one_types
    := Build_PseudoFunctor gquot_functor_rd gquot_functor_rd_is_pseudo.

  Global Instance gquot_functor_pseudo
    : is_pseudo gquot_functor
    := _.
End GQuotFunctor.