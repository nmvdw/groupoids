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
  Context `{Univalence}.

  Definition gquot_functor_rd_obj (G : groupoid)
    : 1 -Type
    := BuildTruncType 1 (gquot G).

  Definition gquot_functor_rd_map
             {G₁ G₂ : grpd}
             (F : Functor G₁.1 G₂.1)
    : gquot_functor_rd_obj G₁ -> gquot_functor_rd_obj G₂.
  Proof.
    simple refine (gquot_rec _ _ _ _ _ _ _).
    - exact (fun g => gcl G₂ (F g)).
    - exact (fun _ _ g => gcleq G₂ (morphism_of F g)).
    - exact (fun a => ap (gcleq G₂) (identity_of F _) @ ge _ _).
    - exact (fun _ _ g => ap (gcleq G₂) (grpd_inverse_of F _) @ ginv _ _).
    - exact (fun _ _ _ g₁ g₂ => ap (gcleq G₂) (composition_of F _ _ _ g₁ g₂)
                                   @ gconcat _ _ _).
  Defined.

  Definition gquot_functor_rd_map_natural_po
             {G₁ G₂ : grpd}
             {F₁ F₂ : Functor G₁.1 G₂.1}
             (α : NaturalTransformation F₁ F₂)
             {x₁ x₂ : under G₁}
             (g : hom G₁ x₁ x₂)
    : path_over
        (fun h : gquot G₁ => gquot_functor_rd_map F₁ h = gquot_functor_rd_map F₂ h)
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

  Definition gquot_functor_rd_map_natural
             {G₁ G₂ : grpd}
             {F₁ F₂ : Functor G₁.1 G₂.1}
             (α : NaturalTransformation F₁ F₂)
    : forall (x : gquot G₁),
      gquot_functor_rd_map F₁ x = gquot_functor_rd_map F₂ x.
  Proof.
    simple refine (gquot_ind_set _ _ _ _).
    - exact (fun x => gcleq G₂ (α x)).
    - apply gquot_functor_rd_map_natural_po.
  Defined.

  Definition gquot_functor_rd_map_compose_po
             {G₁ G₂ G₃ : grpd}
             (F₂ : Functor G₂.1 G₃.1)
             (F₁ : Functor G₁.1 G₂.1)
             {x₁ x₂ : under G₁}
             (g : hom G₁ x₁ x₂)
    : path_over
        (fun h : gquot G₁ =>
           (gquot_functor_rd_map F₂ o gquot_functor_rd_map F₁) h
           =
           gquot_functor_rd_map (F₂ o F₁) h)
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
    - unfold gquot_functor_rd_map.
      refine (_ @ (ap_compose _ _ _)^).
      refine (_ @ ap (ap _) (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _)^).
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _)^.
    - exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _)^.
    - apply vrefl.
  Qed.
  
  (** SLOW, 10 sec for defined *)
  Definition gquot_functor_rd_map_compose
             {G₁ G₂ G₃ : grpd}
             (F₂ : Functor G₂.1 G₃.1)
             (F₁ : Functor G₁.1 G₂.1)
    : forall (x : gquot G₁),
      (gquot_functor_rd_map F₂ o gquot_functor_rd_map F₁) x
      =
      gquot_functor_rd_map (F₂ o F₁)%functor x.
  Proof.
    simple refine (gquot_ind_set _ _ _ _).
    - reflexivity.
    - apply gquot_functor_rd_map_compose_po.
  Defined.

  Definition gquot_functor_rd_map_id_po
             (G : grpd)
             {x₁ x₂ : under G}
             (g : hom G x₁ x₂)
    : path_over
        (fun h : gquot G => h = gquot_functor_rd_map 1 h)
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

  Definition gquot_functor_rd_map_id (G : grpd)
    : forall (x : gquot G),
      x = gquot_functor_rd_map 1%functor x.
  Proof.
    simple refine (gquot_ind_set _ _ _ _).
    - reflexivity.
    - apply gquot_functor_rd_map_id_po.
  Defined.

  Definition gquot_functor_rd
    : PseudoFunctor_rd grpd one_types.
  Proof.
    simple refine (Build_PseudoFunctor_rd _ _ _ _ _ _ _).
    - exact gquot_functor_rd_obj.
    - intros ? ? F; cbn.
      exact (gquot_functor_rd_map F).
    - intros G₁ G₂ F₁ F₂ α ; cbn in *.
      funext x ; revert x.
      exact (gquot_functor_rd_map_natural α).
    - intros G₁ G₂ G₃ F₁ F₂ ; cbn.
      funext x ; revert x.
      exact (gquot_functor_rd_map_compose F₁ F₂).
    - intros G ; cbn.
      funext x ; revert x.
      exact (gquot_functor_rd_map_id G).
    - intros G₁ G₂ G₃ F₁ F₂ ; cbn.
      funext x.
      exact (gquot_functor_rd_map_compose F₁ F₂ x)^.
    - intros G ; cbn.
      funext x.
      exact (gquot_functor_rd_map_id G x)^.
  Defined.

  Definition gquot_functor_rd_is_pseudo
    : is_pseudo_functor_d gquot_functor_rd.
  Proof.
    repeat split.
    - intros X Y f ; simpl.
      rewrite <- path_forall_1.
      f_ap.
      funext x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intros a ; simpl.
      apply ge.
    - intros G₁ G₂ F₁ F₂ F₃ α₁ α₂ ; simpl.
      rewrite <- path_forall_pp.
      f_ap.
      funext x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intros a ; simpl.
      apply gconcat.
    - intros G₁ G₂ G₃ F₁ F₂ F₃ F₄ α₁ α₂ ; unfold hcomp ; simpl.
      rewrite ap_postcompose, ap_precompose.
      refine (_ @ path_forall_pp _ _ _ _ _).
      refine (ap (fun z => z @ _) (path_forall_pp _ _ _ _ _)^ @ _).
      refine ((path_forall_pp _ _ _ _ _)^ @ _).
      f_ap.
      funext x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intros a ; simpl.
      rewrite concat_p1, concat_1p, gquot_rec_beta_gcleq, <- gconcat.
      f_ap.
      apply α₂.
    - intros G₁ G₂ f ; cbn.
      rewrite concat_1p, ap_precompose.
      symmetry.
      refine (_ @ path_forall_1 _).
      refine (ap (fun z => _ @ z) (path_forall_pp _ _ _ _ _)^ @ _).
      refine ((path_forall_pp _ _ _ _ _)^ @ _).
      f_ap.
      funext x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intros a ; simpl.
      rewrite !concat_1p.
      apply ge.
    - intros G₁ G₂ F ; cbn.
      rewrite concat_p1, ap_postcompose.
      symmetry.
      refine (_ @ path_forall_1 _).
      refine (ap (fun z => _ @ z) (path_forall_pp _ _ _ _ _)^ @ _).
      refine ((path_forall_pp _ _ _ _ _)^ @ _).
      f_ap.
      funext x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intros a ; simpl.
      rewrite !concat_1p.
      apply ge.
    - intros G₁ G₂ G₃ G₄ F₁ F₂ F₃ ; cbn.
      rewrite !concat_1p, !concat_p1, !ap_precompose, !ap_postcompose.
      rewrite <- !path_forall_pp.
      f_ap.
      funext x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intros a ; simpl.
      rewrite !concat_1p.
      symmetry.
      apply ge.
    - intros G₁ G₂ G₃ F₁ F₂ ; cbn.
      rewrite path_forall_V.
      apply concat_pV.
    - intros G₁ G₂ G₃ F₁ F₂ ; cbn.
      rewrite path_forall_V.
      apply concat_Vp.
    - intros G ; cbn.
      rewrite path_forall_V.
      apply concat_pV.
    - intros G ; cbn.
      rewrite path_forall_V.
      apply concat_Vp.
    - intros G₁ G₂ G₃ F₁ F₂ F₃ F₄ α₁ α₂ ; cbn.
      rewrite ap_postcompose, ap_precompose.
      rewrite <- !path_forall_pp.
      f_ap.
      funext x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intro a ; simpl.
      rewrite concat_1p, concat_p1, gquot_rec_beta_gcleq, <- gconcat.
      apply ap.
      apply α₁.
  Qed.

  Definition gquot_functor
    : LaxFunctor grpd one_types
    := Build_PseudoFunctor gquot_functor_rd gquot_functor_rd_is_pseudo.

  Global Instance gquot_functor_pseudo
    : is_pseudo_functor gquot_functor.
  Proof.
    apply _.
  Defined.
End GQuotFunctor.
    
(*
    Definition gquot_functorial
               `{Univalence}
               {G₁ G₂ : groupoid}
               (F : grpd_functor G₁ G₂)
      : gquot G₁ -> gquot G₂.
    Proof.
      simple refine (gquot_rec _ _ _ _ _ _ _).
      - exact (fun x => gcl _ (object_of F x)).
      - intros x₁ x₂ g ; cbn.
        exact (gcleq _ (morphism_of F g)).
      - intros x ; cbn.
        refine (ap (gcleq G₂) (identity_of F x) @ _). 
        apply ge.
      - intros x₁ x₂ g ; cbn.
        refine (ap (gcleq G₂) (grpd_inverse_of F g) @ _).
        apply ginv.
      - intros x₁ x₂ x₃ g₁ g₂ ; cbn.
        refine (ap (gcleq G₂) (grpd_composition_of F g₁ g₂) @ _).
        apply gconcat.   
    Defined.

    Definition gquot_functorial_natural
               `{Univalence}
               {G₁ G₂ : groupoid}
               {F₁ F₂ : grpd_functor G₁ G₂}
               (p : NaturalTransformation F₁ F₂)
      : forall (x : gquot G₁), gquot_functorial F₁ x = gquot_functorial F₂ x.
    Proof.
      simple refine (gquot_ind_set _ _ _ _).
      - intros a ; simpl.
        apply gcleq.
        apply p.
      - intros a b g ; simpl.
        apply map_path_over.
        refine (whisker_square
                  idpath
                  ((gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _)^)
                  ((gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _)^)
                  idpath
                  _).
        apply path_to_square.
        refine ((gconcat _ _ _)^ @ ap (gcleq G₂) _ @ gconcat _ _ _).
        exact (commutes p a b g).
    Defined.

    Definition gquot_map `{Univalence} (G₁ G₂ : groupoid)
      : Functor (Hom grpd G₁ G₂) (Hom one_types (gquot_o G₁) (gquot_o G₂)).
    Proof.
      simple refine (Build_Functor _ _ _ _ _ _).
      - intros F ; exact (gquot_functorial F).
      - intros ? ? α.
        funext x.
        exact (gquot_functorial_natural α x).
      - simpl ; intros f g h p q.
        refine (_ @ path_forall_pp _ _ _ _ _).
        apply ap.
        funext x ; revert x.
        simple refine (gquot_ind_prop _ _ _).
        intros a.
        apply gconcat.
      - simpl ; intros f.
        refine (_ @ path_forall_1 _).
        apply ap.
        funext x ; revert x.
        simple refine (gquot_ind_prop _ _ _).
        intros a.
        apply ge.
    Defined.

    Definition gquot_functorial_compose
               `{Univalence}
               {G₁ G₂ G₃ : grpd}
               (F₂ : grpd_functor G₂ G₃)
               (F₁ : grpd_functor G₁ G₂)
      : forall x : gquot G₁,
        gquot_functorial F₂ (gquot_functorial F₁ x) = gquot_functorial (F₂ o F₁)%functor x.
    Proof.
      simple refine (gquot_ind_set _ _ _ _).
      - intros a ; simpl.
        reflexivity.
      - intros ? ? g ; simpl.
        apply map_path_over.
        refine (whisker_square
                  idpath
                  _
                  ((gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _)^)
                  idpath
                  _).
        + refine (_ @ (ap_compose _ _ _)^).
          refine (_ @ ap (ap (gquot_functorial F₂))
                    (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _)^).
          apply (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _)^.
        + apply path_to_square.
          exact (concat_p1 _ @ (concat_1p _)^).
    Defined.

    Definition gquot_compose
               `{Univalence}
               (G₁ G₂ G₃ : groupoid)
      : NaturalTransformation
          (c_m o (gquot_map G₂ G₃, gquot_map G₁ G₂))
          (gquot_map G₁ G₃ o c_m).
    Proof.
      simple refine (Build_NaturalTransformation _ _ _ _).
      - simpl ; intros [F₂ F₁].
        funext x ; revert x.
        apply gquot_functorial_compose.
      - intros [F₂ F₁] [F₄ F₃] [α₂ α₁] ; simpl in *.
        refine (_ @ path_forall_pp _ _ _ _ _).
        rewrite ap_precompose, ap_postcompose.
        rewrite <- !path_forall_pp.
        apply ap.
        funext x ; revert x.
        simple refine (gquot_ind_prop _ _ _).
        intros a.
        refine (concat_p1 _ @ _ @ (concat_1p _)^).
        rewrite gquot_rec_beta_gcleq.
        rewrite <- gconcat.
        simpl ; apply ap.
        apply α₂.
    Defined.

    Global Instance gquot_compose_iso `{Univalence} (G₁ G₂ G₃ : groupoid)
      : @IsIsomorphism (_ -> _) _ _ (gquot_compose G₁ G₂ G₃).
    Proof.
      simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
      - simple refine (Build_NaturalTransformation _ _ _ _).
        + intros [F₂ F₁] ; simpl in *.
          funext x.
          symmetry.
          apply gquot_functorial_compose.
        + intros [F₂ F₁] [F₄ F₃] [α₂ α₁] ; simpl in *.
          rewrite ap_precompose, ap_postcompose.
          rewrite <- !path_forall_pp.
          apply ap.
          funext x ; revert x.
          simple refine (gquot_ind_prop _ _ _).
          intros a.
          refine (concat_p1 _ @ _ @ (concat_1p _)^).
          rewrite gquot_rec_beta_gcleq.
          rewrite <- gconcat.
          simpl ; apply ap.
          apply α₂.
      - apply path_natural_transformation.
        intros F ; simpl in *.
        rewrite <- ! path_forall_pp, <- path_forall_1.
        apply ap.
        funext x ; revert x.
        simple refine (gquot_ind_prop _ _ _).
        intros a.
        reflexivity.
      - apply path_natural_transformation.
        intros F ; simpl in *.
        rewrite <- ! path_forall_pp, <- path_forall_1.
        apply ap.
        funext x ; revert x.
        simple refine (gquot_ind_prop _ _ _).
        intros a.
        reflexivity.
    Defined.

    Definition gquot_functorial_idmap
               `{Univalence}
               (G : groupoid)
      : forall (x : gquot G), x = gquot_functorial 1%functor x.
    Proof.
      simple refine (gquot_ind_set _ _ _ _).
      - reflexivity.
      - intros ; simpl.
        apply map_path_over.
        refine (whisker_square idpath
                               (ap_idmap _)^
                ((gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _)^)
                  idpath
                  _).
        apply vrefl.
    Defined.

    Definition gquot_id `{Univalence} (G : groupoid)
      : (idmap : gquot G -> gquot G) = gquot_functorial 1%functor
      := path_forall _ _ (gquot_functorial_idmap G).

    Global Instance gquot_id_iso `{Univalence} (G : groupoid)
      : @IsIsomorphism (Hom one_types _ _) _ _ (gquot_id G).
    Proof.
      simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
      - symmetry. simpl.
        funext x.
        apply gquot_functorial_idmap.
      - apply concat_pV.
      - apply concat_Vp.
    Defined.

    Definition gquot_functor_d `{Univalence} : LaxFunctor_d grpd one_types.
    Proof.
      simple refine {| Fobj_d := _ |}.
      - exact (fun G => gquot_o G).
      - intros G₁ G₂ ; cbn.
        apply gquot_map.
      - apply gquot_compose.
      - apply gquot_id.
    Defined.

    Definition is_lax_gquot_functor `{Univalence} : is_lax gquot_functor_d.
    Proof.
      repeat split.
      - intros G₁ G₂ F ; simpl.
        rewrite <- path_forall_1.
        unfold bicategory.hcomp ; simpl.
        rewrite ap_precompose, ap_postcompose.
        rewrite <- !path_forall_pp.
        apply ap.
        funext x ; revert x.
        simple refine (gquot_ind_prop _ _ _).
        intros a ; simpl.
        rewrite !concat_1p, ge.
        reflexivity.
      - intros G₁ G₂ F ; cbn.
        rewrite <- path_forall_1.
        unfold bicategory.hcomp ; simpl.
        rewrite ap_postcompose.
        rewrite <- !path_forall_pp.
        rewrite concat_p1.
        rewrite <- !path_forall_pp.
        apply ap.
        funext x ; revert x.
        simple refine (gquot_ind_prop _ _ _).
        intros a ; simpl.
        rewrite !concat_1p, ge.
        reflexivity.
      - intros G₁ G₂ G₃ G₄ F₁ F₂ F₃ ; cbn.
        rewrite !concat_1p, concat_p1.
        rewrite !ap_precompose, !ap_postcompose.
        rewrite <- !path_forall_pp.
        apply ap.
        funext x ; revert x.
        simple refine (gquot_ind_prop _ _ _).
        intros a ; simpl.
        rewrite !concat_1p, ge.
        reflexivity.
    Qed.

    Definition gquot_functor `{Univalence} : LaxFunctor grpd one_types
      := (gquot_functor_d;is_lax_gquot_functor).

    Global Instance gquot_functor_pseudo `{Univalence}
      : is_pseudo_functor gquot_functor.
    Proof.
      simple refine {| Fcomp_iso := _ |}.
    Defined.
*)