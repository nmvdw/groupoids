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

Definition gquot_o `{Univalence} (G : groupoid) : 1 -Type
  := BuildTruncType 1 (gquot G).

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