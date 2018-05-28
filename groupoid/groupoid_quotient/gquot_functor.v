Require Import HoTT.
From HoTT.Categories Require Import
     Functor NaturalTransformation.
From GR.bicategories.bicategory Require Import
     examples.one_types.
From GR.bicategories.lax_functor Require Import
     lax_functor.
From GR.groupoid.groupoid_quotient Require Export
     gquot.
From GR.groupoid Require Import
     grpd_bicategory.grpd_bicategory groupoid_quotient.gquot_principles.

Definition gquot_functorial
           {G₁ G₂ : groupoid}
           (F : Core.Functor G₁.1 G₂.1)
           `{Univalence}
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

Definition gquot_natural
           {G₁ G₂ : groupoid}
           {F₁ F₂ : Core.Functor G₁.1 G₂.1}
           (α : Core.NaturalTransformation F₁ F₂)
           `{Univalence}
  : forall (x : gquot G₁), gquot_functorial F₁ x = gquot_functorial F₂ x.
Proof.
  simple refine (gquot_ind_set _ _ _ _).
  - intros x ; cbn.
    apply gcleq.
    apply α.
  - intros x₁ x₂ g ; cbn.
    apply map_path_over.
    simple refine (whisker_square idpath
                                  ((gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _)^)
                                  ((gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _)^)
                                  idpath _) ; simpl.
    apply path_to_square.
    refine (((gconcat G₂ (morphism_of F₁ g) (α x₂))^)
              @ _
              @ gconcat G₂ (α x₁) (morphism_of F₂ g)).
    apply ap.
    exact (commutes α _ _ g).
Defined.

Definition gquot_functor `{Univalence} : LaxFunctor grpd one_types.
Proof.
  simple refine {| Fobj := _ |}.
  - exact (fun G => BuildTruncType _ (gquot G)).
  - intros G₁ G₂ ; cbn.
    simple refine (Build_Functor _ _ _ _ _ _).
    + intros F ; cbn.
      exact (gquot_functorial F).
    + exact (fun _ _ α => path_forall _ _ (gquot_natural α)).
    + cbn ; intros F₁ F₂ F₃ α₁ α₂.
      refine (_ @ path_forall_pp _ _ _ _ _).
      apply ap.
      funext x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intros x ; simpl.
      apply gconcat.
    + cbn ; intros F.
      rewrite <- path_forall_1.
      apply ap.
      funext x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      intros x ; simpl.
      apply ge.
  - intros G₁ G₂ G₃.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + simpl ; intros [F₁ F₂].
      funext x ; revert x.
      simple refine (gquot_ind_set _ _ _ _).
      * reflexivity.
      * intros ; simpl.
        apply map_path_over.
        refine (whisker_square idpath
                               _
                               ((gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _)^)
                               idpath
                               _).
        ** refine (_ @ (ap_compose _ _ _)^).
           refine (_ @ ap _ ((gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _)^)).
           exact ((gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _)^).
        ** apply vrefl.
    + intros [F₁ F₂] [F₃ F₄] [α₁ α₂] ; simpl.
      admit.
  - intros G ; simpl.
    funext x ; revert x.
    simple refine (gquot_ind_set _ _ _ _).
    + reflexivity.
    + intros ; simpl.
      apply map_path_over.
      refine (whisker_square idpath
                             (ap_idmap _)^
                             ((gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _)^)
                             idpath
                             _).
      apply vrefl.
  - intros G₁ G₂ F ; simpl.
    admit.
  - admit.
  - admit.
Admitted.