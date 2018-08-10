Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     general_category bicategory.bicategory bicategory.univalent.

Section TwoTypeBiGroupoid.
  Variable (X : Type).
  Context `{IsTrunc 2 X}.

  Definition path_bigroupoid_d : BiCategory_d.
  Proof.
    make_bicategory.
    - exact X.
    - exact (fun x y => Core.groupoid_category (x = y)).
    - exact (fun _ => idpath).
    - exact (fun _ _ _ p => Datatypes.snd p @ Datatypes.fst p).
    - intros x y z [p₁ p₂] [q₁ q₂] [s₁ s₂] ; simpl in *.
      exact (ap (fun z => z @ p₁) s₂ @ ap (fun z => q₂ @ z) s₁).
    - intros x y p ; simpl in *.
      exact (concat_p1 p).
    - intros x y p ; simpl in *.
      exact (concat_p1 p)^.
    - intros x y p ; simpl in *.
      exact (concat_1p p).
    - intros x y p ; simpl in *.
      exact (concat_1p p)^.
    - intros w x y z p q r ; simpl in *.
      exact (concat_p_pp r q p).
    - intros w x y z p q r ; simpl in *.
      exact (concat_p_pp r q p)^.
  Defined.

  Definition path_bigroupoid_is_bicategory : is_bicategory path_bigroupoid_d.
  Proof.
    make_is_bicategory.
    - reflexivity.
    - intros x y z [p₁ p₂] [q₁ q₂] [r₁ r₂] [s₁ s₂] [t₁ t₂] ; simpl in *.
      induction s₁, s₂, t₁, t₂ ; simpl.
      reflexivity.
    - intros x y p₁ p₂ s ; simpl in *.
      induction s ; simpl.
      exact (concat_1p _ @ (concat_p1 _)^).
    - intros x y p₁ p₂ s ; simpl in *.
      induction s ; simpl.
      exact (concat_1p _ @ (concat_p1 _)^).
    - intros x y p₁ p₂ s ; simpl in *.
      induction s ; simpl.
      exact (concat_1p _ @ (concat_p1 _)^).
    - intros x y p₁ p₂ s ; simpl in *.
      induction s ; simpl.
      exact (concat_1p _ @ (concat_p1 _)^).
    - intros x y p ; simpl in *.
      exact (concat_Vp _).
    - intros x y p ; simpl in *.
      exact (concat_pV _).
    - intros x y p ; simpl in *.
      exact (concat_Vp _).
    - intros x y p ; simpl in *.
      exact (concat_pV _).
    - intros w x y z p₁ p₂ q₁ q₂ r₁ r₂ sp sq sr ; simpl in *.
      induction sp, sq, sr ; simpl.
      exact (concat_1p _ @ (concat_p1 _)^).
    - intros w x y z p₁ p₂ q₁ q₂ r₁ r₂ sp sq sr ; simpl in *.
      induction sp, sq, sr ; simpl.
      exact (concat_1p _ @ (concat_p1 _)^).
    - intros w x y z p q r ; simpl in *.
      exact (concat_Vp _).
    - intros w x y z p q r ; simpl in *.
      exact (concat_pV _).
    - intros x y z p q ; simpl in *.
      induction p, q ; simpl.
      reflexivity.
    - intros v w x y z p q r s ; simpl in *.
      induction p, q, r, s ; simpl.
      reflexivity.
  Qed.
      
  Definition path_bigroupoid : BiCategory
    := Build_BiCategory path_bigroupoid_d path_bigroupoid_is_bicategory.

  Definition path_bigroupoid_locally_univalent
    : locally_univalent path_bigroupoid.
  Proof.
    intro ; apply _.
  Qed.
End TwoTypeBiGroupoid.