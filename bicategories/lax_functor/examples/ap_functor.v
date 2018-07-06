Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory
     bicategory.examples.two_type
     lax_functor.lax_functor.

Section ApFunctor.
  Context `{Univalence}
          {X Y : 2 -Type}.
  Variable (f : X -> Y).

  Definition ap_functor_rd
    : PseudoFunctor_rd (path_bigroupoid X) (path_bigroupoid Y).
  Proof.
    simple refine (Build_PseudoFunctor_rd _ _ _ _ _ _ _) ; simpl.
    - exact f.
    - exact (fun _ _ => ap f).
    - exact (fun _ _ _ _ => ap02 f).
    - exact (fun _ _ _ p q => (ap_pp f q p)^).
    - exact (fun _ => idpath).
    - exact (fun _ _ _ p q => ap_pp f q p).
    - exact (fun _ => idpath).
  Defined.

  Definition ap_functor_rd_is_pseudo
    : is_pseudo_functor_d ap_functor_rd.
  Proof.
    repeat split ; cbn.
    - exact (fun _ _ _ _ _ => ap02_pp f).
    - intros x y z p₁ p₂ q₁ q₂ r s ; cbn.
      induction r, s ; cbn.
      exact (concat_1p _ @ (concat_p1 _)^).
    - intros x y p.
      induction p ; simpl.
      reflexivity.
    - intros x y p.
      induction p ; simpl.
      reflexivity.
    - intros x₁ x₂ x₃ x₄ p q r ; simpl.
      induction p, q, r.
      reflexivity.
    - intros x y z p q.
      apply concat_Vp.
    - intros x y z p q.
      apply concat_pV.
    - intros x y z p₁ p₂ q₁ q₂ r s ; simpl.
      induction r, s ; cbn.
      exact (concat_1p _ @ (concat_p1 _)^).
  Qed.

  Definition lax_ap_functor
    : LaxFunctor (path_bigroupoid X) (path_bigroupoid Y)
    := Build_PseudoFunctor ap_functor_rd ap_functor_rd_is_pseudo.

  Global Instance lax_ap_functor_pseudo
    : is_pseudo_functor lax_ap_functor.
  Proof.
    apply _.
  Defined.
End ApFunctor.