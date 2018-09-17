Require Import HoTT.
From GR.bicategories Require Import
     bicategory.bicategory
     bicategory.examples.two_type
     lax_functor.lax_functor.

Section ApFunctor.
  Context {X Y : 2 -Type}.
  Variable (f : X -> Y).

  Definition ap_functor_d
    : PseudoFunctor_d (path_bigroupoid X) (path_bigroupoid Y).
  Proof.
    make_pseudo_functor.
    - exact f.
    - exact (fun _ _ => ap f).
    - exact (fun _ _ _ _ => ap02 f).
    - exact (fun _ _ _ p q => (ap_pp f q p)^).
    - exact (fun _ => idpath).
    - exact (fun _ _ _ p q => ap_pp f q p).
    - exact (fun _ => idpath).
  Defined.

  Definition ap_functor_is_pseudo
    : is_pseudo_functor_p ap_functor_d.
  Proof.
    make_is_pseudo.
    - intros x y p ; cbn.
      reflexivity.
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
    - reflexivity.
    - reflexivity.
  Qed.

  Definition lax_ap_functor
    : LaxFunctor (path_bigroupoid X) (path_bigroupoid Y)
    := Build_PseudoFunctor ap_functor_d ap_functor_is_pseudo.

  Global Instance lax_ap_functor_pseudo
    : is_pseudo lax_ap_functor
    := _.
End ApFunctor.