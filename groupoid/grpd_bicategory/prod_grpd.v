Require Import HoTT.
From GR.bicategories.lax_functor Require Import
     lax_functor.
From GR.groupoid.grpd_bicategory Require Import
     grpd_bicategory.

(** Groupoids are closed under products. *)
Definition prod_groupoid (G₁ G₂ : groupoid) : groupoid.
Proof.
  simple refine (Build_grpd _ _ _ _ _ _ _ _ _ _) ; simpl.
  - exact (G₁ * G₂).
  - exact (fun x y => BuildhSet (G₁ (fst x) (fst y) * G₂ (snd x) (snd y))).
  - intros ; simpl.
    split ; apply e.
  - intros ? ? [p1 p2] ; simpl.
    exact (inv p1, inv p2).
  - intros ? ? ? [p1 p2] [q1 q2].
    exact (p1 ● q1, p2 ● q2).
  - intros ? ? ? ? [p1 p2] [q1 q2] [r1 r2].
    apply path_prod ; apply grpd_right_assoc.
  - intros ? ? [p1 p2].
    apply path_prod ; apply grpd_left_identity.
  - intros ? ? [p1 p2].
    apply path_prod ; apply grpd_right_identity.
  - intros ? ? [p1 p2].
    apply path_prod ; apply grpd_left_inverse.
  - intros ? ? [p1 p2].
    apply path_prod ; apply grpd_right_inverse.
Defined.