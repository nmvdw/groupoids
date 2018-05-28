Require Import HoTT.
From GR.groupoid.grpd_bicategory Require Import
     grpd_bicategory.

Definition path_space (X : Type) : groupoid.
Proof.
  simple refine (Build_grpd _ _ _ _ _ _ _ _ _ _) ; simpl.
  - exact X.
  - exact (fun (x y : X) => BuildhSet (Trunc 0 (x = y))).
  - exact (fun _ => tr idpath).
  - exact (fun _ _ => Trunc_rec (fun p => tr p^)).
  - exact (fun _ _ _ p' q' => Trunc_rec (fun p => Trunc_rec (fun q => tr (p @ q)) q') p').
  - intros ? ? ? ? p q r ; simpl.
    strip_truncations ; simpl.
    exact (ap tr (concat_p_pp p q r)).
  - intros ? ? p.
    strip_truncations ; simpl.
    exact (ap tr (concat_1p p)).
  - intros ? ? p.
    strip_truncations ; simpl.
    exact (ap tr (concat_p1 p)).
  - intros ? ? p.
    strip_truncations ; simpl.
    exact (ap tr (concat_Vp p)).
  - intros ? ? p.
    strip_truncations ; simpl.
    exact (ap tr (concat_pV p)).
Defined.