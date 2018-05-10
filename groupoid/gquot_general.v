Require Import HoTT.
From GR Require Import setoid squot_properties.
From GR Require Export groupoid_quotient gquot_encode_decode adjunction.

(** * Setoid quotients and groupoid quotients *)
(** Every setoid induces a groupoid.
    The setoid quotients of a setoid coincides with the groupoid quotient over
    its induced groupoid.
 *)
Section squot_is_gquot.
  Variable (A : Type)
           (R : setoid A).
  Context `{Univalence}.

  Definition gquot_to_squot : gquot (setoid_to_groupoid R) -> squot R.
  Proof.
    simple refine (gquot_rec (squot R) (class_of (rel R)) _ _ _ _ _).
    - exact (fun _ _ p => related_classes_eq _ p).
    - intros ; apply path_ishprop.
    - intros ; apply path_ishprop.
    - intros ; apply path_ishprop.
  Defined.

  (** If you take the groupoid quotient over a setoid, then it is a set. *)
  Global Instance gquot_setoid_set
    : IsHSet (gquot (setoid_to_groupoid R)).
  Proof.
    simple refine (gquot_double_ind_prop (fun a b => IsHProp (a = b)) _ _).
    simpl; intros a b.
    rewrite (path_universe (encode_gquot _ _
                                      (gcl (setoid_to_groupoid R) a)
                                      (gcl (setoid_to_groupoid R) b))).
    simpl.
    apply _.
  Defined.

  (** Now we can show the two quotients coincide. *)
  Definition squot_to_gquot : squot R -> gquot (setoid_to_groupoid R).
  Proof.
    simple refine (quotient_rec _ (gcl _) _).
    simpl ; intros.
    apply gcleq ; assumption.
  Defined.

  Definition squot_to_gquot_to_squot
    : forall (x : squot R), gquot_to_squot(squot_to_gquot x) = x.
  Proof.
    simple refine (quotient_ind _ _ _ _).
    - reflexivity.
    - intros ; apply path_ishprop.
  Defined.

  Definition gquot_to_squot_to_gquot
    : forall (x : gquot (setoid_to_groupoid R)), squot_to_gquot(gquot_to_squot x) = x.
  Proof.
    simple refine (gquot_ind_prop _ _ _).
    reflexivity.
  Defined.
End squot_is_gquot.
