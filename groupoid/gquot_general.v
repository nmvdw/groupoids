Require Import HoTT.
Require Import groupoid_quotient.
Require Import groupoid path_over globe_over general square.
Require Import setoid squot_properties.
Require Import gquot_encode_decode.

(** * A 1-type is a groupoid quotient. *)
Section one_type_is_groupoid_quotient.
  Variable (A : Type).
  Context `{IsTrunc 1 A}.

  (** Every 1-type induces a groupoid (namely, the path groupoid).
      Taking the groupoid quotient over this gives an equivalent type.
   *)
  Definition one_type_path_groupoid : groupoid A
    := {|hom := fun x y => BuildhSet(x = y) ;
         e := fun _ => idpath ;
         inv := fun _ _ => inverse ;
         comp := fun _ _ _ => concat ;
         ca := fun _ _ _ _ => concat_p_pp ;
         ce := fun _ _ => concat_p1 ;
         ec := fun _ _ => concat_1p ;
         ci := fun _ _ => concat_pV ;
         ic := fun _ _ => concat_Vp
       |}.
    
  Definition gquot_to_A : gquot one_type_path_groupoid -> A.
  Proof.
    simple refine (gquot_rec A idmap _ _ _ _ _) ; cbn.
    - exact (fun _ _ => idmap).
    - exact (fun _ => idpath).
    - exact (fun _ _ _ => idpath).
    - exact (fun _ _ _ _ _ => idpath).
  Defined.

  Definition path_over_help
             {a₁ a₂ : A}
             (g : hom one_type_path_groupoid a₁ a₂)
    : path_over (fun z : gquot _ => gcl _ (gquot_to_A z) = z)
                (gcleq _ g)
                idpath
                idpath.
  Proof.
    apply map_path_over.
    induction g ; cbn.
    refine (whisker_square idpath _ _ idpath _).
    - refine (ap_compose _ _ _ @ ap _ _)^.
      apply gquot_rec_beta_gcleq.
    - refine (ap_idmap _ @ _)^.
      apply ge.
    - exact id_square.
  Defined.

  Global Instance gquot_to_A_isequiv : IsEquiv gquot_to_A.
  Proof.
    simple refine (isequiv_adjointify _ (gcl _) _ _).
    - intros x ; reflexivity.
    - intros x.
      simple refine (gquot_ind_set (fun z => _) _ _ _ x).
      + intros a ; cbn.
        reflexivity.
      + intros.
        apply path_over_help.
  Defined.
End one_type_is_groupoid_quotient.

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
