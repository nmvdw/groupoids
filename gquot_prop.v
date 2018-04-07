Require Import HoTT.
Require Import groupoid_quotient.
Require Import groupoid path_over globe_over.

Section one_type_is_groupoid_quotient.
  Variable (A : Type).
  Context `{IsTrunc 1 A}.

  Definition P : groupoid A
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
    
  Definition gquot_to_A : gquot P -> A.
  Proof.
    simple refine (gquot_rec A idmap _ _ _ _ _) ; cbn.
    - exact (fun _ _ => idmap).
    - exact (fun _ => idpath).
    - exact (fun _ _ _ => idpath).
    - exact (fun _ _ _ _ _ => idpath).
  Defined.

  Definition path_over_help
             {a₁ a₂ : A}
             (g : hom P a₁ a₂)
    : path_over (fun z : gquot P => gcl P (gquot_to_A z) = z)
                (geqcl P g)
                idpath
                idpath.
  Proof.
    apply path_to_path_over.
    rewrite transport_paths_FlFr.
    rewrite concat_p1, ap_idmap.
    rewrite ap_compose.
    rewrite gquot_rec_beta_geqcl.
    induction g ; cbn.
    rewrite ge.
    reflexivity.
  Defined.

  Global Instance gquot_to_A_isequiv : IsEquiv gquot_to_A.
  Proof.
    simple refine (isequiv_adjointify _ (gcl P) _ _).
    - intros x ; reflexivity.
    - intros x.
      simple refine (gquot_ind (fun z => _) _ _ _ _ _ _ x).
      + intros a ; cbn.
        reflexivity.
      + intros ; apply path_over_help.
      + intros.
        apply path_to_globe_over.
        apply path_ishprop.
      + intros.
        apply path_to_globe_over.
        apply path_ishprop.
      + intros.
        apply path_to_globe_over.
        apply path_ishprop.
  Defined.
End one_type_is_groupoid_quotient.