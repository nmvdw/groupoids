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
      simple refine (gquot_ind_set (fun z => _) _ _ _ x).
      + intros a ; cbn.
        reflexivity.
      + intros.
        apply path_over_help.
  Defined.
End one_type_is_groupoid_quotient.

Section gquot_sum.
  Variable (A B : Type).
  Context `{HA : IsTrunc 1 A}.
  Context `{HB : IsTrunc 1 B}.
  Variable (G1 : groupoid A)
           (G2 : groupoid B).

  Definition gquot_sum_in : gquot G1 + gquot G2 -> gquot (sum_groupoid G1 G2).
  Proof.
    intros [Q | Q].
    - simple refine (gquot_rec _ _ _ _ _ _ _ Q) ; cbn.
      + intros a. apply (gcl _ (inl a)).
      + intros a1 a2 g; simpl.
        refine (geqcl _ _).
        compute. apply g.
      + intros a. simpl.
        etransitivity ; [ | apply ge ].
        reflexivity.
      + intros a1 a2 g. simpl.
        etransitivity; [ | apply ginv ].
        reflexivity.
      + intros a1 a2 a3 g1 g2. simpl.
        etransitivity; [ | apply gconcat ].
        reflexivity.
    - simple refine (gquot_rec _ _ _ _ _ _ _ Q) ; cbn.
      + intros b. apply (gcl _ (inr b)).
      + intros b1 b2 g; simpl.
        refine (geqcl _ _).
        compute. apply g.
      + intros b. simpl.
        etransitivity ; [ | apply ge ].
        reflexivity.
      + intros b1 b2 g. simpl.
        etransitivity; [ | apply ginv ].
        reflexivity.
      + intros b1 b2 b3 g1 g2. simpl.
        etransitivity; [ | apply gconcat ].
        reflexivity.
  Defined.

  Definition gquot_sum_out : gquot (sum_groupoid G1 G2) -> gquot G1 + gquot G2.
  Proof.
    simple refine (gquot_rec _ _ _ _ _ _ _) ; cbn.
    - intros [x | x]; [ apply inl | apply inr ]; apply (gcl _ x).
    - intros [a1 | b1] [a2 | b2] g; try refine (Empty_rec g).
      + refine (ap inl (geqcl _ g)).
      + refine (ap inr (geqcl _ g)).
    - intros [a | b].
      + refine (ap _ (ge _ a)).
      + refine (ap _ (ge _ b)).
    - intros [a1 | b1] [a2 | b2] g; try refine (Empty_rec g).
      + rewrite <- ap_V.
        f_ap. apply ginv.
      + rewrite <- ap_V.
        f_ap. apply ginv.
    - intros [a1 | b1] [a2 | b2] [a3 | b3] g1 g2;
        try (refine (Empty_rec g1) || refine (Empty_rec g2)).
      + rewrite <- ap_pp. f_ap. apply gconcat.
      + rewrite <- ap_pp. f_ap. apply gconcat.
  Defined.

  Lemma gquot_sum_out_in_sect : Sect gquot_sum_out gquot_sum_in.
  Proof.
    intros x.
    simple refine (gquot_ind_set _ _ (fun x => gquot_sum_in (gquot_sum_out x) = x) _ _ _ x).
    - intros [a | b]; reflexivity.
    - intros [a1 | b1] [a2 | b2] g; try refine (Empty_rec g);
        compute in g.
      + apply path_to_path_over.
        rewrite transport_paths_FlFr. hott_simpl.
        rewrite ap_compose.
        rewrite gquot_rec_beta_geqcl.
        rewrite <- (ap_compose inl gquot_sum_in).
        rewrite gquot_rec_beta_geqcl.
        apply concat_Vp.
      + apply path_to_path_over.
        rewrite transport_paths_FlFr. hott_simpl.
        rewrite ap_compose.
        rewrite gquot_rec_beta_geqcl.
        rewrite <- (ap_compose inr gquot_sum_in).
        rewrite gquot_rec_beta_geqcl.
        apply concat_Vp.
  Qed.

End gquot_sum.
