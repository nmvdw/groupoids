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
  Variable (G₁ : groupoid A)
           (G₂ : groupoid B).

  Definition gquot_sum_in
             (z : gquot G₁ + gquot G₂)
    : gquot (sum_groupoid G₁ G₂).
  Proof.
    destruct z as [x | y].
    - exact (gquot_rec
               _
               (fun a => gcl _ (inl a))
               (fun a₁ a₂ g => @geqcl _ (sum_groupoid G₁ G₂) (inl a₁) (inl a₂) g)
               (fun a => @ge _ (sum_groupoid G₁ G₂) (inl a))
               (fun a₁ a₂ g => @ginv _ (sum_groupoid G₁ G₂) (inl a₁) (inl a₂) g)
               (fun a₁ a₂ a₃ g₁ g₂ =>
                  @gconcat _
                           (sum_groupoid G₁ G₂)
                           (inl a₁)
                           (inl a₂)
                           (inl a₃)
                           g₁
                           g₂)
               _
               x).
    - exact (gquot_rec
               _
               (fun b => gcl _ (inr b))
               (fun b₁ b₂ g => @geqcl _ (sum_groupoid G₁ G₂) (inr b₁) (inr b₂) g)
               (fun b => @ge _ (sum_groupoid G₁ G₂) (inr b))
               (fun b₁ b₂ g => @ginv _ (sum_groupoid G₁ G₂) (inr b₁) (inr b₂) g)
               (fun b₁ b₂ b₃ g₁ g₂ =>
                  @gconcat _
                           (sum_groupoid G₁ G₂)
                           (inr b₁)
                           (inr b₂)
                           (inr b₃)
                           g₁
                           g₂)
               _
               y).
  Defined.

  Definition gquot_sum_out : gquot (sum_groupoid G₁ G₂) -> gquot G₁ + gquot G₂.
  Proof.
    simple refine (gquot_rec _ _ _ _ _ _ _) ; cbn.
    - intros [a | b].
      + exact (inl (gcl _ a)).
      + exact (inr (gcl _ b)).
    - intros [a₁ | b₁] [a₂ | b₂] g ; try refine (Empty_rec g).
      + exact (ap inl (geqcl _ g)).
      + exact (ap inr (geqcl _ g)).
    - intros [a | b].
      + exact (ap _ (ge _ a)).
      + exact (ap _ (ge _ b)).
    - intros [a₁ | b₁] [a₂ | b₂] g ; try refine (Empty_rec g).
      + exact (ap (ap inl) (ginv G₁ g) @ ap_V _ _).
      + exact (ap (ap inr) (ginv G₂ g) @ ap_V _ _).
    - intros [a₁ | b₁] [a₂ | b₂] [a₃ | b₃] g₁ g₂;
        try (exact (Empty_rec g₁) || exact (Empty_rec g₂)).
      + exact (ap (ap inl) (gconcat G₁ g₁ g₂) @ ap_pp _ _ _).
      + exact (ap (ap inr) (gconcat G₂ g₁ g₂) @ ap_pp _ _ _).
  Defined.

  Lemma gquot_sum_out_in_sect : Sect gquot_sum_out gquot_sum_in.
  Proof.
    intros x.
    simple refine (gquot_ind_set (fun x => gquot_sum_in (gquot_sum_out x) = x) _ _ _ x).
    - intros [ | ] ; reflexivity.
    - intros [a1 | b1] [a2 | b2] g ; try refine (Empty_rec g)
      ; compute in g.
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

  Lemma gquot_sum_in_out_sect : Sect gquot_sum_in gquot_sum_out.
  Proof.
    intros [x | y].
    - simple refine (gquot_ind_set
                       (fun z => gquot_sum_out (gquot_sum_in (inl z)) = inl z) _ _ _ x).
      + exact (fun _ => idpath).
      + intros a₁ a₂ g.
        apply path_to_path_over.
        rewrite transport_paths_FlFr. hott_simpl.
        rewrite ap_compose.
        rewrite !gquot_rec_beta_geqcl.
        apply concat_Vp.
    - simple refine (gquot_ind_set
                       (fun z => gquot_sum_out (gquot_sum_in (inr z)) = inr z) _ _ _ y).
      + exact (fun _ => idpath).
      + intros a₁ a₂ g.
        apply path_to_path_over.
        rewrite transport_paths_FlFr. hott_simpl.
        rewrite ap_compose.
        rewrite !gquot_rec_beta_geqcl.
        apply concat_Vp.
  Qed.

  Global Instance gquot_sum_out_isequiv : IsEquiv gquot_sum_out
    := isequiv_adjointify _ gquot_sum_in gquot_sum_in_out_sect gquot_sum_out_in_sect.
End gquot_sum.
