Require Import HoTT.
Require Import groupoid_quotient.
Require Import groupoid path_over globe_over general.

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

Section gquot_prod.
  Variable (A B : Type).
  Variable (G₁ : groupoid A)
           (G₂ : groupoid B).

  Context `{Funext}.

  Definition gquot_prod_in
    : gquot G₁ * gquot G₂ -> gquot (prod_groupoid G₁ G₂).
  Proof.
    simple refine (gquot_double_rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    - exact (fun a b => gcl _ (a, b)).
    - intros a b₁ b₂ g ; simpl.
      apply geqcl.
      exact (e a, g).
    - intros a b ; simpl.
      apply ge.
    - intros a b₁ b₂ g ; simpl.
      rewrite <- ginv ; simpl.
      rewrite inv_e.
      reflexivity.
    - intros a b₁ b₂ b₃ g₁ g₂ ; simpl.
      rewrite <- gconcat ; simpl.
      rewrite ce.
      reflexivity.
    - intros a₁ a₂ b g ; simpl.
      apply geqcl.
      exact (g, e b).
    - intros a b ; simpl.
      apply ge.
    - intros a₁ a₂ b g ; simpl.
      rewrite <- ginv ; simpl.
      rewrite inv_e.
      reflexivity.
    - intros a₁ a₂ a₃ b g₁ g₂ ; simpl.
      rewrite <- gconcat ; simpl.
      rewrite ce.
      reflexivity.
    - intros a₁ a₂ b₁ b₂ g₁ g₂ ; simpl.
      rewrite !gquot_rec_beta_geqcl.
      rewrite <- ginv, <- !gconcat.
      apply ap ; simpl.
      rewrite !inv_e, !ce, ec, ic.
      reflexivity.
  Defined.

  Definition gquot_prod_out : gquot (prod_groupoid G₁ G₂) -> gquot G₁ * gquot G₂.
  Proof.
    simple refine (gquot_rec _ _ _ _ _ _ _) ; cbn.
    - exact (fun x => (gcl _ (fst x), gcl _ (snd x))).
    - intros a₁ a₂ g ; simpl.
      exact (path_prod' (geqcl _ (fst g)) (geqcl _ (snd g))).
    - intros ; simpl.
      refine (ap (fun p => path_prod' p _) (ge _ _) @ _).
      exact (ap (fun p => path_prod' _ p) (ge _ _)).
    - intros ; simpl.
      refine (ap (fun p => path_prod' p _) (ginv _ _) @ _).
      refine (ap (fun p => path_prod' _ p) (ginv _ _) @ _).
      apply path_prod_V.
    - intros ; simpl.
      refine (ap (fun p => path_prod' p _) (gconcat _ _ _) @ _).
      refine (ap (fun p => path_prod' _ p) (gconcat _ _ _) @ _).
      apply path_prod_pp.
  Defined.

  Lemma gquot_prod_out_in_sect : Sect gquot_prod_out gquot_prod_in.
  Proof.
    simple refine (gquot_ind_set (fun x => gquot_prod_in (gquot_prod_out x) = x) _ _ _).
    - reflexivity.
    - intros x₁ x₂ g.
      apply path_to_path_over.
      rewrite transport_paths_FlFr.
      hott_simpl.
      rewrite ap_compose.
      rewrite gquot_rec_beta_geqcl.
      rewrite gquot_double_rec_beta_gcleq.
      rewrite <- gconcat, <- ginv, <- gconcat, <- ge.
      apply ap ; simpl.
      rewrite !ce, !ec, !ic.
      reflexivity.
  Qed.

  Lemma gquot_prod_in_out_sect : Sect gquot_prod_in gquot_prod_out.
  Proof.
    intros [x₁ x₂].
    revert x₁ x₂.
    simple refine (gquot_double_ind_set _ _ _).
    - reflexivity.
    - intros a b₁ b₂ g ; simpl.
      apply path_to_path_over.
      rewrite transport_paths_FlFr.
      hott_simpl.
      rewrite ap_compose.
      rewrite (ap_compose _ gquot_prod_in).
      rewrite ap_pair_r.
      rewrite gquot_double_rec_beta_r_gcleq.
      rewrite gquot_rec_beta_geqcl.
      rewrite <- path_prod_V.
      rewrite ge.
      rewrite <- path_prod_pp.
      hott_simpl.
    - intros a b₁ b₂ g.
      rewrite transport_paths_FlFr.
      hott_simpl.
      rewrite ap_compose.
      rewrite (ap_compose _ gquot_prod_in).
      rewrite ap_pair_l.
      rewrite gquot_double_rec_beta_l_gcleq.
      rewrite gquot_rec_beta_geqcl.
      rewrite <- path_prod_V.
      rewrite ge.
      rewrite <- path_prod_pp.
      hott_simpl.
  Qed.

  Global Instance gquot_prod_out_isequiv : IsEquiv gquot_prod_out
    := isequiv_adjointify _ gquot_prod_in gquot_prod_in_out_sect gquot_prod_out_in_sect.
End gquot_prod.

Section encode_decode.
  Variable (A : Type)
           (G : groupoid A).
  Context `{Univalence}.

  Definition right_action
        {a₁ a₂ : A} (b : A)
        (g : hom G a₁ a₂)
    : hom G a₁ b -> hom G a₂ b
    := fun h => (inv g) × h.

  Definition right_action_inv
             {a₁ a₂ : A} (b : A)
             (g : hom G a₁ a₂)
    : hom G a₂ b -> hom G a₁ b
    := fun h => g × h.

  Global Instance right_action_equiv (a : A) {b₁ b₂ : A} (g : hom G b₁ b₂)
    : IsEquiv (right_action a g).
  Proof.
    simple refine (isequiv_adjointify _ (right_action_inv a g) _ _).
    - intros h ; compute.
      refine (ca _ _ _ _ _ _ _ _ _ @ _).
      exact (ap (fun z => z × h) (ic _ _ _ _ _) @ ec _ _ _ _ _).
    - intros h ; compute.
      refine (ca _ _ _ _ _ _ _ _ _ @ _).
      exact (ap (fun z => z × h) (ci _ _ _ _ _) @ ec _ _ _ _ _).
  Defined.
  
  Definition left_action
        (a : A) {b₁ b₂ : A}
        (g : hom G b₁ b₂)
    : hom G a b₁ -> hom G a b₂
    := fun h => h × g.

  Definition left_action_inv
             (a : A) {b₁ b₂ : A}
             (g : hom G b₁ b₂)
    : hom G a b₂ -> hom G a b₁
    := fun h => h × (inv g).

  Global Instance left_action_equiv (a : A) {b₁ b₂ : A} (g : hom G b₁ b₂)
    : IsEquiv (left_action a g).
  Proof.
    simple refine (isequiv_adjointify _ (left_action_inv a g) _ _).
    - intros h ; compute.
      refine ((ca _ _ _ _ _ _ _ _ _)^ @ _).
      exact (ap (fun z => h × z) (ic _ _ _ _ _) @ ce _ _ _ _ _).
    - intros h ; compute.
      refine ((ca _ _ _ _ _ _ _ _ _)^ @ _).
      exact (ap (fun z => h × z) (ci _ _ _ _ _) @ ce _ _ _ _ _).
  Defined.

  Definition left_action_e (a b : A)
    : left_action a (e b) = idmap.
  Proof.
    funext x ; compute.
    apply ce.
  Defined.

  Definition path_hset_1 { X : hSet } : 
    (path_hset 1%equiv = (@idpath hSet X)).
  Proof.
  Admitted.
  
  Definition test
             {X Y : Type}
             `{IsHSet X} `{IsHSet Y}
             (f g : X -> Y)
             (p : f = g)
             `{IsEquiv _ _ f}
             (eq_g : IsEquiv g)
    : path_hset (BuildEquiv _ _ f _) = path_hset (BuildEquiv _ _ g eq_g).
  Admitted.

  Definition g_fam : gquot G -> gquot G -> hSet.
  Proof.
    simple refine (gquot_double_rec' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    - exact (hom G).
    - intros a b₁ b₂ g.
      apply path_hset.
      exact (BuildEquiv _ _ (left_action a g) _).
    - intros a b ; simpl.
      rewrite (test _ idmap (left_action_e _ _) _).
      rewrite <- path_hset_1.
      reflexivity.
    - admit.
    - admit.
  Admitted.
End encode_decode.