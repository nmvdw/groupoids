Require Import HoTT.
From GR Require Import basics.general.
From GR Require Export basics.polynomial groupoid.groupoid_quotient.

(** * Groupoid quotient commmutes with polynomials *)

(** ** The groupoid quotient commutes with sums.
    We use recursion to define the maps and `gquot_ind_set` to prove they are inverses.
 *)
Section gquot_sum.
  Variable (G₁ G₂ : groupoid).

  Definition gquot_sum_in
             (z : gquot G₁ + gquot G₂)
    : gquot (sum_groupoid G₁ G₂).
  Proof.
    destruct z as [x | y].
    - exact (gquot_rec
               _
               (fun a => gcl (sum_groupoid G₁ G₂) (inl a))
               (fun a₁ a₂ g => @gcleq (sum_groupoid G₁ G₂) (inl a₁) (inl a₂) g)
               (fun a => ge (sum_groupoid G₁ G₂) (inl a))
               (fun a₁ a₂ g => @ginv (sum_groupoid G₁ G₂) (inl a₁) (inl a₂) g)
               (fun a₁ a₂ a₃ g₁ g₂ =>
                  @gconcat (sum_groupoid G₁ G₂)
                           (inl a₁)
                           (inl a₂)
                           (inl a₃)
                           g₁
                           g₂)
               _
               x).
    - exact (gquot_rec
               _
               (fun b => gcl (sum_groupoid G₁ G₂) (inr b))
               (fun b₁ b₂ g => @gcleq (sum_groupoid G₁ G₂) (inr b₁) (inr b₂) g)
               (fun b => ge (sum_groupoid G₁ G₂) (inr b))
               (fun b₁ b₂ g => @ginv (sum_groupoid G₁ G₂) (inr b₁) (inr b₂) g)
               (fun b₁ b₂ b₃ g₁ g₂ =>
                  @gconcat (sum_groupoid G₁ G₂)
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
      + exact (ap inl (gcleq _ g)).
      + exact (ap inr (gcleq _ g)).
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
    - intros [a1 | b1] [a2 | b2] g ; try refine (Empty_rec g) ; simpl in g.
      (**
       <<
                     1
       [inl(a₂)] —————————→ [inl(a₂)]
          |                     |
          |                     |
 ap       |                     |
  (gquot_sum_in o               | ap 1 [g]
    gquot_sum_out) [g]          |
          |                     |
          |                     |
          |                     |
       [inl(a₁)] —————————→ [inl(a₁)]
                     1
       >>
       *)
      + apply map_path_over.
        refine (whisker_square idpath _ (ap_idmap _)^ idpath (vrefl _)).
        refine (_ @ (ap_compose _ _ _)^).
        refine ((ap _ _ @ _)^).
        ** apply gquot_rec_beta_gcleq.
        ** refine ((ap_compose inl gquot_sum_in _)^ @ _).
           apply gquot_rec_beta_gcleq.
      + apply map_path_over.
        refine (whisker_square idpath _ (ap_idmap _)^ idpath (vrefl _)).
        refine (_ @ (ap_compose _ _ _)^).
        refine ((ap _ _ @ _ )^).
        ** apply gquot_rec_beta_gcleq.
        ** refine ((ap_compose inr gquot_sum_in _)^ @ _).
           apply gquot_rec_beta_gcleq.
  Qed.

  Lemma gquot_sum_in_out_sect : Sect gquot_sum_in gquot_sum_out.
  Proof.
    intros [x | y].
    - simple refine (gquot_ind_set
                       (fun z => gquot_sum_out (gquot_sum_in (inl z)) = inl z) _ _ _ x).
      + exact (fun _ => idpath).
      + intros a₁ a₂ g.
        apply map_path_over.
        refine (whisker_square idpath _ idpath idpath (vrefl _)).
        * refine (_ @ (ap_compose (gquot_sum_in o inl) gquot_sum_out _)^).
          refine (ap _ _ @ _)^.
          ** apply gquot_rec_beta_gcleq.
          ** apply gquot_rec_beta_gcleq.
    - simple refine (gquot_ind_set
                       (fun z => gquot_sum_out (gquot_sum_in (inr z)) = inr z) _ _ _ y).
      + exact (fun _ => idpath).
      + intros a₁ a₂ g.
        apply map_path_over.
        refine (whisker_square idpath _ idpath idpath (vrefl _)).
        refine (_ @ (ap_compose (gquot_sum_in o inr) gquot_sum_out _)^).
        refine (ap _ _ @ _)^.
        ** apply gquot_rec_beta_gcleq.
        ** apply gquot_rec_beta_gcleq.
  Qed.

  Global Instance gquot_sum_in_isequiv : IsEquiv gquot_sum_in
    := isequiv_adjointify _ gquot_sum_out gquot_sum_out_in_sect gquot_sum_in_out_sect.

  Definition gquot_sum : (gquot G₁ + gquot G₂) <~> gquot (sum_groupoid G₁ G₂) :=
    BuildEquiv _ _ gquot_sum_in _.
End gquot_sum.

(** ** The groupoid quotient commutes with products.
    We use recursion and double recursion to define the maps.
    We use `gquot_ind_set` to show they are inverses.
 *)
Section gquot_prod.
  Variable (G₁ G₂ : groupoid).

  Context `{Funext}.

  Definition gquot_prod_in
    : gquot G₁ * gquot G₂ -> gquot (prod_groupoid G₁ G₂).
  Proof.
    simple refine (gquot_double_rec _ _ _ _ _ _ _ _ _ _ _).
    - exact (fun a b => gcl (prod_groupoid G₁ G₂) (a, b)).
    - intros a b₁ b₂ g ; simpl.
      apply gcleq.
      exact (e a, g).
    - intros a b ; simpl.
      apply ge.
    - intros a b₁ b₂ g ; simpl.
      rewrite <- ginv ; cbn.
      rewrite inv_e.
      reflexivity.
    - intros a b₁ b₂ b₃ g₁ g₂ ; simpl.
      rewrite <- gconcat ; cbn.
      rewrite ce.
      reflexivity.
    - intros a₁ a₂ b g ; simpl.
      apply gcleq.
      exact (g, e b).
    - intros a b ; simpl.
      apply ge.
    - intros a₁ a₂ b g ; simpl.
      rewrite <- ginv ; cbn.
      rewrite inv_e.
      reflexivity.
    - intros a₁ a₂ a₃ b g₁ g₂ ; simpl.
      rewrite <- gconcat ; cbn.
      rewrite ce.
      reflexivity.
    - intros a₁ a₂ b₁ b₂ g₁ g₂ ; simpl.
      apply path_to_square.
      rewrite <- !gconcat.
      apply ap ; cbn.
      rewrite !ce, !ec.
      reflexivity.
  Defined.

  Definition gquot_prod_out : gquot (prod_groupoid G₁ G₂) -> gquot G₁ * gquot G₂.
  Proof.
    simple refine (gquot_rec _ _ _ _ _ _ _) ; cbn.
    - exact (fun x => (gcl _ (fst x), gcl _ (snd x))).
    - intros a₁ a₂ g ; simpl.
      exact (path_prod' (gcleq _ (fst g)) (gcleq _ (snd g))).
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
      apply map_path_over.
      refine (whisker_square idpath _ (ap_idmap _)^ idpath (vrefl _)).
      refine ((ap_compose _ _ _ @ ap (ap gquot_prod_in) _ @ _ @ _)^).
      * apply gquot_rec_beta_gcleq.
      * apply gquot_double_rec_beta_gcleq.
      * simpl.
        refine ((@gconcat (prod_groupoid G₁ G₂)
                          _
                          (fst x₂, snd x₁)
                          _
                          (fst g, e (snd x₁))
                          (e (fst x₂), snd g))^
                @ _).
        apply ap.
        exact (path_prod' (ce _) (ec _)).
  Qed.

  Lemma gquot_prod_in_out_sect : Sect gquot_prod_in gquot_prod_out.
  Proof.
    intros [x₁ x₂].
    revert x₁ x₂.
    simple refine (gquot_double_ind_set _ _ _).
    - reflexivity.
    - intros a b₁ b₂ g.
      apply map_path_over.
      refine (whisker_square idpath _ (ap_pair_r _ _)^ idpath (vrefl _)).
      refine (_ @ _ @ _ @ _)^.
      * exact (ap_compose (fun z => gquot_prod_in (gcl G₁ a,z)) gquot_prod_out (gcleq G₂ g)).
      * apply ap.
        refine (ap_compose _ _ _ @ _).
        apply gquot_double_rec_beta_r_gcleq.
      * exact (gquot_rec_beta_gcleq (prod_groupoid G₁ G₂)
                                    _ _ _ _ _ _ _
                                    (a, b₁) (a, b₂) (e a, g)).
      * exact (ap (fun z => path_prod' z (gcleq G₂ g)) (ge G₁ a)).
    - intros a₁ a₂ b g.
      apply map_path_over.
      refine (whisker_square idpath _ (ap_pair_l _ _)^ idpath (vrefl _)).
      refine (_ @ _ @ _ @ _)^.
      * exact (ap_compose (fun z => gquot_prod_in (z,gcl G₂ b)) gquot_prod_out (gcleq G₁ g)).
      * apply ap.
        refine (ap_compose _ _ _ @ _).
        apply gquot_double_rec_beta_l_gcleq.
      * exact (gquot_rec_beta_gcleq (prod_groupoid G₁ G₂)
                                    _ _ _ _ _ _ _
                                    (a₁, b) (a₂, b) (g, e b)).
      * exact (ap (path_prod' (gcleq G₁ g)) (ge G₂ b)).
  Qed.

  Global Instance gquot_prod_in_isequiv : IsEquiv gquot_prod_in
    := isequiv_adjointify _ gquot_prod_out gquot_prod_out_in_sect gquot_prod_in_out_sect.

  Definition gquot_prod : (gquot G₁ * gquot G₂) <~> gquot (prod_groupoid G₁ G₂) :=
    BuildEquiv _ _ gquot_prod_in _.
End gquot_prod.
