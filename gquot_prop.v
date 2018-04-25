Require Import HoTT.
Require Import groupoid_quotient.
Require Import groupoid path_over globe_over general square.

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
    apply map_path_over.
    induction g ; cbn.
    refine (whisker_square idpath _ _ idpath _).
    - refine (ap_compose _ _ _ @ ap _ _)^.
      apply gquot_rec_beta_geqcl.
    - refine (ap_idmap _ @ _)^.
      apply ge.
    - exact id_square.
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
    - intros [a1 | b1] [a2 | b2] g ; try refine (Empty_rec g) ; simpl in g.
      + apply map_path_over.
        refine (whisker_square idpath _ (ap_idmap _)^ idpath (vrefl _)).
        refine (_ @ (ap_compose _ _ _)^).
        refine ((ap _ _ @ _)^).
        ** apply gquot_rec_beta_geqcl.
        ** refine ((ap_compose inl gquot_sum_in _)^ @ _).
           apply gquot_rec_beta_geqcl.
      + apply map_path_over.
        refine (whisker_square idpath _ (ap_idmap _)^ idpath (vrefl _)).
        refine (_ @ (ap_compose _ _ _)^).
        refine ((ap _ _ @ _ )^).
        ** apply gquot_rec_beta_geqcl.
        ** refine ((ap_compose inr gquot_sum_in _)^ @ _).
           apply gquot_rec_beta_geqcl.
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
          ** apply gquot_rec_beta_geqcl.
          ** apply gquot_rec_beta_geqcl.
    - simple refine (gquot_ind_set
                       (fun z => gquot_sum_out (gquot_sum_in (inr z)) = inr z) _ _ _ y).
      + exact (fun _ => idpath).
      + intros a₁ a₂ g.
        apply map_path_over.
        refine (whisker_square idpath _ idpath idpath (vrefl _)).
        refine (_ @ (ap_compose (gquot_sum_in o inr) gquot_sum_out _)^).
        refine (ap _ _ @ _)^.
        ** apply gquot_rec_beta_geqcl.
        ** apply gquot_rec_beta_geqcl.
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
    simple refine (gquot_double_rec _ _ _ _ _ _ _ _ _ _ _).
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
      apply path_to_square.
      rewrite <- !gconcat.
      apply ap ; simpl.
      rewrite !ce, !ec.
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
      apply map_path_over.
      refine (whisker_square idpath _ (ap_idmap _)^ idpath (vrefl _)).
      refine ((ap_compose _ _ _ @ ap (ap gquot_prod_in) _ @ _ @ _)^).
      * apply gquot_rec_beta_geqcl.
      * apply gquot_double_rec_beta_gcleq.
      * simpl.
        refine ((@gconcat _ (prod_groupoid G₁ G₂)
                          _ (fst x₂, snd x₁) _
                          (fst g, e (snd x₁)) (e (fst x₂), snd g))^ @ _).
        apply ap.
        exact (path_prod' (ce _ _ _ _ _) (ec _ _ _ _ _)).
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
      * exact (ap_compose (fun z => gquot_prod_in (gcl G₁ a,z)) gquot_prod_out (geqcl G₂ g)).
      * apply ap.
        refine (ap_compose _ _ _ @ _).
        apply gquot_double_rec_beta_r_gcleq.
      * exact (gquot_rec_beta_geqcl (A * B)
                                    (prod_groupoid G₁ G₂)
                                    _ _ _ _ _ _ _
                                    (a, b₁) (a, b₂) (e a, g)).
      * exact (ap (fun z => path_prod' z (geqcl G₂ g)) (ge G₁ a)).
    - intros a₁ a₂ b g.
      apply map_path_over.
      refine (whisker_square idpath _ (ap_pair_l _ _)^ idpath (vrefl _)).
      refine (_ @ _ @ _ @ _)^.
      * exact (ap_compose (fun z => gquot_prod_in (z,gcl G₂ b)) gquot_prod_out (geqcl G₁ g)).
      * apply ap.
        refine (ap_compose _ _ _ @ _).
        apply gquot_double_rec_beta_l_gcleq.
      * exact (gquot_rec_beta_geqcl _
                                    (prod_groupoid G₁ G₂)
                                    _ _ _ _ _ _ _
                                    (a₁, b) (a₂, b) (g, e b)).
      * exact (ap (path_prod' (geqcl G₁ g)) (ge G₂ b)).
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

  Definition right_action_e (a b : A) :
    right_action b (e a) == idmap.
  Proof.
    intro x.
    unfold right_action.
    rewrite inv_e.
    apply ec.
  Qed.

  Definition g_fam : gquot G -> gquot G -> hSet.
  Proof.
    simple refine (gquot_relation A A G G
                          (hom G)
                          (fun _ _ b g => right_action b g)
                          (fun a _ _ g => left_action a g)
                          _ _ _ _ _ _ _
          ).
    - intros a b ; simpl.
      apply right_action_e.
    - intros a b₁ b₂ g x ; unfold right_action ; simpl.
        by rewrite inv_involutive.
    - compute ; intros.
        by rewrite inv_prod, ca.
    - intros ; compute.
      apply ce.
    - intros ; compute.
      reflexivity.
    - compute ; intros.
      apply ca.
    - compute ; intros.
      apply ca.
  Defined.

  Definition gquot_fam_l_gcleq
             {a₁ a₂ : A} (b : A) (g : hom G a₁ a₂)
    : ap (fun z => g_fam z (gcl G b)) (geqcl G g)
      =
      path_hset (BuildEquiv _ _ (right_action b g) _)
    := gquot_relation_beta_l_gcleq A A G G (hom G) _ _ _ _ _ _ _ _ _ _ g.

  Definition gquot_fam_r_gcleq
             (a : A) {b₁ b₂ : A} (g : hom G b₁ b₂)
    : ap (g_fam (gcl G a)) (geqcl G g)
      =
      path_hset (BuildEquiv _ _ (left_action a g) _)
    := gquot_relation_beta_r_gcleq A A G G (hom G) _ _ _ _ _ _ _ _ _ _ g.

  Local Instance g_fam_hset x y : IsHSet (g_fam x y)
    := istrunc_trunctype_type _.

  Definition g_fam_refl : forall (x : gquot G), g_fam x x.
  Proof.
    simple refine (gquot_ind_set (fun x => g_fam x x) _ _ _).
    - intros a.
      exact (@e A G a).
    - intros a₁ a₂ g.
      apply path_to_path_over.
      rewrite transport_idmap_ap_set.
      rewrite (ap_diag2 g_fam (geqcl G g)).
      rewrite (gquot_fam_r_gcleq _ g).
      rewrite (gquot_fam_l_gcleq _ g).
      rewrite <- path_hset_comp.
      rewrite transport_idmap_path_hset.
      compute.
      rewrite ec, ic.
      reflexivity.
  Defined.

  Definition f (x y : gquot G) : x = y -> g_fam x y :=
    fun p => transport (g_fam x) p (g_fam_refl x).

  Local Instance g_fam_eq_hset x y : IsHSet (g_fam x y -> x = y).
  Proof.
    apply trunc_forall.
  Defined.

  Opaque g_fam.
  
  Definition finv (x y : gquot G) : g_fam x y -> x = y.
  Proof.
    simple refine (gquot_double_ind_set (fun x y => g_fam x y -> x = y) _ _ x y).
    - intros a b g.
      exact (@geqcl A G a b g).
    - intros.
      simple refine (path_over_arrow _ _ _ _ _ _).
      intros z.
      simpl in *.
      apply map_path_over.
      refine (whisker_square idpath (ap_const _ _)^ (ap_idmap _)^ _ _).
      + apply ap.
        refine (_^ @ (transport_idmap_ap_set (g_fam (gcl G a)) (geqcl G g)^ z)^).
        refine (ap (fun p => transport _ p z) (ap_V _ _ @ _) @ _ @ _).
        * exact (ap inverse (gquot_fam_r_gcleq a g)).
        * refine (ap (fun p => transport _ p z) _).
          exact ((path_hset_inv (BuildEquiv _ _ (left_action a g) (left_action_equiv a g)))^).
        * apply transport_idmap_path_hset.
      + apply path_to_square.
        refine (concat_1p _ @ _ @ gconcat _ _ _).
        apply ap.
        refine ((ce _ _ _ _ _)^ @ _ @ ca _ _ _ _ _ _ _ _ _).
        refine (ap _ _)^.
        apply ic. 
    - intros.
      simple refine (path_over_arrow _ _ _ _ _ _).
      intros z.
      simpl in *.
      apply map_path_over.
      refine (whisker_square idpath (ap_idmap _)^ (ap_const _ _)^ _ _).
      + apply ap.
        refine (_^ @ (transport_idmap_ap_set (fun z => g_fam z (gcl G b)) (geqcl G g)^ z)^).
        refine (ap (fun p => transport _ p z) (_ @ _) @ _).
        * refine (ap_V (fun z : gquot G => g_fam z (gcl G b)) (geqcl G g) @ _).
          exact (ap inverse (gquot_fam_l_gcleq b g)).
        * exact ((path_hset_inv (BuildEquiv _ _ (right_action b g) (right_action_equiv b g)))^).
        * apply transport_idmap_path_hset.
      + apply path_to_square.
        exact ((gconcat _ _ _)^ @ (concat_p1 _)^).
  Defined.

  Definition finv_f
             {x y : gquot G}
             (p : x = y)
    : finv x y (f x y p) = p.
  Proof.
    induction p.
    revert x.
    simple refine (gquot_ind_set _ _ _ _).
    - intros a.
      apply ge.
    - intros a₁ a₂ g.
      cbn.
      apply path_to_path_over.
      admit.
  Admitted.

  Local Instance f_finv_set (x y : gquot G)
    : IsHSet (forall (p : g_fam x y), f x y (finv x y p) = p).
  Proof.
    apply (@trunc_forall _ (g_fam x y) (fun p => f x y (finv x y p) = p) 0).
    intros a.
    apply (@trunc_succ (-1) (f x y (finv x y a) = a)).
    apply _.
  Defined.
  
  Definition f_finv
    : forall {x y : gquot G} (p : g_fam x y), f x y (finv x y p) = p.
  Proof.
    simple refine (gquot_double_ind_set _ _ _).
    - intros a b g.
      unfold f, g_fam_refl.
      simpl.
      refine (transport_idmap_ap_set (fun x : gquot G => g_fam (gcl G a) x)
                                     (geqcl G g)
                                     (e a) @ _).
      rewrite (gquot_fam_r_gcleq a).
      rewrite transport_idmap_path_hset.
      compute.
      exact (ec _ G a _ g).
    - admit.
    - admit.
  Admitted.      
End encode_decode.
