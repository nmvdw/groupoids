Require Import HoTT.
From GR Require Import general polynomial setoid.

(** The quotient over an setoid. *)
Definition squot (R : setoid) : Type
  := quotient (rel R).

(** The equality of `squot` is given by the setoid. *)
Definition setoid_quotient_path (R : setoid) `{Univalence}
  : forall {a₁ a₂ : under R}, class_of (rel R) a₁ = class_of (rel R) a₂ <~> rel R a₁ a₂
  := sets_exact (rel R).

(** Every `0`-type (set) can be written as a `squot`. *)
Section set_is_setoid_quotient.
  Variable (A : hSet).

  Definition squot_to_A : squot (path_setoid A) -> A
    := quotient_rec (rel (path_setoid A)) idmap (fun _ _ => idmap).

  Global Instance squot_to_A_isequiv : IsEquiv squot_to_A.
  Proof.
    simple refine (isequiv_adjointify _ (class_of (rel (path_setoid A))) _ _).
    - intros x ; reflexivity.
    - unfold Sect.
      simple refine (quotient_ind _ _ _ _).
      + reflexivity.
      + intros.
        apply path_ishprop.
  Defined.
End set_is_setoid_quotient.

(** For arbitrary types, we use a similar construction.
    However, then it gives the set truncation of that type.
 *)
Section path_setoid_quotient.
  Variable (A : Type).
    
  Definition squot_to_TA : squot (path_setoid_type A) -> Trunc 0 A.
  Proof.
    simple refine (quotient_rec _ tr _).
    cbn ; intros x y H.
    simple refine (Trunc_rec _ H).
    exact (ap tr).
  Defined.

  Global Instance squot_to_TA_isequiv : IsEquiv squot_to_TA.
  Proof.
    simple refine (isequiv_adjointify _ _ _ _).
    - intros x.
      simple refine (Trunc_rec _ x).
      apply class_of.
    - unfold Sect.
      simple refine (Trunc_ind _ _) ; reflexivity.
    - unfold Sect.
      simple refine (quotient_ind _ _ _ _).
      + reflexivity.
      + intros.
        apply path_ishprop.
  Defined.
End path_setoid_quotient.

(** Taking the setoid quotient commutes with sums. *)
Section squot_sum.
  Variable (R₁ : setoid) (R₂ : setoid).

  Definition squot_sum_in
             (z : squot R₁ + squot R₂)
    : squot (sum_setoid R₁ R₂).
  Proof.
    destruct z as [z | z].
    - simple refine (quotient_rec _ _ _ z).
      + exact (fun a => class_of _ (inl a)).
      + intros a₁ a₂ p ; cbn in *.
        apply related_classes_eq ; assumption.
    - simple refine (quotient_rec _ _ _ z).
      + exact (fun a => class_of _ (inr a)).
      + intros b₁ b₂ p ; cbn in *.
        apply related_classes_eq ; assumption.
  Defined.

  Definition squot_sum_out
    : squot (sum_setoid R₁ R₂) -> squot R₁ + squot R₂.
  Proof.
    simple refine (quotient_rec _ _ _).
    - intros [z | z].
      + exact (inl(class_of _ z)).
      + exact (inr(class_of _ z)).
    - intros [x | x] [y | y] r ; try contradiction
      ; apply ap ; apply related_classes_eq ; assumption.
  Defined.

  Lemma squot_sum_out_in_sect : Sect squot_sum_out squot_sum_in.
  Proof.
    unfold Sect.
    simple refine (quotient_ind _ _ _ _).
    - intros [z | z] ; reflexivity.
    - intros ; apply path_ishprop.
  Defined.

  Lemma squot_sum_in_out_sect : Sect squot_sum_in squot_sum_out.
  Proof.
    intros [x | x] ; revert x.
    - simple refine (quotient_ind _ _ _ _).
      + intros ; reflexivity.
      + intros ; apply path_ishprop.
    - simple refine (quotient_ind _ _ _ _).
      + intros ; reflexivity.
      + intros ; apply path_ishprop.
  Defined.

  Global Instance squot_sum_out_isequiv : IsEquiv squot_sum_out
    := isequiv_adjointify _ squot_sum_in squot_sum_in_out_sect squot_sum_out_in_sect.
End squot_sum.

(** Taking the setoid quotient commutes with products (assuming function extensionality. *)
Section squot_prod.
  Variable (R₁ : setoid) (R₂ : setoid).
  Context `{Funext}.

  Definition squot_prod_in
             (z : squot R₁ * squot R₂)
    : squot (prod_setoid R₁ R₂).
  Proof.
    destruct z as [z₁ z₂]. revert z₁ z₂.
    simple refine (quotient_rec _ _ _).
    - intros a.
      simple refine (quotient_rec _ _ _).
      + intros b.
        exact (class_of _ (a,b)).
      + simpl ; intros b₁ b₂ p.
        apply related_classes_eq.
        exact (refl _,p).
    - simpl ; intros a₁ a₂ p₁.
      funext b. revert b.
      simple refine (quotient_ind _ _ _ _).
      + intros b ; simpl.
        apply related_classes_eq.
        exact (p₁,refl _).
      + intros ; apply path_ishprop.
  Defined.

  Definition squot_prod_out
    : squot (prod_setoid R₁ R₂) -> squot R₁ * squot R₂.
  Proof.
    simple refine (quotient_rec _ _ _).
    - exact (fun z => (class_of _ (fst z),class_of _ (snd z))).
    - simpl ; intros z₁ z₂ p.
      apply path_prod' ; apply related_classes_eq ; apply p.
  Defined.

  Lemma squot_prod_out_in_sect : Sect squot_prod_out squot_prod_in.
  Proof.
    unfold Sect.
    simple refine (quotient_ind _ _ _ _).
    - simpl ; intros [z₁ z₂] ; reflexivity.
    - intros ; apply path_ishprop.
  Defined.

  Lemma squot_prod_in_out_sect : Sect squot_prod_in squot_prod_out.
  Proof.
    intros [z₁ z₂]. revert z₁ z₂.
    simple refine (quotient_ind _ _ _ _).
    - simpl ; intros a.
      simple refine (quotient_ind _ _ _ _).
      + simpl ; intros b.
        reflexivity.
      + intros ; apply path_ishprop.
    - intros ; apply path_ishprop.
  Defined.

  Global Instance squot_prod_out_isequiv : IsEquiv squot_prod_out
    := isequiv_adjointify _ squot_prod_in squot_prod_in_out_sect squot_prod_out_in_sect.
End squot_prod.

(** Suppose that we have a polynomial `P` and a setoid `R`.
    Then we have a natural map from the quotient of `P R` to the set truncation of `P` applied to the quotient of `R`.
 *)
Definition poly_squot_to_squot
           (P : polynomial)
           (R : setoid)
  : squot (lift_setoid R P) -> Trunc 0 (poly_act P (squot R)).
Proof.
  induction P as [ | | P IHP Q IHQ | P IHP Q IHQ] ; cbn.
  - exact tr.
  - exact (squot_to_TA T).
  - exact ((Trunc_prod 0)
             o (functor_prod IHP IHQ)
             o squot_prod_out _ _).
  - exact ((Trunc_sum 0)
              o (functor_sum IHP IHQ)
              o squot_sum_out _ _).
Defined.

(** This map is an equivalence. *)
Global Instance squot_polynomial
       (Q : polynomial)
       (R : setoid) `{IsHSet (under R)}
       `{Funext}
  : IsEquiv (poly_squot_to_squot Q R).    
Proof.
  induction Q.
  - apply _.
  - apply _.
  - apply _.
  - simpl.
    refine isequiv_compose.
    apply Trunc_sum_isequiv.
    exact tt.
Defined.
(*
Section axiom_of_choice.
  Context `{Univalence}.
  
  Definition axiom_of_choice : hProp
    := BuildhProp(forall (X : hSet)
                         (A : X -> hSet)
                         (P : forall (x : X), A x -> hProp),
                     (forall (x : X), hexists (P x))
                     ->
                     merely {g : forall (x : X), A x & forall (x : X), P x (g x)}).

  Definition axiom_of_choice_rel : hProp
    := BuildhProp(forall (X Y : hSet)
                         (P : X -> Y -> hProp),
                     (forall (x : X), hexists (P x))
                     ->
                     merely {g : X -> Y & forall (x : X), P x (g x)}).

  Definition ac_vs_ac_rel
    : axiom_of_choice <~> axiom_of_choice_rel.
  Proof.
    apply equiv_iff_hprop.
    - unfold axiom_of_choice.
      intros ac X Y P HX.
      specialize (ac X (fun _ => Y)).
      apply ac.
      apply HX.
    - unfold axiom_of_choice_rel.
      intros acr X A P HX.
      specialize (acr X
                      (BuildhSet {x : X & A x})
                      (fun x a => BuildhProp((x = a.1) * P a.1 a.2))
                 ).
      cbn in acr.
      assert (forall x : X, Trunc -1 {x0 : {x0 : X & A x0} & (x = x0.1) * P x0.1 x0.2}).
      {
        intros x.
        specialize (HX x).
        strip_truncations.
        apply tr.
        destruct HX as [a Ha].
        exists (x;a) ; cbn.
        exact (idpath, Ha).
      }
      specialize (acr X0).
      strip_truncations.
      apply tr.
      destruct acr as [g Hg].
      simple refine (_;_).
      + intros x.
        exact (transport A (fst (Hg x))^ (g x).2).
      + intros x.
        pose (snd (Hg x)).
  Admitted.
  
  Definition pick_representatives : hProp
    := BuildhProp(forall (A B : hSet)
                         (R : relation B)
                         `{is_mere_relation _ R}
                         (f : A -> quotient R),
                     merely {g : A -> B & forall (x : A), class_of _ (g x) = f x}).

  Global Instance ja : forall (P : hProp), IsHProp (P + ~P).
  Admitted.

  Definition yolo : pick_representatives -> (forall (P : hProp), P + ~P).
  Proof.
    unfold pick_representatives.
    intros pick P.
    pose (R := fun b1 b2 : Bool =>
                 if b1 then (if b2 then BuildhProp Unit else P)
                 else (if b2 then P else BuildhProp Unit)).
    specialize (pick (BuildhSet Bool) (BuildhSet Bool) R _ (class_of _)).
    strip_truncations.
    destruct pick as [g Hg] ; cbn in *.
    assert (forall (x : Bool), R (g x) x).
    {
      intros x.
      specialize (Hg x).
      admit.
    }
    

  Definition pick_representatives_implies_ac
    : pick_representatives <~> axiom_of_choice.
  Proof.
    apply equiv_iff_hprop.
    - unfold pick_representatives.
      intros Hpc X A P HX.
      admit.
    - unfold axiom_of_choice.
      intros AC A B R ? f.
      apply (AC A (fun _ => B) (fun a b => BuildhProp(class_of R b = f a))).
      intros x.
      simple refine (quotient_ind _ (fun q => Trunc (-1) {x0 : B & class_of R x0 = q}) _ _ (f x)).
      + exact (fun b => tr(b;idpath)).
      + intros ; apply path_ishprop.
  Admitted.
End axiom_of_choice.

(** Taking the setoid quotient commutes with products (assuming function extensionality. *)
Section squot_fun.
  Variable (A B : Type)
           (R₁ : setoid A) (R₂ : setoid B).
  Context `{Univalence} `{IsHSet A} `{IsHSet B}.
  Variable (AC : pick_representatives).
  
  Definition squot_fun_out
    : squot (fun_setoid R₁ R₂) -> (squot R₁ -> squot R₂).
  Proof.
    simple refine (quotient_rec _ _ _).
    - intros f.
      simple refine (quotient_rec _ _ _).
      + exact (fun a => class_of _ (f.1 a)).
      + simpl ; intros a₁ a₂ p.
        apply related_classes_eq.
        apply f.2 ; assumption.
    - simpl ; intros f₁ f₂ p.
      funext x. revert x.
      simple refine (quotient_ind _ _ _ _).
      + intros a ; simpl.
        apply related_classes_eq.
        apply p.
      + intros ; apply path_ishprop.
  Defined.

  Global Instance squot_fun_out_equiv
    : IsEquiv squot_fun_out.
  Proof.
    apply isequiv_surj_emb.
    - apply BuildIsSurjection.
      intros f.
      pose (AC _ _ _ _ f) as t.
      simple refine (Trunc_rec _ t) ; clear t.
      intros t.
      simple refine (tr(_;_)).
      + apply class_of.
        destruct t as [g Hg].
        exists (g o class_of _).
        intros x₁ x₂ Hx.
        apply (setoid_quotient_path _).
        rewrite !Hg.
        apply ap.
        apply related_classes_eq.
        assumption.
      + simpl.
        funext x. revert x.
        simple refine (quotient_ind _ _ _ _).
        * intros a ; simpl.
          rewrite t.2.
          reflexivity.
        * intros ; apply path_ishprop.
    - apply isembedding_isinj_hset.
      unfold isinj.
      simple refine (quotient_ind _ _ _ _) ; simpl.
      + intros f.
        simple refine (quotient_ind _ _ _ _) ; simpl.
        * intros g Hfg.
          apply related_classes_eq.
          intros x.
          pose (ap10 Hfg (class_of _ x)) as p ; cbn in p.
          exact (setoid_quotient_path _ p).
        * intros ; apply path_ishprop.
      + intros ; apply path_ishprop.
  Defined.
  *)