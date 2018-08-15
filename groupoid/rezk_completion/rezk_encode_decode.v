Require Import HoTT.
Require Import Category.
From GR.basics Require Import general path_over globe_over square.
From GR Require Export
     groupoid.rezk_completion.rezk
     groupoid.rezk_completion.rezk_principles.

(** * Encode-decode method for characterizing the path space of [gquot G]. *)
Section encode_decode.
  Variable (C : PreCategory).
  Context `{Univalence}.

  Local Open Scope category.

  (** First, we shall lift the hom set of [G] to a set relation of [gquot G].
      For that, we need an equivalence between [hom G a₁ b] and [hom G a₂ b] (given a morphism [hom G a₁ a₂]),
      and another one between [hom G a b₁] and [hom G a b₂] (given a morphism [hom G b₁ b₂]).
      Those are the [left_action] and the [right_action], resp.
   *)
  Definition right_action
        {x₁ x₂ : C} (y : C)
        (f : x₁ <~=~> x₂)
    : x₁ <~=~> y -> x₂ <~=~> y
    := fun h => isomorphic_trans (isomorphic_sym f) h.

  Definition right_action_inv
             {x₁ x₂ : C} (y : C)
             (f : x₁ <~=~> x₂)
    : x₂ <~=~> y -> x₁ <~=~> y
    := fun h => isomorphic_trans f h.

  Definition right_action_sect
             {x₁ x₂ : C} (y : C)
             (f : x₁ <~=~> x₂)
    : Sect (right_action_inv y f) (right_action y f).
  Proof.
    intros h. 
    apply path_isomorphic ; cbn.
    rewrite associativity.
    rewrite right_inverse.
    apply right_identity.
  Qed.

  Definition right_action_inv_sect
             {x₁ x₂ : C} (y : C)
             (f : x₁ <~=~> x₂)
    : Sect (right_action y f) (right_action_inv y f).
  Proof.
    intros h. 
    apply path_isomorphic ; cbn.
    rewrite associativity.
    rewrite left_inverse.
    apply right_identity.
  Qed.

  Global Instance right_action_equiv
         {x₁ x₂ : C} (y : C)
         (f : x₁ <~=~> x₂)
    : IsEquiv (right_action y f).
  Proof.
    simple refine (isequiv_adjointify _ (right_action_inv y f) _ _).
    - apply right_action_sect.
    - apply right_action_inv_sect.
  Defined.

  Definition left_action
        (x : C) {y₁ y₂ : C}
        (f : y₁ <~=~> y₂)
    : x <~=~> y₁ -> x <~=~> y₂
    := fun h => isomorphic_trans h f.

  Definition left_action_inv
             (x : C) {y₁ y₂ : C}
             (f : y₁ <~=~> y₂)
    : x <~=~> y₂ -> x <~=~> y₁
    := fun h => isomorphic_trans h (isomorphic_sym f).

  Definition left_action_sect
             (x : C) {y₁ y₂ : C}
             (f : y₁ <~=~> y₂)
    : Sect (left_action_inv x f) (left_action x f).
  Proof.
    intros h.
    apply path_isomorphic ; cbn.
    rewrite <- associativity.
    rewrite right_inverse.
    apply left_identity.
  Qed.

  Definition left_action_inv_sect
             (x : C) {y₁ y₂ : C}
             (f : y₁ <~=~> y₂)
    : Sect (left_action x f) (left_action_inv x f).
  Proof.
    intros h.
    apply path_isomorphic ; cbn.
    rewrite <- associativity.
    rewrite left_inverse.
    apply left_identity.
  Qed.

  Global Instance left_action_equiv (x : C) {y₁ y₂ : C} (f : y₁ <~=~> y₂)
    : IsEquiv (left_action x f).
  Proof.
    simple refine (isequiv_adjointify _ (left_action_inv x f) _ _).
    - apply left_action_sect.
    - apply left_action_inv_sect.
  Defined.

  (** The action of the unit element is the identity. *)
  Definition left_action_refl (x y : C)
    : left_action x (isomorphic_refl C y) == idmap.
  Proof.
    intro z.
    apply path_isomorphic ; cbn.
    apply left_identity.
  Qed.

  Definition right_action_refl (x y : C)
    : right_action y (isomorphic_refl C x) == idmap.
  Proof.
    intro z.
    apply path_isomorphic ; cbn.
    apply right_identity.
  Qed.

  Definition left_action_trans
             {y₁ y₂ y₃ : C}
             (x : C)
             (g₃ : x <~=~> y₁)
             (g₂ : y₂ <~=~> y₃)
             (g₁ : y₁ <~=~> y₂)
    : left_action x (isomorphic_trans g₁ g₂) g₃
      =
      left_action x g₂ (left_action x g₁ g₃).
  Proof.
    apply path_isomorphic ; cbn.
    rewrite associativity.
    reflexivity.
  Qed.

  Definition right_action_trans
             {x₁ x₂ x₃ : C}
             (y : C)
             (g₂ : x₂ <~=~> x₃)
             (g₁ : x₁ <~=~> x₂)
             (g₃ : x₁ <~=~> y)
    : right_action y (isomorphic_trans g₁ g₂) g₃
      =
      right_action y g₂ (right_action y g₁ g₃).
  Proof.
    apply path_isomorphic ; cbn.
    rewrite associativity.
    reflexivity.
  Qed.

  Definition right_left
             {x₁ x₂ y₁ y₂ : C}
             (g₁ : x₁ <~=~> x₂)
             (g₂ : y₁ <~=~> y₂)
             (g₃ : x₁ <~=~> y₁)
    : right_action y₂ g₁ (left_action x₁ g₂ g₃)
      =
      left_action x₂ g₂ (right_action y₁ g₁ g₃).
  Proof.
    apply path_isomorphic ; cbn.
    rewrite associativity.
    reflexivity.
  Qed.

  (** The lift of [hom G] to [gquot G]. *)
  Definition r_fam : rezk C -> rezk C -> hSet
    := rezk_relation
         C
         C
         (fun x y => BuildhSet (x <~=~> y))
         (@right_action)
         (@left_action)
         (fun _ _ => right_action_refl _ _)
         (fun _ _ _ _ _ _ _ => right_action_trans _ _ _ _)
         (fun _ _ => left_action_refl _ _)
         (fun _ _ _ _ _ _ _ => left_action_trans _ _ _ _)
         (fun _ _ _ _ _ _ => right_left _ _).

  (** The computation rules of [g_fam] for the paths. *)
  Time Definition r_fam_l_rcleq
             {x₁ x₂ : C} (y : C) (f : x₁ <~=~> x₂)
    : ap (fun z => r_fam z (rcl C y)) (rcleq C f)
      =
      path_hset (BuildEquiv _ _ (right_action y f) (right_action_equiv y f))
    := rezk_relation_beta_l_rcleq C
                                  C
                                  (fun x y => BuildhSet (x <~=~> y))
                                  (@right_action)
                                  (@left_action)
                                  _ _ _ _ _ _ f.

  Definition r_fam_r_rcleq
             (x : C) {y₁ y₂ : C} (f : y₁ <~=~> y₂)
    : ap (r_fam (rcl C x)) (rcleq C f)
      =
      path_hset (BuildEquiv _ _ (left_action x f) _)
    := rezk_relation_beta_r_rcleq C
                                  C
                                  (fun x y => BuildhSet (x <~=~> y))
                                  (@right_action)
                                  (@left_action)
                                  _ _ _ _ _ _ f.

  Local Instance r_fam_hset (x y : rezk C) : IsHSet (r_fam x y)
    := istrunc_trunctype_type _.

  (** The relation [g_fam] is reflexive. *)
  Definition r_fam_refl_help
             {x₁ x₂ : C}
             (f : x₁ <~=~> x₂)
    : path_over (fun x : rezk C => r_fam x x)
                (rcleq C f)
                (isomorphic_refl C x₁)
                (isomorphic_refl C x₂).
  Proof.
    apply path_to_path_over.
    refine (transport_idmap_ap_set
              (fun x => r_fam x x)
              (rcleq C f)
              (isomorphic_refl C x₁)  @ _).
    refine (ap (fun z => transport _ z _) (_ @ _ @ _) @ _).
    + exact (ap_diag2 r_fam (rcleq C f)).
    + refine (ap (fun z => z @ _) (r_fam_r_rcleq x₁ f) @ _).
      exact (ap (fun z => _ @ z) (r_fam_l_rcleq x₂ f)).
    + exact (path_trunctype_pp _ _)^.
    + refine (transport_path_hset _ _ @ _).
      apply path_isomorphic ; cbn.
      rewrite right_identity, right_inverse.
      reflexivity.
  Qed.
  
  Definition r_fam_refl : forall (x : rezk C), r_fam x x.
  Proof.
    simple refine (rezk_ind_set (fun x => r_fam x x) _ _ _).
    - intros x.
      exact (isomorphic_refl C x).
    - intros x₁ x₂ f.
      apply r_fam_refl_help.
  Defined.

  (** Now we can define the encode function. *)
  Definition encode_rezk (x y : rezk C) : x = y -> r_fam x y :=
    fun p => transport (r_fam x) p (r_fam_refl x).

  Local Instance r_fam_eq_hset x y : IsHSet (r_fam x y -> x = y).
  Proof.
    apply trunc_forall.
  Defined.

  Opaque r_fam r_fam_refl.

  Definition decode_rezl_help₁
             (x : C)
             {y₁ y₂ : C}
             (g : y₁ <~=~> y₂)
    : path_over
        (fun z : rezk C => r_fam (rcl C x) z -> (rcl C x) = z) 
        (rcleq C g)
        (fun (f : r_fam (rcl C x) (rcl C y₁)) => rcleq C f)
        (fun (f : r_fam (rcl C x) (rcl C y₂)) => rcleq C f).
  Proof.
    simple refine (path_over_arrow _ _ _ _ _ _) ; simpl.
    intros z.
    apply map_path_over.
    refine (whisker_square idpath (ap_const _ _)^ (ap_idmap _)^ _ _).
    - refine (ap (fun z => rcleq C z) _).
      refine (_^ @ (transport_idmap_ap_set (r_fam (rcl C _)) (rcleq C g)^ z)^).
      refine (ap (fun p => transport _ p z) (ap_V _ _ @ _) @ _ @ _).
      + exact (ap inverse (r_fam_r_rcleq _ g)).
      + refine (ap (fun p => transport _ p z) _).
        exact ((path_trunctype_V (BuildEquiv _ _ (left_action _ g) (left_action_equiv _ g)))^).
      + exact (transport_path_hset _ _).
    - apply path_to_square.
      refine (concat_1p _ @ _ @ rconcat _ _ _).
      apply ap ; unfold left_action_inv.
      apply path_isomorphic.
      refine (_ @ associativity _ _ _ _ _ _ _ _).
      refine (_ @ ap (fun q => q o _)%morphism right_inverse^).
      exact (left_identity _ _ _ _)^.
  Qed.

  Definition decode_rezk_help₂
             {x₁ x₂ : C}
             (y : C)
             (g : x₁ <~=~> x₂)
    : path_over
        (fun z : rezk C => r_fam z (rcl C y) -> z = rcl C y)
        (rcleq C g)
        (fun f : r_fam (rcl C x₁) (rcl C y) => rcleq C f)
        (fun f : r_fam (rcl C x₂) (rcl C y) => rcleq C f).
  Proof.
    simple refine (path_over_arrow _ _ _ _ _ _).
    intros z ; simpl in *.
    apply map_path_over.
    refine (whisker_square idpath (ap_idmap _)^ (ap_const _ _)^ _ _).
    - refine (ap (fun z => rcleq C z) _).
      refine (_^ @ (transport_idmap_ap_set (fun z => r_fam z (rcl C _)) (rcleq C g)^ z)^).
      refine (ap (fun p => transport _ p z) (_ @ _) @ _).
      + refine (ap_V (fun z : rezk C => r_fam z (rcl C _)) (rcleq C g) @ _).
        exact (ap inverse (r_fam_l_rcleq _ g)).
      + exact ((path_trunctype_V (BuildEquiv _ _ (right_action _ g) (right_action_equiv _ g)))^).
      + exact (transport_path_hset _ _).
    - apply path_to_square ; simpl.
      exact ((rconcat _ _ _)^ @ (concat_p1 _)^).
  Qed.

  (** We can also define the decode function.
      For this we use double induction over a family of sets.
   *)
  Definition decode_rezk (x y : rezk C) : r_fam x y -> x = y.
  Proof.
    simple refine (rezk_double_ind_set (fun x y => r_fam x y -> x = y) _ _ x y).
    - intros a b f.
      exact (@rcleq C a b f).
    - intros.
      apply decode_rezl_help₁.
    - intros ; simpl.
      apply decode_rezk_help₂.
  Defined.

  (** The encode and decode maps are inverses of each other. *)
  Definition decode_gquot_encode_rezk
             {x y : rezk C}
             (p : x = y)
    : decode_rezk x y (encode_rezk x y p) = p.
  Proof.
    induction p.
    revert x.
    simple refine (rezk_ind_prop _ _ _).
    intros a ; simpl.
    exact (re _ _).
  Qed.

  Local Instance encode_gquot_decode_gquot_set (x y : rezk C)
    : IsHProp (forall (p : r_fam x y), encode_rezk x y (decode_rezk x y p) = p)
    := _.
  
  Definition encode_gquot_decode_rezk
    : forall {x y : rezk C} (p : r_fam x y), encode_rezk x y (decode_rezk x y p) = p.
  Proof.
    simple refine (rezk_double_ind_prop _ _ _).
    intros a b g.
    simpl.
    refine (transport_idmap_ap_set (fun x : rezk C => r_fam (rcl C a) x)
                                   (rcleq C g)
                                   (isomorphic_refl C a) @ _).
    refine (ap (fun p => transport _ p (isomorphic_refl C a)) (r_fam_r_rcleq a _) @ _).
    refine (transport_path_hset _ _ @ _).
    apply path_isomorphic ; cbn.
    apply right_identity.
  Qed.

  Global Instance encode_gquot_isequiv
    : forall {x y: rezk C}, IsEquiv (encode_rezk x y).
  Proof.
    intros x y.
    simple refine (isequiv_adjointify _ (decode_rezk x y) _ _).
    - intros z.
      apply encode_gquot_decode_rezk.
    - intros z.
      apply decode_gquot_encode_rezk.
  Defined.
End encode_decode.
